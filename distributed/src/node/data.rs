//! What the node programs of all three stacks share: the values they publish and serve, how a message carries its
//! own origin and send time, the histogram their latencies go into, and the identity every stack derives from a node's
//! name.
//!
//! Invariants: the bytes of a value are a pure function of its seed and offset, so a provider and a checker never need
//! to exchange them; a histogram merges without loss of its resolution (a bucket is within 1.6% of its values); a
//! message header that does not parse is dropped, never counted.

use std::collections::BTreeMap;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

/// The wall clock in nanoseconds since the epoch. The nodes of one machine share it, which is what lets a delivery
/// latency be read off a header the sender wrote.
pub fn wall_ns() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_nanos()).unwrap_or(u64::MAX))
}

/// A deterministic byte string of `len` bytes for a node and a purpose: the same name gives every stack, and every
/// process, the same keys, so a node needs no table of its peers' identities from the orchestrator.
pub fn seed_bytes(name: &str, purpose: &str, len: usize) -> Vec<u8> {
    // FNV-1a over name and purpose, then SplitMix64 to fill: stable across runs and builds, not a secret.
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in purpose.bytes().chain([0]).chain(name.bytes()) {
        h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
    }
    let mut out = Vec::with_capacity(len);
    while out.len() < len {
        h = h.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = h;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        out.extend_from_slice(&z.to_le_bytes());
    }
    out.truncate(len);
    out
}

/// A 32-byte seed for `name` and `purpose`.
pub fn seed32(name: &str, purpose: &str) -> [u8; 32] {
    let mut s = [0u8; 32];
    s.copy_from_slice(&seed_bytes(name, purpose, 32));
    s
}

/// Item `i` of the set made from `seed`: 32 bytes, distinct for distinct (seed, i).
pub fn item(seed: u64, i: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut s = seed ^ i.wrapping_mul(0xD6E8_FEB8_6659_FD93);
    for chunk in out.chunks_mut(8) {
        s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        chunk.copy_from_slice(&z.to_le_bytes());
    }
    out
}

/// Bytes of the repeating block a value is made of.
const BLOCK: usize = 1 << 20;

/// The bytes of a value: pseudo-random, generated from a seed at any offset, so a 256 MiB value needs one megabyte.
#[derive(Debug, Clone)]
pub struct Content {
    len: u64,
    base: std::sync::Arc<Vec<u8>>,
}

impl Content {
    /// A value of `len` bytes made from `seed`.
    pub fn new(seed: u64, len: u64) -> Self {
        let mut base = vec![0u8; BLOCK];
        let mut s = seed;
        for chunk in base.chunks_mut(8) {
            s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^= z >> 31;
            let n = chunk.len();
            chunk.copy_from_slice(z.to_le_bytes().get(..n).unwrap_or(&[]));
        }
        Self {
            len,
            base: std::sync::Arc::new(base),
        }
    }

    /// Its length.
    pub const fn len(&self) -> u64 {
        self.len
    }

    /// Whether it has no bytes.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Copy the bytes at `off` into `dst`, clipped to the end; returns how many.
    // A block offset is below 1 MiB and a length below usize.
    #[allow(clippy::cast_possible_truncation)]
    pub fn fill(&self, off: u64, dst: &mut [u8]) -> usize {
        let n = dst
            .len()
            .min(usize::try_from(self.len.saturating_sub(off)).unwrap_or(usize::MAX));
        let mut done = 0;
        while done < n {
            let at = off + done as u64;
            let (blk, within) = (at / BLOCK as u64, (at % BLOCK as u64) as usize);
            let take = (n - done).min(BLOCK - within);
            let (Some(d), Some(s)) = (dst.get_mut(done..done + take), self.base.get(within..within + take)) else {
                break;
            };
            d.copy_from_slice(s);
            // The first 8 bytes of every block carry its number, so no two blocks are equal and a tree over the value
            // has no repeated subtree to take a shortcut on.
            for (q, byte) in blk.to_le_bytes().iter().enumerate() {
                if let Some(x) = (q >= within && q < within + take)
                    .then(|| d.get_mut(q - within))
                    .flatten()
                {
                    *x = *byte;
                }
            }
            done += take;
        }
        n
    }
}

/// Magic of a workload message.
const MAGIC: u16 = 0xD157;
/// Bytes of the header of a workload message.
pub const HEADER: usize = 16;

/// The header of a workload message: who sent it, which of the sender's messages it is, and when.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    /// The sender's index in the scenario's node list.
    pub origin: u16,
    /// The sender's message number from 0.
    pub seq: u32,
    /// The sender's wall clock at publication, in nanoseconds.
    pub sent_ns: u64,
}

impl Header {
    /// A body of `size` bytes (at least [`HEADER`]) that starts with this header.
    pub fn body(&self, size: usize) -> Vec<u8> {
        let mut b = vec![0xA5u8; size.max(HEADER)];
        let head = [
            MAGIC.to_be_bytes().as_slice(),
            &self.origin.to_be_bytes(),
            &self.seq.to_be_bytes(),
            &self.sent_ns.to_be_bytes(),
        ]
        .concat();
        if let Some(dst) = b.get_mut(..HEADER) {
            dst.copy_from_slice(&head);
        }
        b
    }

    /// The header at the start of `body`, if it has one.
    pub fn parse(body: &[u8]) -> Option<Self> {
        let (magic, rest) = body.split_first_chunk::<2>()?;
        let (origin, rest) = rest.split_first_chunk::<2>()?;
        let (seq, rest) = rest.split_first_chunk::<4>()?;
        let (sent, _) = rest.split_first_chunk::<8>()?;
        (u16::from_be_bytes(*magic) == MAGIC).then(|| Self {
            origin: u16::from_be_bytes(*origin),
            seq: u32::from_be_bytes(*seq),
            sent_ns: u64::from_be_bytes(*sent),
        })
    }
}

/// Sub-buckets per octave, as a power of two: 64, so a bucket is within 1.6% of its values.
const SUB_BITS: u32 = 6;

/// A histogram of positive integers (latencies in microseconds) with a bounded number of buckets, mergeable.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hist {
    /// Bucket index to count; only buckets that were hit.
    buckets: BTreeMap<u32, u64>,
    count: u64,
}

impl Hist {
    fn index(v: u64) -> u32 {
        if v < (1 << SUB_BITS) {
            return u32::try_from(v).unwrap_or(0);
        }
        let e = v.ilog2();
        let sub = u32::try_from((v >> (e - SUB_BITS)) & ((1 << SUB_BITS) - 1)).unwrap_or(0);
        (e - SUB_BITS + 1) * (1 << SUB_BITS) + sub
    }

    fn lower(idx: u32) -> u64 {
        if idx < (1 << SUB_BITS) {
            return u64::from(idx);
        }
        let e = idx / (1 << SUB_BITS) + SUB_BITS - 1;
        let sub = u64::from(idx % (1 << SUB_BITS));
        ((1u64 << SUB_BITS) + sub) << (e - SUB_BITS)
    }

    /// Count one value.
    pub fn add(&mut self, v: u64) {
        *self.buckets.entry(Self::index(v)).or_insert(0) += 1;
        self.count += 1;
    }

    /// How many values.
    pub const fn count(&self) -> u64 {
        self.count
    }

    /// Add every value of `other`.
    pub fn merge(&mut self, other: &Self) {
        for (k, c) in &other.buckets {
            *self.buckets.entry(*k).or_insert(0) += c;
        }
        self.count += other.count;
    }

    /// The value below which `q` (0 to 1) of the values fall, as the middle of its bucket; none when empty.
    // A rank of a count that fits an f64.
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss
    )]
    pub fn quantile(&self, q: f64) -> Option<f64> {
        if self.count == 0 {
            return None;
        }
        let rank = ((q.clamp(0.0, 1.0) * self.count as f64).ceil() as u64).max(1);
        let mut seen = 0;
        for (k, c) in &self.buckets {
            seen += c;
            if seen >= rank {
                let lo = Self::lower(*k);
                let hi = Self::lower(*k + 1);
                return Some(f64::midpoint(lo as f64, hi as f64));
            }
        }
        None
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn content_is_a_pure_function_of_seed_and_offset() {
        let c = Content::new(7, 5 << 20);
        let mut whole = vec![0u8; 3 << 20];
        assert_eq!(c.fill(0, &mut whole), whole.len());
        // Reading in odd pieces gives the same bytes.
        let mut pieced = vec![0u8; whole.len()];
        let mut at = 0;
        for step in [1usize, 7, 4093, 1 << 20, 65_537].iter().cycle() {
            if at >= pieced.len() {
                break;
            }
            let end = (at + step).min(pieced.len());
            assert_eq!(c.fill(at as u64, &mut pieced[at..end]), end - at);
            at = end;
        }
        assert_eq!(whole, pieced);
        // Blocks differ, and the end is clipped.
        assert_ne!(whole[..4096], whole[1 << 20..(1 << 20) + 4096]);
        let mut tail = [0u8; 100];
        assert_eq!(c.fill((5 << 20) - 40, &mut tail), 40);
        let (mut a, mut b) = ([0u8; 64], [0u8; 64]);
        Content::new(7, 1 << 20).fill(0, &mut a);
        Content::new(8, 1 << 20).fill(0, &mut b);
        assert_ne!(a[8..], b[8..]);
    }

    #[test]
    fn headers_round_trip_and_short_bodies_are_not_headers() {
        let h = Header {
            origin: 513,
            seq: 70_000,
            sent_ns: 1_700_000_000_123_456_789,
        };
        assert_eq!(Header::parse(&h.body(16)), Some(h));
        assert_eq!(Header::parse(&h.body(1000)), Some(h));
        assert_eq!(h.body(3).len(), HEADER);
        assert_eq!(Header::parse(&[0; 15]), None);
        assert_eq!(Header::parse(&[0; 64]), None);
    }

    #[test]
    fn a_histogram_keeps_quantiles_within_its_resolution_and_merges() {
        let mut h = Hist::default();
        for v in 1..=10_000u64 {
            h.add(v * 10);
        }
        let p50 = h.quantile(0.5).unwrap();
        let p99 = h.quantile(0.99).unwrap();
        assert!((p50 - 50_000.0).abs() / 50_000.0 < 0.02, "{p50}");
        assert!((p99 - 99_000.0).abs() / 99_000.0 < 0.02, "{p99}");
        let (mut a, mut b) = (Hist::default(), Hist::default());
        for v in 1..=5000u64 {
            a.add(v * 10);
            b.add((v + 5000) * 10);
        }
        a.merge(&b);
        assert_eq!(a, h);
        assert_eq!(Hist::default().quantile(0.5), None);
        let mut small = Hist::default();
        for v in [3, 3, 9] {
            small.add(v);
        }
        assert!((small.quantile(0.5).unwrap() - 3.5).abs() < 1e-9);
    }

    #[test]
    fn set_items_differ_by_seed_and_index() {
        assert_eq!(item(1, 5), item(1, 5));
        assert_ne!(item(1, 5), item(1, 6));
        assert_ne!(item(1, 5), item(2, 5));
    }

    #[test]
    fn seeds_are_stable_and_differ_by_name_and_purpose() {
        assert_eq!(seed32("a-1", "x"), seed32("a-1", "x"));
        assert_ne!(seed32("a-1", "x"), seed32("a-2", "x"));
        assert_ne!(seed32("a-1", "x"), seed32("a-1", "y"));
        assert_eq!(seed_bytes("n", "p", 5).len(), 5);
    }
}
