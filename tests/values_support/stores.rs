//! Value contents, the providers' and the requester's stores, and the recording sink of the harness.
#![allow(
    dead_code,
    unreachable_pub,
    unused_imports,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::missing_panics_doc
)]

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BinaryHeap, HashMap, VecDeque};
use std::ops::Range;
use std::rc::Rc;

use vinc_dag::ranges::VerifiedRanges;
use vinc_dag::tree::{Cv, OutboardBuilder, build_outboard_vec};
use vinc_tests::SplitMix64;
use vinc_transport::stream::{StreamId, StreamSource};
use vinc_values::fetch::{Fetch, FetchSpec, In, Io};
use vinc_values::server::{Server, ServerIn};
use vinc_values::session::{Inbound, OpenError, Outbound, PeerInfo, Provider, Session};
use vinc_values::source::ValueSource;
use vinc_values::store::{StoreError, ValueRead, ValueStore};
use vinc_values::trace::{Event, Out, Trace};

pub const GROUP: u64 = 16384;
pub const MS: u64 = 1_000_000;
pub const SEC: u64 = 1_000_000_000;
pub const PACKET: usize = 1452;
pub const BLOCK: usize = 1 << 20;

// ---------------------------------------------------------------------------------------------------------------
// Content and stores
// ---------------------------------------------------------------------------------------------------------------

/// The bytes of a value: real bytes, or a pattern generated on demand so a multi-GiB value needs no memory.
#[derive(Clone)]
pub enum Content {
    Bytes(Rc<Vec<u8>>),
    Pattern { seed: u64, len: u64, base: Rc<Vec<u8>> },
}

impl Content {
    pub fn pattern(seed: u64, len: u64) -> Self {
        let mut rng = SplitMix64::new(seed);
        let mut base = vec![0u8; BLOCK];
        rng.fill(&mut base);
        Self::Pattern {
            seed,
            len,
            base: Rc::new(base),
        }
    }

    pub fn len(&self) -> u64 {
        match self {
            Self::Bytes(b) => b.len() as u64,
            Self::Pattern { len, .. } => *len,
        }
    }

    /// Copy the bytes at `off` into `dst` (clipped to the value end); returns how many.
    pub fn fill(&self, off: u64, dst: &mut [u8]) -> usize {
        let n = dst
            .len()
            .min(usize::try_from(self.len().saturating_sub(off)).unwrap_or(usize::MAX));
        match self {
            Self::Bytes(b) => dst[..n].copy_from_slice(&b[off as usize..off as usize + n]),
            Self::Pattern { base, .. } => {
                let mut done = 0;
                while done < n {
                    let at = off + done as u64;
                    let (blk, within) = (at / BLOCK as u64, (at % BLOCK as u64) as usize);
                    let take = (n - done).min(BLOCK - within);
                    dst[done..done + take].copy_from_slice(&base[within..within + take]);
                    // The first 8 bytes of every block carry the block number, so no two blocks are equal.
                    for q in within..(within + take).min(8) {
                        dst[done + q - within] = blk.to_le_bytes()[q];
                    }
                    done += take;
                }
            }
        }
        n
    }

    pub fn bytes(&self, off: u64, len: u64) -> Vec<u8> {
        let mut v = vec![0; len as usize];
        let n = self.fill(off, &mut v);
        v.truncate(n);
        v
    }
}

/// A fault a provider's store can have.
#[derive(Clone, Copy, Debug)]
pub enum Lie {
    /// Flip a bit of the byte at this value offset when read.
    FlipByte(u64),
    /// Flip a bit in every group read.
    EveryGroup,
    /// Flip a bit in the outboard pair at this byte offset.
    BadPair(u64),
}

pub struct Provided {
    pub root: Cv,
    pub content: Content,
    pub outboard: Vec<u8>,
    pub lie: Option<Lie>,
}

/// A provider's read-only store handle.
#[derive(Clone)]
pub struct PStore(pub Rc<Provided>);

impl PStore {
    pub fn bytes(data: Vec<u8>) -> Self {
        let (root, outboard) = build_outboard_vec(&data, 4).unwrap();
        Self(Rc::new(Provided {
            root,
            content: Content::Bytes(Rc::new(data)),
            outboard,
            lie: None,
        }))
    }

    pub fn pattern(seed: u64, len: u64) -> Self {
        let content = Content::pattern(seed, len);
        let mut b = OutboardBuilder::new(len, 4).unwrap();
        let mut out = vec![0u8; b.layout().outboard_size() as usize];
        let mut buf = vec![0u8; BLOCK];
        let mut off = 0;
        while off < len {
            let n = content.fill(off, &mut buf);
            b.update(&buf[..n], &mut out).unwrap();
            off += n as u64;
        }
        let root = b.finish(&mut out).unwrap();
        Self(Rc::new(Provided {
            root,
            content,
            outboard: out,
            lie: None,
        }))
    }

    pub fn random(seed: u64, len: usize) -> Self {
        let mut v = vec![0u8; len];
        SplitMix64::new(seed).fill(&mut v);
        Self::bytes(v)
    }

    /// The same value with a fault.
    pub fn lying(&self, lie: Lie) -> Self {
        Self(Rc::new(Provided {
            root: self.0.root,
            content: self.0.content.clone(),
            outboard: self.0.outboard.clone(),
            lie: Some(lie),
        }))
    }

    pub fn root(&self) -> Cv {
        self.0.root
    }

    pub fn len(&self) -> u64 {
        self.0.content.len()
    }

    pub fn content(&self) -> &Content {
        &self.0.content
    }
}

impl ValueRead for PStore {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        (*root == self.0.root).then(|| self.0.content.len())
    }

    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        if *root != self.0.root {
            return 0;
        }
        let n = self.0.content.fill(offset, dst);
        match self.0.lie {
            Some(Lie::FlipByte(at)) if (offset..offset + n as u64).contains(&at) => dst[(at - offset) as usize] ^= 1,
            Some(Lie::EveryGroup) if n > 0 => dst[0] ^= 1,
            _ => {}
        }
        n
    }

    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let (ob, off) = (&self.0.outboard, offset as usize);
        if *root != self.0.root || off > ob.len() {
            return 0;
        }
        let n = dst.len().min(ob.len() - off);
        dst[..n].copy_from_slice(&ob[off..off + n]);
        if let Some(Lie::BadPair(at)) = self.0.lie
            && (offset..offset + n as u64).contains(&at)
        {
            dst[(at - offset) as usize] ^= 1;
        }
        n
    }
}

/// The requester's store: written pieces and the verified set, with a record of every write for the checks.
#[derive(Default)]
pub struct ClientStore {
    pub pieces: BTreeMap<u64, Vec<u8>>,
    pub verified: VerifiedRanges<64>,
    pub written: u64,
    pub fail_writes: bool,
    /// Every range committed to the verified set, in order.
    pub commits: Vec<Range<u64>>,
}

impl ClientStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// A store that already holds the verified `ranges` of `content`.
    pub fn seeded(content: &Content, ranges: &[Range<u64>]) -> Self {
        let mut s = Self::new();
        for r in ranges {
            s.pieces.insert(r.start, content.bytes(r.start, r.end - r.start));
            s.verified.insert(r.clone()).unwrap();
        }
        s
    }

    pub fn covered(&self) -> u64 {
        self.verified.covered_len()
    }

    /// Every written byte equals the truth.
    pub fn assert_matches(&self, content: &Content) {
        for (off, data) in &self.pieces {
            assert_eq!(
                data.as_slice(),
                content.bytes(*off, data.len() as u64).as_slice(),
                "written bytes differ at {off}"
            );
        }
    }

    /// Every verified byte was written and equals the truth.
    pub fn assert_verified_is_true(&self, content: &Content) {
        for r in self.verified.iter() {
            let got = self.read(r.start, r.end - r.start);
            assert_eq!(
                got.as_slice(),
                content.bytes(r.start, r.end - r.start).as_slice(),
                "verified bytes wrong in {r:?}"
            );
        }
        self.assert_matches(content);
    }

    pub fn read(&self, off: u64, len: u64) -> Vec<u8> {
        let mut out = vec![0u8; len as usize];
        let mut have = vec![false; len as usize];
        for (k, d) in self.pieces.range(..off + len) {
            let (a, b) = ((*k).max(off), (*k + d.len() as u64).min(off + len));
            if a < b {
                out[(a - off) as usize..(b - off) as usize].copy_from_slice(&d[(a - k) as usize..(b - k) as usize]);
                have[(a - off) as usize..(b - off) as usize].fill(true);
            }
        }
        assert!(have.iter().all(|h| *h), "read of bytes never written");
        out
    }
}

impl ValueRead for ClientStore {
    fn servable_len(&self, _: &[u8; 32]) -> Option<u64> {
        None
    }
    fn read_at(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
        0
    }
    fn read_outboard(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
        0
    }
}

impl ValueStore for ClientStore {
    fn verified_from(&self, _: &[u8; 32], from: u64) -> Option<Range<u64>> {
        vinc_values::store::verified_after(&self.verified, from)
    }

    fn write_at(&mut self, _: &[u8; 32], offset: u64, data: &[u8]) -> Result<(), StoreError> {
        if self.fail_writes {
            return Err(StoreError::Full);
        }
        self.written += data.len() as u64;
        self.pieces.insert(offset, data.to_vec());
        Ok(())
    }

    fn commit(&mut self, _: &[u8; 32], range: Range<u64>) -> Result<(), StoreError> {
        self.verified.insert(range.clone())?;
        self.commits.push(range);
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Recording sink
// ---------------------------------------------------------------------------------------------------------------

#[derive(Default)]
pub struct Rec {
    pub events: Vec<(u64, Event)>,
    pub traces: Vec<(u64, Trace)>,
    /// Every event and trace record in the order the fetcher reported it.
    pub log: Vec<Logged>,
}

/// One item of [`Rec::log`].
#[derive(Clone, Copy, Debug)]
pub enum Logged {
    Ev(u64, Event),
    Tr(u64, Trace),
}

impl Out for Rec {
    fn event(&mut self, now: u64, ev: Event) {
        self.events.push((now, ev));
        self.log.push(Logged::Ev(now, ev));
    }
    fn trace(&mut self, now: u64, t: Trace) {
        self.traces.push((now, t));
        self.log.push(Logged::Tr(now, t));
    }
}

impl Rec {
    pub fn complete(&self) -> bool {
        self.events.iter().any(|(_, e)| matches!(e, Event::Complete))
    }

    pub fn failed(&self) -> Option<vinc_values::trace::FailReason> {
        self.events
            .iter()
            .find_map(|(_, e)| if let Event::Failed(r) = e { Some(*r) } else { None })
    }

    pub fn readable(&self) -> Vec<(u64, u64, u64)> {
        self.events
            .iter()
            .filter_map(|(t, e)| {
                if let Event::Readable { off, len } = e {
                    Some((*t, *off, *len))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn traces_of<T>(&self, f: impl Fn(&Trace) -> Option<T>) -> Vec<(u64, T)> {
        self.traces.iter().filter_map(|(t, x)| f(x).map(|v| (*t, v))).collect()
    }
}
