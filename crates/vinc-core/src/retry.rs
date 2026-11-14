//! Address validation that keeps no state: the retry token.
//!
//! A first flight that the half-open cap refuses is answered with a retry packet ([`LongType::Retry`]) instead of
//! silence. Its token is the second it was made (4 bytes, big-endian) and a 16-byte tag: the BLAKE3 keyed hash, under
//! a key the endpoint draws once at random, of that second, the address the flight came from and the id the dialer
//! chose. The dialer sends its flight again at once behind the token. A token whose tag matches for that flight's
//! address and id, and which is at most [`TOKEN_LIFE_S`] seconds old, shows that the address hears this endpoint, so
//! `rx.rs` admits the flight past the cap and leaves it out of the count, as it does a resumption. The session is
//! still unauthenticated: it lives `HALF_OPEN_LIFE` and takes a slot of the table, which bounds it.
//!
//! Invariants: nothing is held per peer. A retry waits in a ring of at most [`RETRIES`] entries until `poll_transmit`
//! sends it through the ledger, which keeps what an address is sent within three times what it sent; a full ring
//! takes no more, and that dialer resends on its own timer. The key is drawn the first time the cap refuses a flight,
//! so an endpoint that never reaches its cap draws nothing; while no key is drawn (or the randomness failed) no retry
//! is sent and no token opens.

use core::net::SocketAddr;

use vinc_crypto::{Drbg, ct_eq, extract};
use vinc_security::ConnId;
use vinc_transport::packet::{LongHeader, LongType, RETRY_TOKEN_LEN};
use vinc_wire::Writer;

/// The most retries waiting to be sent.
pub const RETRIES: usize = 32;
/// How long a token opens after the second it was made, in seconds.
pub const TOKEN_LIFE_S: u32 = 10;
/// The bytes of the tag.
const TAG_LEN: usize = 16;
/// The bytes of the made-at second.
const AT_LEN: usize = RETRY_TOKEN_LEN - TAG_LEN;

/// A retry to send: from where to where, the ids it names and the second its token is made at.
#[derive(Debug, Clone, Copy)]
struct Pending {
    local: SocketAddr,
    remote: SocketAddr,
    /// The dialer's own id, the retry's destination.
    dcid: ConnId,
    /// The id the dialer chose for this endpoint.
    odcid: ConnId,
    at: u32,
}

/// The key and the retries waiting to leave, oldest at `head`.
pub(crate) struct Retries {
    key: Option<[u8; 32]>,
    ring: [Option<Pending>; RETRIES],
    head: usize,
    len: usize,
}

/// The second of the endpoint's clock `now` (nanoseconds), wrapping every 136 years.
#[allow(
    clippy::cast_possible_truncation,
    reason = "the second wraps on purpose; a token lives seconds"
)]
const fn second(now: u64) -> u32 {
    (now / 1_000_000_000) as u32
}

/// The tag of a token made at second `at` for a flight from `remote` naming `odcid` (`None` only if the fields did not
/// fit, which no id of at most 20 bytes does).
fn tag(key: &[u8; 32], at: u32, remote: &SocketAddr, odcid: &ConnId) -> Option<[u8; TAG_LEN]> {
    // 4 + 1 + 16 + 2 + 1 + 20 bytes at most; the family byte and the id's length keep the fields apart.
    let mut m = [0u8; 48];
    let mut w = Writer::new(&mut m);
    let (family, ip) = match remote {
        SocketAddr::V4(a) => (4, a.ip().to_ipv6_mapped().octets()),
        SocketAddr::V6(a) => (6, a.ip().octets()),
    };
    let id = odcid.as_bytes();
    let ok = w.put_slice(&at.to_be_bytes()).is_ok()
        && w.put_u8(family).is_ok()
        && w.put_slice(&ip).is_ok()
        && w.put_slice(&remote.port().to_be_bytes()).is_ok()
        && u8::try_from(id.len()).is_ok_and(|n| w.put_u8(n).is_ok())
        && w.put_slice(id).is_ok();
    if !ok {
        return None;
    }
    let mut out = [0u8; TAG_LEN];
    for (o, b) in out.iter_mut().zip(extract(key, w.written())) {
        *o = b;
    }
    Some(out)
}

impl Retries {
    /// No key and no retry waiting.
    pub(crate) const fn new() -> Self {
        Self {
            key: None,
            ring: [None; RETRIES],
            head: 0,
            len: 0,
        }
    }

    /// Draw the key from `drbg` if there is none yet. Returns whether there is one.
    pub(crate) fn keyed(&mut self, drbg: &mut Drbg) -> bool {
        if self.key.is_none() {
            let mut k = [0u8; 32];
            self.key = drbg.fill(&mut k).is_ok().then_some(k);
        }
        self.key.is_some()
    }

    /// Whether the ring takes no more retries until one is sent.
    pub(crate) const fn full(&self) -> bool {
        self.len == RETRIES
    }

    /// How many retries wait.
    pub(crate) const fn waiting(&self) -> usize {
        self.len
    }

    /// Queue a retry for a first flight that came from `remote` to `local` with the dialer's id `dcid` and the id it
    /// chose, `odcid`. Returns whether it was queued: not with no key or a full ring.
    pub(crate) fn push(
        &mut self,
        now: u64,
        local: SocketAddr,
        remote: SocketAddr,
        dcid: ConnId,
        odcid: ConnId,
    ) -> bool {
        if self.key.is_none() || self.full() {
            return false;
        }
        let at = (self.head + self.len) % RETRIES;
        let Some(cell) = self.ring.get_mut(at) else {
            return false;
        };
        *cell = Some(Pending {
            local,
            remote,
            dcid,
            odcid,
            at: second(now),
        });
        self.len += 1;
        true
    }

    /// Write the oldest waiting retry into `out` and take it off the ring: its local and remote address and its
    /// length. `None` when none waits or `out` cannot hold it (it is dropped then; the dialer resends).
    pub(crate) fn pop(&mut self, out: &mut [u8]) -> Option<(SocketAddr, SocketAddr, usize)> {
        if self.len == 0 {
            return None;
        }
        let p = self.ring.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % RETRIES;
        self.len -= 1;
        let (p, key) = (p?, self.key.as_ref()?);
        let mut token = [0u8; RETRY_TOKEN_LEN];
        let (at, t) = token.split_at_mut(AT_LEN);
        at.copy_from_slice(&p.at.to_be_bytes());
        t.copy_from_slice(&tag(key, p.at, &p.remote, &p.odcid)?);
        let header = LongHeader {
            ty: LongType::Retry,
            dcid: p.dcid,
            scid: p.odcid,
            body_len: RETRY_TOKEN_LEN,
        };
        let mut w = Writer::new(out);
        (header.write(&mut w, 0).is_ok() && w.put_slice(&token).is_ok()).then(|| (p.local, p.remote, w.written().len()))
    }

    /// Whether `token` opens for a first flight from `remote` naming `odcid` at `now`: this endpoint's key made it for
    /// that address and id at most [`TOKEN_LIFE_S`] seconds before (a clock that stepped back opens nothing).
    pub(crate) fn opens(&self, now: u64, remote: &SocketAddr, odcid: &ConnId, token: &[u8; RETRY_TOKEN_LEN]) -> bool {
        let Some(key) = self.key.as_ref() else { return false };
        let (at, t) = token.split_at(AT_LEN);
        let Ok(at) = <[u8; AT_LEN]>::try_from(at).map(u32::from_be_bytes) else {
            return false;
        };
        second(now).wrapping_sub(at) <= TOKEN_LIFE_S && tag(key, at, remote, odcid).is_some_and(|want| ct_eq(t, &want))
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::indexing_slicing)]

    use super::*;

    const S: u64 = 1_000_000_000;

    fn keyed(seed: u8) -> Retries {
        let mut r = Retries::new();
        assert!(r.keyed(&mut Drbg::new(&[seed; 32])));
        r
    }

    fn ids() -> (ConnId, ConnId) {
        (ConnId::new(&[1, 2, 3, 4]).unwrap(), ConnId::new(&[9; 8]).unwrap())
    }

    fn token_of(r: &mut Retries, now: u64, remote: SocketAddr) -> [u8; RETRY_TOKEN_LEN] {
        let (d, o) = ids();
        assert!(r.push(now, "10.0.0.1:1".parse().unwrap(), remote, d, o));
        let mut out = [0u8; 128];
        let (_, to, n) = r.pop(&mut out).unwrap();
        assert_eq!(to, remote);
        let (h, hl) = LongHeader::parse(&out[..n]).unwrap();
        assert_eq!(
            (h.ty, h.dcid, h.scid, h.body_len),
            (LongType::Retry, d, o, RETRY_TOKEN_LEN)
        );
        out[hl..n].try_into().unwrap()
    }

    #[test]
    fn a_token_opens_for_its_address_and_id_within_its_life_only() {
        let mut r = keyed(5);
        let from: SocketAddr = "10.1.2.3:9000".parse().unwrap();
        let now = 1000 * S;
        let t = token_of(&mut r, now, from);
        let (_, o) = ids();
        assert!(r.opens(now, &from, &o, &t));
        assert!(r.opens(now + u64::from(TOKEN_LIFE_S) * S, &from, &o, &t));
        assert!(
            !r.opens(now + u64::from(TOKEN_LIFE_S + 1) * S, &from, &o, &t),
            "too old"
        );
        assert!(!r.opens(now - S, &from, &o, &t), "made after now");
        assert!(!r.opens(now, &"10.1.2.3:9001".parse().unwrap(), &o, &t), "another port");
        assert!(!r.opens(now, &"10.1.2.4:9000".parse().unwrap(), &o, &t), "another host");
        assert!(!r.opens(now, &from, &ConnId::new(&[8; 8]).unwrap(), &t), "another id");
        let mut bad = t;
        bad[RETRY_TOKEN_LEN - 1] ^= 1;
        assert!(!r.opens(now, &from, &o, &bad), "a changed tag");
        let mut moved = t;
        moved[3] ^= 1;
        assert!(!r.opens(now, &from, &o, &moved), "a changed second");
        assert!(!keyed(6).opens(now, &from, &o, &t), "another endpoint's key");
        assert!(!Retries::new().opens(now, &from, &o, &t), "no key");
    }

    #[test]
    fn the_ring_holds_at_most_its_size_in_order_and_nothing_without_a_key() {
        let (d, o) = ids();
        let here: SocketAddr = "10.0.0.1:1".parse().unwrap();
        let mut r = keyed(5);
        for i in 0..RETRIES {
            assert!(r.push(0, here, ([10, 2, 0, i as u8], 7).into(), d, o));
        }
        assert!(r.full());
        assert!(
            !r.push(0, here, "10.9.9.9:7".parse().unwrap(), d, o),
            "a full ring takes no more"
        );
        let mut out = [0u8; 128];
        for i in 0..RETRIES {
            let (_, to, _) = r.pop(&mut out).unwrap();
            assert_eq!(to, ([10, 2, 0, i as u8], 7).into(), "oldest first");
        }
        assert_eq!((r.waiting(), r.pop(&mut out)), (0, None));
        let mut none = Retries::new();
        assert!(!none.push(0, here, here, d, o));
        assert_eq!(none.waiting(), 0);
    }
}
