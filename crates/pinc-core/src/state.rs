//! Persisted state: what survives a restart.
//!
//! [`Endpoint::export_state`] writes the client tickets (the newest unexpired ones, as `pinc-security` exports them),
//! the remembered handshake round trip of each peer, and which peers are known to cache this node's prekey. After a
//! restart [`Endpoint::restore_state`] loads them back, so the first dial to a known peer resumes with 0-RTT data, waits
//! the right first resend and may use the short Initial.
//!
//! The bytes hold pre-shared keys: they are secret. The host seals them with the key store before they reach a disk and
//! zeroizes the buffer afterwards. Format, all integers big-endian: `version(1) tickets_len(4) tickets
//! krtt_count(2) { alg(1) node(32) rtt(8) } ekk_count(2) { alg(1) node(32) prekey_hash(32) }`.
//!
//! Invariants: restoring bytes that are not exactly one well-formed state changes nothing; tickets that expired by `now`
//! are not restored; a restored table never exceeds its bound.

use pinc_crypto::{IdentityAlg, NodeId};
use pinc_security::tickets::MAX_EXPORT_ENTRY_LEN;
use pinc_wire::{Reader, WireError, Writer};

use crate::endpoint::{PREKEY_PEERS, ep_impl};
use crate::rtt::PEER_RTTS;

/// The state format version.
pub const STATE_VERSION: u8 = 1;

/// Why state could not be written or read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateError {
    /// The buffer is too small; size it with [`state_len`].
    BufferTooSmall,
    /// The bytes are not one well-formed state.
    Malformed,
}

impl core::fmt::Display for StateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::BufferTooSmall => "the state buffer is too small",
            Self::Malformed => "the state bytes are malformed",
        })
    }
}

impl core::error::Error for StateError {}

impl From<WireError> for StateError {
    fn from(e: WireError) -> Self {
        match e {
            WireError::BufferTooSmall { .. } => Self::BufferTooSmall,
            _ => Self::Malformed,
        }
    }
}

/// What a restore loaded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Restored {
    /// Tickets stored.
    pub tickets: usize,
    /// Peers with a remembered round trip.
    pub peers: usize,
    /// Prekey entries read from the input: a repeated peer or an entry past the cache's size is counted too, so
    /// this can be more than the cache holds afterwards.
    pub prekeys: usize,
}

/// The buffer size that always holds the state of an endpoint with `tickets` client ticket slots.
pub const fn state_len(tickets: usize) -> usize {
    1 + 4 + 2 + tickets * MAX_EXPORT_ENTRY_LEN + 2 + PEER_RTTS * (1 + 32 + 8) + 2 + PREKEY_PEERS * (1 + 32 + 32)
}

fn node_of(r: &mut Reader<'_>) -> Result<NodeId, StateError> {
    let alg = IdentityAlg::from_tag(r.read_u8()?).ok_or(StateError::Malformed)?;
    Ok(NodeId {
        alg,
        bytes: r.read_array::<32>()?,
    })
}

ep_impl! {
    /// Write the state into `out` and return its length. See the module docs for the secrecy of the bytes.
    ///
    /// # Errors
    /// [`StateError::BufferTooSmall`] if `out` is shorter than [`state_len`] needs.
    pub fn export_state(&self, now: u64, out: &mut [u8]) -> Result<usize, StateError> {
        let (head, rest) = out.split_at_mut_checked(5).ok_or(StateError::BufferTooSmall)?;
        let n = self.tickets.export(now, CT.min(255), rest)?;
        let (version, len) = head.split_at_mut(1);
        version.copy_from_slice(&[STATE_VERSION]);
        len.copy_from_slice(&u32::try_from(n).map_err(|_| StateError::BufferTooSmall)?.to_be_bytes());
        let mut w = Writer::new(rest.get_mut(n..).ok_or(StateError::BufferTooSmall)?);
        w.put_u16(u16::try_from(self.rtt.peers().count()).map_err(|_| StateError::BufferTooSmall)?)?;
        for (node, rtt) in self.rtt.peers() {
            w.put_u8(node.alg.tag())?;
            w.put_slice(&node.bytes)?;
            w.put_u64(*rtt)?;
        }
        w.put_u16(u16::try_from(self.ekk.len()).map_err(|_| StateError::BufferTooSmall)?)?;
        for (node, hash) in self.ekk.iter() {
            w.put_u8(node.alg.tag())?;
            w.put_slice(&node.bytes)?;
            w.put_slice(hash)?;
        }
        Ok(5 + n + w.written().len())
    }

    /// Load state written by [`export_state`](Self::export_state), after the host unsealed it. Tickets that expired by
    /// `now` are skipped. Nothing is loaded if the bytes are not exactly one well-formed state.
    ///
    /// # Errors
    /// [`StateError::Malformed`].
    pub fn restore_state(&mut self, now: u64, bytes: &[u8]) -> Result<Restored, StateError> {
        let mut r = Reader::new(bytes);
        if r.read_u8()? != STATE_VERSION {
            return Err(StateError::Malformed);
        }
        let tlen = usize::try_from(r.read_u32()?).map_err(|_| StateError::Malformed)?;
        let tickets = r.read_bytes(tlen)?;
        let nk = usize::from(r.read_u16()?);
        let krtt = r.read_bytes(nk.checked_mul(41).ok_or(StateError::Malformed)?)?;
        let ne = usize::from(r.read_u16()?);
        let ekk = r.read_bytes(ne.checked_mul(65).ok_or(StateError::Malformed)?)?;
        if !r.is_empty() {
            return Err(StateError::Malformed);
        }
        // Check every entry before anything is stored.
        let mut k = Reader::new(krtt);
        for _ in 0..nk {
            node_of(&mut k)?;
            k.read_u64()?;
        }
        let mut e = Reader::new(ekk);
        for _ in 0..ne {
            node_of(&mut e)?;
            e.read_array::<32>()?;
        }
        let stored = self.tickets.restore(tickets, now)?;
        let mut k = Reader::new(krtt);
        let mut peers = 0;
        for _ in 0..nk {
            let node = node_of(&mut k)?;
            let rtt = k.read_u64()?;
            if rtt > 0 && self.rtt.restore_peer(node, rtt) {
                peers += 1;
            }
        }
        let mut e = Reader::new(ekk);
        for _ in 0..ne {
            let node = node_of(&mut e)?;
            let hash = e.read_array::<32>()?;
            self.ekk.insert(node, hash);
        }
        self.node_ver += 1;
        Ok(Restored { tickets: stored, peers, prekeys: ne })
    }
}
