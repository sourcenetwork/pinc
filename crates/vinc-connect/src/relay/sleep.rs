//! The signed sleep notice of a node about to be suspended (the relay side of TETHER).
//!
//! # Wire format
//!
//! `node(33) ts(8) public_key signature`, where `ts` is the sender's clock in milliseconds and the signature covers
//! `"vinc-sleep" relay(33) node(33) ts(8)`: it names the relay, so a notice for one relay is useless at another, and
//! it names the sender. The key has the length of the node's algorithm and must belong to the node id.
//!
//! Invariants: a notice counts only if its clock is within [`SKEW_MS`] of the relay's, its sender holds a carrier
//! here or just lost one, and its signature verifies; an accepted notice means that the carrier close which follows
//! is a suspension, not a crash. A notice is sent twice (lossy mobile uplinks); the second changes nothing.

use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify_node};
use vinc_crypto::{CryptoError, Keypair, NodeId};
use vinc_wire::{Reader, WireError, Writer};

use crate::carrier::node::{self, NODE_ID_LEN};

/// The largest difference between the notice's clock and the relay's, in milliseconds.
pub const SKEW_MS: u64 = 10_000;
/// The longest notice.
pub const MAX_LEN: usize = NODE_ID_LEN + 8 + MAX_PUBLIC_KEY_LEN + MAX_SIGNATURE_LEN;

const LABEL: &[u8] = b"vinc-sleep";
const MSG_LEN: usize = LABEL.len() + 2 * NODE_ID_LEN + 8;

/// Why a notice was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SleepError {
    /// The notice is malformed.
    Wire(WireError),
    /// The key does not belong to the node, or the signature does not verify.
    Signature(CryptoError),
    /// The notice's clock is too far from the relay's.
    Skew,
    /// The sender holds no carrier here and lost none lately.
    UnknownNode,
    /// The sender is not the carrier the notice arrived on.
    WrongSender,
}

impl From<WireError> for SleepError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

fn message(relay: &NodeId, node: &NodeId, ts: u64) -> Result<[u8; MSG_LEN], WireError> {
    let mut m = [0u8; MSG_LEN];
    let mut w = Writer::new(&mut m);
    w.put_slice(LABEL)?;
    node::write(&mut w, relay)?;
    node::write(&mut w, node)?;
    w.put_u64(ts)?;
    Ok(m)
}

/// A parsed notice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Notice<'a> {
    /// The sleeping node.
    pub node: NodeId,
    /// The sender's clock in milliseconds.
    pub ts_ms: u64,
    public_key: &'a [u8],
    signature: &'a [u8],
}

impl<'a> Notice<'a> {
    /// Parse the layout of `bytes`.
    ///
    /// # Errors
    /// [`SleepError::Wire`] for anything [`sign`] would not produce.
    pub fn parse(bytes: &'a [u8]) -> Result<Self, SleepError> {
        let mut r = Reader::new(bytes);
        let node = node::read(&mut r)?;
        let ts_ms = r.read_u64()?;
        let public_key = r.read_bytes(node.alg.public_key_len())?;
        let signature = r.read_bytes(node.alg.signature_len())?;
        if !r.is_empty() {
            return Err(SleepError::Wire(WireError::Unexpected("trailing bytes")));
        }
        Ok(Self {
            node,
            ts_ms,
            public_key,
            signature,
        })
    }

    /// Check the signature for `relay`.
    ///
    /// # Errors
    /// [`SleepError::Signature`] with the cause.
    pub fn verify(&self, relay: &NodeId) -> Result<(), SleepError> {
        let m = message(relay, &self.node, self.ts_ms)?;
        verify_node(&self.node, self.public_key, &m, self.signature).map_err(SleepError::Signature)
    }
}

/// Sign a notice for `relay` at `ts_ms` and write it into `out`; returns its length.
///
/// # Errors
/// [`SleepError::Wire`] if `out` is short, [`SleepError::Signature`] if the key pair refuses to sign.
pub fn sign(keypair: &Keypair, relay: &NodeId, ts_ms: u64, out: &mut [u8]) -> Result<usize, SleepError> {
    let me = keypair.node_id();
    let mut w = Writer::new(out);
    node::write(&mut w, &me)?;
    w.put_u64(ts_ms)?;
    let head = w.written().len();
    let tail = out.get_mut(head..).ok_or(WireError::BufferTooSmall { needed: 0 })?;
    let pk = keypair.public_key(tail).map_err(SleepError::Signature)?;
    let sig_out = out
        .get_mut(head + pk..)
        .ok_or(WireError::BufferTooSmall { needed: 0 })?;
    let sig = keypair
        .sign(&message(relay, &me, ts_ms)?, sig_out)
        .map_err(SleepError::Signature)?;
    Ok(head + pk + sig)
}
