//! Custody: signed acknowledgements and the bookkeeping that follows them.
//!
//! A node that accepts custody of a bundle admits it to the [`Ledger`] as [`Class::Custody`] (which may be refused
//! for lack of room) and owes the previous custodian a signed [`CustodyAck`]. The previous custodian, on a valid ack
//! from the node it handed custody to, is relieved: its copy becomes transit and may be evicted. Whoever holds
//! custody keeps the bundle until it is delivered or expires; the [`CustodyBook`] remembers whom each acknowledgement
//! is owed to and whom custody was offered to.
//!
//! Invariants: an ack is valid only if its signature verifies under the custodian's node id; custody is relieved
//! only by a valid ack from exactly the node it was offered to; a custody item leaves the ledger only through
//! delivery ([`CustodyBook::delivered`]), expiry or relief (which keeps the bytes as transit); the book never holds
//! a record for an item the ledger no longer holds ([`CustodyBook::sync`]). All tables are fixed-size arrays.

use core::fmt;

use vinc_crypto::{Keypair, NodeId};
use vinc_wire::{Reader, Writer};

use crate::endorse::Endorsement;
use crate::error::DtnError;
use crate::head::BundleId;
use crate::hlc::Hlc;
use crate::labels;
use crate::store::{Class, Entry, Ledger, StoreError};

/// The signed fields of an acknowledgement: bundle, custodian, previous custodian, time.
const ACK_BODY_LEN: usize = 32 + 33 + 33 + 12;

/// A custodian's signed statement that it holds a bundle and took custody from `previous`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CustodyAck {
    /// The bundle.
    pub bundle: BundleId,
    /// The node that accepted custody and signed.
    pub custodian: NodeId,
    /// The node custody was taken from, to whom the ack is addressed.
    pub previous: NodeId,
    /// When the ack was made.
    pub at: Hlc,
    endorsement: Endorsement,
}

fn put_node(w: &mut Writer<'_>, n: &NodeId) -> Result<(), DtnError> {
    w.put_u8(n.alg.tag())?;
    w.put_slice(&n.bytes)?;
    Ok(())
}

fn get_node(r: &mut Reader<'_>) -> Result<NodeId, DtnError> {
    let alg = vinc_crypto::IdentityAlg::from_tag(r.read_u8()?).ok_or(DtnError::Params)?;
    Ok(NodeId {
        alg,
        bytes: r.read_array()?,
    })
}

fn body(bundle: &BundleId, custodian: &NodeId, previous: &NodeId, at: Hlc) -> Result<[u8; ACK_BODY_LEN], DtnError> {
    let mut out = [0u8; ACK_BODY_LEN];
    let mut w = Writer::new(&mut out);
    w.put_slice(&bundle.0)?;
    put_node(&mut w, custodian)?;
    put_node(&mut w, previous)?;
    w.put_u64(at.wall)?;
    w.put_u32(at.counter)?;
    Ok(out)
}

impl CustodyAck {
    /// Sign an ack from `signer` (the custodian) to `previous` for `bundle` at time `at`.
    ///
    /// # Errors
    /// [`DtnError::Crypto`] if signing fails.
    pub fn sign(bundle: BundleId, previous: NodeId, at: Hlc, signer: &Keypair) -> Result<Self, DtnError> {
        let custodian = signer.node_id();
        let b = body(&bundle, &custodian, &previous, at)?;
        Ok(Self {
            bundle,
            custodian,
            previous,
            at,
            endorsement: Endorsement::sign(signer, labels::CUSTODY_ACK, &b)?,
        })
    }

    /// Check the custodian's signature.
    ///
    /// # Errors
    /// [`DtnError::Crypto`] if the key is not the custodian's or the signature does not verify.
    pub fn verify(&self) -> Result<(), DtnError> {
        let b = body(&self.bundle, &self.custodian, &self.previous, self.at)?;
        self.endorsement.verify(&self.custodian, labels::CUSTODY_ACK, &b)
    }

    /// The encoded length for the custodian's identity algorithm.
    pub const fn encoded_len(&self) -> usize {
        ACK_BODY_LEN + Endorsement::encoded_len(self.custodian.alg)
    }

    /// Encode into the start of `out`, returning the length.
    ///
    /// # Errors
    /// [`DtnError::Wire`] if `out` is too short.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, DtnError> {
        let mut w = Writer::new(out);
        w.put_slice(&body(&self.bundle, &self.custodian, &self.previous, self.at)?)?;
        self.endorsement.encode(&mut w)?;
        Ok(w.written().len())
    }

    /// Decode and validate the structure. The signature is not checked: call [`CustodyAck::verify`].
    ///
    /// # Errors
    /// [`DtnError::Wire`] or [`DtnError::Params`] for malformed input or trailing bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, DtnError> {
        let mut r = Reader::new(bytes);
        let bundle = BundleId(r.read_array()?);
        let custodian = get_node(&mut r)?;
        let previous = get_node(&mut r)?;
        let at = Hlc::new(r.read_u64()?, r.read_u32()?);
        let endorsement = Endorsement::decode(custodian.alg, &mut r)?;
        if !r.is_empty() {
            return Err(DtnError::Params);
        }
        Ok(Self {
            bundle,
            custodian,
            previous,
            at,
            endorsement,
        })
    }
}

/// Why custody bookkeeping refused something.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CustodyError {
    /// The store refused the bundle.
    Store(StoreError),
    /// The ack failed to verify or decode.
    Ack(DtnError),
    /// The book has no free record.
    Capacity,
    /// No such bundle is in custody here.
    Unknown,
    /// The ack is not from the node custody was offered to.
    NotOffered,
}

impl From<StoreError> for CustodyError {
    fn from(e: StoreError) -> Self {
        Self::Store(e)
    }
}

impl fmt::Display for CustodyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Store(e) => write!(f, "custody refused: {e}"),
            Self::Ack(e) => write!(f, "invalid acknowledgement: {e}"),
            Self::Capacity => f.write_str("too many bundles in custody"),
            Self::Unknown => f.write_str("the bundle is not in custody here"),
            Self::NotOffered => f.write_str("custody was not offered to the acknowledging node"),
        }
    }
}

impl core::error::Error for CustodyError {}

/// A bundle offered into custody.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Incoming {
    /// The bundle.
    pub bundle: BundleId,
    /// The bytes to charge.
    pub bytes: u64,
    /// The physical time (milliseconds) at which it expires.
    pub expires: u64,
    /// The node custody is taken from.
    pub previous: NodeId,
}

/// An acknowledgement this node owes after accepting custody.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AckDue {
    /// The bundle.
    pub bundle: BundleId,
    /// The node to acknowledge to.
    pub previous: NodeId,
}

impl AckDue {
    /// Sign the owed ack with this node's key.
    ///
    /// # Errors
    /// [`DtnError::Crypto`] if signing fails.
    pub fn sign(&self, at: Hlc, signer: &Keypair) -> Result<CustodyAck, DtnError> {
        CustodyAck::sign(self.bundle, self.previous, at, signer)
    }
}

#[derive(Debug, Clone, Copy)]
struct Record {
    bundle: BundleId,
    previous: NodeId,
    offered: Option<NodeId>,
}

/// The custody records of one node, at most `N` bundles.
#[derive(Debug, Clone)]
pub struct CustodyBook<const N: usize> {
    records: [Option<Record>; N],
}

impl<const N: usize> Default for CustodyBook<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> CustodyBook<N> {
    /// An empty book.
    pub const fn new() -> Self {
        Self { records: [None; N] }
    }

    /// The number of bundles in custody.
    pub fn len(&self) -> usize {
        self.records.iter().flatten().count()
    }

    /// Whether no bundle is in custody.
    pub fn is_empty(&self) -> bool {
        self.records.iter().all(Option::is_none)
    }

    /// Whether `bundle` is in custody here.
    pub fn holds(&self, bundle: &BundleId) -> bool {
        self.records.iter().flatten().any(|r| r.bundle == *bundle)
    }

    /// Drop the records of items the ledger no longer holds (expired or evicted).
    pub fn sync<const L: usize>(&mut self, ledger: &Ledger<L>) {
        for slot in &mut self.records {
            if slot.is_some_and(|r| !ledger.contains(&r.bundle.store_key())) {
                *slot = None;
            }
        }
    }

    /// Accept custody of the `incoming` bundle. A bundle already kept as
    /// transit is promoted without new room. Evictions go to `on_evict`.
    ///
    /// # Errors
    /// [`CustodyError::Store`] if the ledger refuses (custody cannot be kept without evicting live custody);
    /// [`CustodyError::Capacity`] if the book is full. Nothing changes on error except expired items leaving.
    pub fn accept<const L: usize>(
        &mut self,
        ledger: &mut Ledger<L>,
        incoming: Incoming,
        now: u64,
        mut on_evict: impl FnMut(&Entry),
    ) -> Result<AckDue, CustodyError> {
        let Incoming {
            bundle,
            bytes,
            expires,
            previous,
        } = incoming;
        ledger.expire(now, &mut on_evict);
        self.sync(ledger);
        if self.holds(&bundle) {
            return Ok(AckDue { bundle, previous });
        }
        let slot = self
            .records
            .iter()
            .position(Option::is_none)
            .ok_or(CustodyError::Capacity)?;
        let key = bundle.store_key();
        if ledger.contains(&key) {
            ledger.reclass(&key, Class::Custody)?;
        } else {
            ledger.admit(key, bytes, Class::Custody, expires, now, &mut on_evict)?;
        }
        self.sync(ledger);
        if let Some(s) = self.records.get_mut(slot) {
            *s = Some(Record {
                bundle,
                previous,
                offered: None,
            });
        }
        Ok(AckDue { bundle, previous })
    }

    /// The node an ack for `bundle` is owed to.
    pub fn owed_to(&self, bundle: &BundleId) -> Option<NodeId> {
        self.records
            .iter()
            .flatten()
            .find(|r| r.bundle == *bundle)
            .map(|r| r.previous)
    }

    /// Record that custody of `bundle` was offered to `to`, whose ack will relieve this node.
    ///
    /// # Errors
    /// [`CustodyError::Unknown`] if the bundle is not in custody here.
    pub fn offer(&mut self, bundle: &BundleId, to: NodeId) -> Result<(), CustodyError> {
        let r = self
            .records
            .iter_mut()
            .flatten()
            .find(|r| r.bundle == *bundle)
            .ok_or(CustodyError::Unknown)?;
        r.offered = Some(to);
        Ok(())
    }

    /// Process an ack. If it verifies and comes from the node custody was offered to, this node is relieved: the
    /// bundle stays in the ledger as transit and the record is dropped.
    ///
    /// # Errors
    /// [`CustodyError::Ack`] for a bad signature; [`CustodyError::Unknown`] if the bundle is not in custody here;
    /// [`CustodyError::NotOffered`] if the ack is not from the node it was offered to.
    pub fn on_ack<const L: usize>(&mut self, ledger: &mut Ledger<L>, ack: &CustodyAck) -> Result<(), CustodyError> {
        ack.verify().map_err(CustodyError::Ack)?;
        let slot = self
            .records
            .iter_mut()
            .find(|s| s.is_some_and(|r| r.bundle == ack.bundle))
            .ok_or(CustodyError::Unknown)?;
        if slot.and_then(|r| r.offered) != Some(ack.custodian) {
            return Err(CustodyError::NotOffered);
        }
        *slot = None;
        ledger.reclass(&ack.bundle.store_key(), Class::Transit)?;
        Ok(())
    }

    /// The bundle reached its destination: release it from the ledger and the book.
    ///
    /// # Errors
    /// [`CustodyError::Unknown`] if the bundle is not in custody here.
    pub fn delivered<const L: usize>(&mut self, ledger: &mut Ledger<L>, bundle: &BundleId) -> Result<(), CustodyError> {
        let slot = self
            .records
            .iter_mut()
            .find(|s| s.is_some_and(|r| r.bundle == *bundle))
            .ok_or(CustodyError::Unknown)?;
        *slot = None;
        ledger.release(&bundle.store_key());
        Ok(())
    }

    /// Expire items at `now` and drop their records.
    pub fn expire<const L: usize>(&mut self, ledger: &mut Ledger<L>, now: u64, on_evict: impl FnMut(&Entry)) {
        ledger.expire(now, on_evict);
        self.sync(ledger);
    }
}
