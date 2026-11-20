//! Peer records on the endpoint: the hints a node's record carries, the signed record itself, publishing it to a
//! rendezvous and looking up another node's by id, through the rendezvous or the relays.
//!
//! Invariants: a record's sequence number is above every earlier one this endpoint signed; hints are at most
//! [`MAX_HINTS`] bytes and unchanged when a call refuses them.

use alloc::vec;
use alloc::vec::Vec;

use pinc_connect::record::{self, MAX_ADDRS, MAX_RECORD_LEN, Reach, RecordFields};
use pinc_crypto::NodeId;

use super::{Discovery, Endpoint, LOOKUP_WAIT, NoDiscovery};
use crate::engine::Try;
use crate::error::{Error, ErrorKind, Result};
use crate::host::Hosted;
use crate::platform::{Platform, ns_to_ms};
use crate::records::{MAX_HINTS, PeerRecord, Records, Rendezvous, newest};

impl<H: Hosted, R: Rendezvous> Endpoint<H, Records<R>> {
    /// Set the hints the next [`publish_record`](Self::publish_record) puts in this node's record: at most
    /// [`MAX_HINTS`] bytes the application gives meaning to (a pointer to its service records, say). Empty by default.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TooLarge`] for more than [`MAX_HINTS`] bytes; the hints are unchanged then.
    pub fn set_hints(&self, hints: &[u8]) -> Result<()> {
        if hints.len() > MAX_HINTS {
            return Err(Error::new(
                ErrorKind::TooLarge,
                "a record carries at most 64 bytes of hints",
            ));
        }
        let mut h = self
            .0
            .discovery
            .hints
            .try_borrow_mut()
            .map_err(|_| Error::new(ErrorKind::Busy, "the hints are being read"))?;
        h.clear();
        h.extend_from_slice(hints);
        drop(h);
        self.push_hints(hints);
        Ok(())
    }

    /// This node's record as [`publish_record`](Self::publish_record) sends it: its address ([`addr`](Self::addr)),
    /// its hints and a sequence number above every earlier one (the wall clock in milliseconds, or one more than the
    /// last), signed
    /// with its identity. With no relay client in the endpoint yet, the home relay field names this node and the
    /// reachability class says public; the connectivity client fills both once it runs under the facade.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store refuses to sign, [`crate::ErrorKind::Shutdown`] if the endpoint
    /// stopped.
    pub async fn signed_record(&self) -> Result<Vec<u8>> {
        let records = &self.0.discovery;
        let clock = ns_to_ms(self.0.shared.host.platform().wall_ns());
        let seq = clock.max(records.seq.get().saturating_add(1));
        records.seq.set(seq);
        let hints = records
            .hints
            .try_borrow()
            .map(|h| h.clone())
            .map_err(|_| Error::new(ErrorKind::Busy, "the hints are being changed"))?;
        let mut addrs = self.addr().direct;
        if self.has_relays() {
            let seen = self.0.shared.run(|core, _| Try::Done(core.candidates())).await;
            for a in seen {
                if !addrs.contains(&a) {
                    addrs.push(a);
                }
            }
        }
        let fields = RecordFields {
            home: self.0.home,
            seq,
            reach: Reach::Public,
            addrs: addrs.get(..addrs.len().min(MAX_ADDRS)).unwrap_or_default(),
            hints: &hints,
        };
        let bad = |_| Error::config("the record could not be built");
        let mut out = vec![0u8; MAX_RECORD_LEN];
        let signed = record::prepare(&self.id(), self.public_key(), &fields, &mut out).map_err(bad)?;
        let sig = self.sign_unchecked(out.get(..signed).unwrap_or_default()).await?;
        let len = record::finish(&mut out, signed, &sig).map_err(bad)?;
        out.truncate(len);
        Ok(out)
    }

    /// Publish this node's record ([`signed_record`](Self::signed_record)) to the rendezvous, so a peer can dial it by
    /// node id alone. Publish again after the address or the hints change.
    ///
    /// # Errors
    /// As [`signed_record`](Self::signed_record), and the store's own error.
    pub async fn publish_record(&self) -> Result<()> {
        let record = self.signed_record().await?;
        self.0.discovery.put(&record).await
    }

    /// The newest verified record of `node`, hints included: what the rendezvous holds now if it is newer than what
    /// this endpoint saw before. The relays are asked whenever the rendezvous holds no record of `node`; when none
    /// answers, the newest record already known is the answer. `None` if no record of `node` verifies.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TimedOut`] if the store does not answer within [`LOOKUP_WAIT`], or, with no record known,
    /// no relay does.
    pub async fn lookup(&self, node: &NodeId) -> Result<Option<PeerRecord>> {
        let (best, held) = self
            .within(LOOKUP_WAIT, self.0.discovery.find_held(node))
            .await
            .ok_or(Error::new(ErrorKind::TimedOut, "the rendezvous did not answer in time"))?;
        if held || !self.has_relays() {
            return Ok(best);
        }
        match self.relay_record(node).await {
            // A table that is absent or borrowed hands back the answer alone: keep the newer of it and `best`.
            Ok(relayed) => Ok(self
                .0
                .discovery
                .note(node, relayed.clone())
                .or_else(|| newest(best.as_ref(), relayed))),
            Err(_) if best.is_some() => Ok(best),
            Err(e) => Err(e),
        }
    }
}

impl<H: Hosted> Endpoint<H, NoDiscovery> {
    /// Set the hints this node's record carries: at most [`MAX_HINTS`] bytes the application gives meaning to. The
    /// relays hold the record and republish it as the addresses change; with no relay it is kept nowhere.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TooLarge`] for more than [`MAX_HINTS`] bytes; the hints are unchanged then.
    pub fn set_hints(&self, hints: &[u8]) -> Result<()> {
        if hints.len() > MAX_HINTS {
            return Err(Error::new(
                ErrorKind::TooLarge,
                "a record carries at most 64 bytes of hints",
            ));
        }
        self.push_hints(hints);
        Ok(())
    }

    /// The verified record of `node` that the relays hold, hints included. `None` if no relay has one that checks out.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TimedOut`] if no relay answers within [`LOOKUP_WAIT`].
    pub async fn lookup(&self, node: &NodeId) -> Result<Option<PeerRecord>> {
        if self.has_relays() {
            self.relay_record(node).await
        } else {
            Ok(None)
        }
    }
}

impl<H: Hosted, D: Discovery> Endpoint<H, D> {
    fn has_relays(&self) -> bool {
        !self.0.relays.is_empty()
    }

    /// Hand `hints` to the connectivity client, which puts them in the record the relays hold.
    fn push_hints(&self, hints: &[u8]) {
        let sh = &self.0.shared;
        let now = sh.now();
        if let Some(mut core) = sh.lock() {
            core.set_hints(now, hints);
        }
    }

    /// The record the relays hold for `node`: asked of the home relay, answered within [`LOOKUP_WAIT`].
    async fn relay_record(&self, node: &NodeId) -> Result<Option<PeerRecord>> {
        let (mut deadline, mut since) = (None, None);
        let wait = u64::try_from(LOOKUP_WAIT.as_nanos()).unwrap_or(u64::MAX);
        self.0
            .shared
            .run(|core, now| {
                let at = *deadline.get_or_insert_with(|| now.saturating_add(wait));
                let since = *since.get_or_insert_with(|| core.lookup_start(now, node));
                core.lookup_poll(node, since, at, now)
            })
            .await
    }
}
