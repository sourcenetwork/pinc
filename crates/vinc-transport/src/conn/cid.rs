//! Connection ids: the ones we issue (with stateless-reset tokens) and the ones the peer issued to us.
//!
//! Invariants: sequence numbers only grow; at most [`MAX_CIDS`] ids of each kind are held, so a peer that issues
//! more is a protocol violation; a remote id is used by at most one path while spare ones exist, so paths cannot be
//! linked by an observer; an id the peer retired is never used to send again.

use vinc_crypto::Provider;
use vinc_security::{Env, Failure};

use crate::packet::{ConnId, RESET_TOKEN_LEN};

/// The most ids of each kind held at once.
pub(crate) const MAX_CIDS: usize = 8;

const RESET_LABEL: &str = "VINC 2026 v1 reset token";

/// The stateless-reset token of `cid` under `key`. An endpoint that lost its connections computes the same value to
/// answer a packet for an id it no longer knows, so the peer closes at once.
pub fn reset_token(key: &[u8; 32], cid: &ConnId) -> [u8; RESET_TOKEN_LEN] {
    let mut token = [0u8; RESET_TOKEN_LEN];
    vinc_crypto::expand(key, RESET_LABEL, cid.as_bytes(), &mut token);
    token
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Announce {
    Pending,
    InFlight,
    Done,
}

#[derive(Debug, Clone, Copy)]
struct Local {
    seq: u64,
    cid: ConnId,
    token: [u8; RESET_TOKEN_LEN],
    announce: Announce,
}

#[derive(Debug, Clone, Copy)]
struct Remote {
    seq: u64,
    cid: ConnId,
    token: Option<[u8; RESET_TOKEN_LEN]>,
    retired: bool,
    retire: Announce,
    user: Option<u8>,
}

/// A NEW_CONNECTION_ID to send.
#[derive(Debug, Clone, Copy)]
pub(crate) struct NewCid {
    pub(crate) seq: u64,
    pub(crate) retire_prior_to: u64,
    pub(crate) cid: ConnId,
    pub(crate) token: [u8; RESET_TOKEN_LEN],
}

/// The connection id tables.
#[derive(Debug)]
pub(crate) struct Cids {
    local: [Option<Local>; MAX_CIDS],
    next_seq: u64,
    retire_prior_to: u64,
    remote: [Option<Remote>; MAX_CIDS],
}

impl Cids {
    pub(crate) fn new(first: ConnId) -> Self {
        let mut local = [None; MAX_CIDS];
        if let Some(slot) = local.first_mut() {
            *slot = Some(Local {
                seq: 0,
                cid: first,
                token: [0; RESET_TOKEN_LEN],
                announce: Announce::Done,
            });
        }
        Self {
            local,
            next_seq: 1,
            retire_prior_to: 0,
            remote: [None; MAX_CIDS],
        }
    }

    /// Our id with sequence number 0, the one the handshake carried.
    pub(crate) fn first_local(&self) -> Option<ConnId> {
        self.local.iter().flatten().find(|l| l.seq == 0).map(|l| l.cid)
    }

    /// Whether `cid` is one of ours.
    pub(crate) fn is_local(&self, cid: &ConnId) -> bool {
        self.local.iter().flatten().any(|l| l.cid == *cid)
    }

    /// Issue ids until `target` are live, all asking the peer to retire everything below sequence 1 the first time
    /// (the id of the handshake has no reset token).
    pub(crate) fn issue<P: Provider>(
        &mut self,
        env: &mut Env<'_, P>,
        len: usize,
        key: &[u8; 32],
        target: usize,
    ) -> Result<(), Failure> {
        self.retire_prior_to = self.retire_prior_to.max(1);
        while self
            .local
            .iter()
            .flatten()
            .filter(|l| l.seq >= self.retire_prior_to)
            .count()
            < target
        {
            let Some(slot) = self.local.iter_mut().find(|s| s.is_none()) else {
                break;
            };
            let mut bytes = [0u8; crate::packet::MAX_CID_LEN];
            let raw = bytes.get_mut(..len).ok_or(Failure::InvalidParameter)?;
            env.drbg.fill(raw).map_err(|_| Failure::Randomness)?;
            let cid = ConnId::new(raw).ok_or(Failure::InvalidParameter)?;
            *slot = Some(Local {
                seq: self.next_seq,
                cid,
                token: reset_token(key, &cid),
                announce: Announce::Pending,
            });
            self.next_seq += 1;
        }
        Ok(())
    }

    /// The next NEW_CONNECTION_ID to send; it counts as in flight until acknowledged or lost.
    pub(crate) fn next_new(&mut self) -> Option<NewCid> {
        let retire_prior_to = self.retire_prior_to;
        let l = self
            .local
            .iter_mut()
            .flatten()
            .filter(|l| l.announce == Announce::Pending)
            .min_by_key(|l| l.seq)?;
        l.announce = Announce::InFlight;
        Some(NewCid {
            seq: l.seq,
            retire_prior_to,
            cid: l.cid,
            token: l.token,
        })
    }

    pub(crate) fn new_lost(&mut self, seq: u64) {
        if let Some(l) = self.local.iter_mut().flatten().find(|l| l.seq == seq)
            && l.announce == Announce::InFlight
        {
            l.announce = Announce::Pending;
        }
    }

    pub(crate) fn new_acked(&mut self, seq: u64) {
        if let Some(l) = self.local.iter_mut().flatten().find(|l| l.seq == seq) {
            l.announce = Announce::Done;
        }
    }

    pub(crate) fn has_pending_new(&self) -> bool {
        self.local.iter().flatten().any(|l| l.announce == Announce::Pending)
    }

    /// The peer retired our id `seq`. Returns whether it was live.
    pub(crate) fn on_retire(&mut self, seq: u64) -> bool {
        match self.local.iter_mut().find(|s| s.is_some_and(|l| l.seq == seq)) {
            Some(slot) => {
                *slot = None;
                true
            }
            None => false,
        }
    }

    /// Record an id the peer issued, retiring the ones below `retire_prior_to`.
    ///
    /// # Errors
    /// `Err(())` if the peer exceeded the number of ids we hold or reused a sequence number for another id.
    pub(crate) fn on_new_remote(
        &mut self,
        seq: u64,
        retire_prior_to: u64,
        cid: ConnId,
        token: [u8; RESET_TOKEN_LEN],
    ) -> Result<(), ()> {
        if let Some(r) = self.remote.iter().flatten().find(|r| r.seq == seq) {
            return if r.cid == cid { Ok(()) } else { Err(()) };
        }
        for r in self.remote.iter_mut().flatten().filter(|r| r.seq < retire_prior_to) {
            if !r.retired {
                r.retired = true;
                r.retire = Announce::Pending;
            }
        }
        if seq >= retire_prior_to {
            let slot = match self.remote.iter_mut().find(|s| s.is_none()) {
                Some(s) => s,
                None => self
                    .remote
                    .iter_mut()
                    .find(|s| s.is_some_and(|r| r.retire == Announce::Done))
                    .ok_or(())?,
            };
            *slot = Some(Remote {
                seq,
                cid,
                token: Some(token),
                retired: false,
                retire: Announce::Done,
                user: None,
            });
        } else {
            // Already below the retire point: acknowledge it as retired so the peer stops counting it.
            let slot = self.remote.iter_mut().find(|s| s.is_none()).ok_or(())?;
            *slot = Some(Remote {
                seq,
                cid,
                token: None,
                retired: true,
                retire: Announce::Pending,
                user: None,
            });
        }
        Ok(())
    }

    /// The peer's id with sequence 0, learned from the first long header.
    pub(crate) fn set_first_remote(&mut self, cid: ConnId) {
        if self.remote.iter().flatten().all(|r| r.seq != 0)
            && let Some(slot) = self.remote.iter_mut().find(|s| s.is_none())
        {
            *slot = Some(Remote {
                seq: 0,
                cid,
                token: None,
                retired: false,
                retire: Announce::Done,
                user: None,
            });
        }
    }

    pub(crate) fn remote_cid(&self, seq: u64) -> Option<ConnId> {
        self.remote
            .iter()
            .flatten()
            .find(|r| r.seq == seq && !r.retired)
            .map(|r| r.cid)
    }

    /// Claim an unretired remote id for path `user`, preferring one nobody uses.
    pub(crate) fn claim_remote(&mut self, user: u8) -> Option<u64> {
        let pick = self
            .remote
            .iter_mut()
            .flatten()
            .filter(|r| !r.retired && r.user.is_none())
            .min_by_key(|r| r.seq)?;
        pick.user = Some(user);
        Some(pick.seq)
    }

    /// Retire the remote id `seq` ourselves (its path is gone).
    pub(crate) fn retire_remote(&mut self, seq: u64) {
        if let Some(r) = self.remote.iter_mut().flatten().find(|r| r.seq == seq && !r.retired) {
            r.retired = true;
            r.retire = Announce::Pending;
            r.user = None;
        }
    }

    /// Whether remote id `seq` is retired.
    pub(crate) fn is_retired(&self, seq: u64) -> bool {
        self.remote.iter().flatten().any(|r| r.seq == seq && r.retired)
    }

    pub(crate) fn next_retire(&mut self) -> Option<u64> {
        let r = self
            .remote
            .iter_mut()
            .flatten()
            .filter(|r| r.retire == Announce::Pending)
            .min_by_key(|r| r.seq)?;
        r.retire = Announce::InFlight;
        Some(r.seq)
    }

    pub(crate) fn retire_lost(&mut self, seq: u64) {
        if let Some(r) = self
            .remote
            .iter_mut()
            .flatten()
            .find(|r| r.seq == seq && r.retire == Announce::InFlight)
        {
            r.retire = Announce::Pending;
        }
    }

    pub(crate) fn retire_acked(&mut self, seq: u64) {
        if let Some(r) = self.remote.iter_mut().flatten().find(|r| r.seq == seq) {
            r.retire = Announce::Done;
        }
        for slot in &mut self.remote {
            if slot.is_some_and(|r| r.seq == seq && r.retired) {
                *slot = None;
            }
        }
    }

    pub(crate) fn has_pending_retire(&self) -> bool {
        self.remote.iter().flatten().any(|r| r.retire == Announce::Pending)
    }

    /// The stateless-reset tokens of the ids the peer issued.
    pub(crate) fn peer_tokens(&self) -> impl Iterator<Item = &[u8; RESET_TOKEN_LEN]> {
        self.remote.iter().flatten().filter_map(|r| r.token.as_ref())
    }
}
