//! The record keys of a connection: early (0-RTT) keys, the 1-RTT keys of both directions and key updates.
//!
//! Invariants: each direction has its own key generation, and a generation only moves forward. The sending key flips
//! the phase bit when it moves to the next generation. A received packet whose phase differs from the current one is
//! tried against the previous generation if its number is below the first number seen in the current phase (a
//! reordered old packet; the previous key is kept for one probe timeout), otherwise against the next generation,
//! derived once and cached; the cached key is installed only after a packet authenticated under it, so a forged
//! phase bit costs one failed open and changes nothing.

use vinc_crypto::{CryptoError, Provider};
use vinc_security::{EarlyKeys, HeaderKey, PacketKey, RecordError, Traffic};

/// A packet key and the header key that goes with it.
pub(crate) struct Dir<P: Provider> {
    pub(crate) pk: PacketKey<P>,
    pub(crate) hk: HeaderKey<P>,
}

impl<P: Provider> Dir<P> {
    pub(crate) fn early(p: &P, e: &EarlyKeys) -> Result<Self, CryptoError> {
        Ok(Self {
            pk: PacketKey::from_secret(p, e.aead, &e.secret)?,
            hk: HeaderKey::from_secret(p, e.aead, &e.secret)?,
        })
    }
}

/// The sending keys of the 1-RTT space.
pub(crate) struct SendKeys<P: Provider> {
    pub(crate) pk: PacketKey<P>,
    pub(crate) hk: HeaderKey<P>,
    pub(crate) phase: bool,
}

/// Which receive key a packet is to be opened with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Sel {
    Current,
    Previous,
    Next,
}

/// The receiving keys of the 1-RTT space.
pub(crate) struct RecvKeys<P: Provider> {
    pub(crate) hk: HeaderKey<P>,
    cur: PacketKey<P>,
    phase: bool,
    first_pn: u64,
    prev: Option<(PacketKey<P>, u64)>,
    next: Option<PacketKey<P>>,
}

impl<P: Provider> RecvKeys<P> {
    /// The generation of the current receive key.
    pub(crate) const fn generation(&self) -> u32 {
        self.cur.generation()
    }

    /// Drop the previous generation once its hold time passed.
    pub(crate) fn expire(&mut self, now: u64) {
        if self.prev.as_ref().is_some_and(|(_, until)| *until <= now) {
            self.prev = None;
        }
    }

    /// Choose the key for a packet with phase bit `phase` and full number `pn`; derives the next generation if needed.
    pub(crate) fn select(&mut self, p: &P, phase: bool, pn: u64) -> Result<Sel, RecordError> {
        if phase == self.phase {
            return Ok(Sel::Current);
        }
        if pn < self.first_pn && self.prev.is_some() {
            return Ok(Sel::Previous);
        }
        if self.next.is_none() {
            self.next = Some(self.cur.next_generation(p)?);
        }
        Ok(Sel::Next)
    }

    pub(crate) fn key_mut(&mut self, sel: Sel) -> Option<&mut PacketKey<P>> {
        match sel {
            Sel::Current => Some(&mut self.cur),
            Sel::Previous => self.prev.as_mut().map(|(k, _)| k),
            Sel::Next => self.next.as_mut(),
        }
    }

    /// A packet `pn` authenticated under the next generation: it becomes current and the old one is kept until
    /// `hold_until`.
    pub(crate) fn promote(&mut self, pn: u64, hold_until: u64) {
        if let Some(next) = self.next.take() {
            let old = core::mem::replace(&mut self.cur, next);
            self.prev = Some((old, hold_until));
            self.phase = !self.phase;
            self.first_pn = pn;
        }
    }

    /// Note a packet received under the current key (keeps the first number of the phase as the lowest seen).
    pub(crate) fn note(&mut self, pn: u64) {
        self.first_pn = self.first_pn.min(pn);
    }
}

/// All the keys a connection holds.
pub(crate) struct Keys<P: Provider> {
    pub(crate) early_send: Option<Dir<P>>,
    pub(crate) early_recv: Option<Dir<P>>,
    pub(crate) send: Option<SendKeys<P>>,
    pub(crate) recv: Option<RecvKeys<P>>,
}

impl<P: Provider> Keys<P> {
    pub(crate) const fn new() -> Self {
        Self {
            early_send: None,
            early_recv: None,
            send: None,
            recv: None,
        }
    }

    /// Install the 1-RTT keys of an established session; the early keys are no longer needed for sending.
    pub(crate) fn install(&mut self, p: &P, traffic: &Traffic) -> Result<(), CryptoError> {
        let s = traffic.send_keys(p)?;
        let r = traffic.recv_keys(p)?;
        self.send = Some(SendKeys {
            pk: s.packet,
            hk: s.header,
            phase: false,
        });
        self.recv = Some(RecvKeys {
            hk: r.header,
            cur: r.packet,
            phase: false,
            first_pn: 0,
            prev: None,
            next: None,
        });
        self.early_send = None;
        Ok(())
    }

    /// Whether the sending key should move to the next generation: it sealed `after` packets and the peer already
    /// follows the current generation.
    pub(crate) fn wants_update(&self, after: u64) -> bool {
        match (&self.send, &self.recv) {
            (Some(s), Some(r)) => s.pk.sealed() >= after && s.pk.generation() == r.generation(),
            _ => false,
        }
    }

    /// Whether the peer moved to a generation we have not followed with the sending key.
    pub(crate) fn behind_peer(&self) -> bool {
        match (&self.send, &self.recv) {
            (Some(s), Some(r)) => s.pk.generation() < r.generation(),
            _ => false,
        }
    }

    /// Move the sending key to the next generation and flip its phase bit.
    pub(crate) fn update_send(&mut self, p: &P) -> Result<(), RecordError> {
        if let Some(s) = self.send.as_mut() {
            s.pk = s.pk.next_generation(p)?;
            s.phase = !s.phase;
        }
        Ok(())
    }
}
