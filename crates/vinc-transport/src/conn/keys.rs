//! The record keys of a connection: early (0-RTT) keys, the 1-RTT keys of both directions and the key roll.
//!
//! # The key roll
//!
//! A roll replaces both directions' keys with ones that depend on a fresh Diffie-Hellman value, so a stolen secret
//! does not unlock the keys after it (see `vinc_security::keyroll`). It runs when a key reached its AEAD limit
//! (2^22 AES-128-GCM packets sealed, or the ChaCha20-Poly1305 failed-open count), when the sending key sealed
//! `Config::key_update_after` packets, or when the keys are 10 minutes old.
//!
//! 1. The side whose key is due sends a REKEY request and sends it again every probe timeout until it is answered.
//! 2. The peer answers with its own value and a floor: the lowest packet number it will seal under the new keys.
//!    It stages the new keys but keeps sending under the old ones.
//! 3. On the answer the requester switches its sending key at once and flips the phase bit of its packets; it stages
//!    the new receive key.
//! 4. The first packet that authenticates under the new receive key promotes it. The side that answered then
//!    switches its sending key and flips its phase bit. The old receive key is kept for one probe timeout, for
//!    packets that arrive late.
//!
//! The answer is therefore always sealed under keys the requester has, however often it is repeated.
//!
//! # The REKEY frame
//!
//! The frame layer carries one REKEY body, whose bytes are `vinc_security::Rekey::encode`: `kind(1)` (0 request,
//! 1 answer), `share(32)`, and for an answer `switch_pn(varint)`. Until the frame codec has a frame type for it,
//! [`Connection::poll_rekey_body`] and [`Connection::on_rekey_body`] move the body bytes in and out.
//!
//! Invariants: a receive key of the next generation is installed only after a packet authenticated under it, so a
//! forged phase bit costs one failed open and changes nothing; a generation only moves forward; the sending key of
//! the old generation never seals again after the switch.

use vinc_crypto::{CryptoError, Provider};
use vinc_security::keyroll::{self, Rekey, Roll};
use vinc_security::{EarlyKeys, Env, Failure, HeaderKey, PacketKey, RecordError, Traffic};

use super::event::code;
use super::{Connection, Phase};
use crate::stream::StreamSource;

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
    /// When these keys were installed, for the 10-minute age.
    since: u64,
}

/// Which receive key a packet is to be opened with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Sel {
    Current,
    Previous,
    Next,
}

/// The receive key of the next generation and the lowest packet number the peer may seal under it.
struct Staged<P: Provider> {
    pk: PacketKey<P>,
    floor: u64,
}

/// The receiving keys of the 1-RTT space.
pub(crate) struct RecvKeys<P: Provider> {
    pub(crate) hk: HeaderKey<P>,
    cur: PacketKey<P>,
    phase: bool,
    first_pn: u64,
    prev: Option<(PacketKey<P>, u64)>,
    next: Option<Staged<P>>,
}

impl<P: Provider> RecvKeys<P> {
    /// Drop the previous generation once its hold time passed.
    pub(crate) fn expire(&mut self, now: u64) {
        if self.prev.as_ref().is_some_and(|(_, until)| *until <= now) {
            self.prev = None;
        }
    }

    /// Choose the key for a packet with phase bit `phase` and full number `pn`.
    ///
    /// # Errors
    /// [`RecordError::Authentication`] when no key can apply: the phase differs, and either no next generation is
    /// staged (a roll the peer did not start, or a forged phase bit) or the previous generation is gone.
    pub(crate) fn select(&mut self, _p: &P, phase: bool, pn: u64) -> Result<Sel, RecordError> {
        if phase == self.phase {
            return Ok(Sel::Current);
        }
        match &self.next {
            Some(n) if pn >= n.floor => Ok(Sel::Next),
            _ if pn < self.first_pn && self.prev.is_some() => Ok(Sel::Previous),
            _ => Err(RecordError::Authentication),
        }
    }

    pub(crate) fn key_mut(&mut self, sel: Sel) -> Option<&mut PacketKey<P>> {
        match sel {
            Sel::Current => Some(&mut self.cur),
            Sel::Previous => self.prev.as_mut().map(|(k, _)| k),
            Sel::Next => self.next.as_mut().map(|n| &mut n.pk),
        }
    }

    /// A packet `pn` authenticated under the next generation: it becomes current and the old one is kept until
    /// `hold_until`.
    pub(crate) fn promote(&mut self, pn: u64, hold_until: u64) {
        if let Some(next) = self.next.take() {
            let old = core::mem::replace(&mut self.cur, next.pk);
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

/// All the keys a connection holds, and its roll.
pub(crate) struct Keys<P: Provider> {
    pub(crate) early_send: Option<Dir<P>>,
    pub(crate) early_recv: Option<Dir<P>>,
    pub(crate) send: Option<SendKeys<P>>,
    pub(crate) recv: Option<RecvKeys<P>>,
    roll: Roll,
    /// The sending key of the next generation, kept back until the peer shows it holds the new keys.
    staged_send: Option<PacketKey<P>>,
    /// A REKEY waiting for a packet.
    out: Option<Rekey>,
    /// When the pending request last went out.
    request_at: Option<u64>,
}

impl<P: Provider> Keys<P> {
    pub(crate) const fn new(client: bool) -> Self {
        Self {
            early_send: None,
            early_recv: None,
            send: None,
            recv: None,
            roll: Roll::new(client),
            staged_send: None,
            out: None,
            request_at: None,
        }
    }

    /// Install the 1-RTT keys of an established session at `now`; the early keys are no longer needed for sending.
    pub(crate) fn install(&mut self, p: &P, traffic: &Traffic, now: u64) -> Result<(), CryptoError> {
        let s = traffic.send_keys(p)?;
        let r = traffic.recv_keys(p)?;
        self.send = Some(SendKeys {
            pk: s.packet,
            hk: s.header,
            phase: false,
            since: now,
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

    /// Whether a roll should start now: none is under way, and a key reached its AEAD limit, the sending key
    /// sealed `after` packets, or the keys are 10 minutes old.
    pub(crate) fn roll_due(&self, now: u64, after: u64) -> bool {
        match (&self.send, &self.recv) {
            (Some(s), Some(r)) => {
                self.roll.is_idle()
                    && self.staged_send.is_none()
                    && r.next.is_none()
                    && keyroll::due(&s.pk, &r.cur, now.saturating_sub(s.since), after)
            }
            _ => false,
        }
    }

    /// Whether the peer moved to a generation we have not followed with the sending key.
    pub(crate) fn behind_peer(&self) -> bool {
        self.staged_send.is_some()
    }

    /// Move the sending key to the staged generation and flip its phase bit.
    ///
    /// # Errors
    /// [`RecordError::Authentication`] if no generation is staged.
    pub(crate) fn update_send(&mut self, now: u64) -> Result<(), RecordError> {
        let (Some(s), Some(next)) = (self.send.as_mut(), self.staged_send.take()) else {
            return Err(RecordError::Authentication);
        };
        s.pk = next;
        s.phase = !s.phase;
        s.since = now;
        Ok(())
    }

    /// Start a roll: queue the request.
    fn begin<F: FnOnce(&mut Roll) -> Result<Rekey, Failure>>(&mut self, start: F) -> Result<(), Failure> {
        self.out = Some(start(&mut self.roll)?);
        self.request_at = None;
        Ok(())
    }

    /// The REKEY to send now, if any: a message waiting, or the request again once a probe timeout `pto` passed
    /// without an answer.
    pub(crate) fn poll_rekey(&mut self, now: u64, pto: u64) -> Option<Rekey> {
        if let Some(r) = self.out.take() {
            if !r.answer {
                self.request_at = Some(now);
            }
            return Some(r);
        }
        let r = self.roll.pending()?;
        if self.request_at.is_none_or(|t| now >= t.saturating_add(pto)) {
            self.request_at = Some(now);
            return Some(r);
        }
        None
    }

    /// When the pending request goes out again, if one is waiting for its answer.
    pub(crate) fn rekey_deadline(&self, pto: u64) -> Option<u64> {
        self.roll.pending()?;
        self.request_at.map(|t| t.saturating_add(pto))
    }

    /// The peer asked for a roll: stage the new keys and queue the answer. `next_pn` is the next packet number this
    /// side will seal, a floor for every packet it seals under the new keys.
    fn on_request(&mut self, p: &P, env: &mut Env<'_, P>, request: &Rekey, next_pn: u64) -> Result<(), Failure> {
        let (Some(s), Some(r)) = (self.send.as_ref(), self.recv.as_mut()) else {
            return Err(Failure::UnexpectedMessage);
        };
        if r.next.is_some() {
            return Err(Failure::UnexpectedMessage);
        }
        let answered = self.roll.on_request(env, request, next_pn)?;
        if let Some(dh) = answered.dh {
            self.staged_send = Some(s.pk.rolled(p, &dh).map_err(|_| Failure::KeyOperation)?);
            r.next = Some(Staged {
                pk: r.cur.rolled(p, &dh).map_err(|_| Failure::KeyOperation)?,
                floor: 0,
            });
        }
        self.out = Some(answered.answer);
        Ok(())
    }

    /// The peer answered: switch the sending key at once and stage the new receive key.
    fn on_answer(&mut self, p: &P, env: &Env<'_, P>, answer: &Rekey, now: u64) -> Result<(), Failure> {
        let (Some(s), Some(r)) = (self.send.as_mut(), self.recv.as_mut()) else {
            return Err(Failure::UnexpectedMessage);
        };
        let done = self.roll.on_answer(env, answer)?;
        r.next = Some(Staged {
            pk: r.cur.rolled(p, &done.dh).map_err(|_| Failure::KeyOperation)?,
            floor: done.peer_switch_pn,
        });
        s.pk = s.pk.rolled(p, &done.dh).map_err(|_| Failure::KeyOperation)?;
        s.phase = !s.phase;
        s.since = now;
        self.request_at = None;
        Ok(())
    }
}

conn_impl! {
    /// Start a roll if the keys are due. The send path calls this before it builds packets.
    pub(super) fn roll_tick(&mut self, env: &mut Env<'_, P>) {
        if self.phase != Phase::Connected || !self.keys.roll_due(env.now, self.cfg.key_update_after) {
            return;
        }
        // A failing generator leaves the roll for the next attempt.
        let _ = self.keys.begin(|roll| roll.start(env));
    }

    /// The body of the REKEY frame to send now, written to the start of `out`, and its length; `None` when there is
    /// nothing to send. A request is offered again each probe timeout until it is answered.
    pub fn poll_rekey_body(&mut self, now: u64, out: &mut [u8]) -> Option<usize> {
        let pto = self.rec.pto_duration();
        let rekey = self.keys.poll_rekey(now, pto)?;
        rekey.encode(out).ok()
    }

    /// When the pending REKEY request is due to be sent again, if one waits for its answer.
    pub fn rekey_deadline(&self) -> Option<u64> {
        self.keys.rekey_deadline(self.rec.pto_duration())
    }

    /// Take a received REKEY frame body. A request stages the new keys and queues the answer; an answer switches the
    /// sending key. A body that does not parse, or does not fit the state of the roll, is dropped.
    pub fn on_rekey_body(&mut self, env: &mut Env<'_, P>, body: &[u8]) {
        let Ok(rekey) = Rekey::decode(body) else {
            self.violation(env.now, code::FRAME_ENCODING, "malformed rekey");
            return;
        };
        let p = env.provider;
        let result = if rekey.answer {
            self.keys.on_answer(p, env, &rekey, env.now)
        } else {
            let next_pn = self.next_pn;
            self.keys.on_request(p, env, &rekey, next_pn)
        };
        if let Err(f) = result
            && f.is_fatal()
        {
            self.violation(env.now, code::INTERNAL, "key roll failed");
        }
    }
}
