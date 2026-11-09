//! Driving the handshake machine: its events install keys, open the connection or end it, and key requests are
//! shown to the host.

use vinc_crypto::Provider;
use vinc_security::{
    ClientTickets, Env, Event as SecEvent, Failure, KeyResponse, ServerTickets, SoftKeys, TicketBatch,
};

use super::event::{CloseReason, Ev};
use super::handshake::Machine;
use super::keys::Dir;
use super::params::{CreditRecord, peer_limits};
use super::recv::Rx;
use super::{Connection, Phase};
use crate::stream::StreamSource;

/// The largest early packet replayed: the biggest datagram a path carries.
const EARLY_MAX: usize = 9216;

conn_impl! {
    /// Answer the key request last announced by [`Event::KeyRequest`](super::Event::KeyRequest).
    ///
    /// # Errors
    /// A [`Failure`] if there is no such request or the machine refuses the answer.
    pub fn on_key_response(&mut self, env: &mut Env<'_, P>, resp: KeyResponse<'_>) -> Result<(), Failure> {
        self.hs.request = None;
        let r = match &mut self.hs.machine {
            Machine::Client(m) => m.on_key_response(env, resp),
            Machine::Server(m) => m.on_key_response(env, resp),
        };
        self.pump(env);
        r
    }

    /// Answer the outstanding key request at once from software keys. Returns whether there was one.
    ///
    /// # Errors
    /// As [`on_key_response`](Self::on_key_response).
    pub fn answer_soft(&mut self, env: &mut Env<'_, P>, keys: &SoftKeys<'_, P>) -> Result<bool, Failure> {
        self.hs.request = None;
        let r = match &mut self.hs.machine {
            Machine::Client(m) => m.answer_soft(env, keys),
            Machine::Server(m) => m.answer_soft(env, keys),
        };
        self.pump(env);
        r
    }

    /// Store the tickets of a [`TicketsReceived`](super::Event::TicketsReceived) event in `store`, to resume with.
    pub fn store_tickets<const T: usize>(&self, store: &mut ClientTickets<T>, batch: &TicketBatch, now: u64) {
        if let Some(est) = self.est.as_ref() {
            store.accept_batch(est, batch, now);
        }
    }

    /// Issue `count` (at most 4) tickets for this session from `store` and send them to the peer, which keeps them
    /// to resume towards this side. A responder does this by itself after a full handshake; a dialing side calls it
    /// once the session is open to give the responder its one ticket. The peer receives them as
    /// [`TicketsReceived`](super::Event::TicketsReceived).
    ///
    /// # Errors
    /// [`Failure::UnexpectedMessage`] before the session is established; otherwise as
    /// [`ServerTickets::issue_batch`].
    pub fn issue_tickets<const T: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        store: &mut ServerTickets<T>,
        count: usize,
        lifetime_s: u32,
    ) -> Result<(), Failure> {
        let est = self.est.as_ref().ok_or(Failure::UnexpectedMessage)?;
        let batch = store.issue_batch(env, est, count, lifetime_s)?;
        if !batch.entries().is_empty() {
            self.ctl.tickets = Some(batch);
            self.ctl.tickets_pending = true;
        }
        Ok(())
    }

    /// Send READY to the peer.
    pub fn send_ready(&mut self) {
        self.ctl.ready = true;
    }

    /// Run the handshake machine until it has nothing more to report.
    pub(super) fn pump(&mut self, env: &mut Env<'_, P>) {
        while let Some(ev) = self.hs.step(&mut self.pool) {
            self.on_hs_event(env, ev);
        }
        if let Some(rtt) = self.hs.take_rtt_sample() {
            self.rec.seed_rtt(rtt);
        }
        if self.hs.timed_out() && self.phase == Phase::Handshaking {
            self.silent_close(CloseReason::HandshakeTimeout);
        }
        if self.hs.take_fresh() {
            self.fan_mask = self.fan_set;
        }
        if self.hs.request.is_some() && !self.hs.request_announced {
            self.hs.request_announced = true;
            self.push(Ev::KeyRequest);
        }
    }

    pub(super) fn on_hs_event(&mut self, env: &mut Env<'_, P>, ev: SecEvent) {
        let now = env.now;
        match ev {
            SecEvent::EarlyKeys(e) => match Dir::early(env.provider, &e) {
                Ok(d) if self.client => self.keys.early_send = Some(d),
                Ok(d) => self.keys.early_recv = Some(d),
                Err(err) => self.silent_close(CloseReason::Handshake(Failure::Crypto(err))),
            },
            SecEvent::ResumeRejected => {
                self.keys.early_send = None;
                self.flush_in_flight(now);
            }
            SecEvent::Failed(f) => self.silent_close(CloseReason::Handshake(f)),
            SecEvent::Established(est) => {
                if self.keys.install(env.provider, &est.traffic, now).is_err() {
                    self.silent_close(CloseReason::Handshake(Failure::InvalidParameter));
                    return;
                }
                self.resumed = est.resumed;
                self.phase = Phase::Connected;
                self.life.last_activity = now;
                if self.client {
                    if !est.resumed {
                        let srtt = self.rec.rtt().smoothed();
                        self.hs.finish_sent(now, self.rec.pto_duration(), srtt);
                    }
                    if !est.tickets.entries().is_empty() {
                        self.push(Ev::Tickets(est.tickets));
                    }
                } else {
                    if let Some(p) = self.paths.active_mut() {
                        p.validated = true;
                        p.amp.validate();
                    }
                    self.sess_amp.validate();
                    if !est.resumed && !est.tickets.entries().is_empty() {
                        self.ctl.tickets = Some(est.tickets);
                        self.ctl.tickets_pending = true;
                    }
                }
                if !self.apply_peer_credit(&est) {
                    return;
                }
                self.cids.install(est.cid_secret.expose());
                self.mtu_start();
                self.est = Some(est);
                self.push(Ev::Connected(self.resumed));
                self.drain_early(env);
            }
        }
    }

    /// Apply the peer's authenticated credit record. Returns false if the connection was closed instead.
    fn apply_peer_credit(&mut self, est: &vinc_security::Established) -> bool {
        // A server honours 0-RTT within what it remembered advertising: its limits must not have shrunk.
        if est.resumed && !self.client && !self.local_credit.covers(&est.remembered_credit) {
            self.silent_close(CloseReason::Handshake(Failure::InvalidParameter));
            return false;
        }
        self.streams.set_peer_limits(&peer_limits(&est.peer_credit));
        self.peer_credit = est.peer_credit;
        self.pn_len = crate::packet::pn_len_for(est.peer_credit.window_bytes().max(est.local_credit.window_bytes()));
        true
    }

    /// The peer's credit record, once the handshake gave it ([`CreditRecord::NONE`] before, or what a ticket
    /// remembered): the stream window in 16 KiB units, the concurrent-stream limit and the datagram limit.
    pub const fn peer_credit(&self) -> &CreditRecord {
        &self.peer_credit
    }

    /// Process the early 1-RTT packets held while the peer was not yet authenticated.
    fn drain_early(&mut self, env: &mut Env<'_, P>) {
        let mut buf = [0u8; EARLY_MAX];
        while let Some(front) = self.early.front(&self.pool) {
            let n = front.len();
            let ok = match (buf.get_mut(..n), front.get(..n)) {
                (Some(dst), Some(src)) => {
                    dst.copy_from_slice(src);
                    true
                }
                _ => false,
            };
            self.early.pop(&mut self.pool);
            if !ok {
                continue;
            }
            let Some(pkt) = buf.get_mut(..n) else { continue };
            let pn_off = 1 + self.cfg.cid_len;
            let mut ctx = Rx {
                path_id: self.paths.active().map_or(super::PathId(0), |p| p.id),
                path: Some(self.paths.active),
                dlen: n,
                now: env.now,
            };
            // A packet that does not open now is simply lost: the peer sends its data again.
            let _ = self.on_short(env, &mut ctx, pn_off, pkt);
        }
    }
}
