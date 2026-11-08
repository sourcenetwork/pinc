//! Driving the handshake machine: its events install keys, open the connection or end it, and key requests are
//! shown to the host.

use vinc_crypto::Provider;
use vinc_security::{ClientTickets, Env, Event as SecEvent, Failure, KeyResponse, SoftKeys, TicketBatch};

use super::event::{CloseReason, Ev};
use super::handshake::Machine;
use super::keys::Dir;
use super::path::PathState;
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

    /// Send READY to the peer.
    pub fn send_ready(&mut self) {
        self.ctl.ready = true;
    }

    /// Run the handshake machine until it has nothing more to report.
    pub(super) fn pump(&mut self, env: &mut Env<'_, P>) {
        while let Some(ev) = self.hs.step() {
            self.on_hs_event(env, ev);
        }
        if self.hs.request.is_some() && !self.hs.request_announced {
            self.hs.request_announced = true;
            self.push(Ev::KeyRequest);
        }
    }

    fn on_hs_event(&mut self, env: &mut Env<'_, P>, ev: SecEvent) {
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
                if self.keys.install(env.provider, &est.traffic).is_err() {
                    self.silent_close(CloseReason::Handshake(Failure::InvalidParameter));
                    return;
                }
                self.resumed = est.resumed;
                self.phase = Phase::Connected;
                self.life.last_activity = now;
                if !self.client {
                    self.hs.confirm();
                    if let Some(p) = self.paths.active_mut() {
                        p.state = PathState::Validated;
                        p.amp.validate();
                    }
                    if !est.resumed && !est.tickets.entries().is_empty() {
                        self.ctl.tickets = Some(est.tickets);
                        self.ctl.tickets_pending = true;
                    }
                } else if !est.tickets.entries().is_empty() {
                    self.push(Ev::Tickets(est.tickets));
                }
                let (len, key) = (self.cfg.cid_len, self.cfg.reset_key);
                // A failing generator leaves the peer with fewer ids; the next retirement tries again.
                let _ = self.cids.issue(env, len, &key, NP);
                self.mtu_start();
                self.est = Some(est);
                self.push(Ev::Connected(self.resumed));
                self.drain_early(env);
            }
        }
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
