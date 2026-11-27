//! Driving the handshake machine: its events install keys, open the connection or end it, and key requests are
//! shown to the host.

use pinc_crypto::Provider;
use pinc_security::{
    ClientTickets, Env, Event as SecEvent, Failure, KeyResponse, ResponderStores, ServerTickets, SoftKeys, TicketBatch,
};

use super::event::{CloseReason, Ev};
use super::handshake::Machine;
use super::keys::Dir;
use super::params::{CreditRecord, peer_limits};
use super::recv::Rx;
use super::{Connection, Phase};
use crate::packet::packets;
use crate::stream::StreamSource;

/// The largest early packet replayed: the biggest datagram a path carries.
const EARLY_MAX: usize = 9216;

/// What the buffer of early packets depends on, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EarlyView {
    /// 0 handshaking, 1 connected, 2 closing, 3 closed.
    pub phase: u8,
    /// This endpoint dialed.
    pub client: bool,
    /// Packets held for want of keys.
    pub held: usize,
    /// The 0-RTT receive keys exist.
    pub early_keys: bool,
    /// The 1-RTT receive keys exist.
    pub recv_keys: bool,
}

#[cfg(feature = "trace")]
conn_impl! {
    /// The state the buffer of early packets works on.
    pub fn early_view(&self) -> EarlyView {
        EarlyView {
            phase: match self.phase {
                Phase::Handshaking => 0,
                Phase::Connected => 1,
                Phase::Closing => 2,
                Phase::Closed => 3,
            },
            client: self.client,
            held: self.early.len(),
            early_keys: self.keys.early_recv.is_some(),
            recv_keys: self.keys.recv.is_some(),
        }
    }
}

conn_impl! {
    /// Answer the key request last announced by [`Event::KeyRequest`](super::Event::KeyRequest).
    ///
    /// # Errors
    /// A [`Failure`] if there is no such request or the machine refuses the answer.
    pub fn on_key_response(&mut self, env: &mut Env<'_, P>, resp: KeyResponse<'_>) -> Result<(), Failure> {
        self.hs.request = None;
        let r = match self.hs.machine_mut() {
            Some(Machine::Client(m)) => m.on_key_response(env, resp),
            Some(Machine::Server(m)) => m.on_key_response(env, resp),
            None => Err(Failure::UnexpectedKeyResponse),
        };
        self.count_unauthentic(&r);
        self.pump(env);
        r
    }

    /// Answer the outstanding key request at once from software keys. Returns whether there was one.
    ///
    /// # Errors
    /// As [`on_key_response`](Self::on_key_response).
    pub fn answer_soft(&mut self, env: &mut Env<'_, P>, keys: &SoftKeys<'_, P>) -> Result<bool, Failure> {
        self.hs.request = None;
        let r = match self.hs.machine_mut() {
            Some(Machine::Client(m)) => m.answer_soft(env, keys),
            Some(Machine::Server(m)) => m.answer_soft(env, keys),
            None => Ok(false),
        };
        self.count_unauthentic(&r);
        self.pump(env);
        r
    }

    /// Count a handshake message the machine dropped because it did not authenticate: a forged or damaged one, which
    /// leaves the handshake where it was.
    pub(super) fn count_unauthentic<T>(&mut self, r: &Result<T, Failure>) {
        if matches!(r, Err(Failure::Authentication)) {
            self.stats.handshake_dropped += 1;
        }
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
            self.ctl.hold_tickets(batch);
        }
        Ok(())
    }

    /// Send READY to the peer.
    pub fn send_ready(&mut self) {
        self.ctl.owe_ready();
    }

    /// Run the handshake machine until it has nothing more to report.
    pub(super) fn pump(&mut self, env: &mut Env<'_, P>) {
        while let Some(ev) = self.hs.step(&mut self.pool) {
            self.on_hs_event(env, ev);
        }
        if self.hs.timed_out() && self.phase == Phase::Handshaking {
            self.silent_close(if self.hs.unanswered() {
                CloseReason::Unanswered
            } else {
                CloseReason::HandshakeTimeout
            });
        }
        if self.hs.unconfirmed() && self.phase == Phase::Connected {
            self.silent_close(CloseReason::Unconfirmed);
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
                // The 0-RTT packets held for these keys are processed once the session is established, which the
                // same Hello reports next, as the 0-RTT packets that follow the Hello in its datagram are.
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
                    self.follow_reply(env);
                    if let Some(rtt) = self.hs.take_rtt_sample() {
                        self.rec.seed_rtt(rtt);
                    }
                    // The reply came back on one path: the Finish and each resend of it follow it there, not onto the
                    // other paths the flight was copied to.
                    self.set_flight_fanout(&[]);
                    if !est.resumed {
                        let srtt = self.rec.rtt().smoothed();
                        self.hs.finish_sent(now, srtt, self.rec.pto_duration());
                    }
                    if !est.tickets.entries().is_empty() {
                        self.events.push_tickets(est.tickets);
                    }
                } else {
                    if est.resumed {
                        // A resumption Hello proves nothing about its source: anyone who saw it can send a copy from
                        // any address. The session is established; the Reply goes to this one path, and the dialer's
                        // first 1-RTT packet (it needs the Reply's fresh key share) validates it.
                        self.proof = self.paths.active().map(|p| p.id);
                    } else if let Some(p) = self.paths.active_mut() {
                        p.validated = true;
                        p.amp.validate();
                    }
                    self.sess_amp.validate();
                    if !est.resumed && !est.tickets.entries().is_empty() {
                        self.ctl.hold_tickets(est.tickets);
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

    /// A dialing side's session is established, so the message that led there authenticated: the Reply's sealed block
    /// opened and the responder's signature verified, or the resume Reply's confirmation tag matched. Only now does
    /// the datagram that completed it count: the server id the authenticated message named becomes the peer's first
    /// id (the header's source id is never read), and the session continues on its path; that path is validated when
    /// the dial held it (the flight went there), else it proves nothing, since anyone can send a copy of the reply
    /// from any source: its budget counts the datagram and a challenge goes out on it. The path that did not answer is
    /// validated only when a challenge on it is answered. A handshake packet whose message does not authenticate
    /// moves no path, validates none and names no id.
    ///
    /// The reference model acts on the server flight in the same order: it opens the sealed part and verifies the
    /// signature, and only then takes the peer's id and moves to the path the flight came on; a resumption moves only
    /// after its reply has opened. Here nothing leaves between the signature check and the establishment, so the
    /// Finish leaves on the new active path, as the reference's does.
    fn follow_reply(&mut self, env: &mut Env<'_, P>) {
        let Some((id, at, dlen)) = self.reply_from.take() else { return };
        // An established dialing side always has the authenticated id; without it nothing can be addressed.
        let Some(scid) = self.hs.server_cid() else {
            self.silent_close(CloseReason::Handshake(Failure::UnexpectedMessage));
            return;
        };
        self.cids.set_first_remote(scid);
        let held = self.paths.find(id).is_some();
        // A reply on a path the dial does not hold adds it now, as a responder learns one, at the table's bound; at a
        // full table the session stays on its path.
        let Some(pi) = self.learn_path(id, at) else { return };
        if let Some(p) = self.paths.get_mut(pi) {
            p.last_rx = p.last_rx.max(at);
        }
        if pi == self.paths.active {
            return;
        }
        let old = self.paths.active;
        if let Some(p) = self.paths.get_mut(old) {
            p.validated = false;
        }
        if held {
            if let Some(p) = self.paths.get_mut(pi) {
                p.validated = true;
                p.amp.validate();
            }
        } else {
            if let Some(p) = self.paths.get_mut(pi) {
                p.amp.on_receive(dlen as u64);
            }
            self.challenge_path(env, pi);
        }
        self.switch_active(pi);
    }

    /// Apply the peer's authenticated credit record. Returns false if the connection was closed instead.
    fn apply_peer_credit(&mut self, est: &pinc_security::Established) -> bool {
        // A server honours 0-RTT within what it remembered advertising: its limits must not have shrunk.
        if est.resumed && !self.client && !self.local_credit.covers(&est.remembered_credit) {
            self.silent_close(CloseReason::Handshake(Failure::InvalidParameter));
            return false;
        }
        self.streams.set_peer_limits(&peer_limits(&est.peer_credit));
        self.streams.set_early(false);
        self.peer_credit = est.peer_credit;
        self.pn_len = crate::packet::pn_len_for(est.peer_credit.window_bytes().max(est.local_credit.window_bytes()));
        true
    }

    /// The peer's credit record, once the handshake gave it ([`CreditRecord::NONE`] before, or what a ticket
    /// remembered): the stream window in 16 KiB units, the concurrent-stream limit and the datagram limit.
    pub const fn peer_credit(&self) -> &CreditRecord {
        &self.peer_credit
    }

    /// Process the packets held for want of keys, oldest first, now that the session is established: each is tried
    /// once, and one that does not open is lost (its sender sends the data again).
    fn drain_early(&mut self, env: &mut Env<'_, P>) {
        let mut buf = [0u8; EARLY_MAX];
        for _ in 0..self.early.len() {
            let Some(front) = self.early.front(&self.pool) else { break };
            let n = front.len();
            let copied = buf.get_mut(..n).map(|dst| dst.copy_from_slice(front)).is_some();
            self.early.pop(&mut self.pool);
            if !copied {
                continue;
            }
            let Some(bytes) = buf.get_mut(..n) else { continue };
            let mut ctx = Rx {
                path_id: self.paths.active().map_or(super::PathId(0), |p| p.id),
                path: Some(self.paths.active),
                dlen: n,
                now: env.now,
                old_key: false,
            };
            if let Some(Ok(mut pkt)) = packets(bytes, self.cfg.cid_len).next() {
                let _ = self.on_packet(env, None::<&mut ResponderStores<0, 0>>, &mut ctx, &mut pkt);
            }
            if matches!(self.phase, Phase::Closed | Phase::Closing) {
                break;
            }
        }
    }
}
