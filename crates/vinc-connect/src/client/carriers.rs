//! The stream side of [`Connectivity`]: carriers opening, closing and moving frames, and the timers that drive them.

use vinc_crypto::{NodeId, Provider};
use vinc_security::{ConnId, CreditRecord, Env, InitiatorParams, KeyRequest, KeyResponse};

use super::conn::{Connectivity, Io, Kind, Notice, Rly, pop, push};
use super::link::{Act, Ctx, State};
use super::queue::Held;
use crate::carrier::frame::{BatchBuilder, BatchState, DnsAnswer, MAX_PACKET_LEN, Offer};
use crate::carrier::session::{ALPN, CarrierError, Poll, ProtectedCarrier};
use crate::carrier::{AliasTable, Frame};

/// A node whose peak round trip is this long is on a very slow link: queued handshake copies are deduplicated.
pub(super) const DEDUPE_PEAK_RTT: u64 = 3_500_000_000;
/// The short-header packets kept when the carrier of a slow node opens.
pub(super) const KEPT_SHORT: usize = 8;

/// What one polled frame asks of the connectivity layer, copied out so the carrier borrow ends.
enum Got {
    Idle,
    Handshake,
    Key,
    Open(NodeId),
    Recv(NodeId, usize),
    Pong,
    Ping,
    Dns(NodeId, u8, usize),
    Batch(usize),
    Skip,
    Dead,
}

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    pub(super) fn ctx(&self, i: usize) -> Ctx {
        Ctx {
            home: self.net.home() == Some(i),
            rtt: self.node_rtt,
            udp_any: self.udp_any,
            rides: self.rly.get(i).is_some_and(|r| r.rides),
            queued: self.rly.get(i).is_some_and(|r| !r.q.is_empty()),
        }
    }

    fn push_io(&mut self, io: Io) {
        if !push(&mut self.io, io) {
            self.dropped += 1;
        }
    }

    /// The next stream request for the host.
    pub fn poll_io(&mut self) -> Option<Io> {
        pop(&mut self.io)
    }

    fn start_dial(&mut self, i: usize) {
        let Some(r) = self.rly.get_mut(i) else { return };
        let Some(cfg) = r.cfg else { return };
        let (kind, addr) = match (r.kind, cfg.tcp, cfg.ws) {
            (Kind::Tcp, Some(a), _) => (Kind::Tcp, a),
            (Kind::Ws, _, Some(a)) | (_, None, Some(a)) => (Kind::Ws, a),
            (_, Some(a), None) => (Kind::Tcp, a),
            (_, None, None) => return,
        };
        r.kind = kind;
        r.generation += 1;
        self.push_io(Io::Open {
            relay: i,
            kind,
            to: addr,
        });
    }

    pub(super) fn act_pub(&mut self, now: u64, i: usize, a: Act) {
        self.act(now, i, a);
    }

    /// Check that the carrier of `i` still answers, as a session packet or a PING would.
    pub(super) fn check_carrier(&mut self, now: u64, i: usize) {
        self.act(now, i, Act::Check);
    }

    pub(super) fn close_pub(&mut self, i: usize) {
        self.close_stream(i);
    }

    fn act(&mut self, now: u64, i: usize, a: Act) {
        match a {
            Act::Dial => self.start_dial(i),
            Act::Close => {
                self.lookups.clear();
                if let Some(r) = self.rly.get_mut(i)
                    && !r.carrier_open()
                {
                    // The dial watchdog: a dial that never opened tries the other kind next.
                    r.kind = if r.kind == Kind::Tcp { Kind::Ws } else { Kind::Tcp };
                    self.dial_failed(i);
                }
                self.close_stream(i);
            }
            Act::Ping => {
                self.frame_to(now, i, &Frame::Ping);
            }
            Act::Check => {
                // CHECK_RIDE: a session packet that left on this carrier in this very step carries the check.
                // vertexia: any session packet counts, ack-eliciting or not; an ACK-only packet gets no answer and the
                // real PING that follows the wait covers it. Upgrade: have the endpoint say which packets elicit.
                let ridden = self.rly.get(i).is_some_and(|r| r.etx == Some(now));
                let ctx = self.ctx(i);
                if let Some(Act::Ping) = self.rly.get_mut(i).and_then(|r| r.link.check(now, &ctx, ridden)) {
                    self.frame_to(now, i, &Frame::Ping);
                }
            }
        }
    }

    /// End the stream of `i`: the carrier is dropped, the host is asked to close the stream and the link learns of
    /// it. A link that is already down (it was reset, its retry is scheduled) is left as it is.
    fn close_stream(&mut self, i: usize) {
        let now = self.clock;
        let mut went_down = false;
        let mut dial_failed = false;
        if let Some(r) = self.rly.get_mut(i) {
            let was = r.link.state();
            went_down = was == State::Open || r.carrier_open();
            if was != State::Down {
                if was != State::Open {
                    r.kind = if r.kind == Kind::Tcp { Kind::Ws } else { Kind::Tcp };
                    dial_failed = true;
                }
                r.link.closed(now);
            }
            r.carrier = None;
            r.out_len = 0;
            r.bst = BatchState::new();
            r.keyreq = false;
        }
        if went_down {
            self.notice(Notice::CarrierDown(i));
        }
        if dial_failed {
            self.dial_failed(i);
        }
        self.push_io(Io::Close { relay: i });
    }

    // ---- frames out ----

    /// Queue `frame` for the carrier of `i`. Frames queued back to back join one batch that leaves as a single record
    /// (up to 64 frames and 16 KiB); a long-header packet closes the batch and leaves alone. Returns false if the
    /// carrier is not open or the frame was dropped (counted in `dropped`).
    pub(super) fn frame_to(&mut self, now: u64, i: usize, frame: &Frame<'_>) -> bool {
        if !self.rly.get(i).is_some_and(Rly::carrier_open) {
            return false;
        }
        if let Some(r) = self.rly.get_mut(i) {
            r.link.wrote(now);
        }
        match self.offer(i, frame) {
            Ok(Offer::Added) => return true,
            Ok(Offer::Refused) => {}
            Err(_) => {
                self.dropped += 1;
                return false;
            }
        }
        if !self.flush_batch(i) {
            self.dropped += 1;
            return false;
        }
        if let Ok(Offer::Added) = self.offer(i, frame) {
            return true;
        }
        self.seal_alone(i, frame)
    }

    fn offer(&mut self, i: usize, frame: &Frame<'_>) -> Result<Offer, crate::carrier::FrameError> {
        let r = self.rly.get_mut(i).ok_or(crate::carrier::FrameError::NoRoom)?;
        let mut b = BatchBuilder::resume(r.bbuf.as_mut_slice(), r.bst);
        let o = b.offer(frame)?;
        if o == Offer::Added {
            r.bst = b.state();
        }
        Ok(o)
    }

    fn seal_alone(&mut self, i: usize, frame: &Frame<'_>) -> bool {
        let Some(r) = self.rly.get_mut(i) else { return false };
        let (Some(c), Some(slot)) = (r.carrier.as_mut(), r.out.get_mut(r.out_len..)) else {
            self.dropped += 1;
            return false;
        };
        match c.seal(&self.prov, frame, slot) {
            Ok(n) => {
                r.out_len += n;
                true
            }
            Err(e) => {
                self.dropped += 1;
                if e.is_fatal() {
                    self.close_stream(i);
                }
                false
            }
        }
    }

    /// Seal the waiting batch of the carrier of `i` as one record. Returns true if nothing is left waiting; false
    /// means the write buffer was full (the batch stays) or the carrier failed.
    pub(super) fn flush_batch(&mut self, i: usize) -> bool {
        let Some(r) = self.rly.get_mut(i) else { return false };
        if r.bst.is_empty() {
            return true;
        }
        let Some(c) = r.carrier.as_mut() else {
            r.bst = BatchState::new();
            return false;
        };
        let Ok(Some(plain)) = BatchBuilder::resume(r.bbuf.as_mut_slice(), r.bst).finish() else {
            r.bst = BatchState::new();
            return false;
        };
        let Some(slot) = r.out.get_mut(r.out_len..) else {
            return false;
        };
        match c.seal_bytes(&self.prov, plain, slot) {
            Ok(n) => {
                r.out_len += n;
                r.bst = BatchState::new();
                true
            }
            Err(CarrierError::NoRoom) => false,
            Err(e) => {
                r.bst = BatchState::new();
                if e.is_fatal() {
                    self.close_stream(i);
                }
                false
            }
        }
    }

    /// Send `packet` to `dst` through relay `i`'s carrier, or hold it until the carrier opens. A held packet that
    /// would not fit is dropped (the oldest first); transport recovery resends it.
    pub(super) fn send_packet(&mut self, now: u64, i: usize, dst: &NodeId, packet: &[u8]) {
        let Some(r) = self.rly.get(i) else { return };
        let relay_id = r.cfg.map(|c| c.id);
        let ctx = self.ctx(i);
        let act = {
            let Some(r) = self.rly.get_mut(i) else { return };
            r.link.before_send(now, &self.shared, &ctx)
        };
        if let Some(a) = act {
            self.act(now, i, a);
        }
        if self.rly.get(i).is_some_and(|r| r.link.is_open()) {
            let sent = if relay_id.as_ref() == Some(dst) {
                self.frame_to(now, i, &Frame::SelfSend { packet })
            } else {
                let Some(r) = self.rly.get_mut(i) else { return };
                let f = r.ta.send_frame(dst, 0, packet);
                let ok = self.frame_to(now, i, &f);
                if ok && let Some(r) = self.rly.get_mut(i) {
                    r.etx = Some(now);
                }
                if !ok && let Some(r) = self.rly.get_mut(i) {
                    // The relay never learnt an alias the frame would have defined.
                    r.ta = AliasTable::new();
                }
                ok
            };
            if sent {
                return;
            }
        }
        self.hold(i, dst, packet);
        let ctx = self.ctx(i);
        let act = self
            .rly
            .get_mut(i)
            .and_then(|r| r.link.want_dial(now, &mut self.shared, &ctx));
        if let Some(a) = act {
            self.act(now, i, a);
        }
    }

    fn hold(&mut self, i: usize, dst: &NodeId, packet: &[u8]) {
        let Some(r) = self.rly.get_mut(i) else { return };
        self.dropped += r.q.push(dst, packet) as u64;
    }

    /// Send everything held for the carrier of `relay`, oldest first.
    pub(super) fn drain_held(&mut self, now: u64, relay: usize) {
        let mut buf = [0u8; MAX_PACKET_LEN];
        // A packet the carrier cannot take goes back into the queue behind these, so only the ones held now are sent.
        for _ in 0..self.rly.get(relay).map_or(0, |r| r.q.len()) {
            let Some((dst, n)) = self.rly.get_mut(relay).and_then(|r| r.q.pop(&mut buf)) else {
                break;
            };
            self.send_packet(now, relay, &dst, buf.get(..n).unwrap_or_default());
        }
    }

    /// Thin the packets held for `relay` on a slow node: with `dedupe`, first-flight handshake packets of sessions
    /// that are `done` and identical copies of a handshake packet (only the newest stays); then all but the newest
    /// [`KEPT_SHORT`] short-header packets for peers. Handshake packets and packets for the relay itself stay.
    pub(super) fn trim_held(&mut self, relay: usize, dedupe: bool, mut done: impl FnMut(&Held<'_>) -> bool) {
        let relay_id = self.relay_cfg(relay).map(|c| c.id);
        let Some(r) = self.rly.get_mut(relay) else { return };
        let long = |h: &Held<'_>| h.packet.first().is_some_and(|b| b & 0x80 != 0);
        let short_send = |h: &Held<'_>| Some(h.dst) != relay_id && !long(h) && !h.packet.is_empty();
        if dedupe {
            r.q.retain(|q, i, h| {
                if !long(h) || h.packet.len() < 10 {
                    return true;
                }
                if h.packet.len() >= usize::from(vinc_transport::conn::MIN_MTU) && done(h) {
                    return false;
                }
                !(i + 1..q.len()).any(|j| q.get(j).is_some_and(|o| o.dst == h.dst && o.packet == h.packet))
            });
        }
        let mut surplus = (0..r.q.len())
            .filter(|i| r.q.get(*i).is_some_and(|h| short_send(&h)))
            .count()
            .saturating_sub(KEPT_SHORT);
        r.q.retain(|_, _, h| {
            if surplus > 0 && short_send(h) {
                surplus -= 1;
                false
            } else {
                true
            }
        });
    }

    fn drain_handshake(&mut self, i: usize) {
        let Some(r) = self.rly.get_mut(i) else { return };
        let Some(c) = r.carrier.as_mut() else { return };
        while c.pending_transmit() > 0 {
            let Some(room) = r.out.get_mut(r.out_len..) else { break };
            let n = c.transmit(room);
            if n == 0 {
                break;
            }
            r.out_len += n;
        }
    }

    /// Take the bytes the carrier of `relay` wants written to its stream; returns how many were copied into `buf`.
    /// Call until it returns 0.
    pub fn poll_stream(&mut self, relay: usize, buf: &mut [u8]) -> usize {
        self.flush_batch(relay);
        let Some(r) = self.rly.get_mut(relay) else { return 0 };
        let n = buf.len().min(r.out_len);
        if let (Some(d), Some(s)) = (buf.get_mut(..n), r.out.get(..n)) {
            d.copy_from_slice(s);
        }
        r.out.copy_within(n..r.out_len, 0);
        r.out_len -= n;
        // Room was made: packets held because the buffer was full while the carrier was open go in behind it.
        if n > 0 && !r.q.is_empty() && r.link.is_open() {
            self.drain_held(self.clock, relay);
        }
        n
    }

    /// The stream of `relay` opened: start the carrier handshake toward the relay's identity.
    pub fn stream_opened(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize) {
        self.clock = self.clock.max(now);
        let Some(id) = self.rly.get(relay).and_then(|r| r.cfg).map(|c| c.id) else {
            return;
        };
        self.scid = self.scid.wrapping_add(1);
        let scid = ConnId::new(&self.scid.to_be_bytes()).unwrap_or_default();
        let params = InitiatorParams {
            peer: id,
            alpn: ALPN,
            scid,
            identity: &self.identity,
            prekey: &self.prekey,
            peer_has_prekey: false,
            ticket: None,
            credit: CreditRecord::NONE,
        };
        match ProtectedCarrier::dial(env, params) {
            Ok(c) => {
                if let Some(r) = self.rly.get_mut(relay) {
                    r.carrier = Some(super::conn::carrier(c));
                    r.out_len = 0;
                    r.bst = BatchState::new();
                    r.keyreq = false;
                }
                self.drain_handshake(relay);
            }
            Err(_) => self.close_stream(relay),
        }
        let _ = now;
    }

    /// The stream of `relay` closed or its dial failed.
    pub fn stream_closed(&mut self, now: u64, relay: usize) {
        self.clock = self.clock.max(now);
        let Some(r) = self.rly.get_mut(relay) else { return };
        if r.link.state() == State::Down {
            // closed by this side already (a reset or a failed carrier): the retry is scheduled
            r.carrier = None;
            return;
        }
        self.close_stream_quiet(relay);
    }

    /// The network ended the stream: no close request goes back to the host.
    fn close_stream_quiet(&mut self, relay: usize) {
        let now = self.clock;
        let Some(r) = self.rly.get_mut(relay) else { return };
        let was = r.link.state();
        r.carrier = None;
        r.out_len = 0;
        r.bst = BatchState::new();
        r.keyreq = false;
        if was != State::Open {
            // A dial that never opened tries the other kind next: UDP, then TCP, then WebSocket.
            r.kind = if r.kind == Kind::Tcp { Kind::Ws } else { Kind::Tcp };
        }
        r.link.closed(now);
        if was == State::Open {
            self.notice(Notice::CarrierDown(relay));
        } else {
            self.dial_failed(relay);
        }
    }

    /// A carrier dial of `relay` never opened. A relay that fails repeatedly stops being the home.
    fn dial_failed(&mut self, relay: usize) {
        self.net.failed(relay);
        self.check_failover(self.clock);
    }

    /// Move the home away from an unhealthy relay, dial the new home and republish there.
    pub(super) fn check_failover(&mut self, now: u64) {
        let cfg: [bool; R] = core::array::from_fn(|i| self.rly.get(i).is_some_and(|r| r.cfg.is_some()));
        let Some(h) = self.net.failover(|i| cfg.get(i).copied().unwrap_or(false)) else {
            return;
        };
        self.notice(Notice::Home(h));
        self.next_publish = now;
        let ctx = self.ctx(h);
        let act = self
            .rly
            .get_mut(h)
            .and_then(|r| r.link.want_dial(now, &mut self.shared, &ctx));
        if let Some(a) = act {
            self.act(now, h, a);
        }
    }

    /// Bytes arrived on the stream of `relay`. Returns how many were taken; offer the rest again after answering a
    /// key request ([`Connectivity::key_request`]).
    pub fn stream_data(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize, mut bytes: &[u8]) -> usize {
        self.clock = self.clock.max(now);
        let total = bytes.len();
        loop {
            let n = match self.rly.get_mut(relay).and_then(|r| r.carrier.as_mut()) {
                Some(c) => c.receive(bytes),
                None => return total - bytes.len(),
            };
            bytes = bytes.get(n..).unwrap_or_default();
            self.drive_carrier(now, env, relay);
            let stuck = self.rly.get(relay).is_none_or(|r| r.keyreq || r.carrier.is_none());
            if bytes.is_empty() || stuck || n == 0 {
                return total - bytes.len();
            }
        }
    }

    /// The key operation the carrier handshake of `relay` waits for.
    pub fn key_request(&self, relay: usize) -> Option<KeyRequest<'_>> {
        self.rly.get(relay)?.carrier.as_ref()?.key_request()
    }

    /// Answer the key request of `relay`'s carrier.
    pub fn key_response(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize, resp: KeyResponse<'_>) {
        self.clock = self.clock.max(now);
        let Some(c) = self.rly.get_mut(relay).and_then(|r| r.carrier.as_mut()) else {
            return;
        };
        let ok = c.key_response(env, resp).is_ok();
        if let Some(r) = self.rly.get_mut(relay) {
            r.keyreq = false;
        }
        if !ok {
            self.close_stream(relay);
            return;
        }
        self.after_poll_state(now, env, relay);
    }

    /// Answer the key request of `relay`'s carrier from software keys.
    pub fn answer_soft(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize, soft: &vinc_security::SoftKeys<'_, P>) {
        let Some(c) = self.rly.get_mut(relay).and_then(|r| r.carrier.as_mut()) else {
            return;
        };
        let ok = c.answer_soft(env, soft).is_ok();
        if let Some(r) = self.rly.get_mut(relay) {
            r.keyreq = false;
        }
        if !ok {
            self.close_stream(relay);
            return;
        }
        self.after_poll_state(now, env, relay);
    }

    /// After a key answer the handshake may have finished or queued output: record it, then read what is buffered.
    fn after_poll_state(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize) {
        self.drain_handshake(relay);
        let opened = self
            .rly
            .get(relay)
            .is_some_and(|r| r.carrier_open() && !r.link.is_open());
        if opened {
            self.carrier_open(now, relay);
        }
        self.drive_carrier(now, env, relay);
    }

    fn carrier_open(&mut self, now: u64, relay: usize) {
        self.net.healthy(relay);
        let Some(r) = self.rly.get_mut(relay) else { return };
        let was = r.link.opened(now);
        r.ta = crate::carrier::AliasTable::new();
        r.ra = crate::carrier::AliasTable::new();
        r.reverify = was;
        self.notice(Notice::CarrierUp(relay));
        // What waited for the carrier goes out first, in order. On a slow node the stale copies are thinned first;
        // when that needs to know which sessions are established, the host loop does it with the endpoint.
        let slow = self.node_rtt >= super::dial::TG_SLOW;
        if slow && self.node_tgr >= DEDUPE_PEAK_RTT {
            if let Some(r) = self.rly.get_mut(relay) {
                r.drain_due = true;
            }
        } else {
            if slow {
                self.trim_held(relay, false, |_| false);
            }
            self.drain_held(now, relay);
        }
        if self.net.home() == Some(relay) {
            self.next_publish = now;
        }
    }

    /// Read every frame the carrier of `relay` has buffered.
    fn drive_carrier(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize) {
        let mut stores = vinc_security::ResponderStores::<1, 1>::default();
        let mut scratch = [0u8; MAX_PACKET_LEN];
        let mut rec = [0u8; crate::record::MAX_RECORD_LEN];
        let mut batch = [0u8; crate::carrier::frame::MAX_FRAME_LEN];
        for _ in 0..256 {
            let Some(r) = self.rly.get_mut(relay) else { return };
            let Some(c) = r.carrier.as_mut() else { return };
            let relay_id = r.cfg.map(|c| c.id);
            let got = match c.poll(env, &mut stores) {
                Err(e) => {
                    if e.is_fatal() {
                        Got::Dead
                    } else {
                        Got::Skip
                    }
                }
                Ok(Poll::Idle) => Got::Idle,
                Ok(Poll::Handshake) => Got::Handshake,
                Ok(Poll::KeyRequest) => Got::Key,
                Ok(Poll::Open(peer)) => Got::Open(peer),
                Ok(Poll::Frame(Frame::Batch(b))) => {
                    // copy the batch out of the carrier so its frames can be handled one by one
                    match Frame::Batch(b).encode(&mut batch) {
                        Ok(n) => Got::Batch(n),
                        Err(_) => Got::Skip,
                    }
                }
                Ok(Poll::Frame(f)) => Self::copy_out(&mut r.ra, relay_id, &f, &mut scratch, &mut rec),
            };
            match got {
                Got::Idle => {
                    self.drain_handshake(relay);
                    return;
                }
                Got::Handshake | Got::Skip => self.drain_handshake(relay),
                Got::Key => {
                    self.drain_handshake(relay);
                    if let Some(r) = self.rly.get_mut(relay) {
                        r.keyreq = true;
                    }
                    return;
                }
                Got::Dead => {
                    self.close_stream(relay);
                    return;
                }
                Got::Open(peer) => {
                    self.drain_handshake(relay);
                    if relay_id_of(self, relay) == Some(peer) {
                        self.carrier_open(now, relay);
                    } else {
                        self.close_stream(relay);
                        return;
                    }
                }
                Got::Batch(n) => {
                    if let Ok(Frame::Batch(b)) = Frame::decode(batch.get(..n).unwrap_or_default()) {
                        for sub in b.frames() {
                            let rid = relay_id_of(self, relay);
                            let g = match self.rly.get_mut(relay) {
                                Some(r) => Self::copy_out(&mut r.ra, rid, &sub, &mut scratch, &mut rec),
                                None => return,
                            };
                            self.apply_got(now, relay, g, &scratch, &rec);
                        }
                    }
                }
                g @ (Got::Recv(..) | Got::Pong | Got::Ping | Got::Dns(..)) => {
                    self.apply_got(now, relay, g, &scratch, &rec);
                }
            }
        }
    }

    fn apply_got(&mut self, now: u64, relay: usize, g: Got, scratch: &[u8], rec: &[u8]) {
        match g {
            Got::Recv(src, n) => {
                self.heard(now, relay);
                let from = self.path_addr(relay, &src);
                self.deliver(from, scratch.get(..n).unwrap_or_default());
            }
            Got::Pong => {
                self.heard(now, relay);
                if let Some(r) = self.rly.get_mut(relay) {
                    r.pong = true;
                }
            }
            Got::Ping => {
                self.heard(now, relay);
                self.frame_to(now, relay, &Frame::Pong);
            }
            Got::Dns(peer, status, n) => {
                self.heard(now, relay);
                let answer = match status {
                    1 => DnsAnswer::Record(rec.get(..n).unwrap_or_default()),
                    2 => DnsAnswer::TooLarge,
                    _ => DnsAnswer::Absent,
                };
                self.dns_answer_pub(&peer, &answer);
            }
            _ => {}
        }
    }

    fn heard(&mut self, now: u64, relay: usize) {
        if let Some(r) = self.rly.get_mut(relay) {
            r.link.heard(now);
        }
    }

    fn copy_out(
        ra: &mut crate::carrier::AliasTable,
        relay_id: Option<NodeId>,
        f: &Frame<'_>,
        scratch: &mut [u8; MAX_PACKET_LEN],
        rec: &mut [u8; crate::record::MAX_RECORD_LEN],
    ) -> Got {
        let mut take = |src: NodeId, packet: &[u8]| {
            scratch.get_mut(..packet.len()).map_or(Got::Skip, |d| {
                d.copy_from_slice(packet);
                Got::Recv(src, packet.len())
            })
        };
        match *f {
            Frame::Recv { src, packet, .. } => take(src, packet),
            Frame::RecvNew { src, alias, packet, .. } => {
                ra.learn(alias, src);
                take(src, packet)
            }
            Frame::RecvAlias { alias, packet, .. } => ra.resolve(alias).map_or(Got::Skip, |src| take(src, packet)),
            Frame::SelfRecv { packet } => relay_id.map_or(Got::Skip, |id| take(id, packet)),
            Frame::Pong => Got::Pong,
            Frame::Ping => Got::Ping,
            Frame::DnsReply { peer, answer } => match answer {
                DnsAnswer::Record(b) => rec.get_mut(..b.len()).map_or(Got::Skip, |d| {
                    d.copy_from_slice(b);
                    Got::Dns(peer, 1, b.len())
                }),
                DnsAnswer::TooLarge => Got::Dns(peer, 2, 0),
                DnsAnswer::Absent => Got::Dns(peer, 0, 0),
            },
            _ => Got::Skip,
        }
    }
}

fn relay_id_of<P: Provider, const R: usize, const PEERS: usize>(
    c: &Connectivity<P, R, PEERS>,
    i: usize,
) -> Option<NodeId> {
    c.relay_cfg(i).map(|x| x.id)
}
