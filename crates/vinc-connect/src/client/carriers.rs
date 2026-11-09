//! The stream side of [`Connectivity`]: carriers opening, closing and moving frames, and the timers that drive them.

use vinc_crypto::{NodeId, Provider};
use vinc_security::{ConnId, CreditRecord, Env, InitiatorParams, KeyRequest, KeyResponse};

use super::conn::{Connectivity, Io, Kind, Notice, Queued, pop, push};
use super::link::{Act, Ctx, State};
use crate::carrier::Frame;
use crate::carrier::frame::{DnsAnswer, MAX_PACKET_LEN};
use crate::carrier::session::{ALPN, CarrierError, Poll, ProtectedCarrier};

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
            queued: self.rly.get(i).is_some_and(|r| r.q.iter().any(Option::is_some)),
        }
    }

    fn push_io(&mut self, io: Io) {
        if !push(&mut self.io, io) {
            self.dropped += 1;
        }
    }

    /// The next stream request for the host.
    pub fn poll_io(&mut self) -> Option<Io> {
        // A suspending node's sleep notices leave before its carriers close.
        if self.hold_close && self.udp_q.iter().any(Option::is_some) {
            return self
                .io
                .iter()
                .flatten()
                .find(|i| matches!(i, Io::Open { .. }))
                .copied()
                .and_then(|_| pop(&mut self.io));
        }
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

    pub(super) fn close_pub(&mut self, i: usize) {
        self.close_stream(i);
    }

    fn act(&mut self, now: u64, i: usize, a: Act) {
        match a {
            Act::Dial => self.start_dial(i),
            Act::Close => {
                self.lookups.clear();
                self.close_stream(i);
            }
            Act::Ping => {
                self.frame_to(now, i, &Frame::Ping);
            }
            Act::Check => {
                let ridden = false;
                let ctx = self.ctx(i);
                if let Some(Act::Ping) = self.rly.get_mut(i).and_then(|r| r.link.check(now, &ctx, ridden)) {
                    self.frame_to(now, i, &Frame::Ping);
                }
            }
        }
    }

    fn close_stream(&mut self, i: usize) {
        if let Some(r) = self.rly.get_mut(i) {
            r.carrier = None;
            r.out_len = 0;
            r.keyreq = false;
        }
        self.push_io(Io::Close { relay: i });
    }

    // ---- frames out ----

    /// Seal `frame` onto the carrier of `i`. Returns false if the carrier is not open or the buffer is full.
    pub(super) fn frame_to(&mut self, now: u64, i: usize, frame: &Frame<'_>) -> bool {
        let Some(r) = self.rly.get_mut(i) else { return false };
        let Some(c) = r.carrier.as_mut() else { return false };
        if !c.is_open() {
            return false;
        }
        let Some(slot) = r.out.get_mut(r.out_len..) else {
            return false;
        };
        match c.seal(&self.prov, frame, slot) {
            Ok(n) => {
                r.out_len += n;
                r.link.wrote(now);
                true
            }
            Err(CarrierError::NoRoom) => {
                self.dropped += 1;
                false
            }
            Err(e) => {
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
            let sent = {
                let Some(r) = self.rly.get_mut(i) else { return };
                if relay_id.as_ref() == Some(dst) {
                    false
                } else {
                    let f = r.ta.send_frame(dst, 0, packet);
                    // sealing needs the carrier and the output buffer, both in `r`
                    let Some(c) = r.carrier.as_mut() else { return };
                    match r.out.get_mut(r.out_len..).map(|s| c.seal(&self.prov, &f, s)) {
                        Some(Ok(n)) => {
                            r.out_len += n;
                            r.link.wrote(now);
                            true
                        }
                        _ => false,
                    }
                }
            };
            if sent {
                return;
            }
            if relay_id.as_ref() == Some(dst) && self.frame_to(now, i, &Frame::SelfSend { packet }) {
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
        let mut item = Queued {
            dst: *dst,
            len: packet.len(),
            data: [0; MAX_PACKET_LEN],
        };
        let Some(d) = item.data.get_mut(..packet.len()) else {
            return;
        };
        d.copy_from_slice(packet);
        if !push(&mut r.q, item) {
            pop(&mut r.q);
            self.dropped += 1;
            let _ = push(&mut r.q, item);
        }
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
        let Some(r) = self.rly.get_mut(relay) else { return 0 };
        let n = buf.len().min(r.out_len);
        if let (Some(d), Some(s)) = (buf.get_mut(..n), r.out.get(..n)) {
            d.copy_from_slice(s);
        }
        r.out.copy_within(n..r.out_len, 0);
        r.out_len -= n;
        n
    }

    /// The stream of `relay` opened: start the carrier handshake toward the relay's identity.
    pub fn stream_opened(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize) {
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
                    r.carrier = Some(c);
                    r.out_len = 0;
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
        let Some(r) = self.rly.get_mut(relay) else { return };
        let was = r.link.state();
        r.carrier = None;
        r.out_len = 0;
        r.keyreq = false;
        if was != State::Open {
            // A dial that never opened tries the other kind next: UDP, then TCP, then WebSocket.
            r.kind = if r.kind == Kind::Tcp { Kind::Ws } else { Kind::Tcp };
        }
        r.link.closed(now);
        if was == State::Open {
            self.notice(Notice::CarrierDown(relay));
        }
    }

    /// Bytes arrived on the stream of `relay`. Returns how many were taken; offer the rest again after answering a
    /// key request ([`Connectivity::key_request`]).
    pub fn stream_data(&mut self, now: u64, env: &mut Env<'_, P>, relay: usize, mut bytes: &[u8]) -> usize {
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
            .is_some_and(|r| r.carrier.as_ref().is_some_and(ProtectedCarrier::is_open) && !r.link.is_open());
        if opened {
            self.carrier_open(now, relay);
        }
        self.drive_carrier(now, env, relay);
    }

    fn carrier_open(&mut self, now: u64, relay: usize) {
        let Some(r) = self.rly.get_mut(relay) else { return };
        let was = r.link.opened(now);
        r.ta = crate::carrier::AliasTable::new();
        r.ra = crate::carrier::AliasTable::new();
        self.notice(Notice::CarrierUp(relay));
        let _ = was;
        // What waited for the carrier goes out first, in order.
        while let Some(q) = self.rly.get_mut(relay).and_then(|r| pop(&mut r.q)) {
            let packet = q.data.get(..q.len).unwrap_or_default();
            self.send_packet(now, relay, &q.dst, packet);
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
            Got::Pong => self.heard(now, relay),
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
