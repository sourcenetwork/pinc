//! The simulator's node contract for a simulated node: datagrams, timeouts, commands, stream events, and the
//! crash, restart, suspend and resume lifecycle.

use super::*;

impl<A: SimApps> SimNode<A> {
    // ---------------------------------------------------------------- the simulator's node contract

    pub(super) fn relay_of_stream(&self, s: StreamId) -> Option<usize> {
        self.streams.iter().position(|x| *x == Some(s))
    }

    pub fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if self.down {
            return;
        }
        self.node.set_wall_ms(now, self.wall_ms(now));
        let request = self.hub.is_some() && is_relay_request(data);
        if request {
            let member = self.member_at(&remote);
            let mut s = Collect::default();
            let _ = self
                .hub
                .as_mut()
                .unwrap()
                .relay
                .datagram(now, remote, member.as_ref(), data, &mut s);
            self.apply(now, s);
        } else {
            if self.hub.is_some()
                && data.first().is_some_and(|b| *b >= 0x40)
                && let Some(n) = self.member_at(&remote)
            {
                let _ = self.hub.as_mut().unwrap().relay.udp_heard(&n, now);
            }
            metered(|| self.node.handle_datagram(now, local, remote, data));
        }
        self.pump(now);
    }

    pub fn poll_transmit(&mut self, buf: &mut [u8]) -> Option<vinc_sim::Transmit> {
        let (local, remote, d) = self.out.datagrams.pop_front()?;
        buf[..d.len()].copy_from_slice(&d);
        Some(vinc_sim::Transmit {
            local,
            remote,
            len: d.len(),
            send_at: None,
        })
    }

    pub fn poll_timeout(&self) -> Option<Time> {
        if self.down {
            return None;
        }
        [
            self.node.poll_timeout(),
            self.hub.as_ref().and_then(|h| h.relay.next_deadline()),
            self.held.first().map(|(at, ..)| at + self.carrier_hold),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    pub fn handle_timeout(&mut self, now: Time) {
        if self.down {
            return;
        }
        self.timeouts += 1;
        self.node.set_wall_ms(now, self.wall_ms(now));
        while let Some(pos) = self.held.iter().position(|(at, ..)| at + self.carrier_hold <= now) {
            let (_, relay, bytes) = self.held.remove(pos);
            self.feed(now, relay, &bytes);
        }
        if let Some(h) = self.hub.as_mut()
            && h.relay.next_deadline().is_some_and(|d| d <= now)
        {
            let mut s = Collect::default();
            h.relay.handle_timeout(now, &mut s);
            self.apply(now, s);
        }
        metered(|| self.node.handle_timeout(now));
        self.pump(now);
    }

    pub fn command(&mut self, now: Time, cmd: NCmd) {
        if self.down {
            return;
        }
        self.now = now;
        self.node.set_wall_ms(now, self.wall_ms(now));
        match cmd {
            NCmd::Tick => {}
            NCmd::Subscribe(t) => {
                let _ = self.node.subscribe(now, &t);
            }
            NCmd::Unsubscribe(t) => self.node.unsubscribe(now, &t),
            NCmd::Publish { topic, body } => {
                let _ = self.node.publish(now, &topic, &body);
            }
            NCmd::Leave => self.node.leave(now),
            NCmd::Revoke(p) => {
                let _ = self.node.revoke(now, &p);
            }
            NCmd::AddressChanged => self.node.address_changed(now),
            NCmd::DropCarriers => {
                for i in 0..NRL {
                    if let Some(st) = self.streams[i].take() {
                        self.out.ops.push_back((StreamOp::Close { stream: st }, Vec::new()));
                        self.cws[i] = None;
                        self.node.stream_closed(now, i);
                    }
                }
            }
            NCmd::Deny(d) => self.deny = d,
            NCmd::BroadcastAllow(a) => self.bc_allow = a,
            NCmd::ValuesFetch {
                root,
                length,
                ranges,
                providers,
            } => {
                let spans: Vec<vinc_values::span::Span> = ranges
                    .iter()
                    .map(|(off, len)| vinc_values::span::Span { off: *off, len: *len })
                    .collect();
                let req = vinc_node::ValuesRequest {
                    root,
                    length,
                    ranges: &spans,
                    providers: &providers,
                    deadline: None,
                };
                let _ = self.node.values_fetch(now, &req);
            }
            NCmd::ValuesCancel(f) => {
                let _ = self.node.values_cancel(now, f);
            }
            NCmd::SetsStart { peer, set_ref } => {
                let _ = self.node.sets_start(now, &peer, &set_ref);
            }
            NCmd::DtnSend { to, payload, plan } => {
                let _ = self.node.dtn_send(now, &to, &payload, &plan);
            }
        }
        self.pump(now);
    }

    pub fn poll_stream(&mut self, buf: &mut [u8]) -> Option<StreamOp> {
        let (op, data) = self.out.ops.pop_front()?;
        buf[..data.len()].copy_from_slice(&data);
        Some(op)
    }

    pub fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        if self.down {
            return;
        }
        self.events.push_back(NEv::Stream(event));
        match event {
            StreamEvent::Pending { stream, remote } => {
                if let Some(i) = self.opening.iter().position(|o| *o == Some(remote)) {
                    self.streams[i] = Some(stream);
                    self.opening[i] = None;
                }
            }
            StreamEvent::Opened { stream, .. } => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.cws[i] = (self.kinds[i] == Kind::Ws).then(|| Decoder::new(WsRole::Server));
                    self.node.stream_opened(now, i);
                } else if let Some(h) = self.hub.as_mut() {
                    h.scid += 1;
                    let scid = ConnId::new(&h.scid.to_be_bytes()).unwrap();
                    let identity = LocalIdentity::from_keypair(&self.kp, KeyHandle(1)).unwrap();
                    let cfg = session::responder_config(identity, scid).unwrap();
                    h.streams.insert(
                        stream,
                        RStream {
                            carrier: Box::new(ProtectedCarrier::accept(cfg)),
                            node: None,
                            session: None,
                            ws: None,
                            sniffed: false,
                        },
                    );
                }
            }
            StreamEvent::Failed { stream } | StreamEvent::Closed { stream } => {
                if let Some(i) = self.relay_of_stream(stream) {
                    self.streams[i] = None;
                    self.cws[i] = None;
                    self.node.stream_closed(now, i);
                } else {
                    self.drop_stream(now, stream);
                }
            }
        }
        self.pump(now);
    }

    pub fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        if self.down {
            return;
        }
        if let Some(i) = self.relay_of_stream(stream) {
            if let Some(dec) = self.cws[i].as_mut() {
                let mut rest: &mut [u8] = data;
                let mut payloads: Vec<Vec<u8>> = Vec::new();
                while let Ok(Some((frame, used))) = dec.decode(rest) {
                    if let WsFrame::Data(p) = frame {
                        payloads.push(p.to_vec());
                    }
                    let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
                    rest = tail;
                }
                for p in payloads {
                    self.read_carrier(now, i, &p);
                }
            } else {
                let d = data.to_vec();
                self.read_carrier(now, i, &d);
            }
            self.pump(now);
            return;
        }
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(rs) = hub.streams.get_mut(&stream) else {
            return;
        };
        if !rs.sniffed {
            rs.sniffed = true;
            // A WebSocket frame starts 0x82 (final binary); a handshake unit starts with a length below 0x8000.
            if data.first() == Some(&0x82) {
                rs.ws = Some(Decoder::new(WsRole::Client));
            }
        }
        let mut payloads: Vec<Vec<u8>> = Vec::new();
        if let Some(dec) = rs.ws.as_mut() {
            let mut rest: &mut [u8] = data;
            while let Ok(Some((frame, used))) = dec.decode(rest) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
                rest = tail;
            }
        } else {
            payloads.push(data.to_vec());
        }
        for p in payloads {
            let mut rest: &[u8] = &p;
            for _ in 0..64 {
                let Some(rs) = self.hub.as_mut().unwrap().streams.get_mut(&stream) else {
                    return;
                };
                let n = rs.carrier.receive(rest);
                rest = &rest[n..];
                self.drain(now, stream);
                if rest.is_empty() || n == 0 {
                    break;
                }
            }
        }
        self.pump(now);
    }

    pub fn crash(&mut self, _now: Time) -> Vec<u8> {
        self.down = true;
        self.out = Outbox::default();
        // What the host keeps (its stores and records) survives the crash; the node's memory does not.
        self.apps = self.node.apps_mut().clone();
        self.seal.blob.borrow().clone()
    }

    pub fn restart(&mut self, now: Time, persisted: &[u8]) {
        let seal = self.seal.clone();
        *seal.blob.borrow_mut() = persisted.to_vec();
        let mut spec = self.spec.clone();
        spec.start = now;
        let incs = std::mem::take(&mut self.incarnations);
        let mut fresh = Self::with_seal(self.apps.clone(), &spec, seal, true);
        fresh.clock = self.clock.clone();
        fresh.node.set_wall_ms(now, fresh.wall_ms(now));
        fresh.restored = fresh.node.dtn_restore(now);
        fresh.incarnations = incs;
        let last = fresh.node.membership().incarnation();
        fresh.incarnations.push(last);
        *self = fresh;
        self.pump(now);
    }

    pub fn suspend(&mut self, now: Time) {
        self.node.suspend(now, self.wall_ms(now));
    }

    pub fn resume(&mut self, now: Time) {
        if self.down {
            return;
        }
        self.node.resume(now, false);
        self.pump(now);
    }

    pub fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        if self.down {
            return;
        }
        if let IfaceEvent::Changed { new, .. } = event {
            self.addr = SocketAddr::new(new, self.addr.port());
        }
        self.node.address_changed(now);
        self.pump(now);
    }

    pub fn clock_changed(&mut self, now: Time, clock: &Clock) {
        self.clock = clock.clone();
        if !self.down {
            self.node.set_wall_ms(now, self.wall_ms(now));
        }
    }
}

impl<A: SimApps> vinc_sim::Node for SimNode<A> {
    type Cmd = NCmd;
    type Event = NEv;

    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        SimNode::handle_datagram(self, now, local, remote, data);
    }

    fn poll_transmit(&mut self, _now: Time, buf: &mut [u8]) -> Option<vinc_sim::Transmit> {
        SimNode::poll_transmit(self, buf)
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        SimNode::poll_timeout(self)
    }

    fn handle_timeout(&mut self, now: Time) {
        SimNode::handle_timeout(self, now);
    }

    fn command(&mut self, now: Time, cmd: NCmd) {
        SimNode::command(self, now, cmd);
    }

    fn poll_event(&mut self) -> Option<NEv> {
        self.events.pop_front()
    }

    fn crash(&mut self, now: Time) -> Vec<u8> {
        SimNode::crash(self, now)
    }

    fn restart(&mut self, now: Time, persisted: &[u8]) {
        SimNode::restart(self, now, persisted);
    }

    fn suspend(&mut self, now: Time) {
        SimNode::suspend(self, now);
    }

    fn resume(&mut self, now: Time) {
        SimNode::resume(self, now);
    }

    fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        SimNode::iface_event(self, now, event);
    }

    fn poll_stream(&mut self, _now: Time, buf: &mut [u8]) -> Option<StreamOp> {
        SimNode::poll_stream(self, buf)
    }

    fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        SimNode::handle_stream_event(self, now, event);
    }

    fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        SimNode::handle_stream_record(self, now, stream, data);
    }

    fn clock_changed(&mut self, now: Time, clock: &Clock) {
        SimNode::clock_changed(self, now, clock);
    }
}
