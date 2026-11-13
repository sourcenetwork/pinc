//! The host loop of a simulated node: one turn of key answers, access checks, carrier I/O and stream plumbing,
//! repeated until nothing moves.

use super::*;

impl<A: SimApps> SimNode<A> {
    /// One turn of the host loop, repeated until nothing moves.
    pub fn pump(&mut self, now: Time) {
        if self.down {
            return;
        }
        self.now = now;
        self.node.set_wall_ms(now, self.wall_ms(now));
        for _ in 0..128 {
            metered(|| self.node.poll(now));
            let mut busy = self.events_step(now);
            busy |= self.members_step(now);
            busy |= self.keys_step(now);
            busy |= self.io_step(now);
            busy |= self.tx_step(now);
            busy |= self.udp_step();
            busy |= self.streams_out_step();
            busy |= self.trace_step(now);
            if !busy {
                return;
            }
        }
        panic!("the host loop of a node does not settle at {now}");
    }

    pub(super) fn trace_step(&mut self, now: Time) -> bool {
        let mut did = false;
        while let Some(t) = self.node.poll_trace() {
            did = true;
            if !matches!(t.body, vinc_node::Body::Core(_)) {
                self.traces.push((now, t));
            }
        }
        let inc = self.node.membership().incarnation();
        if self.incarnations.last() != Some(&inc) {
            self.incarnations.push(inc);
        }
        did
    }

    pub(super) fn events_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(ev) = self.node.poll_event() {
            did = true;
            match &ev {
                NodeEvent::Endpoint(e) => self.duty(now, *e),
                NodeEvent::BroadcastAcpCheck { id, .. } => {
                    let allow = self.bc_allow;
                    self.node.broadcast_acp_answer(now, *id, allow);
                }
                _ => {}
            }
            self.events.push_back(NEv::Node(ev));
        }
        did
    }

    /// The host duties of one endpoint event: key requests, access checks, and the relay's view of its members.
    pub(super) fn duty(&mut self, now: u64, ev: Event) {
        match ev {
            Event::KeyRequest { session } => {
                let owned = match self.node.endpoint().query(Query::KeyRequest(session)) {
                    vinc_core::Answer::KeyRequest(req) => Some(answer_parts(
                        &self.prov,
                        &self.kp,
                        &self.prekeys,
                        &mut self.hdrbg,
                        now,
                        &req,
                    )),
                    _ => None,
                };
                if let Some(owned) = owned {
                    let _ = self.node.command(
                        now,
                        Command::KeyResponse {
                            session,
                            response: owned.response(),
                        },
                    );
                }
            }
            Event::AcpCheck { check, .. } => {
                let allow = !self.deny;
                let _ = self.node.command(now, Command::AcpAnswer { check, allow });
            }
            _ => {}
        }
    }

    /// What the node tells the hub's relay about its members: a session ended, a member woke.
    pub(super) fn members_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(n) = self.node.poll_member() {
            did = true;
            let Some(h) = self.hub.as_mut() else { continue };
            match n {
                MemberNotice::Gone(m) => h.relay.udp_gone(&m),
                MemberNotice::Awake(m) => {
                    let mut s = Collect::default();
                    h.relay.member_returned(now, &m, &mut s);
                    self.apply(now, s);
                }
            }
        }
        did
    }

    pub(super) fn keys_step(&mut self, now: u64) -> bool {
        let mut did = false;
        for i in 0..NRL {
            for _ in 0..8 {
                let owned = self
                    .node
                    .key_request(i)
                    .map(|r| answer_parts(&self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &r));
                let Some(owned) = owned else { break };
                did = true;
                self.node.key_response(now, i, owned.response());
            }
        }
        for _ in 0..8 {
            let owned = self
                .node
                .sign_request()
                .map(|r| answer_parts(&self.prov, &self.kp, &self.prekeys, &mut self.hdrbg, now, &r));
            let Some(owned) = owned else { break };
            did = true;
            self.node.sign_response(now, owned.response());
        }
        did
    }

    pub(super) fn io_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(io) = self.node.poll_io() {
            did = true;
            match io {
                Io::Open { relay, kind, to } => {
                    self.kinds[relay] = kind;
                    self.opening[relay] = Some(to);
                    self.out.ops.push_back((
                        StreamOp::Connect {
                            local: self.addr,
                            remote: to,
                            kind: match kind {
                                Kind::Tcp => StreamKind::Tcp,
                                Kind::Ws => StreamKind::Ws,
                            },
                            simultaneous: false,
                        },
                        Vec::new(),
                    ));
                }
                Io::Close { relay } => {
                    if let Some(s) = self.streams[relay].take() {
                        self.out.ops.push_back((StreamOp::Close { stream: s }, Vec::new()));
                    }
                    self.opening[relay] = None;
                    self.cws[relay] = None;
                }
            }
        }
        let _ = now;
        did
    }

    pub(super) fn tx_step(&mut self, now: u64) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some(t) = metered(|| self.node.poll_transmit(now, &mut buf)) {
            did = true;
            if let Some((relay, slot)) = relay_parts(&t.remote)
                && relay == LOCAL_RELAY
            {
                let Some(node) = self.hub.as_ref().and_then(|h| h.slots.get(usize::from(slot)).copied()) else {
                    continue;
                };
                let mut s = Collect::default();
                let _ = self
                    .hub
                    .as_mut()
                    .unwrap()
                    .relay
                    .send_local(now, &node, 0, &buf[..t.len], &mut s);
                self.apply(now, s);
            } else {
                self.out.datagrams.push_back((t.local, t.remote, buf[..t.len].to_vec()));
            }
        }
        did
    }

    pub(super) fn udp_step(&mut self) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some((to, n)) = self.node.poll_udp(&mut buf) {
            did = true;
            if to.port() == vinc_connect::local::PORT {
                continue;
            }
            self.out.datagrams.push_back((self.addr, to, buf[..n].to_vec()));
        }
        did
    }

    pub(super) fn streams_out_step(&mut self) -> bool {
        let mut did = false;
        // One WebSocket frame carries at most one record's payload.
        let mut buf = vec![0u8; 20_000.min(ws::MAX_PAYLOAD)];
        for i in 0..NRL {
            let Some(stream) = self.streams[i] else { continue };
            loop {
                let n = self.node.poll_stream(i, &mut buf);
                if n == 0 {
                    break;
                }
                did = true;
                let data = if self.kinds[i] == Kind::Ws {
                    let mut f = vec![0u8; n + 16];
                    let mask = [0x11, 0x22, 0x33, 0x44];
                    let m = ws::encode(Opcode::Binary, &buf[..n], Some(mask), &mut f).unwrap();
                    f.truncate(m);
                    f
                } else {
                    buf[..n].to_vec()
                };
                self.out.ops.push_back((
                    StreamOp::Write {
                        stream,
                        len: data.len(),
                        send_at: None,
                    },
                    data,
                ));
            }
        }
        did
    }

    pub(super) fn feed(&mut self, now: u64, relay: usize, mut bytes: &[u8]) {
        for _ in 0..64 {
            let n = self.node.stream_data(now, relay, bytes);
            bytes = &bytes[n..];
            self.keys_step(now);
            if bytes.is_empty() || (n == 0 && self.node.key_request(relay).is_none()) {
                return;
            }
        }
    }
}
