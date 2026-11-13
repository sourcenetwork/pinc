//! The relay a hub runs for its members inside the simulated node: carrier frames in and out, the handshake flush, and
//! the stream drain.

use super::*;

impl<A: SimApps> SimNode<A> {
    // ---------------------------------------------------------------- the relay of a hub

    pub(super) fn apply(&mut self, now: Time, s: Collect) {
        for e in s.0 {
            match e {
                Eff::Carrier(to, plain) => self.write_frame(to, &plain),
                Eff::Udp(UdpTarget::Reply(a), d) => self.out.datagrams.push_back((self.addr, a, d)),
                Eff::Udp(UdpTarget::Member(n), d) => {
                    if let Some(a) = self.member_addr(&n) {
                        self.out.datagrams.push_back((self.addr, a, d));
                    }
                }
                Eff::Local(from, packet) => {
                    let slot = self.slot(&from);
                    let mut p = packet;
                    self.node
                        .handle_datagram(now, self.addr, relay_addr(false, LOCAL_RELAY, slot), &mut p);
                }
                Eff::Close(node, session) => {
                    let hub = self.hub.as_mut().unwrap();
                    if let Some(sid) = hub.by_node.get(&node).copied()
                        && hub.streams.get(&sid).and_then(|r| r.session) == Some(session)
                    {
                        self.out.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                        hub.streams.remove(&sid);
                        hub.by_node.remove(&node);
                    }
                }
                Eff::Trace(t) => {
                    self.node.relay_trace(now, &t);
                    self.events.push_back(NEv::Relay(t));
                }
            }
        }
    }

    pub(super) fn write_frame(&mut self, to: NodeId, plain: &[u8]) {
        let hub = self.hub.as_mut().unwrap();
        let Some(sid) = hub.by_node.get(&to).copied() else {
            return;
        };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let Ok(n) = rs.carrier.seal_bytes(&self.prov, plain, &mut out) else {
            return;
        };
        out.truncate(n);
        let data = wrap(rs, &out);
        self.out.ops.push_back((
            StreamOp::Write {
                stream: sid,
                len: data.len(),
                send_at: None,
            },
            data,
        ));
    }

    pub(super) fn flush_handshake(&mut self, sid: StreamId) {
        let hub = self.hub.as_mut().unwrap();
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut buf = vec![0u8; 32 * 1024];
        loop {
            let n = rs.carrier.transmit(&mut buf);
            if n == 0 {
                break;
            }
            let data = wrap(rs, &buf[..n]);
            self.out.ops.push_back((
                StreamOp::Write {
                    stream: sid,
                    len: data.len(),
                    send_at: None,
                },
                data,
            ));
        }
    }

    pub(super) fn drain(&mut self, now: Time, sid: StreamId) {
        for _ in 0..1024 {
            let mut sink = Collect::default();
            let step = {
                let hub = self.hub.as_mut().unwrap();
                let Some(rs) = hub.streams.get_mut(&sid) else { return };
                let mut env = Env {
                    provider: &self.prov,
                    now,
                    drbg: &mut self.hdrbg,
                };
                match rs.carrier.poll(&mut env, &mut hub.stores) {
                    Ok(Poll::Idle) => Step::Idle,
                    Ok(Poll::Handshake) => Step::Flush,
                    Ok(Poll::KeyRequest) => {
                        let soft = SoftKeys {
                            signer: Some((KeyHandle(1), &self.kp)),
                            prekeys: None,
                        };
                        if rs.carrier.answer_soft(&mut env, &soft).is_ok() {
                            Step::Flush
                        } else {
                            Step::Dead
                        }
                    }
                    Ok(Poll::Open(peer)) => Step::Open(peer),
                    Ok(Poll::Frame(f)) => {
                        if let (Some(node), Some(sess)) = (rs.node, rs.session) {
                            let _ = hub.relay.carrier_frame(now, &node, sess, &f, &mut sink);
                        }
                        Step::Frame
                    }
                    Err(e) => {
                        if e.is_fatal() {
                            Step::Dead
                        } else {
                            Step::Flush
                        }
                    }
                }
            };
            match step {
                Step::Idle => {
                    self.flush_handshake(sid);
                    return;
                }
                Step::Flush => self.flush_handshake(sid),
                Step::Frame => self.apply(now, sink),
                Step::Open(peer) => {
                    self.flush_handshake(sid);
                    let mut s = Collect::default();
                    let hub = self.hub.as_mut().unwrap();
                    if let Ok(sess) = hub.relay.carrier_opened(now, peer, &mut s) {
                        if let Some(rs) = hub.streams.get_mut(&sid) {
                            rs.node = Some(peer);
                            rs.session = Some(sess);
                        }
                        if let Some(old) = hub.by_node.insert(peer, sid)
                            && old != sid
                        {
                            hub.streams.remove(&old);
                            self.out.ops.push_back((StreamOp::Close { stream: old }, Vec::new()));
                        }
                    }
                    self.apply(now, s);
                }
                Step::Dead => {
                    self.out.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                    self.drop_stream(now, sid);
                    return;
                }
            }
        }
    }

    pub(super) fn drop_stream(&mut self, now: Time, sid: StreamId) {
        let Some(hub) = self.hub.as_mut() else { return };
        if let Some(rs) = hub.streams.remove(&sid)
            && let (Some(node), Some(sess)) = (rs.node, rs.session)
        {
            if hub.by_node.get(&node) == Some(&sid) {
                hub.by_node.remove(&node);
            }
            let mut s = Collect::default();
            hub.relay.carrier_closed(now, &node, sess, &mut s);
            self.apply(now, s);
        }
    }
}
