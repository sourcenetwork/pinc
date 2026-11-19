//! Stream carriers in the engine: the requests a node makes, the events and records it receives, and what a crash,
//! a suspension or an interface change does to its connections.
//!
//! A node asks for connections, writes and closes through [`Node::poll_stream`]; the simulator answers through
//! [`Node::handle_stream_event`] and [`Node::handle_stream_record`]. The TCP model itself is in `tcp`.
//!
//! Invariants: a node is told of a stream change only while it is running, and only if it has not restarted since
//! the change was scheduled; stream input waits behind the node's busy period like a datagram does; a crash or a
//! suspension closes every stream of the node and sends a FIN to each peer, while an address change or an interface
//! going down closes them locally without telling the peer (the peer finds out by timeout).

use std::net::SocketAddr;

use crate::Time;
use crate::config::{Call, CostModel, NodeState};
use crate::node::{Node, StreamEvent, StreamId, StreamKind, StreamOp};
use crate::rng::Random;
use crate::sim::{Ev, Sim};
use crate::tcp::State;

/// What the engine hands a node from one of its streams.
pub(crate) enum StreamInput {
    Event(StreamEvent),
    Record(u32, Vec<u8>),
}

impl<N: Node, R: Random, C: CostModel> Sim<N, R, C> {
    /// Makes `local` accept connections for `node`: a connection to this address and port creates a stream of the
    /// given kind and reports it with [`StreamEvent::Opened`]. A node behind a NAT does not listen.
    pub fn listen(&mut self, node: crate::NodeId, local: SocketAddr, kind: StreamKind) {
        self.listeners.insert((local.ip(), local.port()), (node.0, kind));
    }

    /// How many streams `node` has that are not closed.
    pub fn stream_count(&self, node: crate::NodeId) -> usize {
        self.nodes[node.index()].streams.len()
    }

    /// Schedules a stream event for the node at `t` (a plain push: the node may be busy).
    pub(crate) fn push_stream_input(&mut self, t: Time, n: u32, input: StreamInput) {
        let inc = self.nodes[n as usize].incarnation;
        self.push(t, Ev::StreamInput { node: n, inc, input });
    }

    /// Tells a running node of a stream change; a crashed or suspended node is not told.
    pub(crate) fn notify_stream(&mut self, t: Time, n: u32, ev: StreamEvent) {
        if self.nodes[n as usize].state == NodeState::Up {
            self.push_stream_input(t, n, StreamInput::Event(ev));
        }
    }

    /// A whole record reached the open end `e`: the node gets it now, or when it stops being busy.
    pub(crate) fn carrier_record(&mut self, t: Time, e: u32, data: Vec<u8>) {
        let end = &self.ends[e as usize];
        let (n, h) = (end.node, end.handle);
        if self.nodes[n as usize].state != NodeState::Up {
            return;
        }
        self.deliver_stream_input(t, n, StreamInput::Record(h, data));
    }

    /// The node gets the input now, or when it stops being busy. Events and records take the same path, so a record
    /// never overtakes the event that opened its stream.
    pub(crate) fn deliver_stream_input(&mut self, t: Time, n: u32, input: StreamInput) {
        let busy = self.nodes[n as usize].busy_until;
        if busy > t {
            let inc = self.nodes[n as usize].incarnation;
            self.push(busy, Ev::StreamInput { node: n, inc, input });
        } else {
            self.run_stream_input(t, n as usize, input);
        }
    }

    /// A deferred stream input is due: run it, or wait again if the node got busy meanwhile.
    pub(crate) fn on_stream_input(&mut self, t: Time, n: u32, inc: u64, input: StreamInput) {
        let slot = &self.nodes[n as usize];
        if slot.state != NodeState::Up || slot.incarnation != inc {
            return;
        }
        if slot.busy_until > t {
            let at = slot.busy_until;
            self.push(at, Ev::StreamInput { node: n, inc, input });
            return;
        }
        self.run_stream_input(t, n as usize, input);
    }

    fn run_stream_input(&mut self, t: Time, n: usize, input: StreamInput) {
        let bytes = match input {
            StreamInput::Event(ev) => {
                if self.trace.is_some() {
                    self.trace_line(format_args!(
                        "{{\"t\":{t},\"k\":\"stream\",\"n\":{n},\"e\":\"{ev:?}\"}}"
                    ));
                }
                self.nodes[n].node.handle_stream_event(t, ev);
                0
            }
            StreamInput::Record(h, mut data) => {
                let len = data.len();
                self.metrics.nodes[n].stream_records_in += 1;
                self.metrics.nodes[n].stream_bytes_in += len as u64;
                if self.cfg.trace_packets {
                    self.trace_line(format_args!(
                        "{{\"t\":{t},\"k\":\"srec\",\"n\":{n},\"h\":{h},\"len\":{len}}}"
                    ));
                }
                self.nodes[n].node.handle_stream_record(t, StreamId(h), &mut data);
                len
            }
        };
        let send_at = self.finish_call(n, t, Call::Stream, bytes);
        self.drive(n, t, send_at, false);
    }

    /// Carries out one request of node `n`, made in a call at `now` whose output leaves at `send_at`.
    pub(crate) fn stream_op(&mut self, n: usize, now: Time, send_at: Time, op: StreamOp, buf: &[u8]) {
        match op {
            StreamOp::Connect {
                local,
                remote,
                kind,
                simultaneous,
            } => {
                if !self.nodes[n].ifaces.iter().any(|i| i.up && i.addr == local.ip()) {
                    self.metrics.stream_op_errors += 1;
                    return;
                }
                let h = self.nodes[n].next_stream;
                self.nodes[n].next_stream += 1;
                let e = self.ends.len() as u32;
                let mut end = crate::tcp::TcpEnd::new(n as u32, h, true, kind, local, remote);
                end.simul = simultaneous;
                self.ends.push(end);
                self.nodes[n].streams.insert(h, e);
                self.tcp_syn(send_at, e);
                let ev = StreamEvent::Pending {
                    stream: StreamId(h),
                    remote,
                };
                self.push_stream_input(now, n as u32, StreamInput::Event(ev));
            }
            StreamOp::Write {
                stream,
                len,
                send_at: pace,
            } => {
                let open = self.nodes[n]
                    .streams
                    .get(&stream.0)
                    .copied()
                    .filter(|e| self.ends[*e as usize].state == State::Open);
                let Some(e) = open else {
                    self.metrics.stream_write_errors += 1;
                    return;
                };
                let at = send_at.max(pace.unwrap_or(0));
                let data = buf[..len.min(buf.len())].to_vec();
                self.tcp_write(at, e, data, 0, false);
            }
            StreamOp::Close { stream } => {
                if let Some(e) = self.nodes[n].streams.get(&stream.0).copied() {
                    self.tcp_close(now, e, true);
                }
            }
        }
    }

    /// Closes every stream of node `n`, telling each peer with a FIN. Returns the handles, in order.
    pub(crate) fn close_all_streams(&mut self, t: Time, n: usize) -> Vec<u32> {
        let ends: Vec<(u32, u32)> = self.nodes[n].streams.iter().map(|(h, e)| (*h, *e)).collect();
        for (_, e) in &ends {
            self.tcp_close(t, *e, true);
        }
        ends.into_iter().map(|(h, _)| h).collect()
    }

    /// Closes the streams of node `n` bound to the address `ip`, locally: the node is told, the peers are not.
    pub(crate) fn close_streams_on(&mut self, t: Time, n: usize, ip: std::net::IpAddr) {
        let ends: Vec<u32> = self.nodes[n]
            .streams
            .values()
            .copied()
            .filter(|e| self.ends[*e as usize].local.ip() == ip)
            .collect();
        for e in ends {
            self.tcp_close(t, e, false);
        }
    }

    /// The one-way time a FIN takes from end `a` to end `b`: the region delay plus the sender's uplink delay and
    /// the receiver's downlink delay, or the pair link's delay for nodes outside a LAN.
    pub(crate) fn fin_delay(&self, a: u32, b: u32) -> Time {
        let (ea, eb) = (&self.ends[a as usize], &self.ends[b as usize]);
        let site_of = |e: &crate::tcp::TcpEnd| {
            self.nodes[e.node as usize]
                .ifaces
                .iter()
                .find(|i| i.addr == e.local.ip())
                .map(|i| i.site)
        };
        let (Some(sa), Some(sb)) = (site_of(ea), site_of(eb)) else {
            return 0;
        };
        if let (Some(la), Some(lb)) = (self.lan_of(sa), self.lan_of(sb)) {
            let (la, lb) = (&self.lans[la as usize], &self.lans[lb as usize]);
            let region = self
                .region_delay
                .get(&(la.cfg.region, lb.cfg.region))
                .copied()
                .unwrap_or(0);
            region + la.up.cfg.delay + lb.down.cfg.delay
        } else {
            let entry = self.entry_for(eb.local.ip()).map_or(sb, |(_, entry)| entry);
            self.links
                .get(&(sa, entry))
                .map(|l| l.cfg.delay)
                .or_else(|| self.cfg.default_link.as_ref().map(|c| c.delay))
                .unwrap_or(0)
        }
    }
}
