//! A hub and two members over in-memory links, drained the way the runtime layer does: what a node writes onto a
//! carrier while it hands out datagrams leaves in that same drain.

#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use std::collections::HashMap;
use std::net::SocketAddr;

use super::*;

type C = Core<16, 160>;

const MS: u64 = 1_000_000;

struct World {
    cores: Vec<C>,
    udp: Vec<SocketAddr>,
    hub_tcp: SocketAddr,
    /// Datagrams and stream bytes in flight: delivered on the next turn.
    dgrams: Vec<(usize, SocketAddr, Vec<u8>)>,
    bytes: Vec<(usize, StreamId, Vec<u8>)>,
    /// (core, stream) at one end of a carrier, and the other end.
    links: HashMap<(usize, StreamId), (usize, StreamId)>,
    unflushed: usize,
}

fn spec(name: &str, addr: &str, hubs: &[HubAddr], is_hub: bool) -> Spec {
    Spec {
        name: name.into(),
        identity_salt: 0,
        addr: addr.parse().unwrap(),
        hubs: hubs.to_vec(),
        is_hub,
        mtu: 1500,
        trace: false,
        batch: 1,
        pool_chunks: 1024,
        portmap: false,
    }
}

impl World {
    fn new() -> Self {
        let hub = HubAddr {
            id: node_id("hub", 0).unwrap(),
            udp: "10.0.0.1:4433".parse().unwrap(),
            tcp: "10.0.0.1:443".parse().unwrap(),
        };
        let specs = [
            spec("hub", "10.0.0.1:4433", &[hub], true),
            spec("a", "10.0.1.1:4433", &[hub], false),
            spec("b", "10.0.1.2:4433", &[hub], false),
        ];
        Self {
            udp: specs.iter().map(|s| s.addr).collect(),
            cores: specs.iter().map(|s| C::new(s, VApps::default()).unwrap()).collect(),
            hub_tcp: hub.tcp,
            dgrams: Vec::new(),
            bytes: Vec::new(),
            links: HashMap::new(),
            unflushed: 0,
        }
    }

    /// One drain of core `i` in the order the core documents: the datagrams, then the stream operations.
    fn drain(&mut self, i: usize, now: u64) {
        let mut buf = vec![0u8; 64 * 1024];
        for _ in 0..64 {
            self.cores[i].pump(now);
            let mut moved = false;
            while let Some(tx) = self.cores[i].poll_transmit(now, &mut buf) {
                moved = true;
                if let Some(to) = self.udp.iter().position(|a| *a == tx.remote) {
                    self.dgrams.push((to, self.udp[i], buf[..tx.len].to_vec()));
                }
            }
            while let Some(op) = self.cores[i].ops.pop_front() {
                moved = true;
                match op {
                    Op::Connect { stream, to } => {
                        assert_eq!(to, self.hub_tcp);
                        let theirs = 1000 + stream;
                        self.links.insert((i, stream), (0, theirs));
                        self.links.insert((0, theirs), (i, stream));
                        self.cores[0].stream_event(now, StreamEv::Accepted(theirs));
                        self.cores[i].stream_event(now, StreamEv::Opened(stream));
                    }
                    Op::Write { stream, data } => {
                        if let Some((to, s)) = self.links.get(&(i, stream)) {
                            self.bytes.push((*to, *s, data));
                        }
                    }
                    Op::Close { .. } => {}
                }
            }
            self.cores[i].events.clear();
            if !moved {
                break;
            }
        }
        // Idle: a further turn must find nothing the drain left behind.
        self.cores[i].pump(now);
        self.unflushed += self.cores[i].ops.len();
        self.cores[i].ops.clear();
    }

    fn turn(&mut self, now: u64) {
        for (to, from, mut d) in std::mem::take(&mut self.dgrams) {
            self.cores[to].handle_datagram(now, from, &mut d);
        }
        for (to, s, d) in std::mem::take(&mut self.bytes) {
            self.cores[to].stream_event(now, StreamEv::Data(s, d));
        }
        for i in 0..self.cores.len() {
            if self.cores[i].poll_timeout().is_some_and(|t| t <= now) {
                self.cores[i].handle_timeout(now);
            }
            self.drain(i, now);
        }
    }
}

#[test]
fn what_a_relay_path_writes_onto_a_carrier_leaves_in_the_same_drain() {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(|| {
            let mut w = World::new();
            let base = w.cores[0].now();
            let b = node_id("b", 0).unwrap().bytes;
            for k in 0..4000u64 {
                let now = base + k * MS;
                if k == 1500 {
                    let fetch = NCmd::Fetch {
                        root: [7; 32],
                        length: 1 << 20,
                        providers: vec![b],
                    };
                    w.cores[1].command(now, fetch).unwrap();
                    w.drain(1, now);
                }
                w.turn(now);
            }
            assert!(
                w.cores[2].counters.get("session_up").copied().unwrap_or(0) > 0,
                "b took no session"
            );
            assert_eq!(w.unflushed, 0, "carrier bytes waited for the next turn");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A node asks its router for a mapping only when it is told to: a node of a site with no port-mapping service runs as
/// the facade builds an endpoint by default.
#[test]
fn only_a_node_told_to_asks_its_router_for_a_mapping() {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(|| {
            let hub = HubAddr {
                id: node_id("hub", 0).unwrap(),
                udp: "10.0.0.1:4433".parse().unwrap(),
                tcp: "10.0.0.1:443".parse().unwrap(),
            };
            for on in [false, true] {
                let mut s = spec("a", "10.0.1.1:4433", &[hub], false);
                s.portmap = on;
                let mut c = C::new(&s, VApps::default()).unwrap();
                let base = c.now();
                let mut buf = vec![0u8; 64 * 1024];
                for k in 0..5u64 {
                    c.pump(base + k * MS);
                    while c.poll_transmit(base + k * MS, &mut buf).is_some() {}
                }
                assert_eq!(c.counters.contains_key("portmap_udp"), on, "port mapping {on}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
