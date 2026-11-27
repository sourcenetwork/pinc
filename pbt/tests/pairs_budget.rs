//! The budget of a punch between two endpoints behind endpoint-dependent translators (`pinc-transport` `Paths::back_left`):
//! the properties of the fix of the chain `repro_pairs.rs` reproduces.

mod core_harness;

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};
use std::net::{IpAddr, SocketAddr};

use core_harness::{ALPN_A, Host, HostCfg, MS, SEC, big_stack};
use pinc_core::{Command, Event, Role, SessionId, Transmit, Value};

/// A translator with endpoint-dependent mapping and endpoint-independent filtering (RFC 4787: a new external port for
/// each new destination, handed out in sequence; any outside host may send to a port it handed out). The kind the
/// world suite calls `DependentOpen`; mappings never expire within the test.
struct Edm {
    ext: IpAddr,
    next: u16,
    map: BTreeMap<SocketAddr, u16>,
}

impl Edm {
    fn new(ext: [u8; 4]) -> Self {
        Self {
            ext: IpAddr::from(ext),
            next: 20_000,
            map: BTreeMap::new(),
        }
    }

    /// The external source of a datagram from the inside host to `dst`.
    fn out(&mut self, dst: SocketAddr) -> SocketAddr {
        let next = &mut self.next;
        let port = *self.map.entry(dst).or_insert_with(|| {
            *next += 1;
            *next - 1
        });
        SocketAddr::new(self.ext, port)
    }

    fn admits(&self, port: u16) -> bool {
        self.map.values().any(|p| *p == port)
    }
}

/// The address host `n` names its peer by on the relay path, as `pinc-core` `relay_net` makes them: `240.relay.peer`.
fn relay_of(n: usize) -> SocketAddr {
    ([240, 0, 0, 1 + n as u8], 0).into()
}

/// Two hosts, each behind an `Edm`, joined by a relay path (20 ms one way, never lost) and by the translators (10 ms
/// one way). What each host sent: (time, sender, over the relay, length).
struct Pair {
    hosts: Vec<Host>,
    nat: [Edm; 2],
    wires: BinaryHeap<Reverse<(u64, u64, usize, SocketAddr, Vec<u8>)>>,
    now: u64,
    seq: u64,
    log: Vec<(u64, usize, bool, usize)>,
}

impl Pair {
    fn new() -> Self {
        let now = 10 * SEC;
        let hosts = vec![
            Host::new(1, ([10, 0, 0, 1], 4433).into(), now, HostCfg::default()),
            Host::new(2, ([10, 0, 1, 1], 4433).into(), now, HostCfg::default()),
        ];
        Self {
            hosts,
            nat: [Edm::new([192, 0, 2, 1]), Edm::new([192, 0, 2, 2])],
            wires: BinaryHeap::new(),
            now,
            seq: 0,
            log: Vec::new(),
        }
    }

    fn pump(&mut self, n: usize) {
        let mut buf = vec![0u8; 65_536];
        for _ in 0..20_000 {
            let now = self.now;
            self.hosts[n].service(now);
            let Some(Transmit {
                remote,
                len,
                segment_size,
                ..
            }) = self.hosts[n].ep.poll_transmit(now, &mut buf)
            else {
                self.hosts[n].service(now);
                return;
            };
            for chunk in buf[..len].chunks(segment_size.max(1)) {
                let m = 1 - n;
                let relay = remote == relay_of(m);
                self.log.push((now, n, relay, chunk.len()));
                self.seq += 1;
                if relay {
                    self.wires
                        .push(Reverse((now + 20 * MS, self.seq, m, relay_of(n), chunk.to_vec())));
                } else {
                    let from = self.nat[n].out(remote);
                    if remote.ip() == self.nat[m].ext && self.nat[m].admits(remote.port()) {
                        self.wires
                            .push(Reverse((now + 10 * MS, self.seq, m, from, chunk.to_vec())));
                    }
                }
            }
        }
        panic!("poll_transmit never returned None");
    }

    fn run_until(&mut self, end: u64, mut stop: impl FnMut(&Self) -> bool) -> bool {
        for _ in 0..2_000_000u32 {
            self.pump(0);
            self.pump(1);
            if stop(self) {
                return true;
            }
            let w = self.wires.peek().map(|Reverse(w)| w.0);
            let t = self
                .hosts
                .iter()
                .filter_map(|h| h.ep.poll_timeout())
                .chain(w)
                .min()
                .unwrap_or(end)
                .max(self.now);
            if t > end {
                self.now = end;
                return stop(self);
            }
            self.now = t;
            while self.wires.peek().is_some_and(|Reverse(w)| w.0 <= t) {
                let Some(Reverse((_, _, m, from, mut d))) = self.wires.pop() else {
                    break;
                };
                let local = self.hosts[m].addr;
                self.hosts[m].ep.handle_datagram(t, local, from, &mut d);
                self.hosts[m].service(t);
            }
            for h in &mut self.hosts {
                if h.ep.poll_timeout().is_some_and(|d| d <= t) {
                    h.ep.handle_timeout(t);
                    h.service(t);
                }
            }
        }
        panic!("the run never reached its end");
    }

    /// Direct (not relayed) datagrams host `n` sent in `[from, to)`.
    fn direct(&self, n: usize, from: u64, to: u64) -> usize {
        self.log
            .iter()
            .filter(|(t, h, relay, _)| *h == n && !*relay && (from..to).contains(t))
            .count()
    }

    fn stream(&mut self, n: usize, s: SessionId) -> u64 {
        let now = self.now;
        match self.hosts[n].cmd(now, Command::OpenStream { session: s, bidi: true }) {
            Ok(core_harness::Reply2 {
                value: Value::Stream(st),
            }) => st,
            _ => panic!("no stream on an established session"),
        }
    }
}

/// A failed punch spends its budget and nothing the peer sends gives it back: the chain of the reproducer
/// (`repro_pairs.rs`, whose fixture this file repeats, as test files share no code) runs for 60 s with data moving
/// the whole time, and after the nine probes' span (about 8.1 s) neither end sends a direct datagram. A peer refills
/// the challenges an end may send back only by a path that validates (`Paths::back_left`), and none does here.
#[test]
fn a_peer_cannot_refill_the_challenges_an_end_sends_back_without_validating_a_path() {
    big_stack(|| {
        let mut p = Pair::new();
        let now = p.now;
        let (peer, to) = (p.hosts[1].id, relay_of(1));
        let rep = p.hosts[0]
            .cmd(
                now,
                Command::Connect {
                    node: peer,
                    alpn: ALPN_A,
                    addrs: &[to],
                    role: Role::Other,
                },
            )
            .expect("dial");
        let Value::Session(sa) = rep.value else {
            panic!("no session")
        };
        assert!(
            p.run_until(now + 10 * SEC, |p| p.hosts[0].opened.contains(&sa)
                && p.hosts[1].count(|e| matches!(e, Event::Incoming { .. })) == 1),
            "the pair did not connect over the relay path"
        );
        let sb = p.hosts[1]
            .session_of(|e| match e {
                Event::Incoming { session, .. } => Some(*session),
                _ => None,
            })
            .expect("an incoming session");
        let hub: SocketAddr = ([198, 18, 0, 1], 3478).into();
        let (ca, cb) = (p.nat[0].out(hub), p.nat[1].out(hub));
        let (st_a, st_b) = (p.stream(0, sa), p.stream(1, sb));
        let now = p.now;
        p.hosts[0].write(now, sa, st_a, vec![1; 100], false);
        p.hosts[1].write(now, sb, st_b, vec![2; 100], false);
        p.run_until(now + 300 * MS, |_| false);
        let punch = p.now;
        p.hosts[0]
            .cmd(punch, Command::Punch { session: sa, addr: cb })
            .expect("punch from host 0");
        p.hosts[1]
            .cmd(punch, Command::Punch { session: sb, addr: ca })
            .expect("punch from host 1");
        // Data keeps moving on the relay path for a minute: the session stays active, so nothing but the budget ends the chain.
        for k in 0..60u64 {
            let at = punch + k * SEC;
            p.run_until(at, |_| false);
            p.hosts[0].write(at, sa, st_a, vec![3; 100], false);
        }
        p.run_until(punch + 60 * SEC, |_| false);
        let after = |n| p.direct(n, punch + 10 * SEC, punch + 60 * SEC);
        let before = |n| p.direct(n, punch, punch + 10 * SEC);
        eprintln!(
            "direct datagrams in the first 10 s and in the 50 s after: host 0 ({}, {}), host 1 ({}, {})",
            before(0),
            after(0),
            before(1),
            after(1)
        );
        assert!(
            after(0) == 0 && after(1) == 0,
            "a peer refilled the budget: host 0 sent {} and host 1 {} direct datagrams after 10 s",
            after(0),
            after(1)
        );
    });
}
