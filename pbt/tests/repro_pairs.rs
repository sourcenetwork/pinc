//! Reproducing tests of the endpoint's table of address pairs (`pinc-core` `endpoint.rs` `paths`): what may add a pair
//! to it and what may push a pair out of it. Each fails on the unmodified code, apart from the tests marked as
//! controls. The driver is `core_harness`: real endpoints on one scripted link, and a third party that hands a host
//! datagrams from any source address (`Net::deliver`).

mod core_harness;

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};
use std::net::{IpAddr, SocketAddr};

use core_harness::{ALPN_A, D, Host, HostCfg, MS, Net, SEC, big_stack};
use pinc_core::{Command, Event, Role, SessionId, Transmit, Value};

/// A server (host 0) with two established sessions, one dialed by host 1 and one by host 2, after a quiet second.
fn two_sessions() -> (Net, SessionId, SessionId) {
    let mut net = Net::new(7);
    let (a, b, c) = (net.add(1, HostCfg::default()), net.add(2, HostCfg::default()), net.add(3, HostCfg::default()));
    let (_, ab) = net.connect_pair(b, a, ALPN_A).expect("host 1 reaches host 0");
    let (_, ac) = net.connect_pair(c, a, ALPN_A).expect("host 2 reaches host 0");
    net.run_for(SEC);
    (net, ab, ac)
}

/// The destination id of the last short-header datagram host `from` sent to host `to`: an id `to` holds for their
/// session, which anyone on the path reads in clear.
fn seen_id(net: &Net, from: usize, to: usize) -> [u8; 4] {
    let (f, t) = (net.hosts[from].addr, net.hosts[to].addr);
    let d = net
        .captured
        .iter()
        .rev()
        .find(|(l, r, d)| *l == f && *r == t && d.first().is_some_and(|b| b & 0x80 == 0) && d.len() > 5)
        .map(|(_, _, d)| d.clone())
        .expect("a short-header datagram on the link");
    [d[1], d[2], d[3], d[4]]
}

/// A forged source address of the third party: nobody lives there.
fn forged(k: usize) -> SocketAddr {
    ([198, 51, (k >> 8) as u8, k as u8], 9000).into()
}

/// Host 0 writes `n` bytes on a new stream of session `s`, and its next `poll_transmit` calls run: the destinations of
/// the datagrams it sent and the growth of `dropped_out`.
fn write_and_pump(net: &mut Net, s: SessionId, n: usize) -> (Vec<SocketAddr>, u64) {
    let now = net.now;
    let Ok(core_harness::Reply2 { value: Value::Stream(st) }) =
        net.hosts[0].cmd(now, Command::OpenStream { session: s, bidi: true })
    else {
        panic!("no stream on an established session")
    };
    let (sent, dropped) = (net.tapped.len(), net.hosts[0].ep.node_stats().dropped_out);
    net.hosts[0].write(now, s, st, vec![9; n], true);
    net.pump(0);
    let to = net.tapped[sent..].iter().filter(|(_, h, _, _)| *h == 0).map(|(_, _, r, _)| *r).collect();
    (to, net.hosts[0].ep.node_stats().dropped_out - dropped)
}

/// Bug: junk datagrams that carry one connection id of one session, sent from as many forged source addresses as the
/// table of address pairs holds, push every other session's pair out of the table: host 0's session with host 2 then
/// has no address for its path and drops what it sends.
///
/// Expected: "nothing is acted on before it authenticated, so a forged packet moves no path, validates none and names
/// no id" (crates/pinc-transport/src/conn/recv.rs:9); the endpoint's own rule, "no table grows; no input panics"
/// (crates/pinc-core/src/endpoint.rs:47), bounds the table but does not let an input that authenticates nothing
/// change another session's state; and every byte written on an established session leaves for its peer (the
/// transport's reliability). So after the junk, the first datagram host 0 sends on its session with host 2 leaves for
/// host 2's address, and nothing is dropped.
///
/// Actual: each junk datagram reaches session (0, 1) by its id (`rx.rs` `handle_datagram`, one candidate), and
/// `deliver` (crates/pinc-core/src/rx.rs:268) calls `path_id` (crates/pinc-core/src/endpoint.rs:723) before the
/// connection opens the packet: `path_id` inserts the forged pair and `Table::insert` (crates/pinc-core/src/table.rs:276)
/// evicts the oldest pair once the table holds `D` (128 here). The connection then refuses the packet as
/// undecryptable and learns nothing, but the pair stays. After `D` forged sources every pair host 0 held is gone,
/// those of its two sessions included; host 0's write on its session with host 2 finds no address for the active path
/// (`path_addrs` is `None`, crates/pinc-core/src/tx.rs:100) and the datagram is dropped (`dropped_out` grows, nothing
/// reaches host 2).
///
/// Suspected fault: `deliver` mints the pair of every datagram before it is authenticated, and the table evicts the
/// oldest pair for it whoever holds that pair (crates/pinc-core/src/rx.rs:268, crates/pinc-core/src/table.rs:276).
///
/// Who: anyone who reads one connection id of any session of the node (any box on the path of that session, or the
/// session's own peer) and can send datagrams with forged source addresses: `D` datagrams of a few dozen bytes evict
/// every pair of the node, its hub links and relay paths included (`D` is ten per session, 960 in the world suite).
#[test]
fn junk_with_a_known_id_from_forged_sources_leaves_every_other_session_its_path() {
    big_stack(|| {
        let (mut net, _ab, ac) = two_sessions();
        let id = seen_id(&net, 1, 0);
        let to = net.hosts[0].addr;
        for k in 0..D {
            let mut junk = vec![0x40];
            junk.extend_from_slice(&id);
            junk.extend_from_slice(&[0xA5; 40]);
            net.deliver(forged(k), to, junk);
        }
        let c = net.hosts[2].addr;
        let (sent_to, dropped) = write_and_pump(&mut net, ac, 600);
        assert_eq!(dropped, 0, "datagrams of session (0, 2) dropped after the junk; sent to {sent_to:?}");
        assert!(sent_to.contains(&c), "nothing of the write left for host 2 ({c}); sent to {sent_to:?}");
    });
}

/// Control: a peer whose address changes (its NAT moved its mapping) is still followed once a datagram from the new
/// address authenticates, and the pair of the new address is used for the answer (rx.rs: "otherwise a new path is
/// added only after a packet from it authenticated"). A fix that refuses every new pair must keep this passing.
#[test]
fn a_peer_that_moves_its_address_is_followed() {
    big_stack(|| {
        let (mut net, ab, _ac) = two_sessions();
        let outside: SocketAddr = ([203, 0, 113, 9], 31000).into();
        let inside = net.hosts[1].addr;
        net.nat.insert(inside, outside);
        // Host 1 writes from behind its new mapping; host 0 reads it and answers to the new address.
        let now = net.now;
        let sb = net.hosts[1].dialed.iter().next().copied().expect("host 1 dialed");
        let Ok(core_harness::Reply2 { value: Value::Stream(st) }) =
            net.hosts[1].cmd(now, Command::OpenStream { session: sb, bidi: true })
        else {
            panic!("no stream on an established session")
        };
        net.hosts[1].write(now, sb, st, vec![5; 2000], true);
        let got = net.run(now + 5 * SEC, |n| n.hosts[0].read.iter().any(|((s, _), d)| *s == ab && d.len() == 2000));
        assert!(got, "host 0 never read host 1's bytes from its new address");
        net.run_for(200 * MS);
        let (sent_to, dropped) = write_and_pump(&mut net, ab, 600);
        assert_eq!(dropped, 0);
        assert!(sent_to.contains(&outside), "host 0 did not answer host 1's new address; sent to {sent_to:?}");
    });
}

// ---------------------------------------------------------------- two endpoints behind endpoint-dependent translators

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
        Self { ext: IpAddr::from(ext), next: 20_000, map: BTreeMap::new() }
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
        Self { hosts, nat: [Edm::new([192, 0, 2, 1]), Edm::new([192, 0, 2, 2])], wires: BinaryHeap::new(), now, seq: 0, log: Vec::new() }
    }

    fn pump(&mut self, n: usize) {
        let mut buf = vec![0u8; 65_536];
        for _ in 0..20_000 {
            let now = self.now;
            self.hosts[n].service(now);
            let Some(Transmit { remote, len, segment_size, .. }) = self.hosts[n].ep.poll_transmit(now, &mut buf) else {
                self.hosts[n].service(now);
                return;
            };
            for chunk in buf[..len].chunks(segment_size.max(1)) {
                let m = 1 - n;
                let relay = remote == relay_of(m);
                self.log.push((now, n, relay, chunk.len()));
                self.seq += 1;
                if relay {
                    self.wires.push(Reverse((now + 20 * MS, self.seq, m, relay_of(n), chunk.to_vec())));
                } else {
                    let from = self.nat[n].out(remote);
                    if remote.ip() == self.nat[m].ext && self.nat[m].admits(remote.port()) {
                        self.wires.push(Reverse((now + 10 * MS, self.seq, m, from, chunk.to_vec())));
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
            let t = self.hosts.iter().filter_map(|h| h.ep.poll_timeout()).chain(w).min().unwrap_or(end).max(self.now);
            if t > end {
                self.now = end;
                return stop(self);
            }
            self.now = t;
            while self.wires.peek().is_some_and(|Reverse(w)| w.0 <= t) {
                let Some(Reverse((_, _, m, from, mut d))) = self.wires.pop() else { break };
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
        self.log.iter().filter(|(t, h, relay, _)| *h == n && !*relay && (from..to).contains(t)).count()
    }

    fn stream(&mut self, n: usize, s: SessionId) -> u64 {
        let now = self.now;
        match self.hosts[n].cmd(now, Command::OpenStream { session: s, bidi: true }) {
            Ok(core_harness::Reply2 { value: Value::Stream(st) }) => st,
            _ => panic!("no stream on an established session"),
        }
    }
}

/// Bug: two endpoints with a session on a relay path, each behind a translator that maps every destination to a new
/// external port and admits anyone to a port it handed out, punch towards each other and never stop: every
/// PATH_CHALLENGE that arrives from a new external port is answered on that port with a PATH_RESPONSE and a new
/// PATH_CHALLENGE, which the answering side's translator sends from yet another new port, so the other side learns
/// another new path and answers the same way. The punch fails (no direct path validates) and costs hundreds of
/// datagrams a second for as long as the session carries data.
///
/// Expected: a punch probes a path "on the cadence of a path that never answered: 9 probes, doubling"
/// (crates/pinc-transport/src/conn/path.rs:693; docs/proofs/properties.md:56: "the punch probe gaps are nine, the first
/// at least 33.3 ms and the rest at most 2 s"), and a challenge sent back with a response is "One challenge, never a
/// second while it is out: the probes of a punch keep their own cadence" (path.rs:673). A failed punch of one candidate
/// per side then costs each side its 9 probes, an answer to each of the peer's 9 and at most one challenge sent back
/// per path it challenged or answered: under 40 direct datagrams per side, all within the 9 probes' span (about 8.1 s:
/// 33.3 ms doubling, at most 2 s), and none after it. The relay path keeps carrying the session.
///
/// Actual: see the failing output; each side sends thousands of direct datagrams in the first 10 s and keeps sending
/// after it.
///
/// Suspected fault: `challenge_back` (crates/pinc-transport/src/conn/path.rs:677) attaches a new challenge to the
/// response on every direct path the connection has not validated and has no challenge on, and a path learned from a
/// new source port is always such a path; `on_path_response` (path.rs:707) takes a response only on the path whose
/// challenge it answers, and behind these translators the answer to a challenge always comes from another port. Nothing
/// bounds the paths a session learns or challenges per punch (the amplification budget does not apply once the
/// session is validated, `send.rs` `amp_room`).
///
/// Who: no adversary: any two nodes behind translators of this kind (kinds 4 and 5 of the world suite: the dependent
/// mapping with open or address-dependent filtering) whose session runs on a relay path and punches.
#[test]
fn a_failed_punch_between_two_endpoint_dependent_translators_ends_after_its_probes() {
    big_stack(|| {
        let mut p = Pair::new();
        let now = p.now;
        let (peer, to) = (p.hosts[1].id, relay_of(1));
        let rep = p.hosts[0].cmd(now, Command::Connect { node: peer, alpn: ALPN_A, addrs: &[to], role: Role::Other }).expect("dial");
        let Value::Session(sa) = rep.value else { panic!("no session") };
        assert!(
            p.run_until(now + 10 * SEC, |p| p.hosts[0].opened.contains(&sa)
                && p.hosts[1].count(|e| matches!(e, Event::Incoming { .. })) == 1),
            "the pair did not connect over the relay path"
        );
        let sb = p.hosts[1].session_of(|e| match e {
            Event::Incoming { session, .. } => Some(*session),
            _ => None,
        }).expect("an incoming session");
        // Each side has a mapping it made towards a server that told it its external address (the candidate).
        let hub: SocketAddr = ([198, 18, 0, 1], 3478).into();
        let (ca, cb) = (p.nat[0].out(hub), p.nat[1].out(hub));
        let (st_a, st_b) = (p.stream(0, sa), p.stream(1, sb));
        let now = p.now;
        p.hosts[0].write(now, sa, st_a, vec![1; 100], false);
        p.hosts[1].write(now, sb, st_b, vec![2; 100], false);
        p.run_until(now + 300 * MS, |_| false);
        let punch = p.now;
        p.hosts[0].cmd(punch, Command::Punch { session: sa, addr: cb }).expect("punch from host 0");
        p.hosts[1].cmd(punch, Command::Punch { session: sb, addr: ca }).expect("punch from host 1");
        p.run_until(punch + 15 * SEC, |_| false);
        // The relay path still carries the session: time to the first byte of a write made now.
        let at = p.now;
        p.hosts[0].write(at, sa, st_a, vec![3; 2000], false);
        let got = p.run_until(at + 5 * SEC, |p| p.hosts[1].read.get(&(sb, st_a)).is_some_and(|d| d.len() >= 2100));
        let ttfb = (p.now - at) / MS;
        let span = |n| (p.direct(n, punch, punch + 10 * SEC), p.direct(n, punch + 10 * SEC, punch + 15 * SEC));
        let (a, b) = (span(0), span(1));
        let pairs = (p.nat[0].map.len(), p.nat[1].map.len());
        eprintln!(
            "direct datagrams in the 10 s after the punch and in the 5 s after: host 0 {a:?}, host 1 {b:?}; translator \
             mappings {pairs:?}; relay write delivered {got} in {ttfb} ms"
        );
        assert!(got, "the relay path no longer carried the session");
        assert!(a.0 < 40 && b.0 < 40, "a failed punch cost more than its probes: host 0 {a:?}, host 1 {b:?}");
        assert!(a.1 == 0 && b.1 == 0, "the punch went on after its probes: host 0 {a:?}, host 1 {b:?}");
    });
}
