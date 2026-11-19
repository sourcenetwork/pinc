//! Trace generation for the endpoint's table of sessions by address: a hub dialed by members that dial twice from one
//! address, move, rebind behind a NAT and close, the state of the table recorded after every step of the pump and
//! after every action, as ndjson (`core_route_index.ndjson`) for the TLA+ trace check (`TraceCoreRouteIndex.tla`).
//!
//! A snapshot holds, for each of the hub's 8 slots, whether it is live, the address its session's active path is
//! validated and direct at (`cur`) and the address its entry in the table is under (`route`); the entries of the
//! table oldest first; and, for each numbered address, the slots `session_from` finds there when the ones found are
//! excluded one by one. Addresses are numbered from 1 in a fixed order, 0 for none.
//!
//! The runs are the scripted scenario of `core_session_from.rs` (copied, not imported) and 16 seeded random ones.
//!
//! The test asserts, without the model: the table answers as a walk of the sessions after every step, at most 16
//! addresses are numbered, and two slots share an address in some snapshot. A slot whose entry is under an address its
//! session has left is reported when it occurs and is not required. The trace is written to the directory in
//! `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::manual_is_multiple_of
)]

use std::fmt::Write as _;
use std::net::SocketAddr;

use pinc_core::{Answer, Command, IfaceEvent, IfaceId, Query, Role, SessionId, Value, is_relay_addr};
use pinc_tests::*;

const SLOTS: usize = 8;
const NUMBERS: usize = 16;

/// The sessions of node `n` whose active path is validated, direct and from `addr`, by a walk of every live session.
fn walk(net: &CoreNet, n: usize, addr: SocketAddr) -> Vec<SessionId> {
    let mut out = Vec::new();
    for k in 0.. {
        let Answer::Stats(st) = net.nodes[n].ep.query(Query::SessionAt(k)) else {
            break;
        };
        if st.path_validated && st.route.map(|(_, r)| r) == Some(addr) && !is_relay_addr(&addr) {
            out.push(st.session);
        }
    }
    out.sort();
    out
}

/// The table answers as the walk does for every address in `addrs`, with every session of the walk excluded in turn.
fn agree(net: &CoreNet, n: usize, addrs: &[SocketAddr]) {
    for a in addrs {
        let all = walk(net, n, *a);
        let ep = &net.nodes[n].ep;
        assert_eq!(ep.session_from(a, |_| true), all.first().copied(), "{a} at {}", net.now);
        for skip in &all {
            let rest = all.iter().copied().find(|s| s != skip);
            assert_eq!(
                ep.session_from(a, |s| s != *skip),
                rest,
                "{a} without {skip:?} at {}",
                net.now
            );
        }
    }
}

/// The sessions of node `n`, by a walk.
fn sessions(net: &CoreNet, n: usize) -> Vec<SessionId> {
    let mut out = Vec::new();
    for k in 0.. {
        let Answer::Stats(st) = net.nodes[n].ep.query(Query::SessionAt(k)) else {
            break;
        };
        out.push(st.session);
    }
    out
}

/// A send on a session; a session that has ended is not an error here.
fn send(net: &mut CoreNet, n: usize, s: SessionId) {
    let now = net.now;
    let Ok(rep) = net.nodes[n].cmd(now, Command::OpenStream { session: s, bidi: true }) else {
        return;
    };
    let Value::Stream(id) = rep.value else { return };
    let _ = net.nodes[n].cmd(
        now,
        Command::Write {
            session: s,
            stream: id,
            data: b"here",
        },
    );
    let _ = net.nodes[n].cmd(now, Command::Finish { session: s, stream: id });
}

/// The addresses of the runs, numbered in this order: the six nodes, the three addresses a member moves among, the
/// three outside addresses of the NAT.
fn pool(net: &CoreNet) -> Vec<SocketAddr> {
    let mut addrs: Vec<SocketAddr> = net.nodes.iter().map(|n| n.addr).collect();
    addrs.extend((1..=3u8).map(|i| SocketAddr::from(([10, 0, 9, i], 4433))));
    addrs.extend((0..3u16).map(|i| SocketAddr::from(([198, 51, 100, 4], 40000 + i))));
    addrs
}

struct Rec {
    out: String,
    addrs: Vec<SocketAddr>,
    hub: usize,
    twice: bool,
    stale: bool,
}

impl Rec {
    fn number(&mut self, a: Option<SocketAddr>) -> usize {
        let Some(a) = a else { return 0 };
        let i = self.addrs.iter().position(|x| *x == a).unwrap_or_else(|| {
            self.addrs.push(a);
            self.addrs.len() - 1
        });
        i + 1
    }

    fn snapshot(&mut self, net: &CoreNet) {
        let ep = &net.nodes[self.hub].ep;
        let (mut live, mut cur, mut route) = ([0; SLOTS], [0; SLOTS], [0; SLOTS]);
        for i in 0..SLOTS {
            let v = ep.route_view(i).unwrap();
            live[i] = usize::from(v.live);
            cur[i] = self.number(v.direct);
            route[i] = self.number(v.route);
            self.stale |= v.live && v.route.is_some() && v.direct != v.route;
        }
        self.twice |= (0..SLOTS).any(|i| cur[i] != 0 && (i + 1..SLOTS).any(|j| cur[j] == cur[i]));
        let idx: Vec<[usize; 2]> = ep
            .route_entries()
            .collect::<Vec<_>>()
            .into_iter()
            .map(|(a, s)| [self.number(Some(a)), s])
            .collect();
        assert!(self.addrs.len() <= NUMBERS, "more than {NUMBERS} addresses");
        let mut found: Vec<Vec<usize>> = Vec::new();
        for a in 0..NUMBERS {
            let mut slots = Vec::new();
            if let Some(addr) = self.addrs.get(a) {
                let mut skip: Vec<SessionId> = Vec::new();
                for _ in 0..SLOTS {
                    let Some(s) = ep.session_from(addr, |s| !skip.contains(&s)) else {
                        break;
                    };
                    slots.push(s.slot());
                    skip.push(s);
                }
            }
            found.push(slots);
        }
        let list = |v: &[usize]| v.iter().map(usize::to_string).collect::<Vec<_>>().join(",");
        let pairs = idx
            .iter()
            .map(|p| format!("[{},{}]", p[0], p[1]))
            .collect::<Vec<_>>()
            .join(",");
        let fnd = found
            .iter()
            .map(|f| format!("[{}]", list(f)))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            self.out,
            r#"{{"t":"route","live":[{}],"cur":[{}],"route":[{}],"idx":[{pairs}],"found":[{fnd}]}}"#,
            list(&live),
            list(&cur),
            list(&route)
        )
        .unwrap();
    }

    /// Run for `span`, checking the table and recording a snapshot after every step.
    fn step(&mut self, net: &mut CoreNet, span: u64) {
        let end = net.now + span;
        let all = self.addrs.clone();
        let hub = self.hub;
        net.run(end, |net| {
            agree(net, hub, &all);
            self.snapshot(net);
            false
        });
        self.snapshot(net);
    }
}

/// Move member `n` to `to`: its old address goes quiet and its interface reports the change.
fn relocate(net: &mut CoreNet, n: usize, to: SocketAddr) {
    let old = net.nodes[n].addr;
    net.nodes[n].addr = to;
    net.loss = Some(Box::new(move |from, _, _| from == old));
    let now = net.now;
    net.nodes[n].ep.iface_event(now, IfaceId(0), IfaceEvent::Down);
    net.nodes[n].ep.iface_event(now, IfaceId(0), IfaceEvent::AddrChange(to));
    net.nodes[n].ep.iface_event(now, IfaceId(0), IfaceEvent::Up);
}

fn scripted(rec: &mut Rec) {
    let mut net = CoreNet::new(5 * MS_NS);
    let hub = net.add(1);
    let (twice, mover, natted, closer) = (net.add(2), net.add(3), net.add(4), net.add(5));
    net.add(6);
    rec.hub = hub;
    rec.addrs = pool(&net);
    let (elsewhere, out1, out2) = (rec.addrs[8], rec.addrs[9], rec.addrs[10]);
    rec.snapshot(&net);

    let (_, two_a) = net.connect_pair(twice, hub, ALPN_A, Role::Other);
    rec.step(&mut net, SEC_NS);
    let (_, two_b) = net.connect_pair(twice, hub, ALPN_B, Role::Other);
    rec.step(&mut net, SEC_NS);
    assert_eq!(walk(&net, hub, net.nodes[twice].addr), {
        let mut v = vec![two_a, two_b];
        v.sort();
        v
    });
    let (m_side, m_hub) = net.connect_pair(mover, hub, ALPN_A, Role::Other);
    let (_, c_hub) = net.connect_pair(closer, hub, ALPN_A, Role::Other);
    net.nat = Some((net.nodes[natted].addr, out1));
    let (n_side, n_hub) = net.connect_pair(natted, hub, ALPN_A, Role::Other);
    rec.step(&mut net, 2 * SEC_NS);
    assert_eq!(net.nodes[hub].ep.session_from(&out1, |_| true), Some(n_hub));

    let old = net.nodes[mover].addr;
    relocate(&mut net, mover, elsewhere);
    rec.snapshot(&net);
    send(&mut net, mover, m_side);
    rec.step(&mut net, 6 * SEC_NS);
    assert_eq!(net.nodes[hub].ep.session_from(&elsewhere, |_| true), Some(m_hub));
    assert_eq!(net.nodes[hub].ep.session_from(&old, |_| true), None);

    net.nat = Some((net.nodes[natted].addr, out2));
    send(&mut net, natted, n_side);
    rec.step(&mut net, 6 * SEC_NS);
    assert_eq!(net.nodes[hub].ep.session_from(&out2, |_| true), Some(n_hub));
    assert_eq!(net.nodes[hub].ep.session_from(&out1, |_| true), None);

    let now = net.now;
    net.nodes[hub]
        .cmd(
            now,
            Command::Close {
                session: c_hub,
                error: 0,
            },
        )
        .unwrap();
    rec.snapshot(&net);
    rec.step(&mut net, 3 * SEC_NS);
    assert_eq!(net.nodes[hub].ep.session_from(&net.nodes[closer].addr, |_| true), None);
    let (_, again) = net.connect_pair(closer, hub, ALPN_A, Role::Other);
    rec.step(&mut net, 2 * SEC_NS);
    assert_eq!(
        net.nodes[hub].ep.session_from(&net.nodes[closer].addr, |_| true),
        Some(again)
    );
}

fn random(rec: &mut Rec, seed: u64) {
    let mut rng = SplitMix64::new(seed);
    let mut net = CoreNet::new(5 * MS_NS);
    let hub = net.add(1);
    let members: Vec<usize> = (2..=6).map(|t| net.add(t)).collect();
    let (mover, natted) = (members[2], members[3]);
    rec.hub = hub;
    rec.addrs = pool(&net);
    net.nat = Some((net.nodes[natted].addr, rec.addrs[9]));
    rec.snapshot(&net);
    for _ in 0..60 {
        let now = net.now;
        match rng.next_u64() % 5 {
            0 => {
                let m = members[(rng.next_u64() % 5) as usize];
                let alpn = if rng.next_u64() % 2 == 0 { ALPN_A } else { ALPN_B };
                let (peer, to) = (net.nodes[hub].node, net.nodes[hub].addr);
                // A refusal (the table is full) is part of the run.
                let _ = net.nodes[m].connect(now, peer, alpn, to, Role::Other);
            }
            1 => {
                let live = sessions(&net, hub);
                if !live.is_empty() {
                    let s = live[(rng.next_u64() % live.len() as u64) as usize];
                    let _ = net.nodes[hub].cmd(now, Command::Close { session: s, error: 0 });
                }
            }
            2 => {
                let to = rec.addrs[6 + (rng.next_u64() % 3) as usize];
                relocate(&mut net, mover, to);
            }
            3 => {
                let to = rec.addrs[9 + (rng.next_u64() % 3) as usize];
                net.nat = Some((net.nodes[natted].addr, to));
                if let Some(s) = sessions(&net, natted).first().copied() {
                    send(&mut net, natted, s);
                }
            }
            _ => {
                let m = members[(rng.next_u64() % 5) as usize];
                if let Some(s) = sessions(&net, m).first().copied() {
                    send(&mut net, m, s);
                }
            }
        }
        rec.snapshot(&net);
        let span = (200 + rng.next_u64() % 1800) * MS_NS;
        rec.step(&mut net, span);
    }
}

#[test]
fn core_route_index_traces() {
    let out = big_stack(|| {
        let mut rec = Rec {
            out: String::new(),
            addrs: Vec::new(),
            hub: 0,
            twice: false,
            stale: false,
        };
        scripted(&mut rec);
        for s in 0..16 {
            random(&mut rec, s);
        }
        assert!(rec.twice, "no snapshot with two slots at one address");
        if !rec.stale {
            println!("an entry under an address its session left did not occur in these runs");
        }
        rec.out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("core_route_index.ndjson"), out).unwrap();
    }
}
