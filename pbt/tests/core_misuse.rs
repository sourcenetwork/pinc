//! `pinc-core`: the local application misuses the endpoint's command and query surface (sessions that never existed,
//! sessions of the other side, closed sessions, stream ids nobody opened or of the wrong direction, empty and oversize
//! payloads, unknown checks, dials of itself or with no address) while one honest transfer runs on its own stream.
//!
//! Where the expected behaviour comes from:
//! - `pinc_core` (lib.rs): "never panics on input. Every table has a fixed bound." Checked after every step by
//!   `core_harness::Host::check_stats`.
//! - commands.rs: "A command that fails changes no session and queues no event" (the exceptions are a dial of the
//!   node's own id and a sub-session open; checked in `Host::cmd`).
//! - `CommandError::NoSession` (api.rs) is the answer to a command that names no session: a command that hands the
//!   endpoint bytes (`OpenStream`, `Write`, `SendDatagram`) for a session it never issued cannot succeed, or the bytes
//!   go nowhere.
//! - Universal: commands that name other sessions and other streams leave the honest stream alone: its bytes arrive
//!   whole and end. Suspend and resume are left out: iface.rs documents that a resume closes the sessions in doubt
//!   ("those sessions close at once with `Redial`"), the honest one included.

mod core_harness;

use core_harness::{ALPN_A, ALPN_B, HostCfg, MS, Net, SEC, Violation, big_stack};
use ephyra::{check_generator, gens};
use pinc_core::{Command, Query, Role, SessionId, Value};

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Sess {
    /// The host's honest session.
    Honest,
    /// The other host's id for the same session.
    Theirs,
    /// A second session, closed by the case before the ops.
    Closed,
    /// An id never issued.
    Bogus(#[ephyra(gen = gens::frequency(vec![(3, gens::int(0u64..=64).boxed()), (1, gens::int(0u64..=u64::MAX).boxed())]))] u64),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Strm {
    /// A stream an op opened (by position), if any.
    Mine(u8),
    /// A stream id of the peer's direction or nobody's.
    Raw(#[ephyra(gen = gens::frequency(vec![(3, gens::int(0u64..=64).boxed()), (1, gens::int(0u64..=u64::MAX).boxed())]))] u64),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    Wait(#[ephyra(gen = gens::int(0u16..=500))] u16),
    Open(Sess, bool),
    Write(Sess, Strm, #[ephyra(gen = gens::frequency(vec![(4, gens::int(0usize..=2_000).boxed()), (1, gens::int(0usize..=200_000).boxed())]))] usize),
    Finish(Sess, Strm),
    Reset(Sess, Strm, u64),
    Stop(Sess, Strm, u64),
    Consume(Sess, Strm, #[ephyra(gen = gens::frequency(vec![(3, gens::int(0usize..=100).boxed()), (1, gens::int(0usize..=usize::MAX).boxed())]))] usize),
    Urgency(Sess, Strm, u8),
    Datagram(Sess, #[ephyra(gen = gens::int(0usize..=10_000))] usize),
    Extension(Sess, #[ephyra(gen = gens::frequency(vec![(3, gens::int(0u64..=0x60).boxed()), (1, gens::int(0u64..=u64::MAX).boxed())]))] u64, #[ephyra(gen = gens::int(0usize..=3_000))] usize),
    /// Close a session other than the honest one.
    CloseOther(#[ephyra(gen = gens::int(0u8..=1))] u8, u64),
    /// Dial: 0 itself, 1 the peer with no address, 2 an empty protocol id, 3 an oversize one, 4 an unregistered one.
    Dial(#[ephyra(gen = gens::int(0u8..=4))] u8),
    Acp(u64, bool),
    Paths(Sess, #[ephyra(gen = gens::int(0u8..=6))] u8, bool),
    Pulse(Sess, bool),
    Query(Sess, Strm, #[ephyra(gen = gens::int(0u8..=12))] u8, u64),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Case {
    /// Which host the application misuses.
    #[ephyra(gen = gens::int(0usize..=1))]
    host: usize,
    #[ephyra(gen = gens::int(0usize..=20_000))]
    len: usize,
    #[ephyra(gen = gens::vec(ephyra::any::<Op>()).len(0..=60))]
    ops: Vec<Op>,
}

fn fail(v: Option<Violation>) {
    if let Some(v) = v {
        ephyra::signature(v.sig);
        panic!("{}: {}", v.sig, v.detail);
    }
}

fn run(c: &Case) {
    let mut net = Net::new(7);
    let (a, b) = (net.add(1, HostCfg::default()), net.add(2, HostCfg::default()));
    let Some((sa, sb)) = net.connect_pair(a, b, ALPN_A) else {
        fail(net.first_violation());
        panic!("the honest pair did not connect");
    };
    // the second session, closed before the ops
    let closed = net.connect_pair(a, b, ALPN_B);
    if let Some((ca, _)) = closed {
        let now = net.now;
        let _ = net.hosts[a].cmd(now, Command::Close { session: ca, error: 9 });
        net.run_for(500 * MS);
    }
    let now = net.now;
    let Ok(core_harness::Reply2 { value: Value::Stream(st) }) =
        net.hosts[a].cmd(now, Command::OpenStream { session: sa, bidi: true })
    else {
        panic!("no stream on a fresh session")
    };
    let payload: Vec<u8> = (0..c.len).map(|i| (i as u8).wrapping_mul(13) ^ (i >> 9) as u8).collect();
    net.hosts[a].write(now, sa, st, payload.clone(), true);

    let (me, other) = if c.host == 0 { (a, b) } else { (b, a) };
    let (mine_s, theirs_s) = if c.host == 0 { (sa, sb) } else { (sb, sa) };
    let closed_s = closed.map(|(ca, cb)| if c.host == 0 { ca } else { cb });
    let issued = |s: SessionId| s == sa || s == sb || closed.is_some_and(|(x, y)| s == x || s == y);
    let peer_id = net.hosts[other].id;
    let self_id = net.hosts[me].id;
    let mut streams: Vec<u64> = Vec::new();
    for op in &c.ops {
        let now = net.now;
        let sess = |s: &Sess| match s {
            Sess::Honest => mine_s,
            Sess::Theirs => theirs_s,
            Sess::Closed => closed_s.unwrap_or(SessionId(u64::MAX)),
            Sess::Bogus(x) => SessionId(*x),
        };
        // the honest stream is never named: an op on it would end the transfer on purpose
        let strm = |t: &Strm, streams: &[u64]| match t {
            Strm::Mine(i) if !streams.is_empty() => streams[usize::from(*i) % streams.len()],
            Strm::Mine(_) => 1_000_000,
            Strm::Raw(x) if *x == st => x.wrapping_add(4),
            Strm::Raw(x) => *x,
        };
        let h = &mut net.hosts[me];
        let fresh = |s: SessionId| !issued(s);
        match op {
            Op::Wait(ms) => net.run_for(u64::from(*ms) * MS),
            Op::Open(s, bidi) => {
                let s = sess(s);
                let r = h.cmd(now, Command::OpenStream { session: s, bidi: *bidi });
                if let Ok(core_harness::Reply2 { value: Value::Stream(x) }) = r {
                    streams.push(x);
                }
                assert!(!(fresh(s) && r.is_ok()), "OpenStream on a session never issued succeeded: {s:?}");
            },
            Op::Write(s, t, len) => {
                let (s, x) = (sess(s), strm(t, &streams));
                let data = vec![0xA5; *len];
                let r = h.cmd(now, Command::Write { session: s, stream: x, data: &data });
                assert!(!(fresh(s) && *len > 0 && r.is_ok()), "Write on a session never issued took the bytes: {s:?} {r:?}");
            },
            Op::Finish(s, t) => {
                let _ = h.cmd(now, Command::Finish { session: sess(s), stream: strm(t, &streams) });
            },
            Op::Reset(s, t, e) => {
                let _ = h.cmd(now, Command::Reset { session: sess(s), stream: strm(t, &streams), error: *e });
            },
            Op::Stop(s, t, e) => {
                let _ = h.cmd(now, Command::StopSending { session: sess(s), stream: strm(t, &streams), error: *e });
            },
            Op::Consume(s, t, n) => {
                let _ = h.cmd(now, Command::Consume { session: sess(s), stream: strm(t, &streams), n: *n });
            },
            Op::Urgency(s, t, u) => {
                let _ = h.cmd(now, Command::SetUrgency { session: sess(s), stream: strm(t, &streams), urgency: *u });
            },
            Op::Datagram(s, len) => {
                let s = sess(s);
                let data = vec![0x5A; *len];
                let r = h.cmd(now, Command::SendDatagram { session: s, data: &data });
                assert!(!(fresh(s) && r.is_ok()), "SendDatagram on a session never issued succeeded: {s:?}");
            },
            Op::Extension(s, ty, len) => {
                let body = vec![0x33; *len];
                let _ = h.cmd(now, Command::SendExtension { session: sess(s), ty: *ty, body: &body });
            },
            Op::CloseOther(k, e) => {
                let s = if *k == 0 { closed_s.unwrap_or(SessionId(77)) } else { theirs_s };
                if s != mine_s {
                    let _ = h.cmd(now, Command::Close { session: s, error: *e });
                }
            },
            Op::Dial(k) => {
                let long = [b'x'; 300];
                let (node, alpn, addrs): (_, &[u8], Vec<_>) = match k {
                    0 => (self_id, ALPN_A, vec![net.hosts[other].addr]),
                    1 => (peer_id, ALPN_B, vec![]),
                    2 => (peer_id, b"", vec![net.hosts[other].addr]),
                    3 => (peer_id, &long, vec![net.hosts[other].addr]),
                    _ => (peer_id, b"pinc/none", vec![net.hosts[other].addr]),
                };
                let h = &mut net.hosts[me];
                let _ = h.cmd(now, Command::Connect { node, alpn, addrs: &addrs, role: Role::Other });
            },
            Op::Acp(check, allow) => {
                let _ = h.cmd(now, Command::AcpAnswer { check: *check, allow: *allow });
            },
            Op::Paths(s, n, skip) => {
                let addrs: Vec<std::net::SocketAddr> =
                    (0..*n).map(|i| ([198, 51, 100, i + 1], 9000).into()).collect();
                let _ = h.cmd(now, Command::FlightPaths { session: sess(s), addrs: &addrs, skip_primary: *skip });
            },
            Op::Pulse(s, sent) => {
                let _ = h.cmd(now, Command::Pulse { session: sess(s), sent: *sent });
            },
            Op::Query(s, t, k, x) => {
                let (s, t) = (sess(s), strm(t, &streams));
                let q = match k {
                    0 => Query::Stats(s),
                    1 => Query::SessionAt(*x as usize),
                    2 => Query::PeerAt(*x as usize),
                    3 => Query::Read { session: s, stream: t },
                    4 => Query::ReadAt { session: s, stream: t, offset: *x },
                    5 => Query::StoredAfter { session: s, stream: t, from: *x },
                    6 => Query::SendState { session: s, stream: t },
                    7 => Query::InFlight(s),
                    8 => Query::KeyRequest(s),
                    9 => Query::Node,
                    10 => Query::Ledger(([192, 0, 2, (*x % 250) as u8], 7000).into()),
                    11 => Query::ReachOut(s),
                    _ => Query::Peer(peer_id),
                };
                let _ = h.ep.query(q);
            },
        }
        net.pump_all();
        net.check();
        if net.first_violation().is_some() {
            break;
        }
    }
    fail(net.first_violation());
    let deadline = net.now + 90 * SEC;
    net.run(deadline, |n| n.hosts[b].fin.contains(&(sb, st)));
    fail(net.first_violation());
    let got = net.hosts[b].read.get(&(sb, st)).cloned().unwrap_or_default();
    assert!(!net.hosts[a].closed.contains(&sa), "the honest session closed");
    assert!(got == payload, "the honest stream's bytes differ: read {} of {}", got.len(), payload.len());
    assert!(net.hosts[b].fin.contains(&(sb, st)), "the honest stream's end never arrived");
}

#[test]
fn misused_commands_fail_cleanly_and_leave_the_honest_stream_whole() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(60)
            .name("misused_commands_fail_cleanly_and_leave_the_honest_stream_whole");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run(&c)).assert_passed();
    });
}

#[test]
fn the_misuse_case_generator_stays_in_support() {
    let ok = |c: &Case| c.host <= 1 && c.len <= 20_000 && c.ops.len() <= 60;
    check_generator(&ephyra::Config::default().tests(300), ephyra::any::<Case>(), ok).assert_passed();
}
