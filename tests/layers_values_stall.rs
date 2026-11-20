//! A fetch starved behind another fetch on the same values session stall-redials, which hangs up the session the
//! other fetch streams on. The other fetch must come through: its provider is not reported down by the old
//! session's close, because a newer session to that provider is already dialed.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod layers_common;

use layers_common::{LWorld, big, data, ids, secs, values_on};
use pinc_node::NodeEvent;
use pinc_node::trace::{Body, NodeTrace, tag};
use pinc_sim::{MS, NodeId as SimId, Time};
use pinc_tests::NCmd;
use pinc_values::trace::Trace;

/// The layer number of values sessions in the node traces.
const VALUES: u64 = 1;

fn fetch(w: &mut LWorld, from: SimId, root: [u8; 32], len: usize, provs: &[SimId], deadline: Option<Time>) {
    let providers = ids(w, provs);
    w.sim.command(
        secs(30),
        from,
        NCmd::ValuesFetch {
            root,
            length: len as u64,
            ranges: vec![],
            providers,
            deadline,
        },
    );
}

/// When the first stall redial of fetch `f` on node `n` is traced.
fn stall_of(w: &LWorld, n: SimId, f: u32) -> Option<Time> {
    w.sim
        .node(n)
        .traces
        .iter()
        .find(|(_, it)| matches!(&it.body, Body::Values(x, Trace::StallRedial { .. }) if *x == f))
        .map(|(t, _)| *t)
}

fn completed(w: &LWorld, n: SimId, f: u32) -> Option<Time> {
    w.node_events(n)
        .iter()
        .find(|(_, e)| matches!(e, NodeEvent::ValueComplete { fetch } if *fetch == f))
        .map(|(t, _)| *t)
}

fn failed(w: &LWorld, n: SimId) -> usize {
    w.node_events(n)
        .iter()
        .filter(|(_, e)| matches!(e, NodeEvent::ValueFailed { .. }))
        .count()
}

/// Runs in 10 ms steps from 30 s to `until` until fetch 1 stall-redials, and returns the values view of member 0
/// from the step before.
fn run_to_stall(w: &mut LWorld, m0: SimId, until: Time) -> pinc_node::ValuesView {
    let mut t = secs(30);
    w.run(t);
    while t < until {
        let before = w.sim.node(m0).node.values_view();
        t += 10 * MS;
        w.run(t);
        if stall_of(w, m0, 1).is_some() {
            return before;
        }
    }
    panic!("fetch 1 did not stall-redial before {until} ns");
}

/// Member 1 provides A (8 MiB) and B (16 MiB); member 0 fetches A from members 1 and 2 (member 2 refuses, so A tops
/// member 1 up on new streams), then B from member 1. B's response, sent first, holds the session: A's top-ups
/// queue behind it, A starves, stall-redials and hangs up the session B streams on. Measured: stall at 34.857 s,
/// B complete at 49.541 s, A at 56.325 s.
#[test]
fn a_fetch_starved_behind_another_fetch_redials_and_both_complete() {
    big(|| {
        let seed = 291u64;
        let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, true, values_on);
        let m = w.members.clone();
        let (va, vb) = (data(seed, 8 << 20), data(seed + 1, 16 << 20));
        let (ra, rb) = (w.provide(m[1], va.clone()), w.provide(m[1], vb.clone()));
        fetch(&mut w, m[0], ra, va.len(), &m[1..3], None);
        fetch(&mut w, m[0], rb, vb.len(), &m[1..2], None);
        let id1 = w.id(m[1]);
        let peer = tag(&id1);
        let before = run_to_stall(&mut w, m[0], secs(60));
        let t_s = stall_of(&w, m[0], 1).unwrap();
        let s_old = before
            .dialed
            .iter()
            .find(|(p, _)| *p == id1)
            .map(|(_, s)| *s)
            .expect("a session to member 1");
        assert!(
            before.streams.iter().any(|(_, _, owner, s)| *owner == 2 && *s == s_old),
            "fetch 2 streams on the session fetch 1 hangs up"
        );
        w.run(secs(130));
        let traces = &w.sim.node(m[0]).traces;
        let down = traces.iter().find(|(t, it)| {
            *t >= t_s && matches!(&it.body, Body::Node(NodeTrace::LayerDown { layer: VALUES, peer: p }) if *p == peer)
        });
        let t_d = down.expect("the old session goes down").0;
        assert!(
            traces.iter().any(|(t, it)| *t >= t_s
                && matches!(&it.body, Body::Node(NodeTrace::LayerUp { layer: VALUES, peer: p, incoming: 0 }) if *p == peer)),
            "a new values session to member 1 comes up"
        );
        assert!(
            traces
                .iter()
                .any(|(t, it)| *t >= t_s && matches!(&it.body, Body::Values(2, Trace::Requested { .. }))),
            "fetch 2 asks again on the new session after t_d {t_d}"
        );
        assert_eq!(failed(&w, m[0]), 0, "no provider is reported down to either fetch");
        // Upper bound with a wide margin over the measured 49.5 s and 56.3 s.
        let (b_at, a_at) = (completed(&w, m[0], 2), completed(&w, m[0], 1));
        assert!(b_at.is_some_and(|t| t < secs(90)), "fetch 2 completes: {b_at:?}");
        assert!(a_at.is_some_and(|t| t < secs(100)), "fetch 1 completes: {a_at:?}");
        assert_eq!(w.apps(m[0]).values.fetched(&ra, va.len() as u64), Some(va));
        assert_eq!(w.apps(m[0]).values.fetched(&rb, vb.len() as u64), Some(vb));
        let (v0, v1) = (w.sim.node(m[0]).node.values_view(), w.sim.node(m[1]).node.values_view());
        assert!(
            !v0.sessions.iter().any(|(s, _, _)| *s == s_old),
            "the old session is gone"
        );
        let s_new = v0.dialed.iter().find(|(p, _)| *p == id1).map(|(_, s)| *s);
        assert!(
            s_new.is_some_and(|s| s != s_old),
            "member 0 dialed a newer session to member 1"
        );
        assert!(
            v0.sessions
                .iter()
                .all(|(s, _, _)| v0.dialed.iter().any(|(_, d)| d == s)),
            "member 0 holds only the sessions it dialed"
        );
        assert!(
            v0.streams.is_empty() && v0.held.is_empty(),
            "member 0 holds no stream: {:?}",
            v0.streams
        );
        assert!(v1.streams.is_empty(), "member 1 holds no stream: {:?}", v1.streams);
        assert_eq!(v1.sessions.len(), 1, "member 1 holds one values session");
        assert_eq!(w.sim.node(m[0]).node.values_stats().providers_in_use, 0);
    });
}

/// As above, with C (6 MiB) ahead of B (64 KiB) so B queues behind C and never verifies a group, and so has no
/// stall of its own. Member 1 stops providing B at 31 s (its request in flight keeps its stream) and provides it
/// again at 38 s. A's stall redial at about 34.9 s closes the session B holds a stream on; B asks again on the new
/// session and is refused until 38 s. B must keep retrying and complete before its 60 s deadline: the old session's
/// close must not leave a stale stream entry that blocks every retry.
#[test]
fn a_fetch_with_nothing_verified_survives_the_old_sessions_close() {
    big(|| {
        let seed = 291u64;
        let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, true, values_on);
        let m = w.members.clone();
        let (va, vc, vb) = (data(seed, 8 << 20), data(seed + 2, 6 << 20), data(seed + 1, 64 << 10));
        let ra = w.provide(m[1], va.clone());
        let rc = w.provide(m[1], vc.clone());
        let rb = w.provide(m[1], vb.clone());
        fetch(&mut w, m[0], ra, va.len(), &m[1..3], None);
        fetch(&mut w, m[0], rc, vc.len(), &m[1..2], None);
        fetch(&mut w, m[0], rb, vb.len(), &m[1..2], Some(secs(60)));
        w.run(secs(31));
        assert!(w.sim.node_mut(m[1]).node.values_unprovide(&rb));
        w.run(secs(38));
        assert!(w.sim.node_mut(m[1]).node.values_provide(&rb));
        w.run(secs(100));
        let t_s = stall_of(&w, m[0], 1).expect("fetch 1 stall-redials");
        assert!(
            t_s > secs(31) && t_s < secs(38),
            "the stall redial comes while B is refused: {t_s}"
        );
        let b_at = completed(&w, m[0], 3);
        assert!(
            b_at.is_some_and(|t| t >= secs(38) && t < secs(60)),
            "fetch 3 completes in its deadline: {b_at:?}"
        );
        assert_eq!(failed(&w, m[0]), 0, "no fetch fails");
        assert_eq!(w.apps(m[0]).values.fetched(&rb, vb.len() as u64), Some(vb));
        assert_eq!(w.apps(m[0]).values.fetched(&ra, va.len() as u64), Some(va));
        assert_eq!(w.apps(m[0]).values.fetched(&rc, vc.len() as u64), Some(vc));
        let streams = w.sim.node(m[0]).node.values_view().streams;
        assert!(streams.is_empty(), "member 0 holds no stream: {streams:?}");
    });
}
