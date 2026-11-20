//! Trace generation for the values layer joined to the node's sessions: six members of a simulated network fetching
//! values from each other, recorded as ndjson (`node_values.ndjson`) for the TLA+ snapshot check
//! (`TraceNodeValues.tla`).
//!
//! Three seeds, one world each (two hubs, six members, a line rate of 8 Mbit/s). Members 1 to 4 provide a value each
//! (the four roots differ), member 3 lies and is evicted by the fetch. At 30 s member 0 fetches each of the four
//! roots from the four providers and member 5 fetches the root of member 1 from members 1 and 2, each with a deadline of
//! 50 s; at 31 s member 0 cancels its lowest running fetch; member 2 fetches the root of member 4 from member 4 at
//! 31.9 s, crashes at 32 s, restarts at 33 s and fetches it again at 33.5 s, so that its new session supersedes the
//! incoming one member 4 still holds from it. The world runs to 60 s in steps of 50 ms, and after
//! each step every member writes one line with the view of the probe `Node::values_view`: its values sessions, the
//! sessions it dialed, the provider table, the streams with their provider, owner and session, and the running
//! fetches' provider lists. Peers, sessions and stream numbers are written as small numbers, numbered per member and
//! per seed in the order first seen.
//!
//! The test checks every snapshot without the model: every stream is on a values session of the table, every stream
//! of a fetch is owned by a running fetch, every dialed session is an outgoing values session of the same peer, and
//! each slot's use count is its holders; at the end of a seed members 0 and 5 run no fetch and hold no fetch stream,
//! member 0 completed its fetch of the root of member 4 and member 5 its fetch of the root of member 1 before the
//! deadline, and some member showed a superseded incoming session of member 2 (its streams gone while a newer one is
//! in the table).
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    unreachable_pub
)]

mod layers_common;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use layers_common::{LWorld, big, data, ids, secs, values_on};
use pinc_core::SessionId;
use pinc_node::{NodeEvent, ValuesView};
use pinc_sim::{MS, SEC};
use pinc_tests::{Lie, NCmd};

/// The time at which the fetches of the run end if nothing else has ended them.
const DEADLINE: u64 = 50 * SEC;

/// The numbers a member's snapshots use: assigned from 1 in the order first seen, and kept.
#[derive(Default)]
struct Names {
    peers: BTreeMap<[u8; 32], u32>,
    sessions: BTreeMap<SessionId, u32>,
    lids: BTreeMap<u64, u32>,
}

/// Looks up `k` in `m`, giving it the next number if it is new.
fn number<K: Ord>(m: &mut BTreeMap<K, u32>, k: K) -> u32 {
    let next = m.len() as u32 + 1;
    *m.entry(k).or_insert(next)
}

/// What one member's snapshots have shown so far.
#[derive(Default)]
struct Member {
    names: Names,
    /// Incoming sessions of member 2's identity (by number) that held a stream at some snapshot.
    streamed: BTreeSet<u32>,
    superseded: bool,
}

/// The checks every snapshot must pass.
fn check(v: &ValuesView, who: &str) {
    for (_, _, _, ses) in &v.streams {
        assert!(
            v.sessions.iter().any(|s| s.0 == *ses),
            "{who}: a stream is on a session that is not in the table"
        );
    }
    for (_, _, owner, _) in &v.streams {
        assert!(
            *owner == 0 || v.held.iter().any(|h| h.0 == *owner),
            "{who}: a stream is owned by a fetch that is not running"
        );
    }
    for (peer, sid) in &v.dialed {
        assert!(
            v.sessions.iter().any(|s| s.0 == *sid && s.1 == *peer && !s.2),
            "{who}: a dialed session is not an outgoing values session of its peer"
        );
    }
    for (k, slot) in v.provs.iter().enumerate() {
        let uses = slot.map_or(0, |s| s.1 as usize);
        let by_streams = v.streams.iter().filter(|s| s.1 as usize == k).count();
        let by_fetches = v.held.iter().flat_map(|h| &h.1).filter(|n| **n as usize == k).count();
        assert_eq!(
            uses,
            by_streams + by_fetches,
            "{who}: slot {k}: its uses are not its holders"
        );
    }
}

/// One line for the snapshot `v` of a member, whose other members' identity of member 2 is `m2`.
fn snapshot(v: &ValuesView, m: &mut Member, m2: &[u8; 32], out: &mut String) {
    let n = &mut m.names;
    let lsess: Vec<String> = v
        .sessions
        .iter()
        .map(|(sid, peer, inc)| {
            let (s, p) = (number(&mut n.sessions, *sid), number(&mut n.peers, *peer));
            format!(r#"{{"sid":{s},"peer":{p},"inc":{inc}}}"#)
        })
        .collect();
    let lout: Vec<String> = v
        .dialed
        .iter()
        .map(|(peer, sid)| {
            let (s, p) = (number(&mut n.sessions, *sid), number(&mut n.peers, *peer));
            format!(r#"{{"peer":{p},"sid":{s}}}"#)
        })
        .collect();
    let provs: Vec<String> = v
        .provs
        .iter()
        .map(|slot| match slot {
            Some((peer, uses)) => format!(r#"{{"peer":{},"uses":{uses}}}"#, number(&mut n.peers, *peer)),
            None => r#"{"peer":0,"uses":0}"#.to_owned(),
        })
        .collect();
    let streams: Vec<String> = v
        .streams
        .iter()
        .map(|(lid, prov, owner, ses)| {
            let (l, s) = (number(&mut n.lids, *lid), number(&mut n.sessions, *ses));
            format!(r#"{{"lid":{l},"prov":{prov},"owner":{owner},"ses":{s}}}"#)
        })
        .collect();
    let held: Vec<String> = v
        .held
        .iter()
        .map(|(f, ps)| {
            let ps: Vec<String> = ps.iter().map(u32::to_string).collect();
            format!(r#"{{"f":{f},"ps":[{}]}}"#, ps.join(","))
        })
        .collect();
    let _ = writeln!(
        out,
        r#"{{"t":"vsnap","v":{{"lsess":[{}],"lout":[{}],"provs":[{}],"streams":[{}],"held":[{}]}}}}"#,
        lsess.join(","),
        lout.join(","),
        provs.join(","),
        streams.join(","),
        held.join(",")
    );
    // an incoming session of member 2 that held streams, and none now, while a newer one is in the table
    let incoming: Vec<u32> = v
        .sessions
        .iter()
        .filter(|(_, peer, inc)| *inc && peer == m2)
        .filter_map(|(sid, _, _)| n.sessions.get(sid).copied())
        .collect();
    for sid in &incoming {
        let held_stream = v.streams.iter().any(|s| n.sessions.get(&s.3) == Some(sid));
        if held_stream {
            m.streamed.insert(*sid);
        }
    }
    for old in &m.streamed {
        let idle = !v.streams.iter().any(|s| n.sessions.get(&s.3) == Some(old));
        if idle && incoming.iter().any(|new| new > old) {
            m.superseded = true;
        }
    }
}

/// One seed: the world, the run and the snapshots.
fn run(seed: u64, out: &mut String) {
    let mut w = LWorld::build_with(seed, 2, 6, 8_000_000, false, values_on);
    let m = w.members.clone();
    let len = 256 << 10;
    let mut roots = Vec::new();
    for (k, p) in m[1..5].iter().enumerate() {
        roots.push(w.provide(*p, data(seed * 16 + k as u64, len)));
    }
    w.apps(m[3]).values.lie(Some(Lie::EveryRead));
    for root in &roots {
        let providers = ids(&w, &m[1..5]);
        w.sim.command(
            secs(30),
            m[0],
            NCmd::ValuesFetch {
                root: *root,
                length: len as u64,
                ranges: vec![],
                providers,
                deadline: Some(DEADLINE),
            },
        );
    }
    let providers = ids(&w, &m[1..3]);
    w.sim.command(
        secs(30),
        m[5],
        NCmd::ValuesFetch {
            root: roots[0],
            length: len as u64,
            ranges: vec![],
            providers,
            deadline: Some(DEADLINE),
        },
    );
    // SUPERSEDE needs a peer that dials: member 2 is a provider of the others, so it fetches too, just before its
    // crash (the transfer is cut) and after its restart (the bytes it did not verify are asked for again).
    for at in [secs(32) - 100 * MS, secs(33) + 500 * MS] {
        w.sim.command(
            at,
            m[2],
            NCmd::ValuesFetch {
                root: roots[3],
                length: len as u64,
                ranges: vec![],
                providers: ids(&w, &m[4..5]),
                deadline: Some(DEADLINE),
            },
        );
    }
    w.sim.crash(secs(32), m[2]);
    w.sim.restart(secs(33), m[2]);
    let m2 = w.id(m[2]);
    let mut members: Vec<Member> = m.iter().map(|_| Member::default()).collect();
    let mut t = 0;
    while t < secs(60) {
        t += 50 * MS;
        w.run(t);
        if t == secs(31) {
            let held = w.sim.node(m[0]).node.values_view().held;
            if let Some(id) = held.iter().map(|h| h.0).min() {
                w.sim.node_mut(m[0]).node.values_cancel(t, id);
            }
        }
        for (i, n) in m.iter().enumerate() {
            let v = w.sim.node(*n).node.values_view();
            check(&v, &format!("seed {seed}, member {i}, {} ms", t / MS));
            snapshot(&v, &mut members[i], &m2, out);
        }
    }
    for i in [0, 5] {
        let v = w.sim.node(m[i]).node.values_view();
        assert!(v.held.is_empty(), "seed {seed}: member {i} still runs a fetch");
        assert!(
            v.streams.iter().all(|s| s.2 == 0),
            "seed {seed}: member {i} still holds a fetch stream"
        );
    }
    // Fetch ids run from 1 in the order the commands were given. The roots of members 2 and 3 have no holder after
    // 33 s (a crashed provider, a liar) and may end at the deadline; the other two have an honest holder all run.
    for (who, fetch, root) in [(0, 4, "member 4"), (5, 1, "member 1")] {
        let done = w
            .node_events(m[who])
            .iter()
            .any(|(t, e)| matches!(e, NodeEvent::ValueComplete { fetch: f } if *f == fetch) && *t < DEADLINE);
        assert!(
            done,
            "seed {seed}: member {who} did not complete its fetch of the root of {root} before the deadline"
        );
    }
    assert!(
        members.iter().any(|x| x.superseded),
        "seed {seed}: no snapshot showed a superseded session (the run did not exercise SUPERSEDE)"
    );
}

#[test]
fn the_values_layer_over_sessions_matches_the_model() {
    let out = big(|| {
        let mut out = String::new();
        for seed in [301u64, 302, 303] {
            run(seed, &mut out);
        }
        out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("node_values.ndjson"), &out).unwrap();
    }
}
