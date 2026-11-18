//! Range sets that spill on an endpoint that owns its memory ([`Endpoint::new_owned`]): once the endpoint is set up and
//! its sessions are warm, scattered loss that pushes every stream's ranges past their inline arrays and back costs no
//! heap allocation. The spill slots come from the arena the endpoint made at setup, never from the pool's chunks.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::cell::Cell;
use std::net::SocketAddr;
use std::rc::Rc;

use pinc_core::{Answer, Command, Query, Role, SessionId, Value};
use pinc_tests::*;

pinc_tests::install_counting_allocator!();

/// Open a stream on `sa`, write `size` bytes and finish it, until the receiver has seen its end.
fn transfer(net: &mut CoreNet, a: usize, sa: SessionId, size: usize, seed: u64) {
    let data = pattern(size, seed);
    let t = net.now;
    let Value::Stream(id) = net.nodes[a]
        .cmd(
            t,
            Command::OpenStream {
                session: sa,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!()
    };
    let mut off = 0;
    let want = net.nodes[1].fin.len() + 1;
    assert!(net.run(t + 60 * SEC_NS, |n| {
        let t = n.now;
        while off < data.len() {
            let Ok(rep) = n.nodes[a].cmd(
                t,
                Command::Write {
                    session: sa,
                    stream: id,
                    data: &data[off..],
                },
            ) else {
                break;
            };
            let Value::Written(w) = rep.value else { break };
            if w == 0 {
                break;
            }
            off += w;
        }
        if off == data.len() {
            let _ = n.nodes[a].cmd(
                t,
                Command::Finish {
                    session: sa,
                    stream: id,
                },
            );
        }
        n.nodes[1].fin.len() >= want
    }));
}

/// The spill counters of a session: (range sets spilled, spills refused).
fn spills(net: &CoreNet, node: usize, s: SessionId) -> (u64, u64) {
    let Answer::Stats(st) = net.nodes[node].ep.query(Query::Stats(s)) else {
        panic!("no session")
    };
    (st.transport.range_spills, st.transport.spill_refused)
}

/// From `from`, while `on` is set, drop every other datagram of the 400 after the 4,000th since `sent` was last zeroed:
/// scores of holes in one flight, so the sender's acknowledged ranges outgrow their inline array and shrink back as the
/// holes are filled.
fn burst(from: SocketAddr, on: Rc<Cell<bool>>, sent: Rc<Cell<u64>>) -> LossFn {
    Box::new(move |src, _, _| {
        if src != from || !on.get() {
            return false;
        }
        let k = sent.get() + 1;
        sent.set(k);
        (4000..4400).contains(&k) && k.is_multiple_of(2)
    })
}

/// Open a stream on `s` and write a byte, so the session never goes quiet.
fn hold_open(net: &mut CoreNet, a: usize, s: SessionId) {
    let t = net.now;
    let Value::Stream(id) = net.nodes[a]
        .cmd(
            t,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!()
    };
    net.nodes[a]
        .cmd(
            t,
            Command::Write {
                session: s,
                stream: id,
                data: &[1],
            },
        )
        .unwrap();
}

/// Make every chunk of the pools of `s` at both ends: three streams (with the open one, all a session of `CN` slots
/// may open) written while `b` reads nothing fill the sender's pool with what waits to be sent and the receiver's with
/// what arrived, then `b` reads them through. The pools keep the chunks while `s` has a stream open, so nothing later
/// grows them.
fn fill_pools(net: &mut CoreNet, a: usize, b: usize, (s, sb): (SessionId, SessionId)) {
    net.nodes[b].auto_read = false;
    let t = net.now;
    let ids: Vec<u64> = (0..3)
        .map(|_| {
            let Value::Stream(id) = net.nodes[a]
                .cmd(
                    t,
                    Command::OpenStream {
                        session: s,
                        bidi: false,
                    },
                )
                .unwrap()
                .value
            else {
                panic!()
            };
            id
        })
        .collect();
    let block = vec![9u8; 1 << 20];
    let deadline = net.now + 3 * SEC_NS;
    net.run(deadline, |n| {
        let t = n.now;
        for &id in &ids {
            let _ = n.nodes[a].cmd(
                t,
                Command::Write {
                    session: s,
                    stream: id,
                    data: &block,
                },
            );
        }
        false
    });
    net.nodes[b].auto_read = true;
    let (t, want) = (net.now, net.nodes[b].fin.len() + ids.len());
    for &id in &ids {
        net.nodes[a].cmd(t, Command::Finish { session: s, stream: id }).unwrap();
    }
    assert!(net.run(t + 60 * SEC_NS, |n| {
        let t = n.now;
        for &id in &ids {
            n.nodes[b].read_stream(t, sb, id);
        }
        n.nodes[b].fin.len() >= want
    }));
}

/// Two warm sessions, each hit by loss bursts on its streams: every range set that spills takes a slot of the arena made
/// at setup and gives it back when it shrinks or its stream ends, and none of it touches the heap. The warm-up makes the
/// chunks the pools come to hold and keeps them (#640 is the pool's own allocation after a trim, kept out of this test);
/// that a spill takes no pool chunk is checked by the stream test
/// `received_ranges_spill_into_the_arena_take_no_chunk_and_move_back_at_half`.
#[test]
fn spills_and_their_return_under_loss_bursts_allocate_nothing_after_setup() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add_owned(1, 8), net.add_owned(2, 8));
        let pairs = [
            net.connect_pair(a, b, ALPN_A, Role::Other),
            net.connect_pair(a, b, ALPN_B, Role::Other),
        ];
        let sessions = pairs.map(|p| p.0);
        // A quiet session's grown pool frees its idle chunks and makes them again on its next stream: an allocation of
        // the pool's own (#640), not of the spill, kept out of this test by a stream that stays open.
        for p in pairs {
            hold_open(&mut net, a, p.0);
            fill_pools(&mut net, a, b, p);
        }
        let (on, sent) = (Rc::new(Cell::new(false)), Rc::new(Cell::new(0)));
        net.loss = Some(burst(net.nodes[a].addr, Rc::clone(&on), Rc::clone(&sent)));
        for (seed, s) in (1..).zip(sessions.iter().chain(&sessions)) {
            transfer(&mut net, a, *s, 8_000_000, seed);
        }
        net.run_for(2 * SEC_NS);
        assert_eq!(spills(&net, a, sessions[0]), (0, 0), "the warm-up spilled");

        meter_endpoint_calls(true);
        metered(|| std::hint::black_box(vec![0u8; 64]));
        assert!(take_metered_allocs() >= 1, "the meter is blind");
        on.set(true);
        for (seed, s) in (10..).zip(sessions.iter().chain(&sessions)) {
            sent.set(0);
            transfer(&mut net, a, *s, 8_000_000, seed);
        }
        net.run_for(5 * SEC_NS);
        meter_endpoint_calls(false);
        let allocs = take_metered_allocs();
        for s in sessions {
            let (spilled, refused) = spills(&net, a, s);
            assert!(spilled > 0, "the bursts on {s:?} spilled nothing");
            assert_eq!(
                refused, 0,
                "a spill on {s:?} was refused: the arena is too small for the test"
            );
        }
        assert_eq!(
            allocs, 0,
            "spilling and moving back allocated {allocs} times after setup"
        );
    });
}
