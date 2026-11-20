//! The chunk store (pinc#651): on an endpoint that owns its table ([`pinc_core::Endpoint::new_owned`], the facade's
//! shape), every chunk comes from one store made with the endpoint, so after setup nothing is allocated for a stream, a
//! session in a slot taken again, or a burst that fills the store; a full store holds the burst back, every slot's
//! floor, held from setup, keeps another session moving and lets a new one in, and the burst completes once chunks
//! come back. Every endpoint call is metered.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]

use pinc_core::{Command, Event, Role, SessionId, Value};
use pinc_tests::*;

pinc_tests::install_counting_allocator!();

/// The stream cycles metered.
const CYCLES: u64 = 20;
/// The bytes of one exchange: two chunks.
const EXCHANGE: usize = 24 * 1024;

/// Open a unidirectional stream on `sa` of node `a`; its id.
fn open(net: &mut CoreNet, a: usize, sa: SessionId) -> u64 {
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
        panic!("no stream")
    };
    id
}

/// Write as much of `data[*off..]` as the stream takes now, and finish it once all is written.
fn feed(n: &mut CoreNet, a: usize, sa: SessionId, id: u64, data: &[u8], off: &mut usize, finished: &mut bool) {
    let t = n.now;
    while *off < data.len() {
        let Ok(rep) = n.nodes[a].cmd(
            t,
            Command::Write {
                session: sa,
                stream: id,
                data: &data[*off..],
            },
        ) else {
            break;
        };
        let Value::Written(w) = rep.value else { break };
        if w == 0 {
            break;
        }
        *off += w;
    }
    if *off == data.len() && !*finished {
        *finished = n.nodes[a]
            .cmd(
                t,
                Command::Finish {
                    session: sa,
                    stream: id,
                },
            )
            .is_ok();
    }
}

/// Read every stream of `b` that reported data on `only` (or on any session).
fn read_all(n: &mut CoreNet, b: usize, only: Option<SessionId>) {
    let readable: Vec<(SessionId, u64)> = n.nodes[b]
        .events
        .iter()
        .filter_map(|(_, e)| match e {
            Event::StreamReadable { session, stream } if only.is_none_or(|s| s == *session) => {
                Some((*session, *stream))
            }
            _ => None,
        })
        .collect();
    let now = n.now;
    for (s, st) in readable {
        n.nodes[b].read_stream(now, s, st);
    }
}

/// One stream cycle: `a` opens a stream on `sa`, writes `EXCHANGE` bytes and finishes it; the peer reads it to the
/// end; the net runs until both ends have forgotten the stream, so the session is quiet again.
fn cycle(net: &mut CoreNet, a: usize, b: usize, sa: SessionId, seed: u64) {
    let data = pattern(EXCHANGE, seed);
    let id = open(net, a, sa);
    let (mut off, mut finished) = (0, false);
    let want = net.nodes[b].fin.len() + 1;
    let t = net.now;
    assert!(net.run(t + 30 * SEC_NS, |n| {
        feed(n, a, sa, id, &data, &mut off, &mut finished);
        n.nodes[b].fin.len() >= want
    }));
    // The acknowledgements and the stream's end on both sides.
    net.run_for(SEC_NS);
}

/// Run `f` with every endpoint call metered; the allocations counted.
fn allocations(f: impl FnOnce()) -> u64 {
    meter_endpoint_calls(true);
    metered(|| std::hint::black_box(vec![0u8; 64]));
    assert!(take_metered_allocs() >= 1, "the meter is blind");
    f();
    meter_endpoint_calls(false);
    take_metered_allocs()
}

#[test]
fn stream_after_stream_on_a_quiet_session_allocates_nothing_after_the_first() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add_owned(1, 0), net.add_owned(2, 0));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        cycle(&mut net, a, b, sa, 0);
        net.run_for(2 * SEC_NS);
        let allocs = allocations(|| {
            for k in 1..=CYCLES {
                cycle(&mut net, a, b, sa, k);
            }
        });
        assert_eq!(
            allocs, 0,
            "{CYCLES} stream cycles on a quiet session allocated {allocs} times"
        );
        assert!(net.nodes[b].fin.len() > CYCLES as usize);
        // A quiet session holds no chunk: they are all back in the store.
        assert_eq!(net.nodes[a].ep.node_stats().store.used, 0);
        assert_eq!(net.nodes[b].ep.node_stats().store.used, 0);
    });
}

#[test]
fn a_session_in_a_slot_taken_again_allocates_nothing_for_its_streams() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add_owned(1, 0), net.add_owned(2, 0));
        let (peer, to) = (net.nodes[b].node, net.nodes[b].addr);
        let session = |net: &mut CoreNet, seed: u64| {
            let now = net.now;
            let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
            net.run_for(SEC_NS);
            let sa = net.nodes[a].session(&rep);
            cycle(net, a, b, sa, seed);
            cycle(net, a, b, sa, seed + 1);
            let now = net.now;
            net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
            net.run_for(2 * SEC_NS);
        };
        // Warm up: the first two sessions make the slots of both ends.
        session(&mut net, 0);
        session(&mut net, 10);
        let allocs = allocations(|| {
            for k in 1..=4 {
                session(&mut net, 100 * k);
            }
        });
        assert_eq!(allocs, 0, "four sessions in slots taken again allocated {allocs} times");
        // Every session ran in the slot the first one made, at both ends, and gave the store all it took.
        for n in [a, b] {
            assert_eq!(net.nodes[n].ep.backed_slots(), 1);
            let store = net.nodes[n].ep.node_stats().store;
            let floors = CK as u64 * pinc_transport::stream::store::floor_chunks(CHUNKS_PER_CONN) as u64;
            assert_eq!((store.used, store.reserved), (0, floors));
        }
    });
}

#[test]
fn a_burst_that_fills_the_store_allocates_nothing_holds_back_and_completes_once_chunks_come_back() {
    big_stack(|| {
        // Three senders of four streams (the most a test table lets a peer open) of 512 KiB: twelve windows of 256 KiB
        // together, at b's store of 2 MiB that also keeps c's floor.
        const SENDERS: usize = 3;
        const PER: usize = 4;
        const LEN: usize = 512 * 1024;
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, d, f, b, c, e) = (
            net.add_owned(1, 0),
            net.add_owned(4, 0),
            net.add_owned(6, 0),
            net.add_owned(2, 0),
            net.add_owned(3, 0),
            net.add_owned(5, 0),
        );
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (sd, _) = net.connect_pair(d, b, ALPN_A, Role::Other);
        let (sf, _) = net.connect_pair(f, b, ALPN_A, Role::Other);
        let (sc, sbc) = net.connect_pair(c, b, ALPN_A, Role::Other);
        // e's slots at both ends are made now, so the dial below takes them again.
        let (se, _) = net.connect_pair(e, b, ALPN_A, Role::Other);
        let now = net.now;
        net.nodes[e].cmd(now, Command::Close { session: se, error: 0 }).unwrap();
        net.run_for(2 * SEC_NS);
        let connected = net.nodes[b].count(|ev| matches!(ev, Event::Incoming { .. }));
        // b holds what arrives: nothing is read until the store is full.
        net.nodes[b].auto_read = false;
        let senders = [(a, sa), (d, sd), (f, sf)];
        let datas: Vec<Vec<u8>> = (0..SENDERS * PER).map(|k| pattern(LEN, k as u64)).collect();
        let small = pattern(EXCHANGE, 99);
        let mut ids: [Vec<u64>; SENDERS] = std::array::from_fn(|_| Vec::new());
        let mut offs = [0usize; SENDERS * PER];
        let mut done = [false; SENDERS * PER];
        // Open each sender's streams as b's credit lets it, and write each as far as it takes. b's sessions never hold
        // a chunk their reservation does not cover.
        let mut burst = |n: &mut CoreNet, ids: &mut [Vec<u64>; SENDERS]| {
            for (j, (node, s)) in senders.iter().enumerate() {
                while ids[j].len() < PER {
                    let t = n.now;
                    let Ok(rep) = n.nodes[*node].cmd(
                        t,
                        Command::OpenStream {
                            session: *s,
                            bidi: false,
                        },
                    ) else {
                        break;
                    };
                    let Value::Stream(id) = rep.value else { break };
                    ids[j].push(id);
                }
                for (k, id) in ids[j].iter().enumerate() {
                    let x = j * PER + k;
                    feed(n, *node, *s, *id, &datas[x], &mut offs[x], &mut done[x]);
                }
            }
            let store = n.nodes[b].ep.node_stats().store;
            assert!(
                store.used <= store.reserved && store.reserved <= store.chunks,
                "{store:?}"
            );
        };
        let (peer, to) = (net.nodes[b].node, net.nodes[b].addr);
        let allocs = allocations(|| {
            let t = net.now;
            net.run(t + 3 * SEC_NS, |n| {
                burst(n, &mut ids);
                false
            });
            let store = net.nodes[b].ep.node_stats().store;
            assert!(store.full > 0, "the store never ran out: {store:?}");
            assert!(
                store.chunks - store.reserved < CHUNKS_PER_CONN.min(8) as u64,
                "{store:?}"
            );
            // A new session gets in at once: its slot's floor was set aside when the store was made, so a full store
            // refuses no one.
            let now = net.now;
            net.nodes[e].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
            let t = net.now;
            assert!(net.run(
                t + 2 * SEC_NS,
                |n| n.nodes[b].count(|ev| matches!(ev, Event::Incoming { .. })) > connected
            ));
            // c's session still moves: its stream reaches b whole while the burst is held back.
            let id = open(&mut net, c, sc);
            let (mut off, mut finished) = (0, false);
            let t = net.now;
            assert!(net.run(t + 10 * SEC_NS, |n| {
                feed(n, c, sc, id, &small, &mut off, &mut finished);
                read_all(n, b, Some(sbc));
                n.nodes[b].fin.iter().any(|(s, _)| *s == sbc)
            }));
            assert!(
                net.nodes[b].fin.iter().all(|(s, _)| *s == sbc),
                "the burst finished before b read it"
            );
            // b reads again: the chunks come back and the burst completes.
            net.nodes[b].auto_read = true;
            let t = net.now;
            assert!(net.run(t + 120 * SEC_NS, |n| {
                burst(n, &mut ids);
                read_all(n, b, None);
                n.nodes[b].fin.len() > SENDERS * PER
            }));
        });
        // Only the first bytes of streams the senders opened on soft credit were ever short; every granted window was
        // backed.
        let store = net.nodes[b].ep.node_stats().store;
        eprintln!(
            "burst: shortage_first {} shortage_backed {}",
            store.shortage_first, store.shortage_backed
        );
        assert_eq!(store.shortage_backed, 0, "{store:?}");
        assert_eq!(allocs, 0, "a burst that filled the store allocated {allocs} times");
        let read: usize = net.nodes[b]
            .read
            .iter()
            .filter(|((s, _), _)| *s != sbc)
            .map(|(_, v)| v.len())
            .sum();
        assert_eq!(read, SENDERS * PER * LEN);
    });
}

#[test]
fn a_session_held_back_by_the_store_moves_as_soon_as_another_session_gives_its_chunks_back() {
    big_stack(|| {
        // The streams of d, f and g sit unread in b's store until it is full. Only then does a start a stream, which b
        // reads as it arrives: a's session has its floor and nothing else, so each window it grants past the floor
        // waits for the store, and once a has sent what it may, neither end of a's session has anything to send.
        const PER: usize = 4;
        const LEN: usize = 512 * 1024;
        const BIG: usize = 4 * 1024 * 1024;
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, d, f, g, b) = (
            net.add_owned(1, 0),
            net.add_owned(4, 0),
            net.add_owned(6, 0),
            net.add_owned(7, 0),
            net.add_owned(2, 0),
        );
        let (sa, sba) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (sd, sbd) = net.connect_pair(d, b, ALPN_A, Role::Other);
        let (sf, _) = net.connect_pair(f, b, ALPN_A, Role::Other);
        let (sg, _) = net.connect_pair(g, b, ALPN_A, Role::Other);
        // One stream on a's session first, so it is back at its floor.
        cycle(&mut net, a, b, sa, 1);
        net.nodes[b].auto_read = false;
        let datas: Vec<Vec<u8>> = (0..3 * PER).map(|k| pattern(LEN, k as u64)).collect();
        let ids: Vec<(usize, SessionId, u64)> = (0..PER)
            .flat_map(|_| [(d, sd), (f, sf), (g, sg)])
            .map(|(n, s)| (n, s, open(&mut net, n, s)))
            .collect();
        let mut offs = vec![0usize; ids.len()];
        let mut done = vec![false; ids.len()];
        let t = net.now;
        net.run(t + 4 * SEC_NS, |n| {
            for (k, (node, s, id)) in ids.iter().enumerate() {
                feed(n, *node, *s, *id, &datas[k], &mut offs[k], &mut done[k]);
            }
            false
        });
        let big = pattern(BIG, 77);
        let ia = open(&mut net, a, sa);
        let (mut off, mut fin) = (0, false);
        let fins = |n: &CoreNet| n.nodes[b].fin.iter().filter(|(s, _)| *s == sba).count();
        let before = fins(&net);
        let a_done = |n: &CoreNet| fins(n) > before;
        // b reads a's stream only when it reports new data, as an application does: a read is a call into b's endpoint
        // that would try a's grants again by itself.
        let mut seen = net.nodes[b].events.len();
        let mut read_new = |n: &mut CoreNet| {
            let now = n.now;
            let fresh: Vec<u64> = n.nodes[b].events[seen..]
                .iter()
                .filter_map(|(_, e)| match e {
                    Event::StreamReadable { session, stream } if *session == sba => Some(*stream),
                    _ => None,
                })
                .collect();
            seen = n.nodes[b].events.len();
            for st in fresh {
                n.nodes[b].read_stream(now, sba, st);
            }
        };
        let t = net.now;
        net.run(t + 3 * SEC_NS, |n| {
            feed(n, a, sa, ia, &big, &mut off, &mut fin);
            read_new(n);
            false
        });
        let store = net.nodes[b].ep.node_stats().store;
        assert!(store.full > 0, "the store never ran out: {store:?}");
        assert!(!a_done(&net), "a's stream finished with the store full");
        // b drops d's session: its chunks and its reservation go back to the store, which wakes a's session. It must
        // finish within 1.5 s; unwoken, it waits for a's blocked signals to make b try again, and takes over 2.5 s.
        let now = net.now;
        net.nodes[b]
            .cmd(now, Command::Close { session: sbd, error: 0 })
            .unwrap();
        let t = net.now;
        let ok = net.run(t + 3 * SEC_NS / 2, |n| {
            feed(n, a, sa, ia, &big, &mut off, &mut fin);
            read_new(n);
            a_done(n)
        });
        assert!(
            ok,
            "a's stream stayed held back after d's chunks came back: {:?}",
            net.nodes[b].ep.node_stats().store
        );
        // a's stream ran past its opening window into windows b granted, and none of them found a chunk short.
        let store = net.nodes[b].ep.node_stats().store;
        assert_eq!(store.shortage_backed, 0, "{store:?}");
    });
}

#[test]
fn the_store_is_made_and_charged_with_the_endpoint_and_only_then() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add_owned(1, 0), net.add_owned(2, 0));
        // Every slot's floor is reserved from the start, before any session.
        let floors = CK as u64 * pinc_transport::stream::store::floor_chunks(CHUNKS_PER_CONN) as u64;
        let before = net.nodes[a].ep.node_stats().store;
        assert_eq!(
            (before.chunks, before.touched, before.reserved),
            (STORE_CHUNKS as u64, 0, floors)
        );
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        assert!(net.nodes[a].ep.node_stats().store.reserved >= floors);
        for k in 0..3 {
            cycle(&mut net, a, b, sa, k);
        }
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(2 * SEC_NS);
        let after = net.nodes[a].ep.node_stats().store;
        assert_eq!(
            (after.chunks, after.used, after.reserved),
            (STORE_CHUNKS as u64, 0, floors)
        );
        assert!(after.touched > 0 && after.touched <= after.chunks);
    });
}
