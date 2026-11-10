//! The endpoint commands and queries a host composition needs: stream urgency, extension frames, bytes in flight,
//! delivery of a stream's data, and reads of stored bytes beyond a hole.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss
)]

use std::cell::Cell;
use std::rc::Rc;

use vinc_core::{
    Answer, Command, CommandError, EXT_BODY_MAX, Event, FAN_URGENCY, Query, Role, SessionId, TraceEvent, Value,
};
use vinc_tests::*;
use vinc_transport::conn::ExtensionError;
use vinc_transport::frame::ext;
use vinc_transport::stream::StreamError;

const S: u64 = SEC_NS;

fn open(net: &mut CoreNet, n: usize, s: SessionId) -> u64 {
    let now = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(now, Command::OpenStream { session: s, bidi: true })
        .unwrap()
        .value
    else {
        panic!("no stream")
    };
    id
}

fn write(net: &mut CoreNet, n: usize, s: SessionId, id: u64, data: &[u8]) {
    let now = net.now;
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
}

#[test]
fn a_stream_set_to_a_lower_urgency_is_sent_first() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let first = open(&mut net, a, sa);
        let second = open(&mut net, a, sa);
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::SetUrgency {
                    session: sa,
                    stream: second,
                    urgency: 1,
                },
            )
            .unwrap();
        write(&mut net, a, sa, first, &[1; 3000]);
        write(&mut net, a, sa, second, &[2; 3000]);
        net.run_for(S);
        // Opening a stream opens every lower one, so the order of arrival is the order of the readable events.
        let order: Vec<u64> = net.nodes[b]
            .events
            .iter()
            .filter_map(|(_, e)| match e {
                Event::StreamReadable { stream, .. } => Some(*stream),
                _ => None,
            })
            .collect();
        assert_eq!(
            order.first(),
            Some(&second),
            "the more urgent stream arrived first: {order:?}"
        );
        // A stream or a session that is not there is refused, not ignored.
        let now = net.now;
        assert!(matches!(
            net.nodes[a].cmd(
                now,
                Command::SetUrgency {
                    session: sa,
                    stream: 4001,
                    urgency: 1
                }
            ),
            Err(CommandError::Stream(StreamError::UnknownStream))
        ));
        assert!(matches!(
            net.nodes[a].cmd(
                now,
                Command::SetUrgency {
                    session: SessionId(99),
                    stream: first,
                    urgency: 1
                }
            ),
            Err(CommandError::NoSession)
        ));
    });
}

#[test]
fn a_write_on_the_broadcast_urgency_does_not_keep_a_quiet_session_awake() {
    big_stack(|| {
        // After the session has gone quiet (130 s), 200 bytes on an ordinary stream plan a ping 5 s after the last
        // send, for 20 s; the same bytes on a stream at the broadcast urgency leave the plan at the idle interval.
        let mut next_ping = Vec::new();
        for urgency in [None, Some(FAN_URGENCY)] {
            let mut net = CoreNet::new(10 * MS_NS);
            let (a, b) = (net.add(1), net.add(2));
            let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Hub);
            let now = net.now;
            net.nodes[b]
                .cmd(
                    now,
                    Command::SetRole {
                        session: sb,
                        role: Role::Member,
                    },
                )
                .unwrap();
            net.run_for(130 * S);
            let id = open(&mut net, a, sa);
            if let Some(urgency) = urgency {
                let now = net.now;
                net.nodes[a]
                    .cmd(
                        now,
                        Command::SetUrgency {
                            session: sa,
                            stream: id,
                            urgency,
                        },
                    )
                    .unwrap();
            }
            let mut plan: Option<u64> = None;
            let drain = |net: &mut CoreNet, plan: &mut Option<u64>| {
                while let Some(r) = net.nodes[a].ep.poll_trace() {
                    if let TraceEvent::Keepalive { slot, ping_at, .. } = r.event
                        && slot == sa.slot() as u64
                    {
                        *plan = Some(ping_at);
                    }
                }
            };
            drain(&mut net, &mut plan);
            let wrote = net.now;
            write(&mut net, a, sa, id, &[7; 200]);
            drain(&mut net, &mut plan);
            next_ping.push(plan.expect("a keepalive plan exists").saturating_sub(wrote));
        }
        assert!(
            next_ping[0] <= 6 * S,
            "an ordinary write plans a ping within 5 s: {next_ping:?}"
        );
        assert!(
            next_ping[1] >= 14 * S,
            "a broadcast-lane write leaves the idle interval: {next_ping:?}"
        );
    });
}

#[test]
fn an_extension_frame_arrives_in_order_through_loss_and_the_ring_keeps_the_newest() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // Every other datagram from a is lost: the frame is sent again until acknowledged.
        let n = Rc::new(Cell::new(0u32));
        let counter = Rc::clone(&n);
        let from = net.nodes[a].addr;
        net.loss = Some(Box::new(move |f, _, _| {
            if f != from {
                return false;
            }
            counter.set(counter.get() + 1);
            counter.get() % 2 == 1
        }));
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::SendExtension {
                    session: sa,
                    ty: ext::PROOF_REQ,
                    body: b"first",
                },
            )
            .unwrap();
        net.nodes[a]
            .cmd(
                now,
                Command::SendExtension {
                    session: sa,
                    ty: ext::PROOF,
                    body: &[9; 1100],
                },
            )
            .unwrap();
        net.run_for(5 * S);
        let mut out = vec![0u8; EXT_BODY_MAX];
        let got = net.nodes[b].ep.read_extension(&mut out).unwrap().unwrap();
        assert_eq!(got, (sb, ext::PROOF_REQ, 5));
        assert_eq!(&out[..5], b"first");
        let got = net.nodes[b].ep.read_extension(&mut out).unwrap().unwrap();
        assert_eq!(got, (sb, ext::PROOF, 1100));
        assert_eq!(out[..1100], [9; 1100]);
        // A retransmitted copy may arrive again; nothing else is left after those.
        while let Some((_, t, _)) = net.nodes[b].ep.read_extension(&mut out).unwrap() {
            assert!(t == ext::PROOF_REQ || t == ext::PROOF);
        }
        // The ring holds eight: ten frames leave the newest eight, oldest first.
        net.loss = None;
        let now = net.now;
        for i in 0..10u8 {
            net.nodes[a]
                .cmd(
                    now,
                    Command::SendExtension {
                        session: sa,
                        ty: ext::PROOF_REQ,
                        body: &[i; 4],
                    },
                )
                .unwrap();
        }
        net.run_for(2 * S);
        let mut seen = Vec::new();
        while let Some((_, _, len)) = net.nodes[b].ep.read_extension(&mut out).unwrap() {
            seen.push(out[0]);
            assert_eq!(len, 4);
        }
        assert_eq!(seen, (2..10u8).collect::<Vec<_>>());
    });
}

#[test]
fn an_extension_frame_that_cannot_be_sent_or_read_says_why() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let now = net.now;
        let big = vec![0u8; 5000];
        assert!(matches!(
            net.nodes[a].cmd(
                now,
                Command::SendExtension {
                    session: sa,
                    ty: ext::PROOF,
                    body: &big
                }
            ),
            Err(CommandError::Extension(ExtensionError::TooLarge { .. }))
        ));
        assert!(matches!(
            net.nodes[a].cmd(
                now,
                Command::SendExtension {
                    session: sa,
                    ty: 0x10,
                    body: b"x"
                }
            ),
            Err(CommandError::Extension(ExtensionError::BadType))
        ));
        assert!(matches!(
            net.nodes[a].cmd(
                now,
                Command::SendExtension {
                    session: SessionId(77),
                    ty: ext::PROOF,
                    body: b"x"
                }
            ),
            Err(CommandError::NoSession)
        ));
        net.nodes[a]
            .cmd(
                now,
                Command::SendExtension {
                    session: sa,
                    ty: ext::PROOF,
                    body: &[5; 40],
                },
            )
            .unwrap();
        net.run_for(S);
        assert_eq!(
            net.nodes[b].ep.read_extension(&mut [0u8; 8]),
            Err(CommandError::BufferTooSmall { len: 40 })
        );
        assert!(net.nodes[b].ep.read_extension(&mut [0u8; 64]).unwrap().is_some());
        assert_eq!(net.nodes[b].ep.read_extension(&mut [0u8; 64]), Ok(None));
    });
}

#[test]
fn bytes_in_flight_rise_with_a_transfer_and_fall_to_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(20 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let flight = |net: &CoreNet| match net.nodes[a].ep.query(Query::InFlight(sa)) {
            Answer::InFlight(n) => n,
            other => panic!("{other:?}"),
        };
        net.run_for(S);
        assert_eq!(flight(&net), 0);
        let id = open(&mut net, a, sa);
        write(&mut net, a, sa, id, &pattern(60_000, 3));
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Finish {
                    session: sa,
                    stream: id,
                },
            )
            .unwrap();
        let mut peak = 0;
        net.run(net.now + 10 * S, |n| {
            peak = peak.max(flight(n));
            false
        });
        assert!(peak > 5_000, "bytes were in flight during the transfer: {peak}");
        assert_eq!(flight(&net), 0, "everything was acknowledged");
        assert!(matches!(
            net.nodes[a].ep.query(Query::InFlight(SessionId(77))),
            Answer::None
        ));
    });
}

#[test]
fn the_send_state_of_a_stream_shows_progress_loss_and_completion() {
    big_stack(|| {
        let mut net = CoreNet::new(20 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let id = open(&mut net, a, sa);
        let data = pattern(30_000, 4);
        let state = |net: &CoreNet| match net.nodes[a].ep.query(Query::SendState {
            session: sa,
            stream: id,
        }) {
            Answer::SendState(s) => s,
            other => panic!("{other:?}"),
        };
        assert!(!state(&net).done, "a stream with no end is not done");
        write(&mut net, a, sa, id, &data);
        net.run_for(S);
        let s = state(&net);
        assert_eq!(
            (s.sent, s.lost, s.done),
            (30_000, None, false),
            "sent and acknowledged, but no end yet"
        );
        assert!(s.window > 0);
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Finish {
                    session: sa,
                    stream: id,
                },
            )
            .unwrap();
        assert!(!state(&net).done, "the end is not acknowledged yet");
        net.run_for(S);
        assert!(state(&net).done);
        assert!(matches!(
            net.nodes[a].ep.query(Query::SendState {
                session: SessionId(77),
                stream: id
            }),
            Answer::None
        ));
    });
}

#[test]
fn bytes_beyond_a_hole_can_be_read_in_place_before_they_are_readable() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.nodes[b].auto_read = false;
        let id = open(&mut net, a, sa);
        let data = pattern(30_000, 5);
        // The first full-size datagram from a is lost; the later ones arrive.
        let dropped = Rc::new(Cell::new(false));
        let flag = Rc::clone(&dropped);
        let from = net.nodes[a].addr;
        net.loss = Some(Box::new(move |f, _, d| {
            if f == from && d.len() > 1000 && !flag.get() {
                flag.set(true);
                return true;
            }
            false
        }));
        write(&mut net, a, sa, id, &data);
        // Run just long enough for the later packets to arrive, not for the retransmission.
        net.run_for(15 * MS_NS);
        assert!(dropped.get());
        let stored = |net: &CoreNet, from: u64| match net.nodes[b].ep.query(Query::StoredAfter {
            session: sb,
            stream: id,
            from,
        }) {
            Answer::Stored(r) => Some(r),
            _ => None,
        };
        let hole = stored(&net, 0).expect("later bytes arrived");
        assert!(hole.start > 0, "the first bytes are missing: {hole:?}");
        assert!(matches!(
            net.nodes[b].ep.query(Query::Read {
                session: sb,
                stream: id
            }),
            Answer::None
        ));
        // Read the run in place and compare it with what was sent.
        let mut at = hole.start;
        while at < hole.end {
            let Answer::Chunk(c) = net.nodes[b].ep.query(Query::ReadAt {
                session: sb,
                stream: id,
                offset: at,
            }) else {
                panic!("no bytes at {at}")
            };
            let n = c.len().min((hole.end - at) as usize);
            assert_eq!(c[..n], data[at as usize..at as usize + n]);
            at += n as u64;
        }
        // Nothing is stored inside the hole or below the read position.
        assert!(matches!(
            net.nodes[b].ep.query(Query::ReadAt {
                session: sb,
                stream: id,
                offset: 0
            }),
            Answer::None
        ));
        // The search from inside the run starts there; past its end it finds the next run or nothing.
        assert_eq!(stored(&net, hole.start + 5).map(|r| r.start), Some(hole.start + 5));
        assert!(stored(&net, hole.end).is_none());
        // The retransmission fills the hole: everything is one run and readable from the start.
        net.run_for(2 * S);
        net.nodes[b].read_stream(net.now, sb, id);
        assert_eq!(
            net.nodes[b].read.get(&(sb, id)).map(Vec::as_slice),
            Some(data.as_slice())
        );
    });
}
