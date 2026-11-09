//! The relay: routing, aliases, forwarding between relays, reply routes, the byte and time limits and sessions.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements
)]

mod connect_common;

use connect_common::*;
use vinc_connect::carrier::{DnsAnswer, Frame};
use vinc_connect::relay::{CloseReason, NodeState, Quota, Reject, Route, SessionId, Trace, rule};

#[test]
fn a_packet_to_a_node_on_this_relay_is_received_with_aliases() {
    let mut fx = Fx::new();
    let (a, b, c) = (nid(0xa1), nid(0xb2), nid(0xc3));
    let sa = fx.open(T0, a);
    let _sb = fx.open(T0, b);
    let _sc = fx.open(T0, c);
    fx.fx();
    let p = [0x41u8; 80];
    fx.send(
        T0,
        a,
        sa,
        &Frame::Send {
            dst: b,
            flag: 5,
            packet: &p,
        },
    )
    .unwrap();
    // the first RECV from a source carries its id with alias 0; the next carries the alias only
    assert_eq!(
        fx.fx(),
        [Rec::Carrier(
            b,
            enc(&Frame::RecvNew {
                src: a,
                alias: 0,
                flag: 5,
                packet: &p
            })
        )]
    );
    fx.send(
        T0,
        a,
        sa,
        &Frame::Send {
            dst: b,
            flag: 6,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Carrier(
            b,
            enc(&Frame::RecvAlias {
                alias: 0,
                flag: 6,
                packet: &p
            })
        )]
    );
    // a second source gets the next alias on the same carrier
    let sc = SessionId(2);
    fx.send(
        T0,
        c,
        sc,
        &Frame::Send {
            dst: b,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Carrier(
            b,
            enc(&Frame::RecvNew {
                src: c,
                alias: 1,
                flag: 0,
                packet: &p
            })
        )]
    );
    let routed: Vec<Trace> = traces_of(&fx)
        .into_iter()
        .filter(|t| matches!(t, Trace::Routed { .. }))
        .collect();
    assert_eq!(routed.len(), 3);
    assert!(routed.iter().all(|t| matches!(
        t,
        Trace::Routed {
            route: Route::Carrier,
            ..
        }
    )));
}

#[test]
fn the_sender_side_aliases_resolve_and_an_unknown_alias_is_refused() {
    let mut fx = Fx::new();
    let (a, b) = (nid(0xa1), nid(0xb2));
    let sa = fx.open(T0, a);
    fx.open(T0, b);
    fx.fx();
    let p = [0x41u8; 20];
    fx.send(
        T0,
        a,
        sa,
        &Frame::SendNew {
            dst: b,
            alias: 7,
            flag: 1,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(fx.fx().len(), 1);
    fx.send(
        T0,
        a,
        sa,
        &Frame::SendAlias {
            alias: 7,
            flag: 2,
            packet: &p,
        },
    )
    .unwrap();
    assert!(matches!(fx.fx()[..], [Rec::Carrier(n, _)] if n == b));
    assert_eq!(
        fx.send(
            T0,
            a,
            sa,
            &Frame::SendAlias {
                alias: 8,
                flag: 2,
                packet: &p
            }
        ),
        Err(Reject::UnknownAlias)
    );
    assert!(fx.fx().is_empty());
}

#[test]
fn at_most_32_aliases_then_the_table_starts_again() {
    let mut fx = Fx::new();
    let (b, p1) = (nid(0xb2), nid(0x91));
    fx.open(T0, b);
    fx.r.add_peer(p1);
    fx.fx();
    let p = [0x41u8; 20];
    // 70 different sources reach b through a peer relay: the aliases run 0..=31 and start again
    for i in 0..70u8 {
        let s = nid(i);
        fx.peer(
            T0,
            p1,
            &Frame::Forward {
                src: s,
                dst: b,
                flag: 0,
                packet: &p,
            },
        )
        .unwrap();
        let out = fx.fx();
        let want = enc(&Frame::RecvNew {
            src: s,
            alias: i % 32,
            flag: 0,
            packet: &p,
        });
        assert_eq!(out, [Rec::Carrier(b, want)], "source {i}");
    }
    // the most recent 6 are known again
    fx.peer(
        T0,
        p1,
        &Frame::Forward {
            src: nid(69),
            dst: b,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Carrier(
            b,
            enc(&Frame::RecvAlias {
                alias: 5,
                flag: 0,
                packet: &p
            })
        )]
    );
}

#[test]
fn packets_for_the_relay_itself_are_local() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    fx.fx();
    let me = fx.me;
    fx.send(
        T0,
        a,
        sa,
        &Frame::Send {
            dst: me,
            flag: 0,
            packet: &[1, 2, 3],
        },
    )
    .unwrap();
    assert_eq!(fx.fx(), [Rec::Local(a, vec![1, 2, 3])]);
    fx.send(T0, a, sa, &Frame::SelfSend { packet: &[4, 5] }).unwrap();
    assert_eq!(fx.fx(), [Rec::Local(a, vec![4, 5])]);
    // the relay's own endpoint answers over SELFR
    fx.r.send_local(T0, &a, 0, &[9, 9], &mut fx.s).unwrap();
    assert_eq!(fx.fx(), [Rec::Carrier(a, enc(&Frame::SelfRecv { packet: &[9, 9] }))]);
    assert_eq!(fx.r.stats().local, 2);
}

#[test]
fn a_batch_is_routed_frame_by_frame() {
    let mut fx = Fx::new();
    let (a, b) = (nid(0xa1), nid(0xb2));
    let sa = fx.open(T0, a);
    fx.open(T0, b);
    fx.fx();
    let mut buf = vec![0u8; 20_000];
    let mut bb = vinc_connect::carrier::BatchBuilder::new(&mut buf);
    let p = [0x41u8; 30];
    for f in [
        Frame::Send {
            dst: b,
            flag: 0,
            packet: &p,
        },
        Frame::Recv {
            src: b,
            flag: 0,
            packet: &p,
        },
        Frame::Send {
            dst: b,
            flag: 1,
            packet: &p,
        },
    ] {
        bb.offer(&f).unwrap();
    }
    let bytes = bb.finish().unwrap().unwrap().to_vec();
    let frame = Frame::decode(&bytes).unwrap();
    // the middle frame is not valid from a client: it is refused, the others still go
    assert_eq!(fx.send(T0, a, sa, &frame), Err(Reject::UnexpectedFrame));
    assert_eq!(fx.fx().len(), 2);
}

#[test]
fn forwarding_to_the_home_relay_of_a_node_homed_elsewhere() {
    let mut fx = Fx::new();
    let (a, p1) = (nid(0xa1), nid(0x91));
    let x_kp = ed(0x71);
    let x = id(&x_kp);
    let sa = fx.open(T0, a);
    assert!(fx.r.add_peer(p1));
    fx.r.add_peer(p1);
    // a record for x says its home is p1 (replicated by p1 itself)
    let rec = record_bytes(&x_kp, p1, 1);
    fx.peer(T0, p1, &Frame::Sync { record: &rec }).unwrap();
    fx.fx();
    let p = [0x41u8; 64];
    fx.send(
        T0,
        a,
        sa,
        &Frame::Send {
            dst: x,
            flag: 3,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Peer(
            p1,
            enc(&Frame::Forward {
                src: a,
                dst: x,
                flag: 3,
                packet: &p
            })
        )]
    );
    assert_eq!(fx.r.stats().peer, 1);
    // no record at all
    assert_eq!(
        fx.send(
            T0,
            a,
            sa,
            &Frame::Send {
                dst: nid(0x55),
                flag: 0,
                packet: &p
            }
        ),
        Err(Reject::NoRoute)
    );
    // a home relay with no authenticated session
    fx.r.remove_peer(&p1);
    assert_eq!(
        fx.send(
            T0,
            a,
            sa,
            &Frame::Send {
                dst: x,
                flag: 3,
                packet: &p
            }
        ),
        Err(Reject::NoPeerSession)
    );
    // a record that says the node is homed here, but it holds no carrier
    let me = fx.me;
    let y_kp = ed(0x72);
    fx.r.add_peer(p1);
    let rec = record_bytes(&y_kp, me, 1);
    fx.peer(T0, p1, &Frame::Sync { record: &rec }).unwrap();
    assert_eq!(
        fx.send(
            T0,
            a,
            sa,
            &Frame::Send {
                dst: id(&y_kp),
                flag: 0,
                packet: &p
            }
        ),
        Err(Reject::NoRoute)
    );
}

#[test]
fn forwarding_and_replication_are_refused_from_unauthenticated_relays() {
    let mut fx = Fx::new();
    let (a, stranger, p1) = (nid(0xa1), nid(0x66), nid(0x91));
    fx.open(T0, a);
    fx.fx();
    let p = [0x41u8; 64];
    // a forward for a node that is right here is still refused
    let fwd = Frame::Forward {
        src: nid(0x77),
        dst: a,
        flag: 0,
        packet: &p,
    };
    assert_eq!(fx.peer(T0, stranger, &fwd), Err(Reject::Unauthenticated));
    assert!(fx.fx().is_empty(), "nothing is delivered");
    assert_eq!(
        traces_of(&fx)
            .iter()
            .filter(|t| matches!(t, Trace::Rejected { .. }))
            .count(),
        1
    );
    // replication from a stranger is refused and stores nothing, even for a well-signed record
    let kp = ed(0x71);
    let rec = record_bytes(&kp, p1, 1);
    assert_eq!(
        fx.peer(T0, stranger, &Frame::Sync { record: &rec }),
        Err(Reject::Unauthenticated)
    );
    assert_eq!(fx.r.record_count(), 0);
    // a client's own node id is not a relay either
    assert_eq!(fx.peer(T0, a, &fwd), Err(Reject::Unauthenticated));
    // once authenticated, the same frames are accepted
    fx.r.add_peer(p1);
    assert_eq!(fx.peer(T0, p1, &fwd), Ok(()));
    assert!(matches!(fx.fx()[..], [Rec::Carrier(n, _)] if n == a));
    fx.peer(T0, p1, &Frame::Sync { record: &rec }).unwrap();
    assert_eq!(fx.r.record_count(), 1);
    // and refused again when the session ends
    fx.r.remove_peer(&p1);
    assert_eq!(fx.peer(T0, p1, &fwd), Err(Reject::Unauthenticated));
    // relays do not exchange these
    fx.r.add_peer(p1);
    assert_eq!(
        fx.peer(T0, p1, &Frame::Publish { record: &rec }),
        Err(Reject::UnexpectedFrame)
    );
    assert_eq!(
        fx.peer(
            T0,
            p1,
            &Frame::Send {
                dst: a,
                flag: 0,
                packet: &p
            }
        ),
        Err(Reject::UnexpectedFrame)
    );
    // a peer session answers keepalives
    fx.fx();
    fx.peer(T0, p1, &Frame::Ping).unwrap();
    assert_eq!(fx.fx(), [Rec::Peer(p1, enc(&Frame::Pong))]);
}

#[test]
fn a_packet_forwarded_by_a_relay_is_never_forwarded_again() {
    let mut fx = Fx::new();
    let (p1, p2) = (nid(0x91), nid(0x92));
    fx.r.add_peer(p1);
    fx.r.add_peer(p2);
    let x_kp = ed(0x71);
    let rec = record_bytes(&x_kp, p2, 1);
    fx.peer(T0, p2, &Frame::Sync { record: &rec }).unwrap();
    fx.fx();
    // x is homed at p2, but this packet came from p1: it stops here
    let r = fx.peer(
        T0,
        p1,
        &Frame::Forward {
            src: nid(0x77),
            dst: id(&x_kp),
            flag: 0,
            packet: &[1, 2, 3],
        },
    );
    assert_eq!(r, Err(Reject::NoRoute));
    assert!(fx.fx().is_empty());
}

#[test]
fn replies_go_back_through_the_forwarding_relay_for_30_seconds() {
    let mut fx = Fx::new();
    let (a, p1) = (nid(0xa1), nid(0x91));
    let x = nid(0x77);
    let sa = fx.open(T0, a);
    fx.r.add_peer(p1);
    let p = [0x41u8; 10];
    // p1 forwards a packet of x (who is not on this relay) to a
    fx.peer(
        T0,
        p1,
        &Frame::Forward {
            src: x,
            dst: a,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    assert!(traces_of(&fx).contains(&Trace::FwdBackLearned { node: x, via: p1 }));
    fx.fx();
    assert_eq!(rule::FWD_BACK_NS, 30 * SEC);
    // x has no record here, yet a's reply is forwarded through p1
    let reply = Frame::Send {
        dst: x,
        flag: 1,
        packet: &p,
    };
    fx.send(T0 + 29_999_999_999, a, sa, &reply).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Peer(
            p1,
            enc(&Frame::Forward {
                src: a,
                dst: x,
                flag: 1,
                packet: &p
            })
        )]
    );
    // at 30 s it has gone
    assert_eq!(fx.send(T0 + 30 * SEC, a, sa, &reply), Err(Reject::NoRoute));
    // a fresh forward renews it
    fx.peer(
        T0 + 40 * SEC,
        p1,
        &Frame::Forward {
            src: x,
            dst: a,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    fx.fx();
    fx.send(T0 + 69 * SEC, a, sa, &reply).unwrap();
    assert_eq!(fx.fx().len(), 1);
}

#[test]
fn a_node_that_has_a_carrier_here_is_not_given_a_reply_route() {
    let mut fx = Fx::new();
    let (a, x, p1) = (nid(0xa1), nid(0x77), nid(0x91));
    fx.open(T0, a);
    fx.open(T0, x);
    fx.r.add_peer(p1);
    fx.fx();
    fx.peer(
        T0,
        p1,
        &Frame::Forward {
            src: x,
            dst: a,
            flag: 0,
            packet: &[1],
        },
    )
    .unwrap();
    assert!(!traces_of(&fx).iter().any(|t| matches!(t, Trace::FwdBackLearned { .. })));
}

#[test]
fn a_node_may_only_relay_its_quota_of_bytes_per_window() {
    let mut fx = Fx::with(|c| {
        c.quota = Quota {
            bytes: 1000,
            window_ns: 10 * SEC,
            session_ns: 1000 * SEC,
        }
    });
    let (a, b) = (nid(0xa1), nid(0xb2));
    let sa = fx.open(T0, a);
    fx.open(T0, b);
    fx.fx();
    let send = |fx: &mut Fx, at: u64, n: usize| {
        fx.send(
            at,
            a,
            sa,
            &Frame::Send {
                dst: b,
                flag: 0,
                packet: &vec![0x41; n],
            },
        )
    };
    send(&mut fx, T0, 600).unwrap();
    send(&mut fx, T0 + SEC, 400).unwrap();
    assert_eq!(send(&mut fx, T0 + 2 * SEC, 1), Err(Reject::Quota));
    assert!(traces_of(&fx).contains(&Trace::QuotaExceeded { node: a }));
    assert_eq!(fx.r.stats().quota_drops, 1);
    assert_eq!(fx.fx().len(), 2, "the dropped frame was not delivered");
    // another node is not affected
    let sb = SessionId(1);
    fx.send(
        T0 + 2 * SEC,
        b,
        sb,
        &Frame::Send {
            dst: a,
            flag: 0,
            packet: &[0x41; 900],
        },
    )
    .unwrap();
    // the window turns over after 10 s
    send(&mut fx, T0 + 10 * SEC, 1000).unwrap();
    assert_eq!(send(&mut fx, T0 + 11 * SEC, 1), Err(Reject::Quota));
}

#[test]
fn a_session_is_closed_at_the_time_limit() {
    let mut fx = Fx::with(|c| c.quota.session_ns = 100 * SEC);
    let (a, b) = (nid(0xa1), nid(0xb2));
    let sa = fx.open(T0, a);
    fx.open(T0 + 50 * SEC, b);
    fx.fx();
    fx.r.handle_timeout(T0 + 99 * SEC, &mut fx.s);
    assert!(fx.fx().is_empty());
    fx.r.handle_timeout(T0 + 100 * SEC, &mut fx.s);
    assert_eq!(fx.fx(), [Rec::Close(a, CloseReason::SessionTime)]);
    assert_eq!(
        fx.r.node_state(&a),
        NodeState::Gone {
            since: T0 + 100 * SEC,
            asleep: false
        }
    );
    assert_eq!(fx.r.node_state(&b), NodeState::Open);
    assert_eq!(fx.r.sessions(), 1);
    // calls about the expired session are ignored or refused
    assert_eq!(fx.send(T0 + 101 * SEC, a, sa, &Frame::Ping), Err(Reject::StaleSession));
    fx.r.carrier_closed(T0 + 101 * SEC, &a, sa, &mut fx.s);
    assert_eq!(
        fx.r.node_state(&a),
        NodeState::Gone {
            since: T0 + 100 * SEC,
            asleep: false
        }
    );
    // the node dials again
    fx.open(T0 + 102 * SEC, a);
    assert_eq!(fx.r.node_state(&a), NodeState::Open);
}

#[test]
fn a_newer_session_replaces_the_older_one() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let old = fx.open(T0, a);
    fx.fx();
    let new = fx.open(T0 + SEC, a);
    assert!(new > old);
    assert!(fx.s.0.contains(&Rec::Close(a, CloseReason::Replaced)));
    fx.r.carrier_closed(T0 + 2 * SEC, &a, old, &mut fx.s);
    assert_eq!(
        fx.r.node_state(&a),
        NodeState::Open,
        "the old carrier's close does not end the new session"
    );
    assert_eq!(fx.send(T0 + 2 * SEC, a, old, &Frame::Ping), Err(Reject::StaleSession));
    fx.send(T0 + 2 * SEC, a, new, &Frame::Ping).unwrap();
    assert_eq!(fx.r.sessions(), 1);
}

#[test]
fn the_session_table_is_bounded() {
    let mut fx = Fx::new();
    for i in 0..16u8 {
        fx.open(T0, nid(i));
    }
    assert_eq!(fx.r.carrier_opened(T0, nid(99), &mut fx.s), Err(Reject::SessionsFull));
    assert_eq!(fx.r.sessions(), 16);
    // a node that already has a session can replace it
    assert!(fx.r.carrier_opened(T0, nid(3), &mut fx.s).is_ok());
}

#[test]
fn keepalives_are_answered_and_frames_clients_may_not_send_are_refused() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    fx.fx();
    fx.send(T0, a, sa, &Frame::Ping).unwrap();
    assert_eq!(fx.fx(), [Rec::Carrier(a, enc(&Frame::Pong))]);
    assert!(traces_of(&fx).contains(&Trace::Pulse { node: a }));
    fx.send(T0, a, sa, &Frame::Pong).unwrap();
    for f in [
        Frame::Recv {
            src: nid(1),
            flag: 0,
            packet: &[1],
        },
        Frame::RecvAlias {
            alias: 0,
            flag: 0,
            packet: &[1],
        },
        Frame::SelfRecv { packet: &[1] },
        Frame::Forward {
            src: nid(1),
            dst: nid(2),
            flag: 0,
            packet: &[1],
        },
        Frame::Sync { record: &[1] },
        Frame::DnsReply {
            peer: nid(1),
            answer: DnsAnswer::Absent,
        },
    ] {
        assert_eq!(fx.send(T0, a, sa, &f), Err(Reject::UnexpectedFrame), "{f:?}");
    }
    assert!(fx.fx().is_empty());
}

#[test]
fn the_same_inputs_give_the_same_effects_and_trace() {
    fn run() -> Vec<Rec> {
        let mut fx = Fx::new();
        let (a, b, p1) = (nid(0xa1), nid(0xb2), nid(0x91));
        fx.r.add_peer(p1);
        let sa = fx.open(T0, a);
        let sb = fx.open(T0, b);
        let kp = ed(0x61);
        let rec = record_bytes(&kp, p1, 1);
        let _ = fx.peer(T0, p1, &Frame::Sync { record: &rec });
        for i in 0..40u8 {
            let _ = fx.send(
                T0 + u64::from(i) * SEC,
                a,
                sa,
                &Frame::Send {
                    dst: b,
                    flag: i,
                    packet: &[i; 50],
                },
            );
            let _ = fx.send(
                T0 + u64::from(i) * SEC,
                b,
                sb,
                &Frame::Send {
                    dst: id(&kp),
                    flag: i,
                    packet: &[i; 50],
                },
            );
            fx.r.handle_timeout(T0 + u64::from(i) * SEC, &mut fx.s);
        }
        fx.s.take()
    }
    let first = run();
    assert!(first.len() > 100);
    assert_eq!(first, run());
}
