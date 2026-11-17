//! The hub tunnel, the signed sleep notice and the mailbox as the relay uses them.
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
use vinc_connect::carrier::Frame;
use vinc_connect::mailbox;
use vinc_connect::relay::datagram::{Datagram, MAX_TUNNEL_DATAGRAM};
use vinc_connect::relay::sleep;
use vinc_connect::relay::{NodeState, Reject, SessionId, Trace, UdpTarget, rule};
use vinc_crypto::NodeId;

#[test]
fn the_hub_tunnel_up_requires_an_authenticated_member_and_routes_like_a_carrier_packet() {
    let mut fx = Fx::new();
    let (m, a, p1) = (nid(0xe1), nid(0xa1), nid(0x91));
    let sa = fx.open(T0, a);
    let _ = sa;
    fx.fx();
    let p = [0x41u8; 100];
    let spu = dg(&Datagram::Spu {
        dst: a,
        flag: 4,
        packet: &p,
    });
    // no validated session: refused
    assert_eq!(
        fx.r.datagram(T0, addr(), None, &spu, &mut fx.s),
        Err(Reject::Unauthenticated)
    );
    assert!(fx.fx().is_empty());
    // delivered to a's carrier
    fx.r.datagram(T0, addr(), Some(&m), &spu, &mut fx.s).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Carrier(
            a,
            enc(&Frame::RecvNew {
                src: m,
                alias: 0,
                flag: 4,
                packet: &p
            })
        )]
    );
    // for the relay itself: dropped
    let to_me = dg(&Datagram::Spu {
        dst: fx.me,
        flag: 0,
        packet: &p,
    });
    assert_eq!(
        fx.r.datagram(T0, addr(), Some(&m), &to_me, &mut fx.s),
        Err(Reject::NoRoute)
    );
    // to a node on another relay: forwarded
    fx.r.add_peer(p1);
    let x_kp = ed(0x71);
    let rec = record_bytes(&x_kp, p1, 1);
    fx.peer(T0, p1, &Frame::Sync { record: &rec }).unwrap();
    fx.fx();
    let spu = dg(&Datagram::Spu {
        dst: id(&x_kp),
        flag: 4,
        packet: &p,
    });
    fx.r.datagram(T0, addr(), Some(&m), &spu, &mut fx.s).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Peer(
            p1,
            enc(&Frame::Forward {
                src: m,
                dst: id(&x_kp),
                flag: 4,
                packet: &p
            })
        )]
    );
}

#[test]
fn the_hub_tunnel_down_uses_a_udp_session_heard_within_20_seconds() {
    assert_eq!(rule::HUB_TUNNEL_FRESH_NS, 20 * SEC);
    let mut fx = Fx::new();
    let (a, member) = (nid(0xa1), nid(0xe1));
    let sa = fx.open(T0, a);
    fx.fx();
    let p = [0x41u8; 50];
    // the member has no carrier but a UDP session heard at T0
    fx.r.udp_heard(T0, &member, &mut fx.s).unwrap();
    let go = |fx: &mut Fx, at: u64| {
        fx.send(
            at,
            a,
            sa,
            &Frame::Send {
                dst: member,
                flag: 2,
                packet: &p,
            },
        )
    };
    go(&mut fx, T0 + 19_999_999_999).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Udp(
            UdpTarget::Member(member),
            dg(&Datagram::Spl {
                src: a,
                flag: 2,
                packet: &p
            })
        )]
    );
    // at 20 s the session is no longer fresh
    assert_eq!(go(&mut fx, T0 + 20 * SEC), Err(Reject::NoRoute));
    // a datagram from the member over its session makes it fresh again
    fx.r.datagram(
        T0 + 30 * SEC,
        addr(),
        Some(&member),
        &dg(&Datagram::Qad { nonce: [0; 8] }),
        &mut fx.s,
    )
    .unwrap();
    fx.fx();
    go(&mut fx, T0 + 31 * SEC).unwrap();
    assert!(matches!(fx.fx()[..], [Rec::Udp(UdpTarget::Member(m), _)] if m == member));
    // the datagram bound: header 35 bytes, 1424 in all
    let fits = vec![0x41u8; MAX_TUNNEL_DATAGRAM - 35];
    let over = vec![0x41u8; MAX_TUNNEL_DATAGRAM - 34];
    fx.send(
        T0 + 31 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: member,
            flag: 0,
            packet: &fits,
        },
    )
    .unwrap();
    assert_eq!(fx.fx().len(), 1);
    assert_eq!(
        fx.send(
            T0 + 31 * SEC,
            a,
            sa,
            &Frame::Send {
                dst: member,
                flag: 0,
                packet: &over
            }
        ),
        Err(Reject::NoRoute)
    );
    fx.r.udp_gone(&member);
    assert_eq!(go(&mut fx, T0 + 32 * SEC), Err(Reject::NoRoute));
}

#[test]
fn a_member_heard_by_udp_without_a_direct_route_is_not_tunnelled_and_goes_to_the_next_rule() {
    let mut fx = Fx::new();
    let (a, p1, member) = (nid(0xa1), nid(0x91), nid(0xe1));
    let sa = fx.open(T0, a);
    let p = [0x41u8; 50];
    let go = |fx: &mut Fx, at: u64| {
        fx.send(
            at,
            a,
            sa,
            &Frame::Send {
                dst: member,
                flag: 2,
                packet: &p,
            },
        )
    };
    // the member has a record at a peer relay and was heard by UDP, but the host has no direct route for it
    fx.r.add_peer(p1);
    let kp = ed(0x71);
    let member_id = id(&kp);
    let rec = record_bytes(&kp, p1, 1);
    fx.peer(T0, p1, &Frame::Sync { record: &rec }).unwrap();
    fx.r.udp_heard(T0, &member_id, &mut fx.s).unwrap();
    fx.fx();
    fx.s.2.push(member_id);
    fx.send(
        T0 + SEC,
        a,
        sa,
        &Frame::Send {
            dst: member_id,
            flag: 2,
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
                dst: member_id,
                flag: 2,
                packet: &p
            })
        )]
    );
    // the guard: with a direct route the same packet is tunnelled
    fx.s.2.clear();
    fx.send(
        T0 + 2 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: member_id,
            flag: 2,
            packet: &p,
        },
    )
    .unwrap();
    assert!(matches!(fx.fx()[..], [Rec::Udp(UdpTarget::Member(m), _)] if m == member_id));
    // a member with neither a record nor a route is a refusal that is counted, not a silent drop
    let before = fx.r.stats().rejected;
    assert_eq!(go(&mut fx, T0 + 3 * SEC), Err(Reject::NoRoute));
    assert_eq!(fx.r.stats().rejected, before + 1);
}

#[test]
fn a_sleeping_member_heard_by_udp_without_a_direct_route_gets_its_packet_in_the_mailbox() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    fx.r.udp_heard(T0 + 2 * SEC, &m, &mut fx.s).unwrap();
    fx.s.2.push(m);
    fx.fx();
    fx.send(
        T0 + 3 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 7,
            packet: &[1, 2, 3],
        },
    )
    .unwrap();
    assert!(!fx.fx().iter().any(|r| matches!(r, Rec::Udp(..))));
    assert_eq!(fx.r.mailbox_pending(&m).0, 1);
}

#[test]
fn a_member_carrier_silent_for_more_than_15_seconds_also_gets_the_tunnel_copy() {
    assert_eq!(rule::TUNNEL_STALE_NS, 15 * SEC);
    let mut fx = Fx::new();
    let (a, b) = (nid(0xa1), nid(0xb2));
    let sa = fx.open(T0, a);
    fx.open(T0, b);
    fx.r.udp_heard(T0 + 100 * SEC, &b, &mut fx.s).unwrap();
    fx.fx();
    let p = [0x41u8; 50];
    // b's carrier last spoke at T0; a sends at T0 + 15 s exactly: not stale yet
    fx.send(
        T0 + 15 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: b,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(fx.fx().len(), 1);
    // one nanosecond later it is stale: carrier and tunnel both
    fx.r.udp_heard(T0 + 15 * SEC + 1, &b, &mut fx.s).unwrap();
    fx.send(
        T0 + 15 * SEC + 1,
        a,
        sa,
        &Frame::Send {
            dst: b,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    let out = fx.fx();
    assert_eq!(out.len(), 2);
    assert!(matches!(out[0], Rec::Carrier(n, _) if n == b));
    assert!(matches!(out[1], Rec::Udp(UdpTarget::Member(n), _) if n == b));
    // a keepalive from b makes the carrier live again
    let sb = SessionId(1);
    fx.send(T0 + 16 * SEC, b, sb, &Frame::Ping).unwrap();
    fx.fx();
    fx.send(
        T0 + 17 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: b,
            flag: 0,
            packet: &p,
        },
    )
    .unwrap();
    assert_eq!(fx.fx().len(), 1);
}

#[test]
fn a_signed_sleep_notice_makes_the_following_close_a_suspension() {
    let mut fx = Fx::new();
    let kp = ed(0x61);
    let n = id(&kp);
    let s = fx.open(T0, n);
    let me = fx.me;
    let now_ms = T0 / 1_000_000;
    let dgram = dg(&Datagram::Sleep {
        notice: &notice(&kp, &me, now_ms),
    });
    // sent twice over UDP, as the sending node does
    fx.r.datagram(T0, addr(), None, &dgram, &mut fx.s).unwrap();
    fx.r.datagram(T0, addr(), None, &dgram, &mut fx.s).unwrap();
    assert_eq!(
        traces_of(&fx)
            .iter()
            .filter(|t| matches!(t, Trace::SleepAccepted { .. }))
            .count(),
        2
    );
    assert_eq!(fx.r.node_state(&n), NodeState::Open);
    fx.r.carrier_closed(T0 + 2 * SEC, &n, s, &mut fx.s);
    assert_eq!(
        fx.r.node_state(&n),
        NodeState::Gone {
            since: T0 + 2 * SEC,
            asleep: true
        }
    );
    assert!(traces_of(&fx).contains(&Trace::CarrierClosed { node: n, asleep: true }));
    // the same close without a notice is a crash
    let kp2 = ed(0x62);
    let n2 = id(&kp2);
    let s2 = fx.open(T0, n2);
    fx.r.carrier_closed(T0 + 2 * SEC, &n2, s2, &mut fx.s);
    assert_eq!(
        fx.r.node_state(&n2),
        NodeState::Gone {
            since: T0 + 2 * SEC,
            asleep: false
        }
    );
    // a close more than 10 s after the notice is a crash too
    let kp3 = ed(0x63);
    let n3 = id(&kp3);
    let s3 = fx.open(T0, n3);
    fx.r.sleep_notice(T0, &notice(&kp3, &me, now_ms), None, &mut fx.s)
        .unwrap();
    assert_eq!(rule::SLEEP_WIN_NS, 10 * SEC);
    fx.r.carrier_closed(T0 + 10 * SEC, &n3, s3, &mut fx.s);
    assert_eq!(
        fx.r.node_state(&n3),
        NodeState::Gone {
            since: T0 + 10 * SEC,
            asleep: true
        }
    );
    let s3 = fx.open(T0 + 11 * SEC, n3);
    fx.r.sleep_notice(
        T0 + 11 * SEC,
        &notice(&kp3, &me, (T0 + 11 * SEC) / 1_000_000),
        Some(&n3),
        &mut fx.s,
    )
    .unwrap();
    fx.r.carrier_closed(T0 + 21 * SEC + 1, &n3, s3, &mut fx.s);
    assert_eq!(
        fx.r.node_state(&n3),
        NodeState::Gone {
            since: T0 + 21 * SEC + 1,
            asleep: false
        }
    );
    // opening the carrier again clears it
    fx.open(T0 + 30 * SEC, n);
    assert_eq!(fx.r.node_state(&n), NodeState::Open);
}

#[test]
fn a_sleep_notice_is_refused_unless_fresh_known_signed_for_this_relay_and_from_its_sender() {
    let mut fx = Fx::new();
    let kp = ed(0x61);
    let n = id(&kp);
    let s = fx.open(T0, n);
    let me = fx.me;
    let ms = T0 / 1_000_000;
    let try_ts = |fx: &mut Fx, ts: u64| fx.r.sleep_notice(T0, &notice(&kp, &me, ts), None, &mut fx.s);
    // the clock window is 10 s either way
    assert!(try_ts(&mut fx, ms + 9_999).is_ok());
    assert!(try_ts(&mut fx, ms - 9_999).is_ok());
    assert!(matches!(
        try_ts(&mut fx, ms + 10_000),
        Err(Reject::BadSleep(sleep::SleepError::Skew))
    ));
    assert!(matches!(
        try_ts(&mut fx, ms - 10_000),
        Err(Reject::BadSleep(sleep::SleepError::Skew))
    ));
    // a node this relay never saw
    let stranger = ed(0x6f);
    assert!(matches!(
        fx.r.sleep_notice(T0, &notice(&stranger, &me, ms), None, &mut fx.s),
        Err(Reject::BadSleep(sleep::SleepError::UnknownNode))
    ));
    // signed for another relay
    assert!(matches!(
        fx.r.sleep_notice(T0, &notice(&kp, &nid(0x50), ms), None, &mut fx.s),
        Err(Reject::BadSleep(sleep::SleepError::Signature(_)))
    ));
    // altered
    let good = notice(&kp, &me, ms);
    for i in 0..good.len() {
        let mut bad = good.clone();
        bad[i] ^= 1;
        assert!(fx.r.sleep_notice(T0, &bad, None, &mut fx.s).is_err(), "flip at {i}");
    }
    // on a carrier, only the node's own notice counts
    let other = fx.open(T0, nid(0xaa));
    assert!(matches!(
        fx.r.carrier_frame(T0, &nid(0xaa), other, &Frame::Sleep { notice: &good }, &mut fx.s),
        Err(Reject::BadSleep(sleep::SleepError::WrongSender))
    ));
    fx.send(T0, n, s, &Frame::Sleep { notice: &good }).unwrap();
    // a node that just lost its carrier is still known
    fx.r.carrier_closed(T0, &n, s, &mut fx.s);
    assert!(fx.r.sleep_notice(T0, &good, None, &mut fx.s).is_ok());
}

#[test]
fn packets_for_a_sleeping_member_are_held_and_delivered_once_when_it_returns() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    fx.fx();
    let packets: Vec<Vec<u8>> = (0..3u8).map(|i| vec![0x40 + i; 100]).collect();
    for (i, p) in packets.iter().enumerate() {
        fx.send(
            T0 + 2 * SEC,
            a,
            sa,
            &Frame::Send {
                dst: m,
                flag: i as u8,
                packet: p,
            },
        )
        .unwrap();
    }
    // one wake-up trigger for the three packets
    let out = fx.fx();
    assert_eq!(out, [Rec::Wake(m)]);
    assert_eq!(fx.r.mailbox_pending(&m).0, 3);
    assert_eq!(fx.r.stats().mailboxed, 3);
    // 30 s after the first trigger another packet triggers again; 29 s after it does not
    assert_eq!(rule::WAKE_REARM_NS, 30 * SEC);
    fx.send(
        T0 + 31 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 3,
            packet: &[0x43; 100],
        },
    )
    .unwrap();
    assert!(fx.fx().is_empty());
    fx.send(
        T0 + 32 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 4,
            packet: &[0x44; 100],
        },
    )
    .unwrap();
    assert_eq!(fx.fx(), [Rec::Wake(m)]);
    // the member returns: everything arrives in order, once
    let sm2 = fx.open(T0 + 40 * SEC, m);
    let out = fx.fx();
    assert_eq!(out.len(), 5);
    let sent: Vec<(u8, Vec<u8>)> = out
        .iter()
        .map(|r| {
            let Rec::Carrier(to, bytes) = r else { panic!("{r:?}") };
            assert_eq!(*to, m);
            match Frame::decode(bytes).unwrap() {
                Frame::RecvNew { src, flag, packet, .. } => {
                    assert_eq!(src, a);
                    (flag, packet.to_vec())
                }
                Frame::RecvAlias { flag, packet, .. } => (flag, packet.to_vec()),
                f => panic!("{f:?}"),
            }
        })
        .collect();
    assert_eq!(sent.iter().map(|(f, _)| *f).collect::<Vec<_>>(), [0, 1, 2, 3, 4]);
    assert_eq!(fx.r.mailbox_pending(&m), (0, 0));
    assert_eq!(fx.r.mailbox_stats().delivered, 5);
    // a second return finds nothing: at most once
    fx.r.carrier_closed(T0 + 41 * SEC, &m, sm2, &mut fx.s);
    fx.fx();
    fx.open(T0 + 42 * SEC, m);
    assert!(fx.fx().is_empty());
    // and the mailbox is not used for a node that did not announce sleep
    let strange = nid(0x66);
    assert_eq!(
        fx.send(
            T0 + 43 * SEC,
            a,
            sa,
            &Frame::Send {
                dst: strange,
                flag: 0,
                packet: &[1]
            }
        ),
        Err(Reject::NoRoute)
    );
}

#[test]
fn a_member_that_wakes_over_udp_gets_its_mailbox_down_the_udp_session() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    fx.send(
        T0 + 2 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 7,
            packet: &[1, 2, 3],
        },
    )
    .unwrap();
    fx.fx();
    // no UDP session yet: nothing to deliver to
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    assert!(fx.fx().is_empty());
    assert_eq!(fx.r.mailbox_pending(&m).0, 1, "still held");
    // its UDP session is heard: the packet goes down it, once
    fx.r.udp_heard(T0 + 4 * SEC, &m, &mut fx.s).unwrap();
    fx.r.member_returned(T0 + 4 * SEC, &m, &mut fx.s);
    assert_eq!(
        fx.fx(),
        [Rec::Udp(
            UdpTarget::Member(m),
            dg(&Datagram::Spl {
                src: a,
                flag: 7,
                packet: &[1, 2, 3]
            })
        )]
    );
    fx.r.member_returned(T0 + 5 * SEC, &m, &mut fx.s);
    assert!(fx.fx().is_empty());
    assert_eq!(fx.r.mailbox_pending(&m).0, 0);
}

#[test]
fn the_mailbox_is_bounded_and_drops_oldest_first_with_counters() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0, &m, sm, &mut fx.s);
    // 4096 bytes per member, 52-byte headers: 700-byte packets, 5 fit
    let per = 700 + mailbox::ENTRY_HEAD;
    let fit = 4096 / per;
    assert_eq!(fit, 5);
    for i in 0..8u8 {
        fx.send(
            T0,
            a,
            sa,
            &Frame::Send {
                dst: m,
                flag: i,
                packet: &[i; 700],
            },
        )
        .unwrap();
    }
    let (count, bytes) = fx.r.mailbox_pending(&m);
    assert_eq!(count, fit);
    assert!(bytes <= 4096);
    let st = fx.r.mailbox_stats();
    assert_eq!((st.stored, st.dropped_oldest), (8, 3));
    assert_eq!(st.dropped_oldest_bytes, 3 * per as u64);
    fx.fx();
    fx.open(T0 + SEC, m);
    let flags: Vec<u8> = fx
        .fx()
        .iter()
        .map(|r| {
            let Rec::Carrier(_, b) = r else { panic!() };
            match Frame::decode(b).unwrap() {
                Frame::RecvNew { flag, .. } | Frame::RecvAlias { flag, .. } => flag,
                f => panic!("{f:?}"),
            }
        })
        .collect();
    assert_eq!(flags, [3, 4, 5, 6, 7], "the three oldest were dropped");
}

#[test]
fn held_packets_expire_after_the_maximum_age() {
    let mut fx = Fx::with(|c| c.mailbox_max_age_ns = 100 * SEC);
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0, &m, sm, &mut fx.s);
    fx.send(
        T0,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 1,
            packet: &[1; 10],
        },
    )
    .unwrap();
    fx.send(
        T0 + 60 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 2,
            packet: &[2; 10],
        },
    )
    .unwrap();
    fx.fx();
    // at T0 + 100 s the first is exactly at the limit and gone, the second is 40 s old
    fx.open(T0 + 100 * SEC, m);
    let out = fx.fx();
    assert_eq!(out.len(), 1);
    assert_eq!(fx.r.mailbox_stats().expired, 1);
    assert_eq!(fx.r.mailbox_stats().delivered, 1);
}

#[test]
fn a_held_packet_too_long_for_a_datagram_stays_held_until_the_carrier_reopens() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    let long = vec![9u8; MAX_TUNNEL_DATAGRAM - 34];
    fx.send(
        T0 + 2 * SEC,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 1,
            packet: &long,
        },
    )
    .unwrap();
    fx.fx();
    // the member wakes over UDP: the packet cannot go down a datagram, so it stays held (it was dropped before)
    fx.r.udp_heard(T0 + 3 * SEC, &m, &mut fx.s).unwrap();
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    assert!(fx.fx().is_empty());
    assert_eq!(fx.r.mailbox_pending(&m).0, 1, "still held");
    assert_eq!(fx.r.mailbox_stats().delivered, 0);
    // its carrier reopens: the packet is delivered there, once
    fx.open(T0 + 4 * SEC, m);
    let out = fx.fx();
    assert!(
        out.iter().any(|r| matches!(r, Rec::Carrier(n, _) if *n == m)),
        "{out:?}"
    );
    assert_eq!(fx.r.mailbox_pending(&m).0, 0);
    assert_eq!(fx.r.mailbox_stats().delivered, 1);
}

/// A relay holding `n` one-byte-numbered packets from `a` for the sleeping `m`.
fn hold_for_sleeper(fx: &mut Fx, n: u8) -> (NodeId, NodeId, Vec<u64>) {
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    for i in 0..n {
        fx.send(
            T0 + 2 * SEC,
            a,
            sa,
            &Frame::Send {
                dst: m,
                flag: 7,
                packet: &[i + 1, 2, 3],
            },
        )
        .unwrap();
    }
    fx.fx();
    let seqs =
        fx.s.1
            .iter()
            .filter_map(|t| match t {
                Trace::MailboxStored { seq, .. } => Some(*seq),
                _ => None,
            })
            .collect();
    fx.s.1.clear();
    (a, m, seqs)
}

fn delivered(fx: &Fx) -> Vec<u64> {
    fx.s.1
        .iter()
        .filter_map(|t| match t {
            Trace::MailboxDelivered { seq, .. } => Some(*seq),
            _ => None,
        })
        .collect()
}

#[test]
fn held_messages_stay_held_while_the_tunnel_is_not_ready_and_arrive_in_order_once_it_is() {
    let mut fx = Fx::new();
    let (a, m, seqs) = hold_for_sleeper(&mut fx, 3);
    assert_eq!(seqs.len(), 3);
    // its UDP session is fresh but it has no validated direct route: the tunnel refuses
    fx.r.udp_heard(T0 + 3 * SEC, &m, &mut fx.s).unwrap();
    fx.s.2.push(m);
    let rejected = fx.r.stats().rejected;
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    assert!(fx.fx().iter().all(|r| !matches!(r, Rec::Udp(..))));
    assert_eq!(fx.r.mailbox_pending(&m).0, 3, "nothing was lost");
    assert_eq!(fx.r.stats().rejected, rejected + 1, "the refused pass is counted once");
    assert_eq!(fx.r.mailbox_stats().delivered, 0);
    assert!(
        delivered(&fx).is_empty(),
        "no delivery trace for a message not handed over"
    );
    // the route is validated: all three go down in order, once, with their sequence numbers
    fx.s.2.clear();
    fx.r.member_returned(T0 + 4 * SEC, &m, &mut fx.s);
    let want: Vec<Rec> = (1..=3u8)
        .map(|i| {
            Rec::Udp(
                UdpTarget::Member(m),
                dg(&Datagram::Spl {
                    src: a,
                    flag: 7,
                    packet: &[i, 2, 3],
                }),
            )
        })
        .collect();
    let got: Vec<Rec> = fx.fx().into_iter().filter(|r| matches!(r, Rec::Udp(..))).collect();
    assert_eq!(got, want);
    assert_eq!(delivered(&fx), seqs);
    assert_eq!(fx.r.mailbox_pending(&m).0, 0);
    fx.r.member_returned(T0 + 5 * SEC, &m, &mut fx.s);
    assert!(fx.fx().iter().all(|r| !matches!(r, Rec::Udp(..))), "once");
}

#[test]
fn a_long_packet_in_front_holds_back_the_shorter_ones_behind_it_and_one_behind_stays_held() {
    let mut fx = Fx::new();
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    let long = vec![9u8; MAX_TUNNEL_DATAGRAM - 34];
    for (flag, packet) in [(1u8, &[1u8, 2][..]), (2, &long[..]), (3, &[3u8][..])] {
        fx.send(T0 + 2 * SEC, a, sa, &Frame::Send { dst: m, flag, packet })
            .unwrap();
    }
    fx.fx();
    fx.r.udp_heard(T0 + 3 * SEC, &m, &mut fx.s).unwrap();
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    let got: Vec<Rec> = fx.fx().into_iter().filter(|r| matches!(r, Rec::Udp(..))).collect();
    assert_eq!(got.len(), 1, "only the short one in front goes: {got:?}");
    assert_eq!(
        fx.r.mailbox_pending(&m).0,
        2,
        "the long one and the one behind it stay held"
    );
}

#[test]
fn the_relay_pings_every_client_carrier_every_600_seconds() {
    assert_eq!(rule::CLIENT_PING_NS, 600 * SEC);
    let mut fx = Fx::new();
    let (a, b) = (nid(0xa1), nid(0xa2));
    fx.open(T0, a);
    fx.open(T0, b);
    fx.fx();
    let ping = enc(&Frame::Ping);
    let pings = |fx: &mut Fx, at: u64| {
        fx.r.handle_timeout(at, &mut fx.s);
        let mut to: Vec<vinc_crypto::NodeId> = fx
            .fx()
            .into_iter()
            .filter_map(|r| match r {
                Rec::Carrier(n, bytes) if bytes == ping => Some(n),
                _ => None,
            })
            .collect();
        to.sort_by_key(|n| n.bytes);
        to
    };
    assert_eq!(pings(&mut fx, T0), [a, b], "the first timer pings every client");
    assert!(pings(&mut fx, T0 + 599 * SEC).is_empty());
    assert_eq!(pings(&mut fx, T0 + 600 * SEC), [a, b]);
    assert!(pings(&mut fx, T0 + 601 * SEC).is_empty());
    assert!(fx.r.next_deadline().is_some_and(|d| d <= T0 + 1200 * SEC));
}
