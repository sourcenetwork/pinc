//! Messages the relay holds for a member are delivered when a packet is heard from the member and its route is ready.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::type_complexity,
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

use std::cell::Cell;

use connect_common::*;
use vinc_connect::carrier::Frame;
use vinc_connect::relay::datagram::{Datagram, MAX_TUNNEL_DATAGRAM};
use vinc_connect::relay::{Effect, Reject, SessionId, Sink, Trace, UdpTarget};
use vinc_crypto::NodeId;

/// A relay holding the given packets (flag 7), oldest first, from `a` for the sleeping `m`.
fn hold(fx: &mut Fx, packets: &[&[u8]]) -> (NodeId, SessionId, NodeId, Vec<u64>) {
    let a = nid(0xa1);
    let sa = fx.open(T0, a);
    let kp = ed(0x61);
    let m = id(&kp);
    let sm = fx.open(T0, m);
    let me = fx.me;
    fx.r.sleep_notice(T0, &notice(&kp, &me, T0 / 1_000_000), None, &mut fx.s)
        .unwrap();
    fx.r.carrier_closed(T0 + SEC, &m, sm, &mut fx.s);
    for packet in packets {
        fx.send(
            T0 + 2 * SEC,
            a,
            sa,
            &Frame::Send {
                dst: m,
                flag: 7,
                packet,
            },
        )
        .unwrap();
    }
    fx.fx();
    let seqs = stored(fx);
    fx.s.1.clear();
    (a, sa, m, seqs)
}

/// A relay holding `n` one-byte-numbered packets from `a` for the sleeping `m`.
fn hold_for_sleeper(fx: &mut Fx, n: u8) -> (NodeId, SessionId, NodeId, Vec<u64>) {
    let packets: Vec<[u8; 3]> = (0..n).map(|i| [i + 1, 2, 3]).collect();
    hold(fx, &packets.iter().map(<[u8; 3]>::as_slice).collect::<Vec<_>>())
}

fn stored(fx: &Fx) -> Vec<u64> {
    fx.s.1
        .iter()
        .filter_map(|t| match t {
            Trace::MailboxStored { seq, .. } => Some(*seq),
            _ => None,
        })
        .collect()
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

/// The tunnel datagram of the one-byte-numbered packet `i` from `a` to `m`.
fn spl(m: NodeId, a: NodeId, i: u8) -> Rec {
    Rec::Udp(
        UdpTarget::Member(m),
        dg(&Datagram::Spl {
            src: a,
            flag: 7,
            packet: &[i, 2, 3],
        }),
    )
}

fn spls(m: NodeId, a: NodeId, range: std::ops::RangeInclusive<u8>) -> Vec<Rec> {
    range.map(|i| spl(m, a, i)).collect()
}

fn send_to(fx: &mut Fx, at: u64, a: NodeId, sa: SessionId, m: NodeId, i: u8) -> Result<(), Reject> {
    fx.send(
        at,
        a,
        sa,
        &Frame::Send {
            dst: m,
            flag: 7,
            packet: &[i, 2, 3],
        },
    )
}

#[test]
fn a_member_back_on_an_unvalidated_route_gets_its_mail_when_it_validates() {
    let mut fx = Fx::new();
    let (a, _, m, seqs) = hold_for_sleeper(&mut fx, 3);
    fx.s.2.push(m);
    let rejected = fx.r.stats().rejected;
    fx.r.udp_heard(T0 + 3 * SEC, &m, &mut fx.s).unwrap();
    assert!(fx.fx().is_empty(), "a heard packet on an unready route sends nothing");
    assert_eq!(fx.r.stats().rejected, rejected, "and refuses nothing");
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    assert!(fx.fx().is_empty());
    assert_eq!(fx.r.stats().rejected, rejected + 1, "the return is refused once");
    assert_eq!(fx.r.mailbox_pending(&m).0, 3, "nothing was lost");
    assert_eq!(fx.r.mailbox_stats().delivered, 0);
    // the route validates: the next heard packet hands over all three, in order, with their sequence numbers
    fx.s.2.clear();
    fx.r.udp_heard(T0 + 4 * SEC, &m, &mut fx.s).unwrap();
    assert_eq!(fx.fx(), spls(m, a, 1..=3), "no carrier and no wake either");
    assert_eq!(delivered(&fx), seqs);
    assert_eq!(fx.r.mailbox_stats().delivered, 3);
    assert_eq!(fx.r.mailbox_pending(&m).0, 0);
    fx.r.udp_heard(T0 + 5 * SEC, &m, &mut fx.s).unwrap();
    assert!(fx.fx().is_empty(), "once");
}

#[test]
fn a_packet_for_a_member_holding_mail_is_forwarded_to_its_home_once_the_sleep_mark_is_gone() {
    let mut fx = Fx::new();
    let p1 = nid(0x91);
    let (a, sa, m, _) = hold_for_sleeper(&mut fx, 2);
    // 600 s on, the sweep drops the sleep mark; the mail is still held
    fx.r.handle_timeout(T0 + 700 * SEC, &mut fx.s);
    fx.r.add_peer(p1);
    let rec = record_bytes(&ed(0x61), p1, 1);
    fx.peer(T0 + 700 * SEC, p1, &Frame::Sync { record: &rec }).unwrap();
    fx.fx();
    send_to(&mut fx, T0 + 701 * SEC, a, sa, m, 9).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Peer(
            p1,
            enc(&Frame::Forward {
                src: a,
                dst: m,
                flag: 7,
                packet: &[9, 2, 3]
            })
        )]
    );
    assert_eq!(fx.r.mailbox_pending(&m).0, 2, "the held mail waits as before");
    assert_eq!(fx.r.mailbox_stats().delivered, 0);
}

#[test]
fn a_packet_goes_down_the_tunnel_of_a_member_whose_oldest_held_message_is_too_long_for_it() {
    let mut fx = Fx::new();
    let long = vec![9u8; MAX_TUNNEL_DATAGRAM - 34];
    let (a, sa, m, _) = hold(&mut fx, &[long.as_slice()]);
    fx.r.udp_heard(T0 + 3 * SEC, &m, &mut fx.s).unwrap();
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    fx.fx();
    send_to(&mut fx, T0 + 3 * SEC, a, sa, m, 4).unwrap();
    assert_eq!(
        fx.fx(),
        [spl(m, a, 4)],
        "the new packet is not held behind the long one"
    );
    assert_eq!(fx.r.mailbox_pending(&m).0, 1, "the long one waits for the carrier");
}

#[test]
fn a_member_whose_held_mail_has_all_expired_routes_like_one_holding_nothing() {
    let mut fx = Fx::with(|c| c.mailbox_max_age_ns = 10 * SEC);
    let p1 = nid(0x91);
    let (a, sa, m, _) = hold_for_sleeper(&mut fx, 2);
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    fx.r.add_peer(p1);
    let rec = record_bytes(&ed(0x61), p1, 1);
    fx.peer(T0 + 13 * SEC, p1, &Frame::Sync { record: &rec }).unwrap();
    fx.fx();
    assert_eq!(fx.r.mailbox_pending(&m).0, 2, "expired, not swept yet");
    send_to(&mut fx, T0 + 13 * SEC, a, sa, m, 9).unwrap();
    assert_eq!(
        fx.fx(),
        [Rec::Peer(
            p1,
            enc(&Frame::Forward {
                src: a,
                dst: m,
                flag: 7,
                packet: &[9, 2, 3]
            })
        )]
    );
}

/// A collector whose route stops being ready once it has taken `left` tunnel datagrams.
struct Flaky<'a> {
    inner: &'a mut Collect,
    left: Cell<usize>,
}

impl Sink for Flaky<'_> {
    fn tunnel_ready(&self, node: &NodeId) -> bool {
        self.inner.tunnel_ready(node) && self.left.get() > 0
    }

    fn emit(&mut self, e: Effect<'_>) {
        if matches!(e, Effect::Udp { .. }) {
            self.left.set(self.left.get().saturating_sub(1));
        }
        self.inner.emit(e);
    }
}

#[test]
fn a_pass_refused_midway_keeps_the_rest_in_order() {
    let mut fx = Fx::new();
    let (a, _, m, seqs) = hold_for_sleeper(&mut fx, 4);
    fx.r.member_returned(T0 + 3 * SEC, &m, &mut fx.s);
    let rejected = fx.r.stats().rejected;
    let mut flaky = Flaky {
        inner: &mut fx.s,
        left: Cell::new(2),
    };
    fx.r.udp_heard(T0 + 4 * SEC, &m, &mut flaky).unwrap();
    assert_eq!(fx.fx(), spls(m, a, 1..=2));
    assert_eq!(fx.r.stats().rejected, rejected + 1, "the refusal is counted once");
    assert!(fx.s.1.contains(&Trace::Rejected {
        reason: Reject::NoTunnel,
        node: Some(m),
    }));
    assert_eq!(
        fx.r.mailbox_pending(&m).0,
        2,
        "the refused one and the one behind it stay held"
    );
    assert_eq!(
        delivered(&fx),
        seqs[..2],
        "no delivery trace for a message not handed over"
    );
    fx.r.udp_heard(T0 + 5 * SEC, &m, &mut fx.s).unwrap();
    assert_eq!(fx.fx(), spls(m, a, 3..=4));
    assert_eq!(delivered(&fx), seqs, "each once, in order");
    assert_eq!(fx.r.mailbox_pending(&m).0, 0);
}

/// A collector that counts the readiness questions and the effects it is given.
#[derive(Default)]
struct Probe {
    asks: Cell<usize>,
    effects: usize,
}

impl Sink for Probe {
    fn tunnel_ready(&self, _: &NodeId) -> bool {
        self.asks.set(self.asks.get() + 1);
        true
    }

    fn emit(&mut self, _: Effect<'_>) {
        self.effects += 1;
    }
}

#[test]
fn hearing_a_member_with_nothing_held_costs_nothing() {
    let mut fx = Fx::new();
    let mut probe = Probe::default();
    let x = nid(0xe1);
    fx.r.udp_heard(T0, &x, &mut probe).unwrap();
    assert_eq!((probe.asks.get(), probe.effects), (0, 0), "no mail anywhere");
    // another member's mail is held: hearing `x` still asks and emits nothing
    let (_, _, m, _) = hold_for_sleeper(&mut fx, 2);
    assert_ne!(m, x);
    let mut probe = Probe::default();
    fx.r.udp_heard(T0 + 3 * SEC, &x, &mut probe).unwrap();
    assert_eq!((probe.asks.get(), probe.effects), (0, 0), "another member's mail");
}

#[test]
fn a_full_udp_table_is_refused_and_traced() {
    let mut fx = Fx::new();
    let mut full = None;
    for i in 0..=255u8 {
        let rejected = fx.r.stats().rejected;
        fx.s.1.clear();
        let r = fx.r.udp_heard(T0, &nid(i), &mut fx.s);
        if r.is_err() {
            full = Some((r, rejected));
            break;
        }
    }
    let (r, rejected) = full.expect("the table fills up");
    assert_eq!(r, Err(Reject::SessionsFull));
    assert_eq!(fx.r.stats().rejected, rejected + 1);
    assert!(matches!(
        fx.s.1.as_slice(),
        [Trace::Rejected {
            reason: Reject::SessionsFull,
            ..
        }]
    ));
}
