//! Reproducers of the bugs the properties of `connect_link.rs`, `connect_net.rs`, `connect_carrier.rs` and
//! `connect_sleep.rs` found on the client side of `pinc-connect` and in the relay role. Each test fails on the
//! unmodified code and passes once the bug is fixed; its doc comment says what is expected and why.

use std::net::{Ipv4Addr, SocketAddr};

use pinc_connect::carrier::Frame;
use pinc_connect::client::dial::{Cand, RelayView, Try, select};
use pinc_connect::client::link::{Act, Ctx, Link, Shared, rule};
use pinc_connect::client::netcheck::{MISS_LIMIT, Netcheck, Observed, classify};
use pinc_connect::record::Reach;
use pinc_connect::relay::{Config, Effect, NodeState, Relay, SessionId, Sink, Trace, sleep};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_000 * SEC;

fn home() -> Ctx {
    Ctx {
        home: true,
        rtt: 0,
        udp_any: false,
        rides: false,
        queued: false,
    }
}

/// Expected: the deadline a link reports is an instant `tick` acts at. `client::link` (module doc): "every deadline
/// returned by [`Link::next_deadline`] is the first instant [`Link::tick`] can act".
///
/// Actual: the home carrier of a node that just restarted reports a deadline of 0 (already due) before its first
/// tick, and that tick does nothing: it only starts the 600 ms restart defer. A host that sleeps until the deadline
/// wakes at once for nothing (one spurious wake per restart, nothing lost).
///
/// Suspected fault: `crates/pinc-connect/src/client/link.rs:413` (`next_deadline`, `State::Down`) returns `self.at`
/// while the defer that `want_dial` (`link.rs:243`) would start is not yet known; it could report
/// `max(at, now + DEFER)` when `restarted` and `defer_until` is unset.
///
/// Who can trigger it: the local application, by starting a node with `restarted` set (every restart).
#[test]
fn a_restarted_home_carrier_reports_a_due_deadline_its_tick_does_not_act_on() {
    let mut link = Link::new();
    let mut sh = Shared {
        restarted: true,
        ..Shared::default()
    };
    let ctx = home();
    let d = link
        .next_deadline(T0, &sh, &ctx)
        .expect("the home carrier has a deadline");
    let act = link.tick(T0.max(d), &mut sh, &ctx);
    assert!(
        act.is_some(),
        "the deadline {d} is due at {T0} and tick does nothing there"
    );
}

/// Expected: as above, "every deadline returned by [`Link::next_deadline`] is the first instant [`Link::tick`] can
/// act"; the keepalive rule: "A silent open carrier is checked after 30 s on a phone or within 10 minutes of a
/// carrier dying silently, and after 65 s otherwise."
///
/// Actual: a carrier that opens 570 s after another died silently reports its check 30 s after it last heard, which is
/// exactly when the 10 minutes run out; `tick` there does nothing (the wait is 65 s by then) and the next deadline is
/// 35 s later. One spurious wake per such carrier; the check itself is not missed.
///
/// Suspected fault: `crates/pinc-connect/src/client/link.rs:427` evaluates `keep_after` at `now` rather than at the
/// instant it reports, while `tick_open` (`link.rs:402`) evaluates it at the tick's own `now`.
///
/// Who can trigger it: the network, by killing a carrier silently (a NAT that drops the mapping) and the carrier
/// reopening about 570 s later.
#[test]
fn a_keepalive_deadline_at_the_end_of_the_short_check_memory_is_not_acted_on() {
    let mut link = Link::new();
    let mut sh = Shared::default();
    let ctx = home();
    assert_eq!(link.want_dial(T0, &mut sh, &ctx), Some(Act::Dial));
    link.opened(T0);
    // silent for 65 s: the check; unanswered for 3 s: the carrier is reset and the death remembered
    let t = T0 + rule::RELAY_KEEP;
    assert_eq!(link.tick(t, &mut sh, &ctx), Some(Act::Check));
    assert_eq!(link.check(t, &ctx, false), Some(Act::Ping));
    let dead = t + rule::CHECK_MIN;
    assert_eq!(link.tick(dead, &mut sh, &ctx), Some(Act::Close));
    assert_eq!(sh.keep_fail, Some(dead));
    // reopened 570 s later
    let reopened = dead + 570 * SEC;
    assert_eq!(link.tick(reopened, &mut sh, &ctx), Some(Act::Dial));
    link.opened(reopened);
    let d = link
        .next_deadline(reopened, &sh, &ctx)
        .expect("the home carrier is checked");
    assert_eq!(
        d,
        dead + rule::KEEP_MEMORY,
        "the check is reported for the instant the memory ends"
    );
    assert!(
        link.tick(d, &mut sh, &ctx).is_some(),
        "tick does nothing at the deadline {d} it was given"
    );
}

/// Expected: a node's class does not depend on whether an IPv4 address reached it in its IPv4-mapped IPv6 form.
/// `client::netcheck`: "Public: a reflexive address equals a local address (IPv4 or IPv6)", "Carrier-grade NAT: a
/// reflexive IPv4 address in the shared range 100.64.0.0/10, or two relays saw different addresses", and the
/// endpoint host of an ordinary node already says "a mapped IPv4 address on a dual-stack socket is IPv4"
/// (`crates/pinc/src/drive.rs:166`, `canon`); `mapped_seen`, the rule `classify` shares with the published
/// addresses, compares the canonical forms.
///
/// Actual: a public node whose relay reports `[::ffff:198.51.100.7]:4000` while the node's own address is
/// `198.51.100.7:4000` is classed `Nat`; two relays that report the same address, one in each form, make it `Cgnat`
/// (a symmetric mapping, which stops hole punching from being predicted); `[::ffff:100.64.0.1]` is not seen as the
/// shared range. A relay reports the form its socket gives: the relay host (`crates/pinc/src/relay/run.rs:121`,
/// `part.datagram(.., from, ..)`) passes the raw source of the host's socket, where the endpoint of an ordinary node
/// canonicalizes it first (`drive.rs:483`), so a node deployed from the relay binary on a dual-stack socket
/// (`relay [::]:4433 ..`, the default on Linux) reports mapped forms, and a mixed network of both shapes gives two
/// forms of one address.
///
/// Suspected fault: `crates/pinc-connect/src/client/netcheck.rs:85` (`o.local.contains(r)`), `:91` (`is_shared` and
/// `r != first` on raw forms); or the relay side, which could canonicalize the source before it answers.
///
/// Who can trigger it: an operator, by running a node from the relay binary on a dual-stack address; then every node
/// of that network that is public, or behind a NAT and served by two relays of different shapes, is misclassed.
#[test]
fn an_ipv4_address_in_its_mapped_form_changes_the_class() {
    let v4 = |a, b, c, d| SocketAddr::from((Ipv4Addr::new(a, b, c, d), 4000));
    let mapped = |a, b, c, d| SocketAddr::new(Ipv4Addr::new(a, b, c, d).to_ipv6_mapped().into(), 4000);
    let class = |local: &[SocketAddr], reflexive: &[SocketAddr]| {
        classify(&Observed {
            local,
            reflexive,
            mapped: &[],
            udp_heard: true,
            since_probe: 0,
            watchdog: 8 * SEC,
        })
    };
    assert_eq!(
        class(&[v4(198, 51, 100, 7)], &[mapped(198, 51, 100, 7)]),
        Some(Reach::Public),
        "the relay saw the node at its own address"
    );
    assert_eq!(
        class(&[v4(192, 168, 1, 2)], &[v4(203, 0, 113, 9), mapped(203, 0, 113, 9)]),
        Some(Reach::Nat),
        "two relays saw the same address"
    );
}

/// Expected: `client::dial` (module doc): "Invariants: [`select`] returns a non-empty subset of the candidates
/// whenever there are candidates, in candidate order."
///
/// Actual: under THIN_HS0 (a hub-session Initial resent within 4 s of the dial on a node that heard nothing yet) a
/// try whose candidates are all UDP addresses selects none, and `reselect` (`client/flight.rs:357`) then sends the
/// resend on no path at all, with `skip_primary` set: until 4 s after the dial the Initial is not resent anywhere. The
/// same holds for a flight whose only candidate is a relay under RLY_ONCE.
///
/// Suspected fault: `crates/pinc-connect/src/client/dial.rs:155` drops every UDP candidate when `hs0 && dialer`
/// without checking that a relay candidate is left (THIN_HS0 is meant to move the resend to the relay paths, not to
/// drop it); the RLY_ONCE drop at `dial.rs:156` has the same gap.
///
/// Who can trigger it: the local application, dialing a hub whose only candidate path is its UDP address (a hub not
/// reachable through any relay carrier) before anything was heard.
#[test]
fn a_thin_hs0_resend_with_only_udp_candidates_goes_nowhere() {
    let cands = [Cand::Udp(SocketAddr::from((Ipv4Addr::new(198, 51, 100, 7), 4001)))];
    let t = Try {
        now: T0,
        dialer: true,
        tries: 2,
        link_rtt: 0,
        no_rtt: true,
        hs0: true,
        last_relay: None,
    };
    let mut out = [Cand::Relay(0); 16];
    let (n, _) = select(&cands, &t, |_| None::<RelayView>, &mut out);
    assert!(n > 0, "a try with a candidate was sent on no path");
}

/// Expected: `client::netcheck`, `Netcheck::failover`: "Move the home away from an unhealthy relay, only to one known
/// to work: a probe answered since it last failed (lowest round trip first), else an `open` carrier (next by table
/// position) ... With no such relay the home stays."
///
/// Actual: a relay whose probe was answered, which then failed three times and whose carrier later opened once
/// (`healthy`, now closed again) is taken as "a probe answered since it last failed": the home moves to it although
/// no probe answered after the failures and no carrier to it is open. Its reflexive address and round trip are the
/// ones measured before it failed.
///
/// Suspected fault: `crates/pinc-connect/src/client/netcheck.rs:229` reads "answered since it last failed" as
/// `missed == 0` plus a reflexive address held, and `healthy` (`netcheck.rs:208`) also sets `missed` to 0 without an
/// answer; a flag set by `answered` and cleared by `failed` would follow the doc.
///
/// Who can trigger it: the network, by dropping a relay's probes and later letting one carrier to it open and close.
#[test]
fn failover_moves_home_to_a_relay_that_failed_since_its_last_answer() {
    let addr = SocketAddr::from((Ipv4Addr::new(203, 0, 113, 9), 5000));
    let mut n: Netcheck<3> = Netcheck::new();
    n.probe_sent(T0, 0, [1; 8], true);
    n.probe_sent(T0, 1, [2; 8], true);
    assert!(n.answered(T0 + 1_000_000, 0, [1; 8], addr).is_some());
    assert!(n.answered(T0 + 9_000_000, 1, [2; 8], addr).is_some());
    assert_eq!(n.home(), Some(0), "the lowest round trip is home");
    for _ in 0..MISS_LIMIT {
        n.failed(1);
    }
    // a carrier to relay 1 opened (and closed again: nothing is reported for a close)
    n.healthy(1);
    for _ in 0..MISS_LIMIT {
        n.failed(0);
    }
    assert!(n.unhealthy(0));
    assert_eq!(
        n.failover(|i| i == 1, |_| false),
        None,
        "no relay is known to work, so the home stays"
    );
}

// ---- the relay role: sleep notices (`connect_sleep.rs`) ----

const MS: u64 = 1_000_000;
/// A wall clock in nanoseconds, as a relay's notice check reads it.
const WALL: u64 = 1_700_000_000 * SEC;

type R = Relay<8, 8, 8, 16_384>;

fn keypair(seed: u8) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[seed; 32]).expect("a seed makes a key")
}

#[derive(Default)]
struct Seen {
    held_for: Vec<NodeId>,
    woken: Vec<NodeId>,
    closes: Vec<(NodeId, bool)>,
}

impl Sink for Seen {
    fn emit(&mut self, e: Effect<'_>) {
        match e {
            Effect::Wake { node } => self.woken.push(node),
            Effect::Trace(Trace::MailboxStored { node, .. }) => self.held_for.push(node),
            Effect::Trace(Trace::CarrierClosed { node, asleep }) => self.closes.push((node, asleep)),
            _ => {}
        }
    }
}

/// A relay, the member `sleeper` with a carrier, and another member `other` with one.
struct Fx {
    me: Keypair,
    relay: Box<R>,
    sleeper: Keypair,
    sid: SessionId,
    other: NodeId,
    other_sid: SessionId,
    seen: Seen,
}

fn fx() -> Fx {
    let me = keypair(10);
    let sleeper = keypair(1);
    let other = keypair(20).node_id();
    let mut relay: Box<R> = Box::new(Relay::new(Config::new(me.node_id(), 7)));
    let mut seen = Seen::default();
    let sid = relay
        .carrier_opened(WALL, sleeper.node_id(), &mut seen)
        .expect("a carrier opens");
    let other_sid = relay.carrier_opened(WALL, other, &mut seen).expect("a carrier opens");
    Fx {
        me,
        relay,
        sleeper,
        sid,
        other,
        other_sid,
        seen,
    }
}

impl Fx {
    fn notice(&self, now: u64) -> Vec<u8> {
        let mut b = vec![0u8; sleep::MAX_LEN];
        let n = sleep::sign(&self.sleeper, &self.me.node_id(), now / MS, &mut b).expect("a notice signs");
        b.truncate(n);
        b
    }

    /// The host's timer, once a second from `from` to `to`, as the relay host runs it.
    fn run_timer(&mut self, from: u64, to: u64) {
        let mut t = from;
        while t < to {
            t = (t + SEC).min(to);
            self.relay.handle_timeout(t, &mut self.seen);
        }
    }

    fn send_to_sleeper(&mut self, now: u64) {
        let f = Frame::Send {
            dst: self.sleeper.node_id(),
            flag: 0,
            packet: &[0x40, 1, 2, 3, 4, 5],
        };
        let _ = self
            .relay
            .carrier_frame(now, &self.other, self.other_sid, &f, &mut self.seen);
    }
}

/// Expected: `relay::sleep` (module doc): "A notice is sent twice (lossy mobile uplinks); the second changes
/// nothing", and a close is a suspension only "if its sleep notice came within [`rule::SLEEP_WIN_NS`] before"
/// (`relay::clients`). A node that sent its notice and lost its carrier 15 s later did not suspend in the window.
///
/// Actual: a copy of the same notice that arrives 9 s after the first (inside the 10 s clock skew) is accepted again
/// and moves the held time forward, so the close 15 s after the notice is traced `asleep: true` and the node is
/// `Gone { asleep: true }`: a crash is reported as a suspension (the hub keeps the member as asleep instead of
/// failed). The same copy also extends the mark's life by up to 10 s per copy.
///
/// Suspected fault: `crates/pinc-connect/src/relay/discovery.rs:113` inserts `Sleeper { at: now, .. }` for every
/// accepted notice, a copy of the held one (same node, same clock) included; it could keep `at` when the copy's
/// clock equals the held notice's.
///
/// Who can trigger it: anyone who saw the notice (it is not secret and may come over UDP from any address,
/// `sender: None`), within 10 s of its clock; or the node's own second copy, delayed.
#[test]
fn a_second_copy_of_a_sleep_notice_moves_its_time_and_makes_a_crash_a_suspension() {
    let mut f = fx();
    let node = f.sleeper.node_id();
    let notice = f.notice(WALL);
    f.relay
        .carrier_frame(WALL, &node, f.sid, &Frame::Sleep { notice: &notice }, &mut f.seen)
        .expect("the notice is taken");
    let copy = WALL + 9 * SEC;
    f.relay
        .sleep_notice(copy, &notice, None, &mut f.seen)
        .expect("the copy is taken");
    let close = WALL + 15 * SEC;
    f.relay.carrier_closed(close, &node, f.sid, &mut f.seen);
    assert_eq!(
        f.seen.closes,
        vec![(node, false)],
        "the close 15 s after the notice is no suspension"
    );
}

/// Expected: `relay::route`, rule 4: "`dst` is asleep (its sleep notice is held and it has no carrier): the packet
/// goes into the mailbox and the host is asked to wake the member"; `mailbox`: "A relay that holds a member's sleep
/// notice keeps the packets addressed to that member here, up to a byte quota per member and a maximum age"; the
/// maximum age is one day (`mailbox_max_age_ns`, `relay/mod.rs:115`). No document gives the held notice a shorter
/// life.
///
/// Actual: 600 s after the notice the sweep drops it, so a packet for a member that has slept 10 minutes is no longer
/// held and the member is not woken: the packet goes to rule 5 (the home in the record is this relay) and is
/// refused (`NoRoute` here). A phone asleep for longer than 10 minutes gets nothing held and no wake, while packets
/// held before stay up to a day.
///
/// Suspected fault: `crates/pinc-connect/src/relay/clients.rs:348` sweeps `sleeping` with `rule::GONE_TTL_NS` (the
/// life of the gone table, 600 s) instead of the mailbox's maximum age; or the docs are to say the mailbox serves
/// only the first 10 minutes of a sleep.
///
/// Who can trigger it: no one in particular: every member that sleeps longer than 10 minutes, on an ordinary node that
/// carries the relay role or on one deployed from the relay binary.
#[test]
fn a_member_asleep_for_more_than_ten_minutes_gets_nothing_held_and_no_wake() {
    let mut f = fx();
    let node = f.sleeper.node_id();
    let notice = f.notice(WALL);
    f.relay
        .carrier_frame(WALL, &node, f.sid, &Frame::Sleep { notice: &notice }, &mut f.seen)
        .expect("the notice is taken");
    f.relay.carrier_closed(WALL + SEC, &node, f.sid, &mut f.seen);
    assert_eq!(
        f.relay.node_state(&node),
        NodeState::Gone {
            since: WALL + SEC,
            asleep: true
        }
    );
    let later = WALL + 601 * SEC;
    f.run_timer(WALL + SEC, later);
    f.send_to_sleeper(later);
    assert_eq!(f.seen.held_for, vec![node], "a packet for the sleeping member is held");
    assert_eq!(f.seen.woken, vec![node], "the sleeping member is woken");
}

/// Expected: the relay host's store (`crates/pinc/src/relay/store.rs`, module doc): "What a relay keeps across a
/// restart: the signed records it stores and the packets it holds for sleeping members"; the packets come back as
/// held for a member that still sleeps, and `relay::route`, rule 4, holds the next packet for a sleeping member and
/// wakes it. The doc does not list the notice itself among what is kept, so this is a gap between the two rules
/// rather than a broken sentence: the operator decides which one gives.
///
/// Actual: the held notice is not kept (`Kept` holds records and mailboxes, `crates/pinc/src/relay/store.rs:30`, and
/// `Relay` has no call to restore a notice), so after the restart the member is not asleep: the next packet is
/// refused, nothing wakes the member, and the packets restored for it wait until it returns by itself.
///
/// Suspected fault: `crates/pinc/src/relay/store.rs:30` (`Kept` has no sleep marks) with no restore call beside
/// `restore_held` (`crates/pinc-connect/src/relay/mod.rs:495`); `restore_held` could also mark the member asleep.
///
/// Who can trigger it: an operator, by restarting a node deployed from the relay binary (an upgrade) while a member
/// sleeps; on a network whose only relay is that binary, every sleeping member is affected.
#[test]
fn a_restarted_relay_forgets_which_members_sleep() {
    let mut f = fx();
    let node = f.sleeper.node_id();
    let notice = f.notice(WALL);
    f.relay
        .carrier_frame(WALL, &node, f.sid, &Frame::Sleep { notice: &notice }, &mut f.seen)
        .expect("the notice is taken");
    f.relay.carrier_closed(WALL + SEC, &node, f.sid, &mut f.seen);
    f.send_to_sleeper(WALL + 2 * SEC);
    assert_eq!(
        f.relay.mailbox_pending(&node).0,
        1,
        "before the restart the packet is held"
    );
    let mut body = [0u8; pinc_connect::carrier::MAX_PACKET_LEN];
    let (held, at) = f.relay.held_packet(&node, 0, &mut body).expect("a held packet");
    let body = body[..held.len].to_vec();

    // the same relay, restarted: its host gives back what it kept
    let restart = WALL + 30 * SEC;
    let mut relay: Box<R> = Box::new(Relay::new(Config::new(f.me.node_id(), 8)));
    relay
        .restore_held(restart, at, &node, &held.src, held.flag, &body)
        .expect("the held packet is restored");
    let mut seen = Seen::default();
    let other_sid = relay
        .carrier_opened(restart, f.other, &mut seen)
        .expect("a carrier opens");
    let pkt = Frame::Send {
        dst: node,
        flag: 0,
        packet: &[0x40, 9, 9, 9, 9, 9],
    };
    let r = relay.carrier_frame(restart + SEC, &f.other, other_sid, &pkt, &mut seen);
    assert!(r.is_ok(), "the next packet for the sleeping member is refused: {r:?}");
    assert_eq!(
        relay.mailbox_pending(&node).0,
        2,
        "the next packet for the sleeping member is held"
    );
}
