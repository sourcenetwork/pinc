//! A size probe's outcome follows the probe, not the active path, and an echo is taken only with a probe in flight
//! and under the path's ceiling (#608). A probe acknowledged or declared lost while the session sits on another path
//! raised that path to a size it never carried, or barred it from probing for 600 s over a probe it never sent, and
//! the probe's own path kept its probe marked in flight and never probed again. An echo raised a path with no probe
//! in flight at all, to any size the frame named.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::RefCell;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{JUMBO_MTU, MIN_MTU, PROBE_MTU, PathId, PathInfo};

/// Everything both ends send from here on, kept separately: the dialer's datagrams first, the responder's second.
fn tap(net: &mut Net<'_, '_>) -> (Rc<RefCell<Vec<Vec<u8>>>>, Rc<RefCell<Vec<Vec<u8>>>>) {
    let a: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let b: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let (a2, b2) = (Rc::clone(&a), Rc::clone(&b));
    net.on_tx = Some(Box::new(move |is_a, d, _| {
        if is_a {
            a2.borrow_mut().push(d.to_vec());
        } else {
            b2.borrow_mut().push(d.to_vec());
        }
    }));
    (a, b)
}

/// Whether `buf` holds a datagram of `len` bytes.
fn has(buf: &Rc<RefCell<Vec<Vec<u8>>>>, len: u16) -> bool {
    buf.borrow().iter().any(|d| d.len() == usize::from(len))
}

/// The first datagram of `len` bytes in `buf`, for the caller to hand over.
fn first_of(buf: &Rc<RefCell<Vec<Vec<u8>>>>, len: u16) -> Option<Vec<u8>> {
    buf.borrow().iter().find(|d| d.len() == usize::from(len)).cloned()
}

/// One direction of one route dies: nothing crosses it any more.
fn dead(net: &mut Net<'_, '_>, path: PathId, ab: bool, ba: bool) {
    let r = net.link.route(path);
    if ab {
        r.ab.p.loss_ppm = 1_000_000;
    }
    if ba {
        r.ba.p.loss_ppm = 1_000_000;
    }
}

/// Hand one datagram to one end as arriving on `path`. With `service`, the end polls at once; without it, its answer
/// waits for its own timer, which is what carries an echo out.
fn hand(net: &mut Net<'_, '_>, to_b: bool, path: PathId, d: &[u8], service: bool) {
    let now = net.now;
    let mut d = d.to_vec();
    let r = if to_b {
        net.b.with_env(now, |c, env| c.handle_datagram(env, path, &mut d))
    } else {
        net.a.with_env(now, |c, env| c.handle_datagram(env, path, &mut d))
    };
    assert!(r.is_ok(), "the handover was refused");
    if service {
        if to_b {
            net.b.service(now);
        } else {
            net.a.service(now);
        }
    }
}

/// Hand `datagrams` to the dialing side as arriving on `path`, in order.
fn deliver_on(net: &mut Net<'_, '_>, path: PathId, datagrams: &[Vec<u8>]) {
    let now = net.now;
    for d in datagrams {
        hand(net, false, path, d, false);
    }
    net.a.service(now);
    assert!(
        net.rx_drops.is_empty(),
        "the peer's answer was refused: {:?}",
        net.rx_drops.iter().rev().take(4).collect::<Vec<_>>()
    );
}

/// Both ends hold a validated second path 9 at the same one-way delay as path 1: the session stays on path 1, and
/// `set_active` can move it.
fn with_second_path(net: &mut Net<'_, '_>) {
    net.link.add_route(
        PathId(9),
        PathId(9),
        Params::new(MS).mtu(1500),
        Params::new(MS).mtu(1500),
    );
    let now = net.now;
    net.a
        .with_env(now, |c, env| c.add_path(env, PathId(9), PathInfo::default()))
        .unwrap();
    net.b
        .with_env(now, |c, env| c.add_path(env, PathId(9), PathInfo::default()))
        .unwrap();
    assert!(
        net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(9))
            && n.b.conn.path_validated(PathId(9))),
        "the second path never validated"
    );
}

/// The capture of everything the peer sends on `path`'s way back, with the link holding it there so nothing arrives
/// but what the test hands over.
fn arm(net: &mut Net<'_, '_>, path: PathId) -> (Rc<RefCell<Vec<Vec<u8>>>>, u64) {
    let at = net.now;
    dead(net, path, false, true);
    let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let sink = Rc::clone(&sent);
    net.on_tx = Some(Box::new(move |is_a, d, _| {
        if !is_a {
            sink.borrow_mut().push(d.to_vec());
        }
    }));
    (sent, at)
}

/// Whether the dialing side has sent a datagram of `size` on `path` since `since`.
fn sent_of(net: &Net<'_, '_>, path: PathId, size: u16, since: u64) -> bool {
    net.a
        .tx_log
        .iter()
        .any(|(t, l, p)| *t >= since && *l == usize::from(size) && *p == path)
}

/// Wait for the probe of `size` on `path` and the peer's captured answer; take the capture back and return the
/// answer, for the caller to deliver when it suits it.
fn collect(
    net: &mut Net<'_, '_>,
    path: PathId,
    size: u16,
    armed: (Rc<RefCell<Vec<Vec<u8>>>>, u64),
    more: impl Fn(&Net<'_, '_>) -> bool,
) -> Vec<Vec<u8>> {
    let (sent, at) = armed;
    assert!(
        net.run(net.now + 20 * SEC, |n| sent_of(n, path, size, at)
            && !sent.borrow().is_empty()
            && more(n)),
        "the probe of {size} never left, was never answered or never settled"
    );
    net.on_tx = None;
    let got = sent.borrow().clone();
    assert!(!got.is_empty(), "the peer answered nothing");
    got
}

/// A probe of 8952 acknowledged while the session sits on path 9: the probe's own path 1 rises, path 9 is untouched.
#[test]
fn a_probes_acknowledgment_rises_the_path_it_left_on_not_the_active_one() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(91, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        with_second_path(&mut net);
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)), "the session left path 1");
        let armed = arm(&mut net, PathId(1));
        net.a.conn.set_path_info(
            PathId(1),
            PathInfo {
                interface_mtu: 9000,
                ..PathInfo::default()
            },
        );
        let got = collect(&mut net, PathId(1), JUMBO_MTU, armed, |_| true);

        // The session moves to path 9 before the answer arrives.
        net.a.conn.set_active(PathId(9)).unwrap();
        assert_eq!(net.a.conn.active_path(), Some(PathId(9)));
        deliver_on(&mut net, PathId(9), &got);

        // The probe's own path rose; the path the session sits on did not.
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(JUMBO_MTU),
            "the probe's path did not rise"
        );
        assert_eq!(
            net.a.conn.path_mtu(PathId(9)),
            Some(MIN_MTU),
            "the active path rose to a size it never probed"
        );
    });
}

/// A probe of 8952 declared lost while the session sits on path 9: path 9 may still probe, and its probe is the one
/// that rises; the probe's own path 1 waits for a path event.
#[test]
fn a_lost_probe_bars_its_own_path_not_the_active_one() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(92, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        with_second_path(&mut net);
        let armed = arm(&mut net, PathId(1));
        net.a.conn.set_path_info(
            PathId(1),
            PathInfo {
                interface_mtu: 9000,
                ..PathInfo::default()
            },
        );
        // The probe leaves on path 1, the peer's answer never comes, the probe is declared lost.
        let got = collect(&mut net, PathId(1), JUMBO_MTU, armed, |n| {
            n.a.conn.stats().packets_lost > 0
        });
        let _ = got;
        // Both ends sit on path 9, so the peer's acknowledgements of what leaves there arrive.
        net.a.conn.set_active(PathId(9)).unwrap();
        net.b.conn.set_active(PathId(9)).unwrap();

        // The path the session sits on probes.
        let at = net.now;
        assert!(
            net.run(net.now + 30 * SEC, |n| sent_of(n, PathId(9), PROBE_MTU, at)),
            "the active path did not probe after the probe's loss"
        );
        // Its probe is the one that rises.
        assert!(
            net.run(net.now + 30 * SEC, |n| n.a.conn.path_mtu(PathId(9)) == Some(PROBE_MTU)),
            "the active path's probe did not raise it"
        );
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(PROBE_MTU),
            "the probe's own path rose without a probe of its own"
        );
    });
}

/// The peer's echo taken on a path with no probe in flight, or above what the path's interface carries, changes
/// nothing there: the echo answers a probe, and the biggest datagram a path carries is the smaller of the jumbo size
/// and what its interface carries.
#[test]
fn an_echo_without_a_probe_in_flight_or_above_the_ceiling_raises_nothing() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(93, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        with_second_path(&mut net);
        // Path 9's interface carries 1372 bytes of payload: its ceiling is under the probe.
        net.a.conn.set_path_info(
            PathId(9),
            PathInfo {
                interface_mtu: 1400,
                ..PathInfo::default()
            },
        );
        // The dialer's route dies both ways: the probe reaches the responder only by hand, and nothing either sends
        // arrives until the test hands it over. The responder's own way back dies too.
        dead(&mut net, PathId(1), true, true);
        dead(&mut net, PathId(9), false, true);
        let (a_tx, b_tx) = tap(&mut net);
        net.a.conn.set_path_info(
            PathId(1),
            PathInfo {
                interface_mtu: 9000,
                ..PathInfo::default()
            },
        );
        // The probe of 8952 leaves on path 1.
        assert!(
            net.run(net.now + 20 * SEC, |n| has(&a_tx, JUMBO_MTU)),
            "the probe of {JUMBO_MTU} never left"
        );
        let probe = first_of(&a_tx, JUMBO_MTU).unwrap();
        // It arrives at the responder on path 9, where no probe of its own is in flight and whose interface cannot
        // carry it. The responder is not served yet: its answer waits for its own timer.
        hand(&mut net, true, PathId(9), &probe, false);
        // The responder's timer sends its echo on path 9, held at the link.
        assert!(
            net.run(net.now + 5 * SEC, |n| !b_tx.borrow().is_empty()),
            "the responder answered nothing"
        );
        let got = b_tx.borrow().clone();
        // The echo arrives on path 9.
        deliver_on(&mut net, PathId(9), &got);
        // It answers a probe path 9 never sent, at a size its interface cannot carry: nothing rises there.
        assert_eq!(
            net.a.conn.path_mtu(PathId(9)),
            Some(MIN_MTU),
            "the echo raised a path with no probe in flight"
        );
    });
}

/// A probe a flush took rises when exactly its acknowledgement arrives: the flush keeps its size and packet number,
/// and an acknowledgement of that packet number raises the path as an acknowledgement in time would have.
#[test]
fn a_probe_a_flush_took_rises_when_its_acknowledgment_arrives() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(94, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        with_second_path(&mut net);
        // The probe's route dies towards the dialer, and so does path 9's: nothing B sends arrives on its own, the
        // test hands every answer over.
        dead(&mut net, PathId(1), false, true);
        dead(&mut net, PathId(9), false, true);
        let (a_tx, b_tx) = tap(&mut net);
        net.a.conn.set_path_info(
            PathId(1),
            PathInfo {
                interface_mtu: 9000,
                ..PathInfo::default()
            },
        );
        // The probe leaves on path 1 and its first acknowledgement is held at the link.
        assert!(
            net.run(net.now + 20 * SEC, |n| has(&a_tx, JUMBO_MTU)),
            "the probe of {JUMBO_MTU} never left"
        );
        assert!(
            net.run(net.now + 5 * SEC, |n| !b_tx.borrow().is_empty()),
            "the responder answered nothing"
        );
        let first = b_tx.borrow().clone();

        // A link return flushes everything in flight, the probe among it, before its loss is timed.
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.link.route(PathId(1)).up = true;
        // The session moves to path 9 before the answers arrive.
        net.a.conn.set_active(PathId(9)).unwrap();
        // The dialer's probe-timeout pings reach the responder, which keeps answering with fresh acknowledgements
        // of the probe. Each is handed over once, a look apart: one lands in the recovery ring's look at what it
        // declared lost, and that look raises the path the flush took the probe from.
        deliver_on(&mut net, PathId(9), &first);
        for _ in 0..8 {
            let before = b_tx.borrow().len();
            net.run(net.now + 200 * MS, |n| b_tx.borrow().len() > before);
            let fresh: Vec<Vec<u8>> = b_tx.borrow().iter().skip(before).cloned().collect();
            for d in &fresh {
                deliver_on(&mut net, PathId(9), std::slice::from_ref(d));
            }
        }

        // The flush did not lose the probe's size: its acknowledgement raised path 1, path 9 is untouched.
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(JUMBO_MTU),
            "the probe the flush took did not rise on its acknowledgement"
        );
        assert_eq!(
            net.a.conn.path_mtu(PathId(9)),
            Some(MIN_MTU),
            "the answer to a probe the session left behind raised the active path"
        );
    });
}

/// A probe a flush took rises when its acknowledgement arrives even with data in flight around it: the
/// acknowledgements of a whole flushed flight reach the machine in one batch, and the probe's packet number is
/// among them however many data packets flank it.
#[test]
fn a_flushed_probe_rises_with_data_in_flight_around_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(97, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        with_second_path(&mut net);
        // Both of the responder's ways back die: nothing it sends arrives until the test hands it over.
        dead(&mut net, PathId(1), false, true);
        dead(&mut net, PathId(9), false, true);
        let (a_tx, b_tx) = tap(&mut net);
        // Data in flight first, while the interface is still the default one and no jumbo probe is due.
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &[0x42; 8_000]).unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(
            net.run(net.now + 20 * SEC, |n| {
                n.a.tx_log
                    .iter()
                    .filter(|(_, l, _)| (1400..usize::from(PROBE_MTU)).contains(l))
                    .count()
                    >= 5
            }),
            "the data never left as full packets: lens {:?}",
            {
                let mut lens: Vec<usize> = net.a.tx_log.iter().map(|(_, l, _)| *l).collect();
                lens.sort_unstable();
                lens.dedup();
                lens
            }
        );
        // Only now does the interface carry a jumbo frame: the probe of 8952 is due, and leaves above the data.
        net.a.conn.set_path_info(
            PathId(1),
            PathInfo {
                interface_mtu: 9000,
                ..PathInfo::default()
            },
        );
        assert!(
            net.run(net.now + 20 * SEC, |n| has(&a_tx, JUMBO_MTU)),
            "the probe of {JUMBO_MTU} never left"
        );
        assert!(
            net.run(net.now + 5 * SEC, |n| !b_tx.borrow().is_empty()),
            "the responder answered nothing"
        );
        let first = b_tx.borrow().clone();

        // A link return flushes everything in flight, the probe among it, before its loss is timed.
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.link.route(PathId(1)).up = true;
        // The session moves to path 9 before the answers arrive.
        net.a.conn.set_active(PathId(9)).unwrap();
        // The held answer and the fresh ones that follow are handed over one look apart, as in the flight of one.
        deliver_on(&mut net, PathId(9), &first);
        for _ in 0..8 {
            let before = b_tx.borrow().len();
            net.run(net.now + 200 * MS, |n| b_tx.borrow().len() > before);
            let fresh: Vec<Vec<u8>> = b_tx.borrow().iter().skip(before).cloned().collect();
            for d in &fresh {
                deliver_on(&mut net, PathId(9), std::slice::from_ref(d));
            }
        }

        // The flush did not lose the probe's size: its acknowledgement raised path 1, path 9 is untouched.
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(JUMBO_MTU),
            "the probe the flush took did not rise on its acknowledgement"
        );
        assert_eq!(
            net.a.conn.path_mtu(PathId(9)),
            Some(MIN_MTU),
            "the answer to a probe the session left behind raised the active path"
        );
    });
}

/// A late answer after the path dropped on the black-hole signature raises nothing: nothing is in flight there.
#[test]
fn an_answer_after_the_black_hole_drop_raises_nothing() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(95, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        // The dialer's route dies both ways: the probe reaches the responder by hand, and nothing either sends
        // arrives until the test hands it over.
        dead(&mut net, PathId(1), true, true);
        let (a_tx, b_tx) = tap(&mut net);
        net.a.conn.set_path_info(
            PathId(1),
            PathInfo {
                interface_mtu: 9000,
                ..PathInfo::default()
            },
        );
        // The probe of 8952 leaves on path 1.
        assert!(
            net.run(net.now + 20 * SEC, |n| has(&a_tx, JUMBO_MTU)),
            "the probe of {JUMBO_MTU} never left"
        );
        let probe = first_of(&a_tx, JUMBO_MTU).unwrap();
        // It reaches the responder, which is not served yet: its answer waits for its own acknowledgement timer,
        // and the echo rides that answer.
        hand(&mut net, true, PathId(1), &probe, false);
        let after_probe = a_tx.borrow().len();
        assert!(
            net.run(net.now + 5 * SEC, |n| !b_tx.borrow().is_empty()),
            "the responder answered nothing"
        );
        let stale = b_tx.borrow().clone();
        // The probe's answer never comes: it is declared lost, and the probe-timeout ping leaves with the loss.
        assert!(
            net.run(net.now + 30 * SEC, |n| n.a.conn.stats().packets_lost > 0),
            "the probe was never declared lost"
        );

        // From here the dialer's probe-timeout pings and the responder's acknowledgements of them are handed over by
        // hand, until the black-hole signature drops the path: a small ping answered while the full-size probe
        // before it stays unacknowledged. The ping that left with the loss is handed first.
        let pending: Vec<Vec<u8>> = a_tx.borrow().iter().skip(after_probe).cloned().collect();
        for d in &pending {
            hand(&mut net, true, PathId(1), d, false);
        }
        let mut rounds = 0;
        while net.a.conn.path_mtu(PathId(1)) != Some(MIN_MTU) {
            rounds += 1;
            assert!(
                rounds <= 40,
                "the path did not drop to the minimum on the black-hole signature"
            );
            let before_a = a_tx.borrow().len();
            let before_b = b_tx.borrow().len();
            net.run(net.now + 25 * MS, |_| false);
            let out: Vec<Vec<u8>> = a_tx.borrow().iter().skip(before_a).cloned().collect();
            let back: Vec<Vec<u8>> = b_tx.borrow().iter().skip(before_b).cloned().collect();
            for d in &out {
                hand(&mut net, true, PathId(1), d, false);
            }
            for d in &back {
                hand(&mut net, false, PathId(1), d, false);
            }
        }

        // The answer held back at the start raises nothing.
        deliver_on(&mut net, PathId(1), &stale);
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(MIN_MTU),
            "a stale answer raised the path after the black-hole drop"
        );
    });
}

/// A late answer after a real loss of the probe raises nothing: a lost probe is no evidence the path carries the size.
#[test]
fn an_answer_after_a_real_loss_of_the_probe_raises_nothing() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.keepalive = Some(SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(96, Params::new(MS / 4).mtu(9000)));
        assert!(net.connect(net.now + 10 * SEC));
        with_second_path(&mut net);
        // Both of the responder's ways back die: nothing it sends arrives until the test hands it over.
        dead(&mut net, PathId(1), false, true);
        dead(&mut net, PathId(9), false, true);
        let (a_tx, b_tx) = tap(&mut net);
        // The session moves to path 9: the probe of 1452 leaves there.
        net.a.conn.set_active(PathId(9)).unwrap();
        assert!(
            net.run(net.now + 20 * SEC, |n| has(&a_tx, PROBE_MTU)),
            "the probe of {PROBE_MTU} never left"
        );
        // The probe's answer never comes: it is declared lost.
        assert!(
            net.run(net.now + 30 * SEC, |n| n.a.conn.stats().packets_lost > 0),
            "the probe was never declared lost"
        );
        // The responder's echo of the probe, held all this time, arrives now.
        let got = b_tx.borrow().clone();
        deliver_on(&mut net, PathId(9), &got);
        // A lost probe is no evidence the path carries the size: nothing rises there.
        assert_eq!(
            net.a.conn.path_mtu(PathId(9)),
            Some(MIN_MTU),
            "the answer to a lost probe raised the path"
        );
    });
}
