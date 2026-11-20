//! The scripted and the random runs of the path-move trace.

use crate::common::*;
use pinc_tests::*;
use pinc_transport::conn::PathId;

pub fn fixed_runs(tr: &mut PmTrace) {
    // 0: validation
    fixed(tr, 0, false, |net, r| {
        r.add(net, 2, false, false);
        r.send_all(net);
        r.adv(3 * MS);
        let c = r.outstanding(net, 2).unwrap();
        assert!(!validated(net, 2));
        r.resp_real(net, 2, c);
        assert!(validated(net, 2), "an answer on its path validates it");
    });
    // 1: a wrong path and forged bytes
    fixed(tr, 1, false, |net, r| {
        r.add(net, 2, false, false);
        r.send_all(net);
        r.adv(3 * MS);
        let c = r.outstanding(net, 2).unwrap();
        r.resp_real(net, 1, c);
        r.resp_real(net, 7, c);
        r.resp_forged(net, 2);
        assert!(!validated(net, 2));
        r.resp_real(net, 2, c);
    });
    // 2: a replaced challenge is still kept
    fixed(tr, 2, false, |net, r| {
        r.add(net, 2, false, false);
        for _ in 0..2 {
            r.probe(net, 2);
            r.send_all(net);
            r.adv(3 * MS);
        }
        let first = r.kept(net, 2)[0];
        r.resp_real(net, 2, first);
        assert!(validated(net, 2), "an answer to a replaced challenge validates");
    });
    // 3: the table wraps
    fixed(tr, 3, false, |net, r| {
        r.add(net, 2, false, false);
        r.probe(net, 2);
        r.send_all(net);
        r.adv(3 * MS);
        let first = r.kept(net, 2)[0];
        for _ in 0..4 {
            r.probe(net, 2);
            r.send_all(net);
            r.adv(3 * MS);
        }
        r.resp_real(net, 2, first);
        assert!(!validated(net, 2), "an overwritten challenge validated a path");
        let newest = *r.kept(net, 2).last().unwrap();
        r.resp_real(net, 2, newest);
    });
    // 4: a rebind during validation
    fixed(tr, 4, false, |net, r| {
        r.add(net, 2, false, false);
        r.send_all(net);
        r.adv(3 * MS);
        r.rebind(net, 2, 3);
        let c = r.outstanding(net, 3).unwrap();
        r.resp_real(net, 3, c);
        assert!(validated(net, 3), "the answer after a rebind validates the path");
        r.resp_real(net, 2, c);
        r.rebind(net, 3, 1);
        r.rebind(net, 9, 5);
    });
    // 5: host calls refused
    fixed(tr, 5, false, |net, r| {
        r.add(net, 2, false, false);
        r.remove(net, 1);
        r.remove(net, 9);
        r.lost(net, 9);
        r.set(net, 9);
        r.probe(net, 9);
        r.set(net, 2);
        assert!(!r.returned(net, 1, 7 * MS));
    });
    // 6: a full table
    fixed(tr, 6, false, |net, r| {
        for id in [2, 3, 4] {
            r.add(net, id, true, false);
        }
        r.add(net, 5, false, false);
        r.chal(net, 6);
        r.data(net, 6, true, false);
        r.remove(net, 4);
        r.add(net, 5, false, false);
        r.add(net, 6, false, false);
    });
    // 7: following the peer
    fixed(tr, 7, false, |net, r| {
        r.add(net, 2, true, false);
        r.adv(5 * MS);
        r.data(net, 2, true, false);
        r.adv(5 * MS);
        r.data(net, 2, true, true);
        r.adv(5 * MS);
        r.data(net, 1, false, false).expect("an older packet number is free");
        r.adv(5 * MS);
        r.data(net, 1, true, false);
        r.adv(5 * MS);
        r.data(net, 3, true, false);
    });
    // 8: the idle boundary
    fixed(tr, 8, false, |net, r| {
        r.add(net, 2, true, false);
        r.data(net, 1, true, false);
        let t = r.now;
        r.timer_at(net, t + IDLE);
        assert!(validated(net, 1), "a path silent for exactly 15 s is still validated");
        r.timer_at(net, t + IDLE + 1);
        assert!(!validated(net, 1), "a path silent for more than 15 s is validated");
        assert_eq!(active(net), 2);
        r.data(net, 1, true, false);
        r.send_all(net);
        r.answer(net, 1);
    });
    // 9: three probe timeouts with a relayed path
    fixed(tr, 9, false, |net, r| {
        r.add(net, 2, true, false);
        flight(net, 1000);
        r.send_all(net);
        r.until_pto(net, 3);
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(2)),
            "three probe timeouts fail over to the relayed path"
        );
        for _ in 0..2 {
            r.timer_next(net);
            r.send_all(net);
        }
        r.data(net, 1, true, false);
        r.send_all(net);
        r.answer(net, 1);
    });
    // 10: three probe timeouts with no relayed path
    fixed(tr, 10, false, |net, r| {
        flight(net, 1000);
        r.send_all(net);
        r.until_pto(net, 3);
        for _ in 0..2 {
            r.timer_next(net);
            r.send_all(net);
        }
        r.data(net, 1, true, false);
        r.send_all(net);
        r.answer(net, 1);
    });
    // 11: followed onto an unvalidated path, and no fall back
    fixed(tr, 11, false, |net, r| {
        r.add(net, 2, true, false);
        r.data(net, 3, true, false);
        flight(net, 1000);
        r.send_all(net);
        r.until_pto(net, 4);
    });
    // 12: lost
    fixed(tr, 12, false, |net, r| {
        r.lost(net, 1);
        r.add(net, 2, true, false);
        r.timer_next(net);
        r.add(net, 3, false, false);
        r.send_all(net);
        r.answer(net, 3);
    });
    // 13: gone
    fixed(tr, 13, false, |net, r| {
        r.add(net, 2, true, false);
        r.set(net, 2);
        let t = r.now;
        r.timer_at(net, t + 16 * SEC);
        r.lost(net, 2);
        r.set(net, 1);
        r.punch(net);
        // The probe of a punch leaves at the timer of the path, not with the next datagram built.
        let t = r.now;
        r.timer_at(net, t);
        flight(net, 1000);
        r.send_all(net);
        r.answer(net, 1);
        r.until_pto(net, 3);
    });
    // 19: a gone path is never followed: the active path is lost while the other is unvalidated, a data packet on
    // the other follows, then a higher numbered data packet on the lost path's id leaves the active path alone
    fixed(tr, 19, false, |net, r| {
        r.add(net, 2, false, false);
        r.set(net, 2);
        r.lost(net, 1);
        r.data(net, 2, true, false);
        r.data(net, 1, true, false);
        assert_eq!(active(net), 2, "a packet on a gone path moved the active path");
    });
    // 14: path info
    fixed(tr, 14, false, |net, r| {
        r.add(net, 2, false, false);
        r.info(net, 2, true, false);
        r.info(net, 2, false, true);
        r.info(net, 1, true, false);
        r.info(net, 1, true, false);
    });
    // 15: punch
    fixed(tr, 15, false, |net, r| {
        r.add(net, 2, false, false);
        r.add(net, 3, false, false);
        r.lost(net, 3);
        r.punch(net);
    });
    // 16: a thin session re-joins a path that idled out
    fixed(tr, 16, true, |net, r| {
        r.add(net, 2, true, false);
        r.data(net, 1, true, false);
        let t = r.now;
        r.timer_at(net, t + IDLE + 1);
        let floor = r.now + 10 * SEC;
        PmRun::rejoin_floor(net, 1, floor);
        r.timer_next(net);
        PmRun::rejoin_floor(net, 1, 0);
        r.timer_next(net);
        r.send_all(net);
        assert!(r.returned(net, 1, 7 * MS), "a re-joined path that answers is validated");
        assert!(
            !r.returned(net, 1, 7 * MS),
            "a path already validated is not returned twice"
        );
    });
    // 17: a thin node declared thin does not challenge back
    fixed(tr, 17, true, |net, r| {
        r.add(net, 2, true, false);
        r.set(net, 2);
        r.chal(net, 3);
        r.add(net, 4, false, false);
        r.send_all(net);
        r.adv(5 * MS);
        r.data(net, 4, true, false);
    });
    // 18: a session that moved application data challenges back, once
    fixed(tr, 18, false, |net, r| {
        r.add(net, 2, true, false);
        r.set(net, 2);
        flight(net, 100);
        r.send_all(net);
        r.chal(net, 3);
        r.chal(net, 3);
    });
}

pub fn random_runs(tr: &mut PmTrace) {
    for k in 0..40u32 {
        with_net(k % 4 == 3, 6000 + u64::from(k), |net| {
            let mut r = PmRun::new(tr, 100 + k, net, 0x504D_0001 + u64::from(k));
            flight(net, 500);
            let start = r.now;
            for _ in 0..60 {
                if !r.live || r.now - start >= 60 * SEC {
                    break;
                }
                if !r.random_step(net, start) {
                    let gap = 1 + r.rng.next_u64() % 40;
                    r.adv(gap * MS);
                }
            }
        });
    }
}
