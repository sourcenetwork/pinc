//! The fixed and the seeded runs of `trace_facade_waits.rs`, split out below the file limit; included with `#[path]`, not a test target.

use super::*;

// ---- the fixed runs ----

pub(super) fn run_accept_order<H: Hosted + 'static>(t: &mut T<H>) {
    t.begin();
    let a1 = t.accept_bi();
    let first = t.peer_open(false);
    t.expect_ids(&[a1], &[first]);
    let (a2, a3) = (t.accept_bi(), t.accept_bi());
    assert!(t.x.pending().contains(&a2) && t.x.pending().contains(&a3));
    let (second, third) = (t.peer_open(false), t.peer_open(false));
    t.expect_ids(&[a2, a3], &[second, third]);
    assert!(first < second && second < third, "the peer's ids grow");
    // Two wait in the queue and the third is refused.
    let queued = [t.peer_open(false), t.peer_open(false), t.peer_open(false)];
    let (a4, a5) = (t.accept_bi(), t.accept_bi());
    t.expect_ids(&[a4, a5], &queued[..2]);
    let a6 = t.accept_bi();
    t.peer_close(9);
    let by_peer = ErrorKind::Closed { code: 9, by_peer: true };
    t.expect_err(a6, by_peer);
    t.expect_err(3, by_peer);
}

pub(super) fn run_read_write<H: Hosted + 'static>(t: &mut T<H>) {
    t.begin();
    let a = t.accept_bi();
    let id0 = t.peer_open(false);
    t.expect_ids(&[a], &[id0]);
    let st = t.sub(0);
    let r1 = t.read(&st);
    assert!(
        matches!(t.result(r1), Out::Ok(_)),
        "the first read returns the opening bytes"
    );
    let r2 = t.read(&st);
    assert!(t.x.pending().contains(&r2), "the second read waits");
    let ps = t.peer_stream(0);
    t.act(peer_write(Rc::clone(&ps)));
    assert!(matches!(t.result(r2), Out::Ok(_)), "the peer's bytes end the wait");
    let w = t.write(&st);
    assert!(matches!(t.result(w), Out::Ok(_)));
    t.act(peer_drain(Rc::clone(&ps)));
    t.act(peer_stop(Rc::clone(&ps), 6));
    let w = t.write(&st);
    t.expect_err(w, ErrorKind::Stopped(6));
    t.act(peer_finish(Rc::clone(&ps)));
    let r3 = t.read(&st);
    assert!(matches!(t.result(r3), Out::End), "the end of the stream");
}

pub(super) fn run_datagrams<H: Hosted + 'static>(t: &mut T<H>) {
    t.begin();
    let d1 = t.recv_dg(64);
    assert!(t.x.pending().contains(&d1));
    t.peer_dgram();
    assert!(matches!(t.result(d1), Out::Ok(_)));
    let d2 = t.recv_dg(4);
    assert!(t.x.pending().contains(&d2));
    t.peer_dgram();
    t.expect_err(d2, ErrorKind::TooLarge);
    let d3 = t.recv_dg(64);
    assert!(
        matches!(t.result(d3), Out::Ok(_)),
        "the datagram that did not fit is still queued"
    );
}

pub(super) fn run_cancel<H: Hosted + 'static>(t: &mut T<H>) {
    t.begin();
    let a = t.accept_bi();
    let id0 = t.peer_open(false);
    t.expect_ids(&[a], &[id0]);
    let st = t.sub(0);
    let r0 = t.read(&st);
    assert!(matches!(t.result(r0), Out::Ok(_)));
    // A stream's read takes `&mut` of its half, so two waiting reads are on two streams.
    let b = t.accept_bi();
    let id1 = t.peer_open(false);
    t.expect_ids(&[b], &[id1]);
    let st2 = t.sub(1);
    let r00 = t.read(&st2);
    assert!(matches!(t.result(r00), Out::Ok(_)));
    let (a1, a2, a3) = (t.accept_bi(), t.accept_bi(), t.accept_bi());
    let (r1, r2) = (t.read(&st), t.read(&st2));
    t.drop_f(a2);
    t.drop_f(r1);
    t.rest();
    let id = t.peer_open(false);
    t.expect_ids(&[a1], &[id]);
    assert!(t.x.pending().contains(&a3) && t.x.pending().contains(&r2));
}

pub(super) fn run_shutdown<H: Hosted + 'static>(t: &mut T<H>) {
    t.begin();
    let a = t.accept_bi();
    let id0 = t.peer_open(false);
    t.expect_ids(&[a], &[id0]);
    let st = t.sub(0);
    let r0 = t.read(&st);
    assert!(matches!(t.result(r0), Out::Ok(_)));
    let (u, r, d) = (t.accept_uni(), t.read(&st), t.recv_dg(64));
    let e = t.subject.clone();
    let c = t.spawn_s(32, 0, ep_close(e));
    t.settle_until(&mut |x| x.done.contains_key(&c));
    t.rest();
    let reason = t.conn().close_reason().expect("the endpoint closed the session");
    for f in [u, r, d, 3] {
        match t.result(f) {
            Out::Err(e) => assert_eq!(e, reason, "future {f} ends with the session's reason"),
            _ => panic!("future {f} did not end with an error"),
        }
    }
}

// ---- a seeded run ----

/// One random run of 80 steps; the subject calls and the peer's actions are chosen as the test specification lists.
pub(super) fn run_seeded<H: Hosted + 'static>(t: &mut T<H>, seed: u64) {
    t.begin();
    let mut rng = SplitMix64::traced(seed);
    let (c, peers) = (t.pconn(), Rc::clone(&t.peers));
    t.x.spawn(t.next_p, false, peer_acceptor(c, peers));
    t.next_p += 1;
    t.settle();
    let mut opened = 0;
    for _ in 0..80 {
        let roll = rng.next_u64() % 100;
        let live = t.conn().close_reason().is_none();
        let subject_pending = t.x.pending().into_iter().filter(|f| *f < PEER_BASE).collect::<Vec<_>>();
        match roll {
            0..=29 => {
                if subject_pending.len() >= 12 || t.next_f >= 60 {
                    continue;
                }
                let (c, subs) = (t.conn(), Rc::clone(&t.subs));
                match rng.next_u64() % 8 {
                    0 => {
                        t.accept_bi();
                    }
                    1 => {
                        t.accept_uni();
                    }
                    2 => {
                        t.recv_dg(if rng.next_u64().is_multiple_of(2) { 64 } else { 4 });
                    }
                    3 | 4 => {
                        let all: Vec<_> = t.subs.borrow().iter().cloned().collect();
                        let read = rng.next_u64().is_multiple_of(2);
                        let ok: Vec<_> = all
                            .into_iter()
                            .filter(|s| {
                                if read {
                                    !s.ended.get() && s.recv.try_borrow().is_ok_and(|g| g.is_some())
                                } else {
                                    s.send.try_borrow().is_ok_and(|g| g.is_some())
                                }
                            })
                            .collect();
                        if ok.is_empty() {
                            continue;
                        }
                        let st = Rc::clone(&ok[(rng.next_u64() % ok.len() as u64) as usize]);
                        if read {
                            t.read(&st);
                        } else {
                            t.write(&st);
                        }
                    }
                    5 => {
                        t.call(9, 0, answered(c));
                    }
                    6 => {
                        t.call(4, 0, closed(c));
                    }
                    _ => {
                        if opened >= 8 {
                            continue;
                        }
                        opened += 1;
                        t.call(5, 0, open_bi(c, subs));
                    }
                }
            }
            30..=39 => {
                let ids: Vec<_> = subject_pending.into_iter().filter(|f| *f > 1).collect();
                if ids.is_empty() {
                    continue;
                }
                let f = ids[(rng.next_u64() % ids.len() as u64) as usize];
                t.drop_f(f);
                t.rest();
            }
            40..=59 if live => {
                let uni = rng.next_u64().is_multiple_of(2);
                t.peer_open(uni);
            }
            60..=69 if live => {
                let ok: Vec<_> = t
                    .peers
                    .borrow()
                    .iter()
                    .filter(|p| !p.sent_end.get() && t.subs.borrow().iter().any(|s| s.id == p.id))
                    .cloned()
                    .collect();
                if ok.is_empty() {
                    continue;
                }
                let ps = Rc::clone(&ok[(rng.next_u64() % ok.len() as u64) as usize]);
                if rng.next_u64().is_multiple_of(4) {
                    t.act(peer_finish(ps));
                } else {
                    t.act(peer_write(ps));
                }
            }
            70..=79 if live => t.peer_dgram(),
            80..=87 if live => {
                let stop = rng.next_u64().is_multiple_of(2);
                let ok: Vec<_> = t
                    .peers
                    .borrow()
                    .iter()
                    .filter(|p| {
                        if stop {
                            !p.stopped.get() && p.recv.borrow().is_some()
                        } else {
                            !p.sent_end.get()
                        }
                    })
                    .cloned()
                    .collect();
                if ok.is_empty() {
                    continue;
                }
                let ps = Rc::clone(&ok[(rng.next_u64() % ok.len() as u64) as usize]);
                if stop {
                    t.act(peer_stop(ps, 6));
                } else {
                    t.act(peer_reset(ps, 5));
                }
            }
            88..=95 if live => {
                let all: Vec<_> = t.peers.borrow().iter().cloned().collect();
                for ps in all {
                    t.act(peer_drain(ps));
                }
            }
            96..=98 => {
                let all: Vec<_> = t.subs.borrow().iter().cloned().collect();
                if all.is_empty() {
                    continue;
                }
                let st = Rc::clone(&all[(rng.next_u64() % all.len() as u64) as usize]);
                // A pending call keeps its half borrowed: only a half nobody waits on is dropped.
                if rng.next_u64().is_multiple_of(2) {
                    if let Ok(mut g) = st.recv.try_borrow_mut() {
                        drop(g.take());
                    }
                } else if let Ok(mut g) = st.send.try_borrow_mut() {
                    drop(g.take());
                }
                t.log.drain();
            }
            99 if live => {
                match rng.next_u64() % 3 {
                    0 => t.peer_close(9),
                    1 => {
                        let c = t.conn();
                        t.call(32, 0, conn_close(c, 11));
                    }
                    _ => {
                        let e = t.subject.clone();
                        t.call(32, 0, ep_close(e));
                    }
                }
                let c = t.conn();
                t.settle_until(&mut |_| c.close_reason().is_some());
                t.rest();
                return;
            }
            _ => {}
        }
        t.step();
    }
}
