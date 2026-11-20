//! The signing work of a suspending node: a sleep notice asked for and then not wanted is answered and dropped, and a
//! tick without a wall clock signs nothing.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod connect_common;
mod connect_rig;

use connect_common::{SEC, big_stack};
use connect_rig::{Ans, Custody, Rig};
use pinc_connect::record::Record;
use pinc_connect::relay::datagram::Datagram;
use pinc_connect::relay::sleep;
use pinc_crypto::Software;
use pinc_security::{Env, KeyRequest};
use pinc_tests::{Answer, Host};

struct Soft(Box<Host>);

impl Custody for Soft {
    fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans {
        match self.0.answer(now, req) {
            Answer::Sig(b, n) => Ans::Sig(b[..n].to_vec()),
            Answer::Secret(s) => Ans::Secret(s),
            Answer::Failed => panic!("the software keys failed"),
        }
    }
}

fn tick(rig: &mut Rig, now: u64, wall_ms: Option<u64>) {
    let Rig { conn, drbg, .. } = rig;
    let mut env = Env {
        provider: &Software,
        now,
        drbg,
    };
    conn.tick(now, &mut env, wall_ms);
}

/// The signature the host gives for the request the layer waits on now (it answers later).
fn take_answer(rig: &Rig, keys: &mut Soft, now: u64) -> Ans {
    let req = rig.conn.sign_request().expect("a signature is outstanding");
    keys.answer(now, &req)
}

/// The clocks of the sleep notices the layer queued for the relay.
fn notices(rig: &mut Rig) -> Vec<u64> {
    let mut buf = vec![0u8; 2048];
    let mut out = Vec::new();
    while let Some((_, n)) = rig.conn.poll_udp(&mut buf) {
        if let Ok(Datagram::Sleep { notice }) = Datagram::decode(&buf[..n]) {
            out.push(sleep::Notice::parse(notice).unwrap().ts_ms);
        }
    }
    out
}

/// A rig with its home carrier open and nothing queued, and the time after.
fn up() -> (Rig, Soft, u64, usize) {
    let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
    let (identity, prekey) = (host.identity, host.prekey_info.clone());
    let mut keys = Soft(host);
    let mut rig = Rig::new(&identity, prekey);
    let mut answered = 0;
    let now = rig.bring_up(&mut keys, 1000 * SEC, &mut answered) + SEC;
    notices(&mut rig);
    (rig, keys, now, answered)
}

#[test]
fn a_resumed_notice_answer_signs_nothing_else() {
    big_stack(|| {
        let (mut rig, mut keys, now, mut answered) = up();
        let wall = now / 1_000_000;
        rig.conn.suspend(now, wall);
        let old = take_answer(&rig, &mut keys, now);
        rig.conn.resume(now);
        // The record falls due while the host still holds the notice's request.
        tick(&mut rig, now + SEC, Some(wall + 1000));
        rig.conn.sign_response(now + SEC, old.response());
        assert!(notices(&mut rig).is_empty(), "a notice nobody wants was sent");
        // The next request is the record's, and its signature is the record's own.
        let sig = take_answer(&rig, &mut keys, now + SEC);
        rig.conn.sign_response(now + SEC, sig.response());
        for _ in 0..8 {
            rig.shuttle(&mut keys, now + SEC, &mut answered);
        }
        let me = keys.0.identity.node_id();
        let stored = rig
            .relay
            .lookup(now + SEC, &me)
            .expect("the relay took the record")
            .to_vec();
        Record::parse_verified(&stored).expect("a record that verifies");
    });
}

#[test]
fn a_notice_cancelled_then_owed_again_goes_twice() {
    big_stack(|| {
        let (mut rig, mut keys, now, _) = up();
        let wall = now / 1_000_000;
        rig.conn.suspend(now, wall);
        let old = take_answer(&rig, &mut keys, now);
        rig.conn.resume(now);
        rig.conn.suspend(now, wall + 5000);
        rig.conn.sign_response(now, old.response());
        assert!(notices(&mut rig).is_empty(), "the cancelled notice was sent");
        let new = take_answer(&rig, &mut keys, now);
        rig.conn.sign_response(now, new.response());
        assert_eq!(
            notices(&mut rig),
            [wall + 5000, wall + 5000],
            "the new notice goes twice"
        );
    });
}

#[test]
fn a_second_suspend_drops_the_first_notice_asked_for() {
    big_stack(|| {
        let (mut rig, mut keys, now, _) = up();
        let wall = now / 1_000_000;
        rig.conn.suspend(now, wall);
        let old = take_answer(&rig, &mut keys, now);
        rig.conn.suspend(now, wall + 5000);
        rig.conn.sign_response(now, old.response());
        assert!(notices(&mut rig).is_empty(), "the first notice was sent");
        let new = take_answer(&rig, &mut keys, now);
        rig.conn.sign_response(now, new.response());
        assert_eq!(
            notices(&mut rig),
            [wall + 5000, wall + 5000],
            "exactly two, with the second clock"
        );
    });
}
