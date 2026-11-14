//! A record's sequence number rises with each record built, within a millisecond and across a clock set back, so the
//! relay never refuses a newer record as stale.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod connect_common;
mod connect_rig;

use connect_common::{SEC, big_stack};
use connect_rig::{Ans, Custody, Rig};
use vinc_connect::record::Record;
use vinc_crypto::Software;
use vinc_security::{Env, KeyRequest};
use vinc_tests::{Answer, Host};

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

/// The sequence number inside the record the layer asks to have signed: `magic(8) node(33) home(33) seq(8)`.
fn requested_seq(rig: &Rig) -> u64 {
    let Some(KeyRequest::Sign { message, .. }) = rig.conn.sign_request() else {
        panic!("the layer waits for no signature");
    };
    u64::from_be_bytes(message[74..82].try_into().unwrap())
}

fn tick(rig: &mut Rig, now: u64, wall_ms: u64) {
    let Rig { conn, drbg, .. } = rig;
    let mut env = Env {
        provider: &Software,
        now,
        drbg,
    };
    conn.tick(now, &mut env, Some(wall_ms));
}

/// Answer the outstanding record signature and let the relay take the record.
fn publish(rig: &mut Rig, keys: &mut Soft, now: u64, answered: &mut usize) {
    let sig = {
        let req = rig.conn.sign_request().expect("a signature is outstanding");
        keys.answer(now, &req)
    };
    rig.conn.sign_response(now, sig.response());
    for _ in 0..8 {
        rig.shuttle(keys, now, answered);
    }
}

#[test]
fn a_record_signed_again_within_a_millisecond_or_after_the_clock_was_set_back_gets_a_higher_number() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let me = identity.node_id();
        let mut keys = Soft(host);
        let mut rig = Rig::new(&identity, prekey);
        let mut answered = 0;
        let mut now = rig.bring_up(&mut keys, 1000 * SEC, &mut answered) + SEC;
        let wall = now / 1_000_000;

        // The first record is outstanding when the hints change: the next job is built without a new tick.
        assert!(rig.conn.set_hints(b"a"));
        tick(&mut rig, now, wall);
        let first = requested_seq(&rig);
        assert_eq!(first, wall);
        assert!(rig.conn.set_hints(b"b"));
        let sig = {
            let req = rig.conn.sign_request().unwrap();
            keys.answer(now, &req)
        };
        rig.conn.sign_response(now, sig.response());
        let second = requested_seq(&rig);
        assert!(second > first, "the second record carries {second}, the first {first}");
        publish(&mut rig, &mut keys, now, &mut answered);
        let stored = rig.relay.lookup(now, &me).expect("the record").to_vec();
        let rec = Record::parse(&stored).unwrap();
        assert_eq!(
            (rec.seq, rec.hints),
            (second, b"b".as_slice()),
            "the relay keeps the newer record"
        );
        assert_eq!(rig.conn.record_seq(), second);

        // The wall clock was set back: the next record is still above the last.
        now += SEC;
        assert!(rig.conn.set_hints(b"c"));
        tick(&mut rig, now, wall - 500);
        let third = requested_seq(&rig);
        assert!(third > second, "the third record carries {third}, the second {second}");
        publish(&mut rig, &mut keys, now, &mut answered);
        let stored = rig.relay.lookup(now, &me).expect("the record").to_vec();
        let rec = Record::parse(&stored).unwrap();
        assert_eq!((rec.seq, rec.hints), (third, b"c".as_slice()));

        // A number restored from a saved state raises the floor, and a lower one changes nothing.
        rig.conn.restore_record_seq(third + 1_000);
        rig.conn.restore_record_seq(1);
        assert_eq!(rig.conn.record_seq(), third + 1_000);
        now += SEC;
        assert!(rig.conn.set_hints(b"d"));
        tick(&mut rig, now, wall);
        assert_eq!(requested_seq(&rig), third + 1_001);
    });
}
