//! A node whose mapping is no longer vouched for keeps a class and keeps publishing: the record that withdraws the
//! mapping is signed at once, and the record is republished as on a node with no mapping, even when no relay answers
//! UDP again.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_common;
mod connect_rig;

use std::net::SocketAddr;

use connect_common::{SEC, big_stack};
use connect_rig::{Ans, Custody, Rig};
use pinc_connect::record::Reach;
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

/// One turn of the node: its timers, then the bytes between it and the relay.
fn step(rig: &mut Rig, keys: &mut Soft, now: u64) {
    let mut env = Env {
        provider: &Software,
        now,
        drbg: &mut rig.drbg,
    };
    rig.conn.tick(now, &mut env, Some(now / 1_000_000));
    let mut answered = 0;
    rig.shuttle(keys, now, &mut answered);
}

#[test]
fn a_withdrawn_mapping_leaves_the_class_it_replaced_and_its_record_is_signed_at_once() {
    big_stack(|| {
        let mut keys = Soft(Box::new(Host::new(
            0x31,
            "192.168.1.2:4433".parse().unwrap(),
            1000 * SEC,
        )));
        let (identity, prekey) = (keys.0.identity, keys.0.prekey_info.clone());
        let me = identity.node_id();
        let mut rig = Rig::new(&identity, prekey);
        let mut answered = 0;
        let mut now = rig.bring_up(&mut keys, 1000 * SEC, &mut answered);
        assert_eq!(rig.conn.class(), Some(Reach::Nat), "the class before the mapping");
        // the mapping on the IP the relay saw: the node is port-mapped and publishes it
        let mapped: SocketAddr = "198.51.100.5:7777".parse().unwrap();
        rig.conn.set_mapped(now, &[mapped]);
        assert_eq!(rig.conn.class(), Some(Reach::PortMapped));
        for _ in 0..5 {
            now += SEC;
            step(&mut rig, &mut keys, now);
        }
        let with = rig
            .relay
            .record_received(&me)
            .expect("the record with the mapping is published");
        // the link changes; no relay answers UDP again
        now += 10 * SEC;
        rig.conn.link_changed(now);
        rig.conn.set_mapped(now, &[]);
        assert_eq!(
            rig.conn.class(),
            Some(Reach::Nat),
            "the class falls back to the one before the mapping"
        );
        for _ in 0..5 {
            now += SEC;
            step(&mut rig, &mut keys, now);
        }
        let without = rig.relay.record_received(&me).unwrap();
        assert!(
            without > with,
            "the record without the mapping was not published at once"
        );
        // three hours with no relay answer: the class stays and the record is republished
        let mut received = vec![without];
        let end = now + 3 * 3600 * SEC;
        while now < end {
            now += 60 * SEC;
            step(&mut rig, &mut keys, now);
            assert_eq!(rig.conn.class(), Some(Reach::Nat));
            let r = rig.relay.record_received(&me).unwrap();
            if received.last() != Some(&r) {
                received.push(r);
            }
        }
        assert!(
            received.len() >= 6,
            "the record was republished {} times in three hours, expected about every 1,800 s",
            received.len() - 1
        );
    });
}
