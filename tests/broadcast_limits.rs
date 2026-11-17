//! The size limits are configuration: the body limit, the log ring, the topic count and the subscriber cap are
//! validated at start, enforced at publish and on receipt, and a large body is delivered end to end.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::assert_is_empty,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

use common::{Net, SEC, keypair};
use vinc_broadcast::wire::MAX_HEAD;
use vinc_broadcast::{Config, Limits, Refused, StartError, Topics};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"lim";

fn start(limits: Limits) -> Result<Topics, StartError> {
    let key = keypair(IdentityAlg::Ed25519, 1);
    let cfg = Config {
        me: key.node_id().bytes,
        is_hub: true,
        hubs: &[],
        incarnation: 1,
        trace: false,
        limits,
        map_keys: vinc_tests::id_key(0x5eed),
    };
    Topics::start(&cfg, Box::new(key), SEC, 1)
}

#[test]
fn a_one_mebibyte_body_is_delivered_end_to_end_when_configured() {
    let limits = Limits {
        max_body: 1 << 20,
        log_bytes: 4 << 20,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 3], 1, SEC, limits);
    for i in 1..3 {
        net.attach(i);
        net.set_primary(i, 0);
    }
    net.subscribe(2, T);
    let body: Vec<u8> = (0..(1u32 << 20)).map(|i| (i % 251) as u8).collect();
    let mid = net.publish(1, T, &body);
    net.advance(SEC);
    assert_eq!(net.delivered(2), vec![mid]);
    assert_eq!(net.bodies(2), vec![body]);
    assert_eq!(net.nodes[0].t.log_len(T), 1);
}

#[test]
fn the_default_limit_refuses_a_big_body_and_names_the_limit() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1, SEC);
    let n = &mut net.nodes[1];
    let err = n.t.publish(&mut n.h, SEC, T, &vec![0; 65_537]).unwrap_err();
    assert_eq!(err, Refused::BodyTooLarge { limit: 65_536 });
    assert!(err.to_string().contains("65536"));
}

#[test]
fn a_body_is_accepted_at_the_configured_limit_and_refused_one_byte_over() {
    let limits = Limits {
        max_body: 1000,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 2], 1, SEC, limits);
    net.attach(1);
    net.set_primary(1, 0);
    net.subscribe(1, T);
    let n = &mut net.nodes[0];
    assert!(n.t.publish(&mut n.h, SEC, T, &[7; 1000]).is_ok());
    assert_eq!(
        n.t.publish(&mut n.h, SEC, T, &[7; 1001]).unwrap_err(),
        Refused::BodyTooLarge { limit: 1000 }
    );
    net.pump();
    assert_eq!(net.bodies(1), vec![vec![7u8; 1000]]);
}

#[test]
fn a_node_refuses_a_received_body_over_its_own_limit() {
    // The hub allows 2000, the subscriber only 1000: the subscriber rejects the larger message.
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    let small = Limits {
        max_body: 1000,
        ..Limits::default()
    };
    let key = keypair(IdentityAlg::Ed25519, 3);
    let hub = net.id(0);
    let cfg = Config {
        me: key.node_id().bytes,
        is_hub: false,
        hubs: &[hub],
        incarnation: 1,
        trace: false,
        limits: small,
        map_keys: vinc_tests::id_key(0x5eed),
    };
    net.nodes[2].t = Topics::start(&cfg, Box::new(key), SEC, common::WALL0 + 1000).unwrap();
    net.set_primary(2, 0);
    net.attach(2);
    net.subscribe(2, T);
    net.publish(1, T, &[1; 1000]);
    net.publish(1, T, &[2; 2000]);
    assert_eq!(net.bodies(2), vec![vec![1u8; 1000]]);
}

#[test]
fn an_invalid_config_is_refused_at_start() {
    let ok = Limits::default();
    assert!(start(ok).is_ok());
    // The ring must hold a full message: the body and its head.
    let exact = Limits {
        max_body: 1000,
        log_bytes: 1000 + MAX_HEAD,
        ..ok
    };
    assert!(start(exact).is_ok());
    let short = Limits {
        log_bytes: exact.log_bytes - 1,
        ..exact
    };
    assert_eq!(start(short).err(), Some(StartError::InvalidLimits));
    assert_eq!(
        start(Limits { max_topics: 0, ..ok }).err(),
        Some(StartError::InvalidLimits)
    );
    assert_eq!(
        start(Limits {
            max_subscribers: 0,
            ..ok
        })
        .err(),
        Some(StartError::InvalidLimits)
    );
    assert_eq!(
        start(Limits {
            max_subscribers: 65_536,
            ..ok
        })
        .err(),
        Some(StartError::InvalidLimits)
    );
    assert_eq!(
        start(Limits { reach_bytes: 0, ..ok }).err(),
        Some(StartError::InvalidLimits)
    );
}

#[test]
fn the_topic_table_size_is_configured() {
    let limits = Limits {
        max_topics: 2,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 2], 1, SEC, limits);
    let n = &mut net.nodes[1];
    assert!(n.t.subscribe(&mut n.h, SEC, b"a").is_ok());
    assert!(n.t.subscribe(&mut n.h, SEC, b"b").is_ok());
    assert_eq!(n.t.subscribe(&mut n.h, SEC, b"c").unwrap_err(), Refused::TopicsFull);
}

#[test]
fn the_subscriber_set_a_publisher_learns_is_capped_by_config() {
    let limits = Limits {
        max_subscribers: 2,
        ..Limits::default()
    };
    // Hub 0, publisher 1, subscribers 2..=4.
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 5], 1, SEC, limits);
    for i in 1..5 {
        net.attach(i);
        net.set_primary(i, 0);
    }
    for i in 2..5 {
        net.subscribe(i, T);
    }
    net.publish(1, T, b"x");
    assert_eq!(net.nodes[1].t.known_subscribers(T).len(), 2);
}
