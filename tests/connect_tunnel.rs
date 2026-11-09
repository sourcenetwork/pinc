//! The member side of the hub tunnel, SPLICE_LIVE and THIN_SPLICE at their boundary numbers.
#![allow(
    clippy::doc_markdown,
    clippy::unnested_or_patterns,
    clippy::nonminimal_bool,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::many_single_char_names
)]

use vinc_connect::client::tunnel::{
    HUB_TUNNEL_FRESH, HubSession, Rides, SPL_LIVE, SPLICE_SPAN, Splices, THIN_SPLICE_FRESH, TUNNEL_STALE, ThinSplice,
    Via, decide, hub_ok, thin_splice,
};

const S: u64 = 1_000_000_000;

fn rides(pto: u32, hs: bool, tries: u32, thin: bool) -> Rides {
    Rides {
        pto_count: pto,
        handshaking: hs,
        hs_tries: tries,
        thin,
    }
}

#[test]
fn a_hub_session_must_be_validated_direct_and_heard_within_20s() {
    let mut h = HubSession {
        validated_direct: true,
        heard: 100 * S,
        remote: "192.0.2.1:1".parse().unwrap(),
    };
    assert!(hub_ok(&h, 100 * S + HUB_TUNNEL_FRESH - 1));
    assert!(!hub_ok(&h, 100 * S + HUB_TUNNEL_FRESH));
    h.validated_direct = false;
    assert!(!hub_ok(&h, 100 * S));
}

#[test]
fn no_usable_hub_session_means_the_carrier() {
    assert_eq!(
        decide(false, 99 * S, Some(rides(9, true, 9, false)), false),
        Via::Carrier
    );
}

#[test]
fn a_carrier_that_is_not_open_is_replaced_by_the_tunnel() {
    assert_eq!(decide(false, 0, None, true), Via::Tunnel);
}

#[test]
fn a_carrier_silent_over_15s_also_gets_a_tunnel_copy() {
    assert_eq!(
        decide(true, TUNNEL_STALE, None, true),
        Via::Carrier,
        "exactly 15 s is not over"
    );
    assert_eq!(decide(true, TUNNEL_STALE + 1, None, true), Via::Both);
}

#[test]
fn loss_recovery_and_handshake_send_a_copy() {
    // one probe timeout on a node that is not thin, two on a thin one
    assert_eq!(decide(true, 0, Some(rides(0, false, 0, false)), true), Via::Carrier);
    assert_eq!(decide(true, 0, Some(rides(1, false, 0, false)), true), Via::Both);
    assert_eq!(decide(true, 0, Some(rides(1, false, 0, true)), true), Via::Carrier);
    assert_eq!(decide(true, 0, Some(rides(2, false, 0, true)), true), Via::Both);
    // handshake: at once when not thin, from the second try when thin
    assert_eq!(decide(true, 0, Some(rides(0, true, 1, false)), true), Via::Both);
    assert_eq!(decide(true, 0, Some(rides(0, true, 1, true)), true), Via::Carrier);
    assert_eq!(decide(true, 0, Some(rides(0, true, 2, true)), true), Via::Both);
}

#[test]
fn splice_live_keeps_the_hub_path_for_30s_or_twice_the_rtt() {
    let mut s = Splices::<4, 2>::new();
    let hub = "192.0.2.9:7".parse().unwrap();
    let p = connect_node(1);
    s.seen(10 * S, 1, p, hub);
    assert_eq!(s.live(10 * S + SPL_LIVE - 1, 1, 0), Some(hub));
    assert_eq!(s.live(10 * S + SPL_LIVE, 1, 0), None);
    assert_eq!(s.live(10 * S + 59 * S, 1, 30 * S), Some(hub), "2 x 30 s rtt = 60 s");
    assert_eq!(s.live(10 * S + 60 * S, 1, 30 * S), None);
    assert_eq!(s.live(11 * S, 0, 0), None, "another relay never spliced");
    assert_eq!(s.age(12 * S, 1, &p), Some(2 * S));
    assert_eq!(s.age(12 * S, 0, &p), None);
}

fn connect_node(tag: u8) -> vinc_crypto::NodeId {
    vinc_crypto::NodeId {
        alg: vinc_crypto::IdentityAlg::Ed25519,
        bytes: [tag; 32],
    }
}

#[test]
fn thin_splice_withholds_the_carrier_only_when_every_condition_holds() {
    let ok = ThinSplice {
        thin: true,
        established: true,
        splice_age: Some(SPLICE_SPAN - 1),
        rtt: 0,
        carrier_fresh: false,
        tunnel_took: true,
        pto_count: 1,
    };
    assert!(thin_splice(&ok));
    assert!(!thin_splice(&ThinSplice { thin: false, ..ok }));
    assert!(!thin_splice(&ThinSplice {
        established: false,
        ..ok
    }));
    assert!(!thin_splice(&ThinSplice {
        tunnel_took: false,
        ..ok
    }));
    assert!(
        !thin_splice(&ThinSplice {
            carrier_fresh: true,
            ..ok
        }),
        "a carrier heard within 2 s is not backlogged"
    );
    assert!(!thin_splice(&ThinSplice { pto_count: 2, ..ok }), "THIN_SPLICE_PTO is 2");
    assert!(!thin_splice(&ThinSplice { splice_age: None, ..ok }));
    assert!(!thin_splice(&ThinSplice {
        splice_age: Some(SPLICE_SPAN),
        ..ok
    }));
    assert!(
        thin_splice(&ThinSplice {
            splice_age: Some(2 * 5 * S - 1),
            rtt: 5 * S,
            ..ok
        }),
        "max(4 s, 2 x rtt)"
    );
    assert!(!thin_splice(&ThinSplice {
        splice_age: Some(10 * S),
        rtt: 5 * S,
        ..ok
    }));
    assert_eq!(THIN_SPLICE_FRESH, 2 * S);
}
