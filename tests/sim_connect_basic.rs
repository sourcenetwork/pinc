//! The connectivity layer end to end in the simulator: boot, address discovery, home relay, record, dial.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_sim_common;

use connect_sim_common::*;
use vinc_connect::client::Notice;
use vinc_sim::{NatKind, SEC};
use vinc_tests::Ev;

#[test]
fn a_client_behind_a_nat_boots_to_a_home_relay_an_open_carrier_and_a_published_record() {
    big(boots);
}

fn boots() {
    let mut w = World::new(1);
    let (r, rs) = w.relay(1, relay_ip(10));
    let nat = w.nat(NatKind::FullCone, ext(1), 120 * SEC, 7200 * SEC);
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), nat);
    w.run(secs(5));
    let n = w.notices(a);
    assert!(n.iter().any(|(_, x)| matches!(x, Notice::Home(0))), "{n:?}");
    assert!(n.iter().any(|(_, x)| matches!(x, Notice::CarrierUp(0))), "{n:?}");
    assert_eq!(w.relay_node(r).relay.record_count(), 1);
    let _ = Ev::Wake;
}

#[test]
fn a_dial_with_no_address_finds_the_peer_through_the_relay_and_moves_data() {
    big(dial_through_the_relay);
}

fn dial_through_the_relay() {
    let mut w = World::new(2);
    let (_r, rs) = w.relay(1, relay_ip(10));
    let nat_a = w.nat(NatKind::FullCone, ext(1), 120 * SEC, 7200 * SEC);
    let nat_b = w.nat(NatKind::FullCone, ext(2), 120 * SEC, 7200 * SEC);
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), nat_a);
    let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[rs]), nat_b);
    w.run(secs(5));
    w.dial(secs(5), a, b, vec![]);
    w.run(secs(20));
    let sa = w.connected(a).expect("a connected");
    let sb = w.incoming(b).expect("b has an incoming session");
    w.sim.command(
        secs(20),
        a,
        vinc_tests::Cmd::Send {
            session: sa,
            data: b"hello over the relay".to_vec(),
        },
    );
    w.run(secs(25));
    assert_eq!(w.client(b).host.received(sb), b"hello over the relay");
}

#[test]
fn a_direct_dial_between_public_nodes_connects() {
    big(|| {
        let mut w = World::new(3);
        let sa = priv_addr(1);
        let sb = priv_addr(2);
        let a = w.client_public(&client_spec(0xa1, sa, &[]));
        let b = w.client_public(&client_spec(0xb1, sb, &[]));
        w.dial(secs(1), a, b, vec![sb]);
        w.run(secs(5));
        assert!(w.connected(a).is_some());
    });
}

/// Everything observable about a run: the simulator's trace and each node's events, as text.
fn run_once(seed: u64) -> String {
    let mut w = World::new(seed);
    let (r, rs) = w.relay(1, relay_ip(10));
    let nat_a = w.nat(NatKind::PortRestricted, ext(1), 120 * SEC, 7200 * SEC);
    let nat_b = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), nat_a);
    let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[rs]), nat_b);
    w.run(secs(5));
    w.dial(secs(5), a, b, vec![]);
    w.run(secs(12));
    let sa = w.connected(a).expect("connected");
    w.sim.command(
        secs(12),
        a,
        vinc_tests::Cmd::Send {
            session: sa,
            data: vec![7; 5000],
        },
    );
    w.sim.command(secs(13), a, vinc_tests::Cmd::Suspend);
    w.sim.suspend(secs(14), a);
    w.sim.resume(secs(30), a);
    w.run(secs(40));
    format!("{}\n{}\n{}\n{}", w.sim.trace(), w.dump(a), w.dump(b), w.dump(r))
}

#[test]
fn the_same_seed_gives_the_same_run_and_the_trace_is_not_empty() {
    big(|| {
        let first = run_once(5);
        let second = run_once(5);
        assert!(first.len() > 10_000, "a real trace: {}", first.len());
        assert_eq!(first, second, "two runs of one seed differ");
    });
}
