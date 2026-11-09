//! Each NAT kind against the connectivity layer: the reachability class a node reads from its observations, the
//! session it gets through the relay, and whether hole punching moves it onto a direct path.
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
use vinc_connect::record::Reach;
use vinc_core::is_relay_addr;
use vinc_sim::{NatKind, NodeId, SEC};

/// Two relays, A behind a NAT of `ka` and B behind one of `kb`; A dials B at 6 s. Returns the world and the nodes.
fn pair(ka: NatKind, kb: NatKind, seed: u64) -> (World, NodeId, NodeId) {
    let mut w = World::new(seed);
    let (_r1, r1) = w.relay(1, relay_ip(10));
    let (_r2, r2) = w.relay(2, relay_ip(20));
    let na = w.nat(ka, ext(1), 120 * SEC, 7200 * SEC);
    let nb = w.nat(kb, ext(2), 120 * SEC, 7200 * SEC);
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[r1, r2]), na);
    let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[r1, r2]), nb);
    w.run(secs(6));
    w.dial(secs(6), a, b, vec![]);
    w.run(secs(9));
    (w, a, b)
}

fn class_of(w: &World, n: NodeId) -> Option<Reach> {
    w.client(n).conn.class()
}

fn direct(w: &World, n: NodeId) -> Option<bool> {
    let c = w.client(n);
    let s = *c.dialed.first().or(c.host.sessions.first())?;
    let st = c.session_stats(s)?;
    st.route.map(|(_, r)| !is_relay_addr(&r))
}

#[test]
fn every_nat_kind_gets_a_class_a_session_and_a_path() {
    big(|| {
        use NatKind::*;
        // (a's NAT, b's NAT, a's class, whether hole punching puts the session on a direct path)
        let table = [
            (FullCone, FullCone, Reach::Nat, true),
            (AddressRestricted, AddressRestricted, Reach::Nat, true),
            (PortRestricted, PortRestricted, Reach::Nat, true),
            (PortRestricted, FullCone, Reach::Nat, true),
            (DependentOpen, FullCone, Reach::Cgnat, true),
            (Symmetric, Symmetric, Reach::Cgnat, false),
            (Symmetric, PortRestricted, Reach::Cgnat, false),
            (DependentAddress, DependentAddress, Reach::Cgnat, false),
        ];
        for (i, (ka, kb, class, punched)) in table.into_iter().enumerate() {
            let (mut w, a, b) = pair(ka, kb, 10 + i as u64);
            assert_eq!(class_of(&w, a), Some(class), "{ka:?}/{kb:?}");
            assert!(w.connected(a).is_some(), "{ka:?}/{kb:?} did not connect\n{}", w.dump(a));
            let sb = w.incoming(b).expect("b has the session");
            assert_eq!(direct(&w, a), Some(punched), "{ka:?}/{kb:?}\n{}", w.dump(a));
            // Whatever path carries the session, data flows both ways.
            let sa = w.connected(a).unwrap();
            w.sim.command(
                secs(9),
                a,
                vinc_tests::Cmd::Send {
                    session: sa,
                    data: b"ping".to_vec(),
                },
            );
            w.run(secs(10));
            assert_eq!(w.client(b).host.received(sb), b"ping", "{ka:?}/{kb:?}");
            w.sim.command(
                secs(10),
                b,
                vinc_tests::Cmd::Send {
                    session: sb,
                    data: b"pong".to_vec(),
                },
            );
            w.run(secs(12));
            assert_eq!(w.client(a).host.received(sa), b"pong", "{ka:?}/{kb:?}");
            let _ = Notice::SignFailed;
        }
    });
}
