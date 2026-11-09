//! TETHER in the simulator: a node about to be suspended tells its relay (a signed notice, signed through the key
//! request path), the relay holds packets for it in the mailbox and asks for a wake-up, and the packets arrive when
//! the node resumes.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_sim_common;

use connect_sim_common::*;
use vinc_connect::relay::Trace;
use vinc_core::Event;
use vinc_sim::{NatKind, SEC};
use vinc_tests::{Cmd, Ev};

#[test]
fn a_sleeping_member_is_held_for_woken_and_served_from_the_mailbox() {
    big(|| {
        let mut w = World::new(51);
        let (r, rs) = w.relay(1, relay_ip(10));
        let na = w.nat(NatKind::Symmetric, ext(1), 120 * SEC, 7200 * SEC);
        let nb = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), na);
        let mut sb = client_spec(0xb1, priv_addr(2), &[rs]);
        sb.phone = true;
        let b = w.client_behind(&sb, nb);
        w.run(secs(6));
        w.dial(secs(6), a, b, vec![]);
        w.run(secs(15));
        let sa = w.connected(a).expect("connected");
        let sbs = w.incoming(b).unwrap();
        w.sim.command(
            secs(15),
            a,
            Cmd::Send {
                session: sa,
                data: b"awake".to_vec(),
            },
        );
        w.run(secs(20));
        assert_eq!(w.client(b).host.received(sbs), b"awake");

        // B announces its suspension: sessions sleep, the relay gets the signed notice, the carrier closes.
        w.sim.command(secs(20), b, Cmd::Suspend);
        w.sim.suspend(secs(21), b);
        w.run(secs(25));
        let b_id = w.client(b).host.me;
        let traces = |w: &World| w.relay_node(r).traces.iter().map(|(_, t)| *t).collect::<Vec<_>>();
        assert!(
            traces(&w).contains(&Trace::SleepAccepted { node: b_id }),
            "the signed sleep notice was accepted"
        );
        assert!(
            traces(&w)
                .iter()
                .any(|t| matches!(t, Trace::CarrierClosed { node, asleep: true } if *node == b_id)),
            "the close that followed is a suspension, not a crash"
        );
        assert!(
            w.sim
                .events(a)
                .iter()
                .any(|(_, e)| matches!(e, Ev::Ep(Event::PeerAsleep { .. }))),
            "the peer was told"
        );

        // A sends while B sleeps: the relay holds the packets and asks for a wake-up.
        w.sim.command(
            secs(30),
            a,
            Cmd::Send {
                session: sa,
                data: b"while asleep".to_vec(),
            },
        );
        w.run(secs(40));
        assert!(
            traces(&w)
                .iter()
                .any(|t| matches!(t, Trace::MailboxStored { node, .. } if *node == b_id)),
            "a packet went into the mailbox"
        );
        assert!(
            traces(&w).contains(&Trace::WakeRequested { node: b_id }) && !w.relay_node(r).wakes.is_empty(),
            "the wake-up was requested"
        );
        assert!(w.relay_node(r).relay.mailbox_pending(&b_id).0 > 0);
        assert_eq!(w.client(b).host.received(sbs), b"awake", "B is frozen");

        // B resumes: its carrier opens, the mailbox is delivered, the session wakes and the data arrives.
        w.sim.resume(secs(60), b);
        w.run(secs(75));
        assert!(
            traces(&w)
                .iter()
                .any(|t| matches!(t, Trace::MailboxDelivered { node, .. } if *node == b_id)),
            "the mailbox was delivered"
        );
        assert_eq!(w.client(b).host.received(sbs), b"awakewhile asleep");
        assert_eq!(w.relay_node(r).relay.mailbox_pending(&b_id).0, 0);
    });
}
