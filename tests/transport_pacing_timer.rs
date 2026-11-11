//! The pacing timer is for data that waits for its turn. A connection that polls inside the pacer's gap arms a timer to
//! wake the endpoint when the pacer lets data go, if a stream or a datagram is waiting (new data or a retransmission),
//! and arms none when nothing waits: acknowledgements, probes, pings, control and path frames do not wait for the
//! pacer, so a timer for them would wake the endpoint for no reason.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::manual_assert_eq
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::stream::SendView;

/// A connected pair on a fast link, quiet, with a round-trip sample on both ends so the pacer is on.
fn quiet_pair<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store) -> Net<'a, 'a> {
    let mut net = setup(w, sa, sb, Link::new(3, Params::new(5 * MS)));
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    net.run(net.now + 2 * SEC, |_| false);
    net
}

/// Everything the connection of `A` will send at `now`, polled until it has nothing more.
fn drain(net: &mut Net<'_, '_>, now: u64) -> usize {
    let mut buf = vec![0u8; 65_535];
    let mut n = 0;
    while net.a.with_env(now, |c, env| c.poll_transmit(env, &mut buf)).is_some() {
        n += 1;
    }
    n
}

#[test]
fn a_stream_waiting_for_the_pacer_arms_its_timer() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = quiet_pair(&mut w, &mut sa, &mut sb);
        let id = net.a.conn.open_bi().unwrap();
        let data = pattern(200_000, 1);
        assert!(net.a.conn.write(id, &data).unwrap() > 100_000);
        let now = net.now;
        let sent = drain(&mut net, now);
        let pace = net.a.conn.recovery().pacer().next_release(now);
        // The burst is the pacer's ten packets, the window still has room, and data is left.
        assert!((1..=10).contains(&sent), "{sent} packets left");
        assert!(pace > now && net.a.conn.recovery().can_send());
        assert!(
            net.a.conn.poll_timeout().is_some_and(|t| t <= pace),
            "no timer for the pacer"
        );
    });
}

#[test]
fn a_datagram_waiting_for_the_pacer_arms_its_timer() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = quiet_pair(&mut w, &mut sa, &mut sb);
        for _ in 0..40 {
            net.a.conn.send_datagram(&[9u8; 1200]).unwrap();
        }
        let now = net.now;
        let sent = drain(&mut net, now);
        let pace = net.a.conn.recovery().pacer().next_release(now);
        assert!((1..=10).contains(&sent), "{sent} packets left");
        assert!(pace > now && net.a.conn.recovery().can_send());
        assert!(
            net.a.conn.poll_timeout().is_some_and(|t| t <= pace),
            "no timer for the pacer"
        );
    });
}

#[test]
fn a_poll_inside_the_pacing_gap_with_nothing_waiting_arms_no_timer() {
    big_stack(|| {
        // The size of a write that leaves the pacer in its gap with every byte sent: ten packets and a little.
        for size in (12_000..20_000).step_by(100) {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = quiet_pair(&mut w, &mut sa, &mut sb);
            let id = net.a.conn.open_bi().unwrap();
            let data = pattern(size, 2);
            assert_eq!(net.a.conn.write(id, &data).unwrap(), size);
            let now = net.now;
            drain(&mut net, now);
            let pace = net.a.conn.recovery().pacer().next_release(now);
            let all_sent = net
                .a
                .conn
                .send_view(id)
                .is_some_and(|v: SendView| v.sent == size as u64);
            if pace > now && all_sent {
                // A second poll inside the gap, with nothing to send.
                drain(&mut net, now);
                assert_ne!(
                    net.a.conn.poll_timeout(),
                    Some(pace),
                    "a timer for a pacer with nothing waiting"
                );
                return;
            }
        }
        panic!("no write size left the pacer in its gap with everything sent");
    });
}
