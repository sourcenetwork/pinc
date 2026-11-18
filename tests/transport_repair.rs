//! The pending tail repair is taken by the packet that carries it once that packet is sealed: a build that ends
//! without a packet (a datagram buffer too small for a packet, or for the repair's frames, or a sent ring with no slot
//! left) leaves the repair pending, and it leaves with the next packet that can be sealed, the same as if it had been
//! sealed at once.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use pinc_crypto::IdentityAlg;
use pinc_security::Env;
use pinc_tests::*;
use pinc_transport::conn::Lent;

pinc_tests::install_counting_allocator!();

/// Sent-packet slots of the ring test: few enough that a handful of packets fill it.
const SLOTS: usize = 8;

/// One poll of A, by hand, so that nothing else is built in between. The datagram goes onto the link.
fn send_a<const F: usize>(net: &mut Net<'_, '_, RING, F>) -> Option<usize> {
    let mut env = Env {
        provider: &net.a.prov,
        now: net.now,
        drbg: &mut net.a.drbg,
    };
    let t = net.a.conn.poll_transmit(
        &mut env,
        &mut Lent {
            spill: &mut net.a.spill,
        },
        &mut net.buf,
    )?;
    net.link.send_a(net.now, t.path, &net.buf[..t.len]);
    Some(t.len)
}

/// A connected pair, the client old enough and with a loss average high enough to repair its tail.
fn net_with_a_repair_pending<'a, const F: usize>(
    w: &'a mut World,
    sa: &'a mut Store<RING, F>,
    sb: &'a mut Store<RING, F>,
) -> Net<'a, 'a, RING, F> {
    w.cfg.probe_mtu = false;
    sa.loss.record(1000, 0);
    let mut net = setup(w, sa, sb, Link::new(31, Params::new(10 * MS).mtu(1500)));
    assert!(net.connect(net.now + 30 * SEC), "{:?}", net.rx_drops);
    net.run(net.now + 3 * SEC, |_| false);
    net
}

/// The size of the datagram that carries the repair after a first poll with a buffer of `room` bytes, if any;
/// `None` for `room` is no first poll at all.
fn repair_after_a_poll_with_room(room: Option<usize>) -> Option<usize> {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = net_with_a_repair_pending(&mut w, &mut sa, &mut sb);
        let id = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id, &pattern(100, 7)).unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(send_a(&mut net).is_some(), "the stream packet leaves");
        assert_eq!(net.a.conn.stats().repairs, 0, "{:?}", net.a.conn.stats());
        if let Some(room) = room {
            net.buf.truncate(room);
            assert_eq!(send_a(&mut net), None, "no packet fits in {room} bytes");
            net.buf.resize(65_536, 0);
        }
        let n = send_a(&mut net)?;
        assert_eq!(net.a.conn.stats().repairs, 1, "{:?}", net.a.conn.stats());
        assert_eq!(net.a.conn.stats().ptos, 0, "{:?}", net.a.conn.stats());
        Some(n)
    })
}

#[test]
fn a_tail_repair_leaves_with_the_next_packet_when_the_buffer_had_no_room_for_a_packet() {
    let control = repair_after_a_poll_with_room(None);
    assert!(
        control.is_some_and(|n| n < 700),
        "the repair leaves at once: {control:?}"
    );
    // Smaller than the smallest packet (header, tag and a frame) and no smaller than the room a build starts at.
    let late = repair_after_a_poll_with_room(Some(24));
    assert_eq!(
        late, control,
        "the repair leaves with the next packet, the same as if it had left at once"
    );
}

#[test]
fn a_tail_repair_leaves_with_the_next_packet_when_the_buffer_had_no_room_for_its_frames() {
    let control = repair_after_a_poll_with_room(None);
    // Room for a header, a tag and a few bytes, not for the 100 byte stream frame of the repair.
    let late = repair_after_a_poll_with_room(Some(60));
    assert_eq!(
        late, control,
        "the repair leaves with the next packet, the same as if it had left at once"
    );
}

#[test]
fn a_tail_repair_leaves_with_the_next_packet_when_the_sent_ring_had_no_slot() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (
            Store::<RING, SLOTS>::sized(1024, &stream_cfg(true)),
            Store::sized(1024, &stream_cfg(false)),
        );
        let mut net = net_with_a_repair_pending(&mut w, &mut sa, &mut sb);
        net.buf.truncate(400);
        // Seven packets of one burst: no repair, and one slot of the ring left.
        let big = pattern(2300, 1);
        let first = net.a.conn.open_uni().unwrap();
        net.a.conn.write(first, &big).unwrap();
        net.a.conn.finish(first).unwrap();
        let mut sent = 0;
        for _ in 0..200 {
            if sent == SLOTS - 1 {
                break;
            }
            net.now += 2 * MS;
            sent += usize::from(send_a(&mut net).is_some());
        }
        assert_eq!(sent, SLOTS - 1, "the burst takes all but one slot of the ring");
        net.now += 2 * MS;
        assert_eq!(send_a(&mut net), None, "the burst is all sent");
        // One small packet fills the ring, and its repair is pending.
        let small = pattern(100, 7);
        let second = net.a.conn.open_uni().unwrap();
        net.a.conn.write(second, &small).unwrap();
        net.a.conn.finish(second).unwrap();
        net.now += 2 * MS;
        assert!(send_a(&mut net).is_some(), "the small packet takes the last slot");
        net.now += 2 * MS;
        assert_eq!(send_a(&mut net), None, "the ring has no slot for the repair");
        assert_eq!(net.a.conn.stats().repairs, 0, "{:?}", net.a.conn.stats());
        let before = net.a.tx_log.len();
        // The peer acknowledges: the repair leaves with the next packet, before any probe timeout.
        let done = net.run(net.now + SEC, |n| n.a.conn.stats().repairs == 1);
        assert!(done, "the repair never left: {:?}", net.a.conn.stats());
        assert_eq!(net.a.conn.stats().ptos, 0, "{:?}", net.a.conn.stats());
        assert_eq!(
            net.a.tx_log.len() - before,
            1,
            "only the repair leaves: the bytes it carries are in flight, not lost"
        );
        assert!(net.run(net.now + 10 * SEC, |n| n.b.fin.contains(&first)
            && n.b.fin.contains(&second)));
        assert!(
            net.b.read[&first] == big && net.b.read[&second] == small,
            "every byte arrived as written"
        );
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
    });
}

fn stream_cfg(client: bool) -> pinc_transport::stream::Config {
    pinc_transport::stream::Config::new(client)
}
