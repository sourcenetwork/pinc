//! Steady state allocates nothing: the carrier, the relay and the mailbox, after setup.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod connect_common;

use connect_common::{Rig, SEC, big_stack, ed, id, nid};
use vinc_connect::carrier::{DnsAnswer, Frame};
use vinc_connect::mailbox::Mailbox;
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::{Config, Effect, Relay, Sink};

vinc_tests::install_counting_allocator!();

/// A sink that drops everything but counts it; it never allocates.
#[derive(Default)]
struct Count(u64);

impl Sink for Count {
    fn emit(&mut self, _: Effect<'_>) {
        self.0 += 1;
    }
}

#[test]
fn the_relay_allocates_nothing_in_steady_state() {
    big_stack(|| {
        let kp = ed(0x10);
        let mut r: Box<Relay<16, 16, 4, 2048>> = Box::new(Relay::new(Config::new(id(&kp), 7)));
        let mut s = Count::default();
        let (a, b, p1, m) = (nid(0xa1), nid(0xb2), nid(0x91), nid(0xe1));
        let sa = r.carrier_opened(0, a, &mut s).unwrap();
        let sb = r.carrier_opened(0, b, &mut s).unwrap();
        r.add_peer(p1);
        r.udp_heard(0, &m, &mut s).unwrap();
        let packet = [0x41u8; 900];
        let spu = {
            let mut buf = [0u8; 2048];
            let n = Datagram::Spu {
                dst: b,
                flag: 1,
                packet: &packet[..200],
            }
            .encode(&mut buf)
            .unwrap();
            buf[..n].to_vec()
        };
        let qad = {
            let mut buf = [0u8; 64];
            let n = Datagram::Qad { nonce: [3; 8] }.encode(&mut buf).unwrap();
            buf[..n].to_vec()
        };
        let src = "198.51.100.9:4000".parse().unwrap();
        let step = |r: &mut Relay<16, 16, 4, 2048>, s: &mut Count, i: u64| {
            let now = i * 1_000_000;
            r.carrier_frame(
                now,
                &a,
                sa,
                &Frame::Send {
                    dst: b,
                    flag: 0,
                    packet: &packet,
                },
                s,
            )
            .unwrap();
            r.carrier_frame(
                now,
                &b,
                sb,
                &Frame::SendAlias {
                    alias: 0,
                    flag: 0,
                    packet: &packet,
                },
                s,
            )
            .ok();
            r.carrier_frame(now, &a, sa, &Frame::Ping, s).unwrap();
            r.carrier_frame(now, &a, sa, &Frame::DnsQuery { peer: nid(5) }, s)
                .unwrap();
            r.peer_frame(
                now,
                &p1,
                &Frame::Forward {
                    src: m,
                    dst: a,
                    flag: 0,
                    packet: &packet,
                },
                s,
            )
            .unwrap();
            r.datagram(now, src, Some(&m), &spu, s).unwrap();
            r.datagram(now, src, None, &qad, s).unwrap();
            r.udp_heard(now, &m, s).unwrap();
            r.handle_timeout(now, s);
            let _ = r.send_local(now, &a, 0, &packet[..100], s);
            // a packet nobody can take is a refusal, which is also allocation free
            let _ = r.carrier_frame(
                now,
                &a,
                sa,
                &Frame::Send {
                    dst: nid(0x77),
                    flag: 0,
                    packet: &packet,
                },
                s,
            );
        };
        for i in 0..50 {
            step(&mut r, &mut s, i);
        }
        let before = s.0;
        let stats = vinc_tests::measure(|| {
            for i in 50..2050 {
                step(&mut r, &mut s, i);
            }
        });
        assert!(s.0 > before + 10_000, "the loop did real work");
        assert_eq!(stats.count(), 0, "{stats:?}");
        let _ = (SEC, DnsAnswer::Absent);
    });
}

#[test]
fn the_mailbox_allocates_nothing_in_steady_state() {
    let mut m: Mailbox<4, 4096> = Mailbox::new(10 * SEC, 1);
    let (to, from) = (nid(1), nid(2));
    let mut buf = [0u8; 1452];
    let body = [9u8; 300];
    for i in 0..50 {
        m.push(i, &to, &from, 0, &body);
    }
    let stats = vinc_tests::measure(|| {
        for i in 50..20_000u64 {
            m.push(i * 1000, &to, &from, 1, &body);
            if i % 3 == 0 {
                m.pop(i * 1000, &to, &mut buf);
            }
            if i % 1000 == 0 {
                m.sweep(i * 1000);
            }
        }
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}

#[test]
fn a_release_pass_with_mail_held_allocates_nothing() {
    big_stack(|| {
        let kp = ed(0x10);
        let mut r: Box<Relay<16, 16, 4, 2048>> = Box::new(Relay::new(Config::new(id(&kp), 7)));
        let mut s = Count::default();
        let (a, m) = (nid(0xa1), nid(0xe1));
        // short messages go down the tunnel; the long one is stepped over and compacted past, pass after pass
        let long = [0x42u8; 1400];
        let short = [0x41u8; 30];
        let step = |r: &mut Relay<16, 16, 4, 2048>, s: &mut Count, i: u64| {
            let now = i * 1_000_000;
            r.restore_held(now, now, &m, &a, 1, &short).unwrap();
            r.restore_held(now, now, &m, &a, 2, &long).unwrap();
            r.restore_held(now, now, &m, &a, 3, &short).unwrap();
            r.udp_heard(now, &m, s).unwrap();
        };
        for i in 0..50 {
            step(&mut r, &mut s, i);
        }
        let (before, delivered) = (s.0, r.mailbox_stats().delivered);
        let stats = vinc_tests::measure(|| {
            for i in 50..2050 {
                step(&mut r, &mut s, i);
            }
        });
        assert!(s.0 > before + 3000, "the passes did real work");
        assert!(r.mailbox_stats().delivered > delivered + 3000);
        assert_eq!(r.mailbox_pending(&m).0, 1, "the long one is still held");
        assert_eq!(stats.count(), 0, "{stats:?}");
    });
}

#[test]
fn the_protected_carrier_allocates_nothing_in_steady_state() {
    big_stack(|| {
        let mut rig = Rig::new(None);
        rig.handshake();
        let packet = [0x41u8; 1200];
        let mut unit = vec![0u8; 20 * 1024];
        let f = Frame::Send {
            dst: nid(3),
            flag: 1,
            packet: &packet,
        };
        for _ in 0..5 {
            let n = rig.seal_client_into(&f, &mut unit);
            rig.feed_relay(&unit[..n]);
            assert!(rig.relay_next_kind().is_some());
        }
        let stats = vinc_tests::measure(|| {
            for _ in 0..2000 {
                let n = rig.seal_client_into(&f, &mut unit);
                let took = rig.relay.receive(&unit[..n]);
                assert_eq!(took, n);
                assert_eq!(rig.relay_next_kind(), Some(2));
            }
        });
        assert_eq!(stats.count(), 0, "{stats:?}");
    });
}
