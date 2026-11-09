//! The client connectivity layer allocates nothing in steady state: routing session packets onto an open carrier,
//! flushing the batch, reading the relay's frames, handing packets to the endpoint, and the periodic drive.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_common;
mod connect_rig;

use connect_common::{SEC, big_stack, nid};
use connect_rig::{Ans, Custody, Rig};
use vinc_connect::carrier::Frame;
use vinc_crypto::Software;
use vinc_security::{Env, KeyRequest};
use vinc_tests::{Answer, Host};

vinc_tests::install_counting_allocator!();

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

#[test]
fn the_client_allocates_nothing_in_steady_state() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut keys = Soft(host);
        let mut rig = Rig::new(identity, prekey);
        let mut answered = 0;
        let mut now = rig.bring_up(&mut keys, 1000 * SEC, &mut answered);
        // The record is published and the carrier is quiet.
        now += SEC;
        {
            let Rig { conn, drbg, .. } = &mut rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.tick(now, &mut env, Some(now / 1_000_000));
        }
        for _ in 0..8 {
            rig.shuttle(&mut keys, now, &mut answered);
        }
        assert_eq!(rig.relay.record_count(), 1);

        // What the relay will send the node, sealed ahead: the node counts the records it opens.
        let peer = nid(0xb7);
        let packet = [0x41u8; 900];
        let inbound: Vec<Vec<u8>> = (0..200)
            .map(|_| {
                let mut out = vec![0u8; 20 * 1024];
                let n = rig
                    .rc
                    .seal(
                        &Software,
                        &Frame::Recv {
                            src: peer,
                            flag: 0,
                            packet: &packet,
                        },
                        &mut out,
                    )
                    .unwrap();
                out.truncate(n);
                out
            })
            .collect();
        let to_peer = rig.conn.path_addr(0, &peer);
        let mut out = vec![0u8; 32 * 1024];
        let mut seen = 0usize;

        // Warm up once, then count.
        let one = |rig: &mut Rig, keys: &mut Soft, i: usize, now: u64, out: &mut [u8], seen: &mut usize| {
            let Rig { conn, drbg, .. } = rig;
            conn.route(now, &*keys.0.ep, to_peer, &packet);
            conn.route(now, &*keys.0.ep, to_peer, &packet);
            let _ = conn.poll_stream(0, out);
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.stream_data(now, &mut env, 0, &inbound[i]);
            conn.deliver_inbound(|_, d| *seen += d.len());
            conn.drive(now, &mut *keys.0.ep, &mut env, Some(now / 1_000_000));
            let _ = (
                conn.poll_udp(out),
                conn.poll_io(),
                conn.poll_notice(),
                conn.poll_event(),
            );
        };
        one(&mut rig, &mut keys, 0, now, &mut out, &mut seen);
        let stats = vinc_tests::measure(|| {
            for i in 1..200 {
                one(&mut rig, &mut keys, i, now + (i as u64) * 1_000, &mut out, &mut seen);
            }
        });
        assert_eq!(stats.count(), 0, "{stats:?}");
        assert_eq!(
            seen,
            200 * packet.len(),
            "every inbound packet reached the endpoint's queue"
        );
    });
}
