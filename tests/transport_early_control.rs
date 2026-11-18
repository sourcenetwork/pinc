//! A stream opened before the handshake ended, past the stream limit the peer then states, waits for the limit with its
//! control frames as it does with its data: a reset or a stop request on it does not reach the peer before the peer's
//! limit covers the stream (the peer would close the connection for a stream beyond its cap), and it leaves once it does.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{Lent, credit_for_streams};
use pinc_transport::stream;

pinc_tests::install_counting_allocator!();

/// The streams the peer admits at once, and so the limit the early streams run into.
const LIMIT: u64 = 4;

fn config(client: bool) -> stream::Config {
    let mut cfg = stream::Config::new(client);
    cfg.max_streams = LIMIT;
    cfg
}

#[test]
fn a_reset_of_a_stream_opened_past_the_peers_limit_leaves_once_the_limit_covers_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&config(false));
        let (mut sa, mut sb) = (
            Store::with_stream(1024, &config(true)),
            Store::with_stream(1024, &config(false)),
        );
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(61, Params::new(5 * MS)));
        net.a.conn.allow_early_streams();
        let ids: Vec<u64> = (0..LIMIT + 2).map(|_| net.a.conn.open_uni().unwrap()).collect();
        for &id in &ids[..LIMIT as usize] {
            net.a.conn.write(id, &pattern(10, id)).unwrap();
            net.a.conn.finish(id).unwrap();
        }
        let late = ids[LIMIT as usize + 1];
        net.a
            .conn
            .reset(
                &mut Lent {
                    spill: &mut net.a.spill,
                },
                late,
                7,
            )
            .unwrap();
        let seen = net.run(net.now + 10 * SEC, |n| {
            n.b.saw(|r| *r == Rec::Reset(late, 7)) || n.b.closed().is_some()
        });
        assert_eq!(net.b.closed(), None, "the peer closed the connection");
        assert!(seen, "the reset never arrived");
        assert_eq!(net.a.closed(), None);
    });
}

#[test]
fn a_stop_request_on_a_stream_opened_past_the_peers_limit_leaves_once_the_limit_covers_it() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&config(false));
        let (mut sa, mut sb) = (
            Store::with_stream(1024, &config(true)),
            Store::with_stream(1024, &config(false)),
        );
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(62, Params::new(5 * MS)));
        net.a.conn.allow_early_streams();
        let ids: Vec<u64> = (0..=LIMIT).map(|_| net.a.conn.open_bi().unwrap()).collect();
        for &id in &ids[..LIMIT as usize] {
            net.a.conn.write(id, &pattern(10, id)).unwrap();
            net.a.conn.finish(id).unwrap();
        }
        let late = ids[LIMIT as usize];
        net.a.conn.stop_sending(late, 9).unwrap();
        // The peer ends its half of each stream that finished, so the stream gives its place back.
        let seen = net.run(net.now + 10 * SEC, |n| {
            for id in n.b.fin.clone() {
                let _ = n.b.conn.finish(id);
            }
            n.b.saw(|r| *r == Rec::Stopped(late, 9)) || n.b.closed().is_some()
        });
        assert_eq!(net.b.closed(), None, "the peer closed the connection");
        assert!(seen, "the stop request never arrived");
        assert_eq!(net.a.closed(), None);
    });
}
