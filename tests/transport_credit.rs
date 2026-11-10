//! Stream credit end to end: an opener that opens far more streams than the receiver's pool holds waits for the
//! credit instead of sending them, every stream arrives with its bytes, and the receiver holds none back.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::credit_for_streams;
use vinc_transport::stream;

/// Streams the opener wants open in all; the receiver's pool holds the windows of a few.
const STREAMS: usize = 60;
/// Bytes on each.
const LEN: usize = 3000;

fn config(client: bool) -> stream::Config {
    let mut cfg = stream::Config::new(client);
    cfg.initial_stream_window = 64 * 1024;
    cfg.max_stream_window = 64 * 1024;
    cfg
}

#[test]
fn an_opener_far_beyond_the_credit_delivers_every_stream_and_the_receiver_holds_none_back() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&config(false));
        // The receiver's pool is 16 chunks: windows of 4 chunks, so it tells the opener it admits two to start.
        let (mut sa, mut sb) = (
            Store::<RING>::sized(256, &config(true)),
            Store::<RING>::sized(16, &config(false)),
        );
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(41, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
        net.run(net.now + SEC, |_| false);
        let first = net.a.conn.peer_credit().max_streams;
        assert!(
            first > 0 && usize::from(first) < STREAMS,
            "the handshake credit is {first}"
        );

        let mut opened: Vec<u64> = Vec::new();
        let mut waited = 0usize;
        let done = net.run(net.now + 600 * SEC, |n| {
            while opened.len() < STREAMS {
                let ready = n.a.conn.open_ready(false);
                match n.a.conn.open_uni() {
                    Ok(id) => {
                        assert_eq!(ready, Ok(()), "open_ready said no to an open that worked");
                        let k = opened.len();
                        let data = pattern(LEN, 1000 + k as u64);
                        assert_eq!(n.a.conn.write(id, &data).unwrap(), LEN);
                        n.a.conn.finish(id).unwrap();
                        opened.push(id);
                    }
                    Err(e) => {
                        assert_eq!(ready, Err(e), "open_ready disagrees with the open");
                        waited += 1;
                        break;
                    }
                }
            }
            opened.len() == STREAMS && opened.iter().all(|id| n.b.fin.contains(id))
        });
        assert!(done, "opened {} of {STREAMS}", opened.len());
        assert!(
            waited > 0,
            "the opener never had to wait for credit: the test does not exercise it"
        );
        for (k, id) in opened.iter().enumerate() {
            assert!(net.b.read[id] == pattern(LEN, 1000 + k as u64), "stream {id} differs");
        }
        assert_eq!(net.b.conn.stats().held_back, 0, "the receiver held a stream back");
    });
}
