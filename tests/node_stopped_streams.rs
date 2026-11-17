//! A node that stops request streams one after another, as its layers do when they abandon a stream (a reset of
//! its answer half, a stop for the peer's request, and no further read), gives each stream's place back: the peer
//! can still open a new request after the node stopped more streams than the peer's limit allows at once.
//!
//! The commands are the ones the node's layers issue for an abandoned stream, sent to a real endpoint; the layers
//! themselves are not involved because none of them abandons streams on demand in a count above the limit.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::similar_names
)]

use vinc_core::{Answer, Command, CommandError, Event, Query, Role, SessionId, Value};
use vinc_tests::*;
use vinc_transport::stream::NoSource;

const S: u64 = SEC_NS;
/// More requests than the default limit of 100 streams a peer may open.
const REQUESTS: u32 = 150;

fn cmd(net: &mut CoreNet, n: usize, c: Command<'_, NoSource>) -> Result<Value, CommandError> {
    let now = net.now;
    net.nodes[n].cmd(now, c).map(|r| r.value)
}

/// Open a stream, waiting for the peer's stream credit while it has none.
fn open(net: &mut CoreNet, n: usize, session: SessionId, k: u32) -> u64 {
    for _ in 0..30 {
        match cmd(net, n, Command::OpenStream { session, bidi: true }) {
            Ok(Value::Stream(id)) => return id,
            Ok(other) => panic!("{other:?}"),
            Err(_) => net.run_for(S / 10),
        }
    }
    panic!("request {k} could not be opened: the peer's stopped streams kept their places");
}

#[test]
fn a_peer_can_still_send_a_request_after_the_node_stopped_more_streams_than_its_limit() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.nodes[b].auto_read = false;
        let request = b"request";
        for k in 0..REQUESTS {
            let stream = open(&mut net, a, sa, k);
            cmd(
                &mut net,
                a,
                Command::Write {
                    session: sa,
                    stream,
                    data: request,
                },
            )
            .unwrap();
            cmd(&mut net, a, Command::Finish { session: sa, stream }).unwrap();
            let heard = |n: &mut CoreNet| {
                n.nodes[b]
                    .events
                    .iter()
                    .any(|(_, e)| matches!(e, Event::StreamReadable { stream: s, .. } if *s == stream))
            };
            let t = net.now + 5 * S;
            assert!(net.run(t, |n| heard(n)), "request {k} never reached the node");
            if k + 1 < REQUESTS {
                cmd(
                    &mut net,
                    b,
                    Command::Reset {
                        session: sb,
                        stream,
                        error: 4,
                    },
                )
                .unwrap();
                cmd(
                    &mut net,
                    b,
                    Command::StopSending {
                        session: sb,
                        stream,
                        error: 4,
                    },
                )
                .unwrap();
                // The client hears the reset of its answer half and reads it to its end, as its layers do.
                let t = net.now + 5 * S;
                let reset = |n: &mut CoreNet| {
                    n.nodes[a]
                        .events
                        .iter()
                        .any(|(_, e)| matches!(e, Event::StreamReset { stream: s, .. } if *s == stream))
                };
                assert!(net.run(t, |n| reset(n)), "request {k} was never reset at the client");
                let now = net.now;
                net.nodes[a].read_stream(now, sa, stream);
            } else {
                match net.nodes[b].ep.query(Query::Read { session: sb, stream }) {
                    Answer::Chunk(c) => assert_eq!(c, request),
                    other => panic!("the last request cannot be read: {other:?}"),
                }
            }
        }
    });
}
