//! How a stream ends at the endpoint: `finished` in the send state, and a code that cannot be encoded is refused.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::similar_names
)]

use vinc_core::{Answer, Command, CommandError, Query, Role, SendState, SessionId, Value};
use vinc_tests::*;
use vinc_transport::stream::StreamError;

const S: u64 = SEC_NS;

fn state(net: &CoreNet, n: usize, session: SessionId, stream: u64) -> SendState {
    match net.nodes[n].ep.query(Query::SendState { session, stream }) {
        Answer::SendState(s) => s,
        other => panic!("{other:?}"),
    }
}

fn cmd(net: &mut CoreNet, n: usize, c: Command<'_, vinc_transport::stream::NoSource>) -> Result<Value, CommandError> {
    let now = net.now;
    net.nodes[n].cmd(now, c).map(|r| r.value)
}

fn open(net: &mut CoreNet, n: usize, session: SessionId, bidi: bool) -> u64 {
    match cmd(net, n, Command::OpenStream { session, bidi }).unwrap() {
        Value::Stream(id) => id,
        other => panic!("{other:?}"),
    }
}

#[test]
fn the_send_state_says_whether_the_end_is_fixed() {
    big_stack(|| {
        let mut net = CoreNet::new(20 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (open_id, finished, reset) = (
            open(&mut net, a, sa, true),
            open(&mut net, a, sa, true),
            open(&mut net, a, sa, false),
        );
        for stream in [open_id, finished, reset] {
            cmd(
                &mut net,
                a,
                Command::Write {
                    session: sa,
                    stream,
                    data: b"x",
                },
            )
            .unwrap();
        }
        cmd(
            &mut net,
            a,
            Command::Finish {
                session: sa,
                stream: finished,
            },
        )
        .unwrap();
        cmd(
            &mut net,
            a,
            Command::Reset {
                session: sa,
                stream: reset,
                error: 4,
            },
        )
        .unwrap();
        assert!(
            !state(&net, a, sa, open_id).finished,
            "a stream with no end is finished"
        );
        assert!(state(&net, a, sa, finished).finished);
        assert!(
            !state(&net, a, sa, reset).finished,
            "a reset with no finish counts as finished"
        );
        // The one-way stream has no receive half: once its reset is acknowledged it is gone, and a stream that is
        // gone counts as finished. The two-way streams stay while their receive halves are open.
        net.run_for(S);
        assert!(!state(&net, a, sa, open_id).finished);
        assert!(state(&net, a, sa, reset).finished);
        assert!(state(&net, a, sa, 4000).finished);
    });
}

#[test]
fn a_code_that_cannot_be_encoded_is_refused_at_the_command() {
    big_stack(|| {
        let mut net = CoreNet::new(20 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let stream = open(&mut net, a, sa, true);
        for error in [1u64 << 63, u64::MAX] {
            assert_eq!(
                cmd(&mut net, a, Command::Close { session: sa, error }).err(),
                Some(CommandError::BadCode)
            );
            assert_eq!(
                cmd(
                    &mut net,
                    a,
                    Command::Reset {
                        session: sa,
                        stream,
                        error
                    }
                )
                .err(),
                Some(CommandError::Stream(StreamError::BadCode))
            );
            assert_eq!(
                cmd(
                    &mut net,
                    a,
                    Command::StopSending {
                        session: sa,
                        stream,
                        error
                    }
                )
                .err(),
                Some(CommandError::Stream(StreamError::BadCode))
            );
        }
        // The session is still open after the refused close: the largest code closes it.
        let top = (1u64 << 63) - 1;
        cmd(
            &mut net,
            a,
            Command::Close {
                session: sa,
                error: top,
            },
        )
        .unwrap();
        net.run_for(S);
        assert!(net.nodes[b].saw(|e| matches!(e, vinc_core::Event::Closed { .. })));
    });
}
