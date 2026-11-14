//! The send queue keeps a session with data on it when the buffer left after the first datagram of a batch is too
//! short for another packet: the next call, with a large buffer, sends.
#![allow(clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use vinc_core::{Command, Role, Value};
use vinc_tests::*;

/// One session with 30000 bytes to send; the host polls with `first` bytes of buffer, then with a large one.
/// Returns the length of the first call's datagram and whether the second call sent anything.
fn run(first: usize) -> (usize, bool) {
    big_stack(move || {
        let mut net = CoreNet::new(10 * MS_NS);
        let h = net.add(1);
        let p1 = net.add(2);
        let (s1, _) = net.connect_pair(h, p1, ALPN_A, Role::Other);
        net.run_for(2 * SEC_NS);
        let now = net.now;
        let data = vec![7u8; 30_000];
        let Value::Stream(id) = net.nodes[h]
            .cmd(
                now,
                Command::OpenStream {
                    session: s1,
                    bidi: true,
                },
            )
            .unwrap()
            .value
        else {
            panic!("no stream")
        };
        net.nodes[h]
            .cmd(
                now,
                Command::Write {
                    session: s1,
                    stream: id,
                    data: &data,
                },
            )
            .unwrap();
        let ep = &mut net.nodes[h].ep;
        let mut small = vec![0u8; first];
        let sent = ep.poll_transmit(now, &mut small).unwrap().len;
        let mut big = vec![0u8; 65_536];
        (sent, ep.poll_transmit(now, &mut big).is_some())
    })
}

#[test]
fn a_tight_buffer_does_not_drop_a_session_with_data() {
    // control: a roomy buffer, the second call sends
    assert!(run(65_536).1);
    // the first datagram is 1452 bytes; a buffer a few bytes longer leaves no room for a packet of the batch
    for extra in [1, 3, 20, 40] {
        let (first, second) = run(1452 + extra);
        assert_eq!(first, 1452, "the first datagram is not the size this test is built on");
        assert!(
            second,
            "a buffer {extra} bytes longer than the first datagram: the next call sent nothing with 30000 bytes waiting"
        );
    }
}
