#![allow(clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]
use vinc_core::{Command, Role, Value};
use vinc_tests::*;

/// One session with 30000 bytes to send; the host polls with `first` bytes of buffer, then with a large one.
/// Returns what the second call gave, the queue after the first call, and whether anything left at the second call.
fn run(first: usize) -> (bool, Vec<usize>) {
    big_stack(move || {
        let mut net = CoreNet::new(10 * MS_NS);
        let h = net.add(1);
        let p1 = net.add(2);
        let (s1, _) = net.connect_pair(h, p1, ALPN_A, Role::Other);
        net.run_for(2 * SEC_NS);
        let now = net.now;
        let data = vec![7u8; 30_000];
        let Value::Stream(id) = net.nodes[h]
            .cmd(now, Command::OpenStream { session: s1, bidi: true })
            .unwrap()
            .value
        else {
            panic!()
        };
        net.nodes[h]
            .cmd(now, Command::Write { session: s1, stream: id, data: &data })
            .unwrap();
        let ep = &mut net.nodes[h].ep;
        let mut small = vec![0u8; first];
        assert!(ep.poll_transmit(now, &mut small).is_some());
        let q: Vec<_> = (0..9).map_while(|k| ep.send_queue_at(0, k)).map(|e| e.slot).collect();
        let mut big = vec![0u8; 65_536];
        (ep.poll_transmit(now, &mut big).is_some(), q)
    })
}

#[test]
fn a_tight_buffer_does_not_drop_a_session_with_data() {
    // control: a roomy buffer, the second call sends
    assert!(run(65_536).0);
    // the first datagram is 1452 bytes; a buffer 3 bytes longer leaves no room for a packet of the batch
    let (second, queue) = run(1452 + 3);
    assert!(second, "poll_transmit returned None with 30000 bytes waiting; the session left the queue: {queue:?}");
}
