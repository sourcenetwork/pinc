//! Reproducing test of a stream whose end is reported again: the duplicate end the world suite reports as "bytes or
//! an end after the end of a stream" (`EPHYRA_REPLAY=11:148` of `world`). It fails on the unmodified code. The driver
//! is `core_harness`: real endpoints on one scripted link whose faults the test sets.

mod core_harness;

use core_harness::{ALPN_A, HostCfg, MS, Net, Reply2, SEC, big_stack};
use pinc_core::{Command, Event, Value};

/// Bug: a STREAM frame sent again (its acknowledgement was lost) that reaches a stream whose end the application has
/// already read is reported as `StreamReadable`, though it brings nothing to read. A host that reads the stream on
/// that event finds its end again (`Consume` of 0 bytes answers `Finished` while the stream is kept for its send
/// half) and reports the end twice: the simulator's node driver does (`pinc-sim` `suite/node/events.rs`
/// `read_stream`), and its layers then see bytes or an end after the end.
///
/// Expected: `StreamReadable` means "A stream has bytes to read" (crates/pinc-transport/src/conn/event.rs:154), and
/// the suite's layer event `StreamData` means "Bytes arrived on a stream (already consumed); `fin` says the peer
/// finished it with these bytes" (crates/pinc-sim/src/suite/proto/host.rs:91): once the end was read, a copy of a
/// frame already received gives no event.
///
/// Actual: see the failing output; the copy of the last frame raises `StreamReadable` after the end was consumed.
///
/// Suspected fault: `on_packet` pushes `Ev::Readable` for every STREAM frame, whatever it changed
/// (crates/pinc-transport/src/conn/recv.rs:599), and `read_stream` in the simulator's node driver reports `fin` on
/// every `Finished` it reads, not once (crates/pinc-sim/src/suite/node/events.rs:468).
///
/// Who: no adversary: any lost acknowledgement of the last packet of a stream, at any loss rate. The peer itself can
/// also send the frame again at will.
#[test]
fn a_frame_sent_again_after_the_end_was_read_raises_no_readable_event() {
    big_stack(|| {
        let mut net = Net::new(11);
        let (a, b) = (net.add(1, HostCfg::default()), net.add(2, HostCfg::default()));
        net.hosts[a].auto_read = true;
        let (sb, sa) = net.connect_pair(b, a, ALPN_A).expect("host 1 reaches host 0");
        net.run_for(SEC);
        let now = net.now;
        let Ok(Reply2 { value: Value::Stream(st) }) = net.hosts[b].cmd(now, Command::OpenStream { session: sb, bidi: true })
        else {
            panic!("no stream on an established session")
        };
        net.hosts[b].write(now, sb, st, vec![7; 100], true);
        assert!(net.run(now + 2 * SEC, |n| n.hosts[a].fin.contains(&(sa, st))), "the end of the stream never arrived");
        // The acknowledgement of the last packet is lost: everything is dropped for 40 ms, until host 1 sends it again.
        let end_read = net.now;
        net.faults.cut = true;
        net.run_for(40 * MS);
        net.faults.cut = false;
        net.run_for(3 * SEC);
        let sent_again = net.tapped.iter().filter(|(t, h, ..)| *t > end_read + 40 * MS && *h == b).count();
        let late: Vec<u64> = net.hosts[a]
            .events
            .iter()
            .filter(|(t, e)| *t > end_read && matches!(e, Event::StreamReadable { session, stream } if *session == sa && *stream == st))
            .map(|(t, _)| (t - end_read) / MS)
            .collect();
        eprintln!(
            "read {} bytes and the end; host 1 sent {sent_again} datagrams after the cut; StreamReadable after the end \
             at {late:?} ms",
            net.hosts[a].read.get(&(sa, st)).map_or(0, Vec::len)
        );
        assert!(late.is_empty(), "the stream was reported readable after its end was read, at {late:?} ms after it");
    });
}
