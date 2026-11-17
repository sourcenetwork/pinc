//! How a stream ends at the connection: data for a stream nobody can read raises no readable event (a reset is heard
//! for every stream the table holds), and an error code no frame can carry is refused where it enters without
//! stalling the other streams.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{Event, PathId};
use vinc_transport::frame::Frame;
use vinc_transport::stream::StreamError;
use vinc_wire::Writer;

/// A connected pair; `f` runs on it with the server's startup events already read.
fn pair(f: impl FnOnce(&mut Net<'_, '_, RING>) + Send + 'static) {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::with_chunks(false, 20_000));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        let t = net.now + SEC;
        net.run(t, |_| false);
        while net.b.conn.poll_event().is_some() {}
        f(&mut net);
    });
}

/// Hand the server a packet of `frames` as packet number `pn`, and return the events it raised.
fn deliver(net: &mut Net<'_, '_, RING>, pn: u64, frames: &[Frame<'_>]) -> Vec<(&'static str, u64)> {
    let mut buf = vec![0u8; 2000];
    let mut w = Writer::new(&mut buf);
    for f in frames {
        f.write(&mut w).unwrap();
    }
    let n = w.written().len();
    let now = net.now;
    net.b
        .with_env(now, |c, env| c.inject_payload(env, PathId(1), now, pn, &buf[..n]))
        .unwrap();
    let mut seen = Vec::new();
    while let Some(e) = net.b.conn.poll_event() {
        match e {
            Event::StreamReadable(id) => seen.push(("readable", id)),
            Event::StreamReset { id, .. } => seen.push(("reset", id)),
            _ => {}
        }
    }
    seen
}

fn data(id: u64, offset: u64, fin: bool, bytes: &[u8]) -> Frame<'_> {
    Frame::Stream {
        id,
        offset,
        fin,
        data: bytes,
        implicit_len: false,
    }
}

fn readable(events: &[(&str, u64)], id: u64) -> bool {
    events.contains(&("readable", id))
}

fn reset_seen(events: &[(&str, u64)], id: u64) -> bool {
    events.contains(&("reset", id))
}

fn reset(id: u64, final_size: u64) -> Frame<'static> {
    Frame::ResetStream {
        id,
        error: 1,
        final_size,
    }
}

#[test]
fn a_frame_for_a_stream_that_ended_and_was_freed_raises_no_event() {
    pair(|net| {
        // Stream 2 is a client unidirectional stream: it has no send half, so reading it to its end frees the slot.
        let first = deliver(net, 7000, &[data(2, 0, true, b"hi")]);
        assert!(readable(&first, 2), "the first frame of a live stream raises no event");
        let now = net.now;
        net.b.read_stream(now, 2);
        assert!(net.b.fin.contains(&2) && net.b.conn.read_chunk(2).is_none());
        let again = deliver(net, 7001, &[data(2, 0, true, b"hi")]);
        assert!(
            !readable(&again, 2),
            "a frame for a freed stream raised a readable event: {again:?}"
        );
        let late = deliver(net, 7002, &[reset(2, 2)]);
        assert!(
            !reset_seen(&late, 2),
            "a reset for a freed stream raised an event: {late:?}"
        );
    });
}

#[test]
fn data_for_a_half_the_application_stopped_raises_no_readable_event_and_its_reset_is_heard() {
    pair(|net| {
        let first = deliver(net, 7000, &[data(6, 0, false, b"abc")]);
        assert!(readable(&first, 6));
        net.b.conn.stop_sending(6, 5).unwrap();
        let more = deliver(net, 7001, &[data(6, 3, false, b"def")]);
        assert!(
            !readable(&more, 6),
            "data for a stopped half raised a readable event: {more:?}"
        );
        let end = deliver(net, 7002, &[reset(6, 6)]);
        assert_eq!(
            end.iter().filter(|e| **e == ("reset", 6)).count(),
            1,
            "the stopper did not hear the reset once: {end:?}"
        );
        let again = deliver(net, 7003, &[reset(6, 6)]);
        assert!(again.is_empty(), "a second reset raised an event: {again:?}");
    });
}

#[test]
fn a_frame_for_a_live_half_still_raises_its_event() {
    pair(|net| {
        let first = deliver(net, 7000, &[data(10, 0, false, b"abc")]);
        assert!(readable(&first, 10));
        let more = deliver(net, 7001, &[data(10, 3, false, b"def")]);
        assert!(readable(&more, 10), "data for a live half raised no readable event");
        let end = deliver(net, 7002, &[reset(10, 6)]);
        assert!(reset_seen(&end, 10), "a reset for a live half raised no event");
    });
}

#[test]
fn a_code_no_frame_can_carry_is_refused_and_the_other_streams_still_send() {
    pair(|net| {
        let bad = net.a.conn.open_bi().unwrap();
        let other = net.a.conn.open_bi().unwrap();
        let again = net.a.conn.open_bi().unwrap();
        for id in [bad, other, again] {
            net.a.conn.write(id, b"request").unwrap();
        }
        let refused = net.a.conn.reset(bad, 1 << 63);
        let t = net.now + SEC;
        net.run(t, |_| false);
        net.a.conn.reset(other, 5).unwrap();
        let t = net.now + 2 * SEC;
        net.run(t, |n| n.b.saw(|r| matches!(r, Rec::Reset(i, 5) if *i == other)));
        assert!(
            net.b.saw(|r| matches!(r, Rec::Reset(i, 5) if *i == other)),
            "the reset of another stream never left after a code no frame can carry ({refused:?})"
        );
        assert_eq!(refused, Err(StreamError::BadCode));
        // The refused call changed nothing: the stream takes a valid reset afterwards.
        net.a.conn.reset(bad, 3).unwrap();
        let t = net.now + 2 * SEC;
        net.run(t, |n| n.b.saw(|r| matches!(r, Rec::Reset(i, 3) if *i == bad)));
        assert!(net.b.saw(|r| matches!(r, Rec::Reset(i, 3) if *i == bad)));
        assert_eq!(net.a.conn.stop_sending(again, u64::MAX), Err(StreamError::BadCode));
    });
}
