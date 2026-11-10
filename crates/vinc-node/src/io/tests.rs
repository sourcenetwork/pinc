//! Unit tests of the stream hand-off of [`Io`] over a stub endpoint: what a main-lane, a reply-lane and a membership
//! frame do with no session, with a session and no write stream, and with a full backlog.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::assert_is_empty,
    missing_docs,
    reason = "tests assert freely"
)]

use alloc::collections::BTreeMap;
use alloc::vec;
use core::net::SocketAddr;
use core::ops::Range;

use vinc_broadcast::Lane;
use vinc_connect::client::Port;
use vinc_core::{
    Command, CommandError, Event, Events, NodeStats, Reply, SendState, SessionId, SessionStats, TraceRecord, Transmit,
    Value,
};
use vinc_crypto::IdentityAlg;
use vinc_transport::stream::{NoSource, StreamId};

use super::{Io, Link};
use crate::ep::Ep;
use crate::trace::{Body, NodeTrace};

/// An endpoint that accepts no stream bytes and counts what it was asked.
#[derive(Default)]
struct Stub {
    closes: usize,
}

impl Port for Stub {
    type Src = NoSource;
    fn command(&mut self, _now: u64, cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let value = match cmd {
            Command::Write { .. } => Value::Written(0),
            Command::Close { .. } => {
                self.closes += 1;
                Value::None
            }
            _ => Value::None,
        };
        Ok(Reply {
            value,
            events: Events::default(),
        })
    }
    fn stats(&self, _session: SessionId) -> Option<SessionStats> {
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; vinc_core::REACH_BODY_MAX]) -> usize {
        0
    }
}

impl Ep for Stub {
    fn handle_datagram(&mut self, _now: u64, _local: SocketAddr, _remote: SocketAddr, _buf: &mut [u8]) {}
    fn poll_transmit(&mut self, _now: u64, _out: &mut [u8]) -> Option<Transmit> {
        None
    }
    fn poll_event(&mut self) -> Option<Event> {
        None
    }
    fn poll_timeout(&self) -> Option<u64> {
        None
    }
    fn handle_timeout(&mut self, _now: u64) {}
    fn register_alpn(&mut self, _alpn: &[u8]) -> bool {
        true
    }
    fn read_chunk(&self, _session: SessionId, _stream: StreamId) -> Option<&[u8]> {
        None
    }
    fn read_at(&self, _session: SessionId, _stream: StreamId, _offset: u64) -> Option<&[u8]> {
        None
    }
    fn stored_after(&self, _session: SessionId, _stream: StreamId, _from: u64) -> Option<Range<u64>> {
        None
    }
    fn send_state(&self, _session: SessionId, _stream: StreamId) -> Option<SendState> {
        None
    }
    fn in_flight(&self, _session: SessionId) -> Option<u64> {
        None
    }
    fn read_extension(&mut self, _out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
        Ok(None)
    }
    fn session_at(&self, _n: usize) -> Option<SessionStats> {
        None
    }
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
}

const PEER: [u8; 32] = [7; 32];
const SESSION: SessionId = SessionId(1);
const STREAM: StreamId = 4;
/// The least backlog cap: twice a 4 KiB frame is below 1 MiB.
const CAP: usize = 1 << 20;

fn io() -> Io<Stub, ()> {
    Io::new(
        Stub::default(),
        (),
        [1; 32],
        IdentityAlg::Ed25519,
        true,
        b"t",
        1,
        0,
        0,
        vec![],
        BTreeMap::new(),
        4096,
        true,
    )
}

/// A session of `PEER` with a write stream.
fn with_stream(io: &mut Io<Stub, ()>) {
    io.register_stream(SESSION, STREAM);
    io.links.insert(
        PEER,
        Link {
            conn: Some(SESSION),
            out: Some(STREAM),
            fan: None,
            opened: 0,
        },
    );
}

#[test]
fn a_reply_to_a_peer_without_a_session_is_dropped_and_nothing_is_dialed() {
    let mut io = io();
    assert!(!io.send_stream(&PEER, Lane::Reply, b"frame"));
    assert!(io.dials.is_empty());
    assert!(io.queue.is_empty());
}

#[test]
fn a_main_lane_frame_to_a_peer_without_a_session_is_queued_and_asks_for_a_dial() {
    let mut io = io();
    assert!(io.send_stream(&PEER, Lane::Main, b"frame"));
    assert_eq!(io.dials, [PEER]);
    assert_eq!(io.queue.get(&PEER).map(|(q, _)| q.len()), Some(1));
}

#[test]
fn a_session_without_a_write_stream_queues_main_lane_frames_and_drops_replies() {
    let mut io = io();
    io.links.insert(
        PEER,
        Link {
            conn: Some(SESSION),
            out: None,
            fan: None,
            opened: 0,
        },
    );
    assert!(!io.send_stream(&PEER, Lane::Reply, b"frame"));
    assert!(io.queue.is_empty());
    assert!(io.send_stream(&PEER, Lane::Main, b"frame"));
    assert_eq!(io.queue.get(&PEER).map(|(q, _)| q.len()), Some(1));
}

#[test]
fn a_reply_to_a_peer_with_a_write_stream_is_written() {
    let mut io = io();
    with_stream(&mut io);
    assert!(io.send_stream(&PEER, Lane::Reply, b"frame"));
    assert!(io.queue.is_empty());
}

/// Fill the backlog of the stream with frames until `room` bytes are left.
fn fill(io: &mut Io<Stub, ()>, room: usize) {
    let frame = [0u8; 4096];
    while io.strm.get(&(SESSION, STREAM)).unwrap().pending() + frame.len() <= CAP - room {
        assert!(io.send_stream(&PEER, Lane::Main, &frame));
    }
    let left = CAP - io.strm.get(&(SESSION, STREAM)).unwrap().pending();
    if left > room {
        assert!(io.send_stream(&PEER, Lane::Main, &vec![0u8; left - room]));
    }
}

#[test]
fn a_membership_frame_the_full_backlog_refuses_closes_the_session_once_and_is_counted() {
    let mut io = io();
    with_stream(&mut io);
    fill(&mut io, 10);
    // 10 bytes of room: a 24 byte frame is refused and the session is closed.
    assert!(!io.send_membership(&PEER, Lane::Main, &[1u8; 24]));
    assert_eq!(io.ep.closes, 1);
    let mut counted = 0;
    while let Some(item) = io.tq.pop(0) {
        counted += usize::from(matches!(item.body, Body::Node(NodeTrace::BacklogClosed { .. })));
    }
    assert_eq!(counted, 1);
}

#[test]
fn a_membership_frame_that_fits_is_written_and_closes_nothing() {
    let mut io = io();
    with_stream(&mut io);
    fill(&mut io, 100);
    assert!(io.send_membership(&PEER, Lane::Main, &[1u8; 24]));
    assert_eq!(io.ep.closes, 0);
}

#[test]
fn a_membership_frame_for_a_peer_without_a_session_closes_nothing() {
    let mut io = io();
    assert!(io.send_membership(&PEER, Lane::Main, &[1u8; 24]), "queued for a dial");
    assert!(
        !io.send_membership(&PEER, Lane::Reply, &[1u8; 24]),
        "a reply is dropped"
    );
    assert_eq!(io.ep.closes, 0);
}
