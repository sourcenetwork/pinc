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
use alloc::vec::Vec;
use core::net::SocketAddr;
use core::ops::Range;

use pinc_broadcast::Lane;
use pinc_connect::client::Port;
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use pinc_crypto::IdentityAlg;
use pinc_transport::stream::{NoSource, StreamId};

use super::{Io, Link};
use crate::config::EVENT_CAP;
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::trace::{Body, NodeTrace};

/// The first session id the stub gives a dial, and the first stream id it gives an open.
pub(crate) const DIALED: u64 = 1 << 40;
const OPENED: u64 = 1 << 32;

/// An endpoint that accepts no stream bytes and counts what it was asked.
#[derive(Default)]
pub(crate) struct Stub {
    pub(crate) closes: usize,
    /// The nodes dialed, with the protocol id of each.
    pub(crate) dials: Vec<(pinc_crypto::NodeId, Vec<u8>)>,
    pub(crate) opens: u64,
    /// Streams reset and streams told to stop sending.
    pub(crate) resets: usize,
    pub(crate) stops: usize,
    /// The next urgency setting is refused.
    pub(crate) fail_urgency: bool,
    /// The packets the endpoint has to send, by destination: each goes as one byte.
    pub(crate) transmits: alloc::collections::VecDeque<SocketAddr>,
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
            Command::Connect { node, alpn, .. } => {
                self.dials.push((node, alpn.to_vec()));
                Value::Session(SessionId(DIALED + self.dials.len() as u64 - 1))
            }
            Command::OpenStream { .. } => {
                self.opens += 1;
                Value::Stream(OPENED + self.opens)
            }
            Command::Reset { .. } => {
                self.resets += 1;
                Value::None
            }
            Command::StopSending { .. } => {
                self.stops += 1;
                Value::None
            }
            Command::SetUrgency { .. } if self.fail_urgency => return Err(CommandError::NoSession),
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
    fn peer(&self, _node: &pinc_crypto::NodeId) -> Option<pinc_core::PeerInfo> {
        None
    }
    fn by_conn_id(&self, _cid: &pinc_security::ConnId) -> Option<SessionStats> {
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }
}

impl Ep for Stub {
    fn handle_datagram(&mut self, _now: u64, _local: SocketAddr, _remote: SocketAddr, _buf: &mut [u8]) {}
    fn poll_transmit(&mut self, _now: u64, out: &mut [u8]) -> Option<Transmit> {
        let remote = self.transmits.pop_front()?;
        *out.first_mut()? = 0;
        Some(Transmit {
            local: SocketAddr::from(([192, 0, 2, 9], 4000)),
            remote,
            len: 1,
            segment_size: 1,
        })
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
    fn session_from(&self, _remote: &SocketAddr, _keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
        None
    }
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
    fn add_iface(&mut self, _local: SocketAddr) -> Option<IfaceId> {
        None
    }
    fn iface_event(&mut self, _now: u64, _id: IfaceId, _ev: IfaceEvent) {}
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

fn readable(i: u64) -> Event {
    Event::StreamReadable {
        session: SessionId(i),
        stream: 0,
    }
}

#[test]
fn the_queue_of_command_replies_holds_no_more_than_the_event_cap() {
    let mut io = io();
    io.evq.extend((0..2 * EVENT_CAP as u64).map(readable));
    assert!(
        io.evq.len() <= EVENT_CAP,
        "the queue of command replies grew to {} events",
        io.evq.len()
    );
}

#[test]
fn a_full_queue_of_command_replies_drops_a_recoverable_event_first_and_reports_the_count() {
    let mut io = io();
    io.evq.extend((0..EVENT_CAP as u64).map(readable));
    let closed = |i| Event::Closed {
        session: SessionId(i),
        reason: pinc_core::EndReason::Denied,
    };
    io.evq.extend((0..3).map(closed));
    let mut kept = Vec::new();
    while let Some(e) = io.next_reply() {
        kept.push(e);
    }
    assert_eq!(kept.len(), EVENT_CAP, "the queue stays at its cap");
    assert_eq!(
        kept.iter().filter(|e| matches!(e, Event::Closed { .. })).count(),
        3,
        "an event the application cannot recover stays"
    );
    assert_eq!(io.out.pop(), Some(NodeEvent::Lost { count: 3 }), "the drop is reported");
}

fn host(io: &mut Io<Stub, ()>) -> crate::hosts::MemHost<'_, Stub, ()> {
    crate::hosts::MemHost { io, topics: None }
}

#[test]
fn a_relayed_probe_for_a_member_without_a_session_is_refused() {
    use pinc_membership::session::{Route, Session};
    let mut io = io();
    assert!(!host(&mut io).send(&PEER, Route::Via([9; 32]), b"probe"));
    assert!(io.probes.is_empty());
}

#[test]
fn a_relayed_probe_the_full_queue_cannot_take_is_refused_and_the_queue_stays_bounded() {
    use pinc_membership::session::{Route, Session};
    let mut io = io();
    with_stream(&mut io);
    let mut taken = 0;
    while host(&mut io).send(&PEER, Route::Via([9; 32]), b"probe") {
        taken += 1;
        assert!(taken < 10_000, "the queue never fills");
    }
    assert_eq!(io.probes.len(), taken);
    assert!(!host(&mut io).send(&PEER, Route::Via([9; 32]), b"probe"));
    assert_eq!(io.probes.len(), taken, "a refused probe is not queued");
}

#[test]
fn a_stream_the_full_table_cannot_record_is_reset_and_not_left_open() {
    let mut io = io();
    for i in 0..crate::config::TABLE_MAX as u64 {
        io.register_stream(SESSION, i);
    }
    assert_eq!(io.try_open_stream(SESSION), Err(false));
    assert_eq!(
        (io.ep.opens, io.ep.resets, io.ep.stops),
        (1, 1, 1),
        "the opened stream is ended"
    );
    assert_eq!(io.strm.len(), crate::config::TABLE_MAX);
}

#[test]
fn a_stream_whose_urgency_the_endpoint_refuses_is_reset_and_not_left_open() {
    let mut io = io();
    io.ep.fail_urgency = true;
    assert_eq!(io.try_open_stream_at(SESSION, 3), Err(false));
    assert_eq!(
        (io.ep.opens, io.ep.resets, io.ep.stops),
        (1, 1, 1),
        "the opened stream is ended"
    );
    assert!(io.strm.is_empty());
}
