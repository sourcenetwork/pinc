//! A scripted node for stream carriers: it connects, writes and closes when commands tell it to, and reports every
//! stream event and every record it receives.

use std::collections::VecDeque;
use std::net::SocketAddr;

use crate::Time;
use crate::node::{IfaceEvent, Node, StreamEvent, StreamId, StreamKind, StreamOp, Transmit};

/// A command to a [`StreamProbe`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StreamCmd {
    /// Open a connection.
    Connect {
        /// Source address.
        local: SocketAddr,
        /// Destination address.
        remote: SocketAddr,
        /// Carrier kind.
        kind: StreamKind,
        /// Simultaneous open.
        simultaneous: bool,
    },
    /// Write one record.
    Send {
        /// The stream.
        stream: StreamId,
        /// The record.
        data: Vec<u8>,
    },
    /// Write `count` records of `len` bytes each, the bytes of record `i` being `(i + j) as u8` at offset `j`.
    SendMany {
        /// The stream.
        stream: StreamId,
        /// Number of records.
        count: usize,
        /// Bytes per record.
        len: usize,
    },
    /// Close the stream.
    Close(StreamId),
    /// Send a datagram (for tests that mix datagrams and streams).
    Datagram {
        /// Source address.
        local: SocketAddr,
        /// Destination address.
        remote: SocketAddr,
        /// The bytes.
        data: Vec<u8>,
    },
}

/// An event of a [`StreamProbe`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamProbeEvent {
    /// A stream event.
    Stream(StreamEvent),
    /// A record arrived (its bytes are in [`StreamProbe::records`]).
    Record {
        /// The stream.
        stream: StreamId,
        /// Its length.
        len: usize,
    },
    /// A datagram arrived.
    Datagram {
        /// Its length.
        len: usize,
    },
}

/// The scripted stream node.
#[derive(Default)]
pub struct StreamProbe {
    ops: VecDeque<(StreamOp, Vec<u8>)>,
    datagrams: VecDeque<(SocketAddr, SocketAddr, Vec<u8>)>,
    events: VecDeque<StreamProbeEvent>,
    /// Every record received, with its arrival time and stream.
    pub records: Vec<(Time, StreamId, Vec<u8>)>,
    /// Every stream event, with its time.
    pub stream_events: Vec<(Time, StreamEvent)>,
}

impl StreamProbe {
    /// A node with nothing to do.
    pub fn new() -> Self {
        Self::default()
    }

    /// The handles of the streams this node has been told about with [`StreamEvent::Pending`] or
    /// [`StreamEvent::Opened`], in order.
    pub fn handles(&self) -> Vec<StreamId> {
        self.stream_events
            .iter()
            .filter_map(|(_, e)| match e {
                StreamEvent::Pending { stream, .. } => Some(*stream),
                StreamEvent::Opened { stream, .. } if !self.has_pending(*stream) => Some(*stream),
                _ => None,
            })
            .collect()
    }

    fn has_pending(&self, s: StreamId) -> bool {
        self.stream_events
            .iter()
            .any(|(_, e)| matches!(e, StreamEvent::Pending { stream, .. } if *stream == s))
    }

    /// The time of the first event matching `f`.
    pub fn when(&self, f: impl Fn(&StreamEvent) -> bool) -> Option<Time> {
        self.stream_events.iter().find(|(_, e)| f(e)).map(|(t, _)| *t)
    }

    /// All received bytes of `stream`, joined in arrival order.
    pub fn received(&self, stream: StreamId) -> Vec<u8> {
        self.records
            .iter()
            .filter(|(_, s, _)| *s == stream)
            .flat_map(|(_, _, d)| d.iter().copied())
            .collect()
    }
}

impl Node for StreamProbe {
    type Cmd = StreamCmd;
    type Event = StreamProbeEvent;

    fn handle_datagram(&mut self, _now: Time, _local: SocketAddr, _remote: SocketAddr, data: &mut [u8]) {
        self.events.push_back(StreamProbeEvent::Datagram { len: data.len() });
    }

    fn poll_transmit(&mut self, _now: Time, buf: &mut [u8]) -> Option<Transmit> {
        let (local, remote, data) = self.datagrams.pop_front()?;
        buf[..data.len()].copy_from_slice(&data);
        Some(Transmit {
            local,
            remote,
            len: data.len(),
            send_at: None,
        })
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        None
    }

    fn handle_timeout(&mut self, _now: Time) {}

    fn command(&mut self, _now: Time, cmd: StreamCmd) {
        match cmd {
            StreamCmd::Connect {
                local,
                remote,
                kind,
                simultaneous,
            } => self.ops.push_back((
                StreamOp::Connect {
                    local,
                    remote,
                    kind,
                    simultaneous,
                },
                Vec::new(),
            )),
            StreamCmd::Send { stream, data } => self.ops.push_back((
                StreamOp::Write {
                    stream,
                    len: data.len(),
                    send_at: None,
                },
                data,
            )),
            StreamCmd::SendMany { stream, count, len } => {
                for i in 0..count {
                    let data: Vec<u8> = (0..len).map(|j| (i + j) as u8).collect();
                    self.ops.push_back((
                        StreamOp::Write {
                            stream,
                            len,
                            send_at: None,
                        },
                        data,
                    ));
                }
            }
            StreamCmd::Close(stream) => self.ops.push_back((StreamOp::Close { stream }, Vec::new())),
            StreamCmd::Datagram { local, remote, data } => self.datagrams.push_back((local, remote, data)),
        }
    }

    fn poll_event(&mut self) -> Option<StreamProbeEvent> {
        self.events.pop_front()
    }

    fn crash(&mut self, _now: Time) -> Vec<u8> {
        self.ops.clear();
        self.datagrams.clear();
        Vec::new()
    }

    fn restart(&mut self, _now: Time, _persisted: &[u8]) {}

    fn suspend(&mut self, _now: Time) {}

    fn resume(&mut self, _now: Time) {}

    fn iface_event(&mut self, _now: Time, _event: IfaceEvent) {}

    fn poll_stream(&mut self, _now: Time, buf: &mut [u8]) -> Option<StreamOp> {
        let (op, data) = self.ops.pop_front()?;
        buf[..data.len()].copy_from_slice(&data);
        Some(op)
    }

    fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        self.stream_events.push((now, event));
        self.events.push_back(StreamProbeEvent::Stream(event));
    }

    fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        self.records.push((now, stream, data.to_vec()));
        self.events.push_back(StreamProbeEvent::Record {
            stream,
            len: data.len(),
        });
    }
}
