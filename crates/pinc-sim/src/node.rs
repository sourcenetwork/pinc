//! The contract between the engine and a node under test.
//!
//! The engine is generic over one [`Node`] type (an enum when a scenario mixes kinds), so no call is dynamic.
//! A node never reads a clock or a socket: time, datagrams and commands go in; datagrams, timers and events come out.

use std::fmt::Debug;
use std::net::{IpAddr, SocketAddr};

use crate::{Clock, Time};

/// One datagram a node wants sent: the bytes are the first `len` bytes of the buffer given to `poll_transmit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Transmit {
    /// The source address; its IP selects the interface the datagram leaves from.
    pub local: SocketAddr,
    /// The destination address.
    pub remote: SocketAddr,
    /// How many bytes of the buffer are the datagram.
    pub len: usize,
    /// The true time before which the datagram must not leave (the node's own pacing); `None` sends it at once.
    pub send_at: Option<Time>,
}

/// The handle the simulator gives a stream endpoint (one end of a TCP or WebSocket carrier). A node learns the
/// handle of an end it opens from [`StreamEvent::Pending`], and the handle of an end it accepts from
/// [`StreamEvent::Opened`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StreamId(pub u32);

/// What a stream carries: plain TCP, or a WebSocket over TLS over TCP (three round trips to set up).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamKind {
    /// Records go straight onto the TCP byte stream.
    Tcp,
    /// Records are WebSocket frames inside TLS records; the TLS and upgrade exchanges precede the first record.
    Ws,
}

/// One request a node makes of its stream endpoints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamOp {
    /// Open a connection from `local` (its IP selects the interface) to `remote`. The simulator answers with
    /// [`StreamEvent::Pending`] at once and [`StreamEvent::Opened`] or [`StreamEvent::Failed`] later.
    /// `simultaneous` asks for a simultaneous open: both ends call `Connect` toward each other's public address.
    Connect {
        /// The source address.
        local: SocketAddr,
        /// The destination address.
        remote: SocketAddr,
        /// The kind of carrier.
        kind: StreamKind,
        /// A simultaneous open.
        simultaneous: bool,
    },
    /// Write one record: the first `len` bytes of the buffer given to `poll_stream`. The peer receives it whole
    /// and in order. A write to a stream that is not open is dropped, and the node learns of the end from
    /// [`StreamEvent::Closed`] or [`StreamEvent::Failed`].
    Write {
        /// The stream.
        stream: StreamId,
        /// How many bytes of the buffer are the record.
        len: usize,
        /// The true time before which the record must not be written; `None` writes it at once.
        send_at: Option<Time>,
    },
    /// Close the stream; the peer is told with a FIN.
    Close {
        /// The stream.
        stream: StreamId,
    },
}

/// A change of one stream endpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamEvent {
    /// A [`StreamOp::Connect`] was accepted; the connection is being set up under this handle.
    Pending {
        /// The new handle.
        stream: StreamId,
        /// The address being connected to.
        remote: SocketAddr,
    },
    /// The stream is open: records can be written and will arrive. For a stream the node accepted, `remote` is the
    /// peer's address as this node sees it.
    Opened {
        /// The stream.
        stream: StreamId,
        /// The peer's address.
        remote: SocketAddr,
    },
    /// The connection could not be set up or died (no answer, too many timeouts, refused by a middlebox).
    Failed {
        /// The stream.
        stream: StreamId,
    },
    /// The stream ended: the peer closed it, the node's interface changed, or the operating system closed it while
    /// the node was suspended.
    Closed {
        /// The stream.
        stream: StreamId,
    },
}

/// Work a node did in one call, as it reports it to the cost model.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    /// Instrumented steps (function entries, loop iterations).
    pub ticks: u64,
    /// Nanoseconds spent in metered primitives.
    pub ns: u64,
}

/// A change of one network interface of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IfaceEvent {
    /// The interface with this address came up.
    Up(IpAddr),
    /// The interface with this address went down.
    Down(IpAddr),
    /// The interface kept its place but changed its address.
    Changed {
        /// The address before the change.
        old: IpAddr,
        /// The address after the change.
        new: IpAddr,
    },
}

/// A node the engine drives. Every time argument is monotonic virtual time in nanoseconds.
pub trait Node {
    /// A command from the scenario.
    type Cmd;
    /// An event the node reports; the engine logs it with its time and prints it with `Debug` in the trace.
    type Event: Debug;

    /// A datagram arrived at `local` from `remote`. The node may use `data` as scratch.
    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]);
    /// The next datagram to send, written into `buf`, or `None` when nothing is ready.
    fn poll_transmit(&mut self, now: Time, buf: &mut [u8]) -> Option<Transmit>;
    /// When the node next wants `handle_timeout`, or `None`.
    fn poll_timeout(&mut self) -> Option<Time>;
    /// The time returned by `poll_timeout` has come.
    fn handle_timeout(&mut self, now: Time);
    /// A scenario command; its results come out of `poll_event`.
    fn command(&mut self, now: Time, cmd: Self::Cmd);
    /// The next event, or `None`.
    fn poll_event(&mut self) -> Option<Self::Event>;
    /// The process died. The node drops all volatile state and returns the bytes that were durable at this instant.
    fn crash(&mut self, now: Time) -> Vec<u8>;
    /// The process started again with the bytes `crash` returned (empty before the first crash).
    fn restart(&mut self, now: Time, persisted: &[u8]);
    /// The app or the OS froze the node; no call arrives until `resume`.
    fn suspend(&mut self, now: Time);
    /// The node runs again after `suspend`; its monotonic clock kept counting.
    fn resume(&mut self, now: Time);
    /// An interface changed.
    fn iface_event(&mut self, now: Time, event: IfaceEvent);
    /// The next request for a stream endpoint, written into `buf` for a write. Nodes without streams keep the
    /// default. The simulator asks for datagrams first, then stream requests.
    fn poll_stream(&mut self, _now: Time, _buf: &mut [u8]) -> Option<StreamOp> {
        None
    }
    /// A stream endpoint changed.
    fn handle_stream_event(&mut self, _now: Time, _event: StreamEvent) {}
    /// A record arrived whole on `stream`. The node may use `data` as scratch.
    fn handle_stream_record(&mut self, _now: Time, _stream: StreamId, _data: &mut [u8]) {}
    /// The work done by the calls since the last time this was asked, and reset it. Only the CPU cost model reads it.
    fn take_work(&mut self) -> Work {
        Work::default()
    }
    /// The node's local clock changed (set, jumped or drifted). Adapters keep it to convert wall-clock inputs.
    fn clock_changed(&mut self, _now: Time, _clock: &Clock) {}
}
