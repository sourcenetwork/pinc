//! The error every layer above the endpoint returns: a kind a caller can match and one short plain sentence.
//!
//! Invariants: an error carries no key material, address or payload; its message is a fixed sentence; the kinds are
//! the ones an application acts on (a lost connection, a timeout, a refusal, an unreachable peer, a reset stream).

use core::fmt;
use std::io;

use vinc_core::{CommandError, ConnectFailure, EndReason};
use vinc_transport::conn::CloseReason;
use vinc_transport::stream::StreamError;
use vinc_transport::stream::datagram::DatagramError;

/// What went wrong, in the terms an application acts on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    /// The connection is closed: `code` is the application code, `by_peer` says which side closed.
    Closed {
        /// The close code.
        code: u64,
        /// Whether the peer closed it (otherwise this node did, or the transport gave up).
        by_peer: bool,
    },
    /// Nothing was heard in time: a handshake or an idle connection timed out.
    TimedOut,
    /// The access check refused the peer.
    Refused,
    /// The peer cannot be reached: no address, no route, or a failed handshake.
    Unreachable,
    /// The peer reset the stream with this code.
    Reset(u64),
    /// This side reset or stopped the stream with this code.
    Stopped(u64),
    /// A datagram or message is larger than the connection can carry.
    TooLarge,
    /// A table is full: connections, streams or a queue. Try again later.
    Busy,
    /// The configuration is not valid.
    Config,
    /// The endpoint has stopped.
    Shutdown,
}

/// An error: a [`kind`](Error::kind) and a short plain message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Error {
    kind: ErrorKind,
    message: &'static str,
}

impl Error {
    /// An error of `kind` with `message`.
    pub const fn new(kind: ErrorKind, message: &'static str) -> Self {
        Self { kind, message }
    }

    /// What went wrong.
    pub const fn kind(&self) -> ErrorKind {
        self.kind
    }

    /// The message, one plain sentence.
    pub const fn message(&self) -> &'static str {
        self.message
    }

    /// The endpoint has stopped.
    pub const fn shutdown() -> Self {
        Self::new(ErrorKind::Shutdown, "the endpoint has stopped")
    }

    /// The configuration is not valid for `message`.
    pub const fn config(message: &'static str) -> Self {
        Self::new(ErrorKind::Config, message)
    }

    /// Why a session ended, as the error its users see.
    pub const fn ended(reason: EndReason) -> Self {
        match reason {
            EndReason::Transport(r) => Self::closed(r),
            EndReason::Orphaned => Self::new(
                ErrorKind::Closed {
                    code: 0,
                    by_peer: false,
                },
                "the connection was never used",
            ),
            EndReason::Denied => Self::new(ErrorKind::Refused, "the access check refused the peer"),
            EndReason::Redial => Self::new(
                ErrorKind::Closed {
                    code: 0,
                    by_peer: false,
                },
                "the node woke up elsewhere: dial again",
            ),
        }
    }

    /// The error for a transport close.
    pub const fn closed(reason: CloseReason) -> Self {
        match reason {
            CloseReason::IdleTimeout => Self::new(ErrorKind::TimedOut, "the connection was idle for too long"),
            CloseReason::Local { error } => Self::new(
                ErrorKind::Closed {
                    code: error,
                    by_peer: false,
                },
                "the connection was closed",
            ),
            CloseReason::Peer { error } => Self::new(
                ErrorKind::Closed {
                    code: error,
                    by_peer: true,
                },
                "the peer closed the connection",
            ),
            CloseReason::Violation { error } => Self::new(
                ErrorKind::Closed {
                    code: error,
                    by_peer: false,
                },
                "the connection broke a protocol rule",
            ),
            CloseReason::PathDead | CloseReason::HandshakeTimeout => {
                Self::new(ErrorKind::TimedOut, "the peer stopped answering")
            }
            CloseReason::Handshake(_) => Self::new(ErrorKind::Unreachable, "the handshake failed"),
        }
    }

    /// The error for a dial that did not produce a session.
    pub const fn dial(reason: ConnectFailure) -> Self {
        match reason {
            ConnectFailure::Refused => Self::new(ErrorKind::Config, "a node cannot dial itself"),
            ConnectFailure::Denied => Self::new(ErrorKind::Refused, "the access check refused the peer"),
            ConnectFailure::Timeout => Self::new(ErrorKind::TimedOut, "the peer did not answer in time"),
            ConnectFailure::Handshake(_) => Self::new(ErrorKind::Unreachable, "the handshake failed"),
            ConnectFailure::Closed => Self::new(
                ErrorKind::Closed { code: 0, by_peer: true },
                "the peer closed during the handshake",
            ),
        }
    }

    /// The error for a refused command.
    pub const fn command(e: CommandError) -> Self {
        match e {
            CommandError::NoSession => Self::new(
                ErrorKind::Closed {
                    code: 0,
                    by_peer: false,
                },
                "the connection is closed",
            ),
            CommandError::Full => Self::new(ErrorKind::Busy, "the connection table is full"),
            CommandError::NoRoute => Self::new(ErrorKind::Unreachable, "no address can be reached"),
            CommandError::NoPrekey | CommandError::Failure(_) => {
                Self::new(ErrorKind::Unreachable, "the handshake could not start")
            }
            CommandError::Stream(s) => Self::stream(s),
            CommandError::Datagram(d) => Self::datagram(d),
            CommandError::BadAlpn => Self::new(ErrorKind::Config, "the protocol name is empty or too long"),
            CommandError::NoCheck | CommandError::NoKeyRequest => {
                Self::new(ErrorKind::Config, "no such request is waiting")
            }
            CommandError::Refused => Self::new(ErrorKind::Config, "a node cannot dial itself"),
            CommandError::EventsPending => Self::new(ErrorKind::Busy, "the endpoint is catching up: try again"),
            CommandError::BufferTooSmall { .. } => Self::new(ErrorKind::TooLarge, "the datagram does not fit the buffer"),
        }
    }

    /// The error for a refused stream operation.
    pub const fn stream(e: StreamError) -> Self {
        match e {
            StreamError::StreamLimit | StreamError::TableFull | StreamError::Busy | StreamError::Exhausted => {
                Self::new(ErrorKind::Busy, "too many streams are open")
            }
            StreamError::Finished => Self::new(ErrorKind::Stopped(0), "the stream is already finished"),
            _ => Self::new(
                ErrorKind::Closed {
                    code: 0,
                    by_peer: false,
                },
                "the stream is closed",
            ),
        }
    }

    /// The error for a refused datagram.
    pub const fn datagram(e: DatagramError) -> Self {
        match e {
            DatagramError::TooLarge { .. } => Self::new(ErrorKind::TooLarge, "the datagram is too large"),
            DatagramError::Exhausted => Self::new(ErrorKind::Busy, "the datagram queue is full"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message)
    }
}

impl core::error::Error for Error {}

impl From<Error> for io::Error {
    fn from(e: Error) -> Self {
        let kind = match e.kind {
            ErrorKind::Closed { .. } => io::ErrorKind::ConnectionAborted,
            ErrorKind::TimedOut => io::ErrorKind::TimedOut,
            ErrorKind::Refused => io::ErrorKind::PermissionDenied,
            ErrorKind::Unreachable => io::ErrorKind::HostUnreachable,
            ErrorKind::Reset(_) => io::ErrorKind::ConnectionReset,
            ErrorKind::Stopped(_) => io::ErrorKind::BrokenPipe,
            ErrorKind::Busy => io::ErrorKind::WouldBlock,
            ErrorKind::TooLarge | ErrorKind::Config => io::ErrorKind::InvalidInput,
            ErrorKind::Shutdown => io::ErrorKind::NotConnected,
        };
        Self::new(kind, e)
    }
}

/// The result of an operation of the driver or the facade.
pub type Result<T, E = Error> = core::result::Result<T, E>;
