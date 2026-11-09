//! VINC for applications: one entry point, with no executor, thread or socket loop of its own.
//!
//! The host's runtime drives everything: [`Builder::bind`] takes the host's datagram socket and timer and returns an
//! [`Endpoint`] and a driver future, which the host spawns on its own executor, on the core that owns the socket. Every
//! method of the handles is `async`. With the `nuclei` feature, [`Builder::bind_nuclei`] does the binding on the
//! [nuclei](https://crates.io/crates/nuclei) runtime; a host with no executor (a microcontroller, say) drives the
//! SANS-IO `vinc-core` crate directly.
//!
//! # The shape
//!
//! - [`Vinc::builder`] sets the identity (a seed, or a key store), the protocols (ALPNs), relays, discovery, limits and
//!   the access hook, then [`bind`](Builder::bind) returns the [`Endpoint`] and the [`Driver`].
//! - [`Endpoint::connect`] gives a [`Connection`]; [`Endpoint::accept`] gives an [`Incoming`] with its ALPN.
//! - A connection opens and accepts bidirectional and unidirectional streams and sends and reads datagrams. Streams
//!   implement `futures-io` `AsyncRead` and `AsyncWrite`.
//! - Handles are `Clone + Send + Sync + 'static`. Their futures wait on channels and wake through the waker they are
//!   polled with; every await is cancel safe (see [`stream`]).
//! - A higher layer is a [`Protocol`]; [`Endpoint::register`] gives it an ALPN and returns the sessions to serve.
//! - Errors are one small [`Error`] with an [`ErrorKind`] to match on and a short plain message.
//!
//! # Adding a host
//!
//! Implement [`Datagrams`] and [`Timer`] for the host's sockets and clock and pass them to [`Builder::bind`]; the
//! facade's types do not change.
#![forbid(unsafe_code)]

/// The README's examples, compiled and run as doctests so they cannot drift.
#[cfg(doctest)]
#[doc = include_str!("../../../README.md")]
pub struct ReadmeDoctests;

mod addr;
mod conn;
mod endpoint;
mod protocol;
pub mod stream;

pub use addr::{NodeAddr, node_from_str, node_to_string};
pub use conn::{ConnStats, Connection, Incoming};
pub use endpoint::{Admission, AllowAll, Bound, Builder, Direction, Discovery, Endpoint, NoDiscovery, Vinc};
pub use protocol::{MAX_TAG, Protocol, Registered, read_tag, write_tag};
pub use stream::{RecvStream, SendStream};
pub use vinc_crypto::NodeId;
pub use vinc_driver::{Datagrams, Driver, Error, ErrorKind, Identity, Limits, NodeStats, Result, Timer};

/// The nuclei runtime's sockets and timers for the driver.
#[cfg(feature = "nuclei")]
pub use vinc_nuclei as nuclei;
