//! VINC for applications: one entry point.
//!
//! ```no_run
//! use vinc::Vinc;
//!
//! # fn main() -> vinc::Result<()> {
//! let node = Vinc::builder().alpn(b"echo/1".to_vec()).bind_blocking()?;
//! let node = node.blocking();
//! println!("listening as {}", node.addr().ticket());
//! # Ok(())
//! # }
//! ```
//!
//! # The shape
//!
//! - [`Vinc::builder`] sets the identity (a seed, or a key store), the protocols (ALPNs), relays, discovery, limits and
//!   the access hook, then [`bind_blocking`](Builder::bind_blocking) or [`spawn_on`](Builder::spawn_on) starts the
//!   reference driver and returns an [`Endpoint`].
//! - [`Endpoint::connect`] gives a [`Connection`]; [`Endpoint::accept`] gives an [`Incoming`] with its ALPN.
//! - A connection opens and accepts bidirectional and unidirectional streams and sends and reads datagrams. Streams
//!   implement `futures-io` `AsyncRead` and `AsyncWrite`.
//! - Handles are `Clone + Send + Sync + 'static`. Their futures are plain `std` futures that need no executor and
//!   no runtime; every await is cancel safe (see [`stream`]).
//! - The [`blocking`] module mirrors all of it for threads that are not async.
//! - A higher layer is a [`Protocol`]; [`Endpoint::register`] gives it an ALPN and runs it for each session.
//! - Errors are one small [`Error`] with an [`ErrorKind`] to match on and a short plain message.
//!
//! # Adding a driver
//!
//! The endpoint the facade drives is the SANS-IO `vinc-core` endpoint, run by `vinc-driver`'s [`Engine`](vinc_driver::Engine)
//! behind a [`Remote`](vinc_driver::Remote). A different driver (a runtime's sockets and timers) builds the same engine,
//! feeds it datagrams and time and hands the application the same handles; the facade's types do not change.
#![forbid(unsafe_code)]

/// The README's examples, compiled and run as doctests so they cannot drift.
#[cfg(doctest)]
#[doc = include_str!("../../../README.md")]
pub struct ReadmeDoctests;

mod addr;
pub mod blocking;
mod conn;
mod endpoint;
mod protocol;
mod rt;
pub mod stream;

pub use addr::{NodeAddr, node_from_str, node_to_string};
pub use conn::{ConnStats, Connection, Incoming};
pub use endpoint::{Admission, Builder, Direction, Discovery, Endpoint, Vinc};
pub use protocol::{MAX_TAG, Protocol, read_tag, write_tag};
pub use rt::{Spawn, Task, ThreadSpawner, block_on};
pub use stream::{RecvStream, SendStream};
pub use vinc_crypto::NodeId;
pub use vinc_driver::{Error, ErrorKind, Identity, Limits, NodeStats, Result};
