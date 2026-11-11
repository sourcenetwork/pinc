//! VINC for applications: one entry point, with no runtime, task, channel or thread of its own.
//!
//! The host passes its I/O as three async closures and calls async methods. Nothing runs in the background: the
//! futures of the handles drive the endpoint when the host polls them, on the host's executor and core, so tokio, smol
//! and nuclei all work. A host with no executor at all (a microcontroller, say) drives the SANS-IO `vinc-core` crate
//! directly.
//!
//! ```no_run
//! # async fn demo() -> vinc::Result<()> {
//! use nuclei::{Handle, time::sleep_until_precise};
//! use std::net::{SocketAddr, UdpSocket};
//!
//! const ALPN: &[u8] = b"app/1";
//! let sock = Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0))).await.expect("bind");
//! let ep = vinc::Vinc::builder().alpn(ALPN).local_addr(sock.local_addr().expect("addr")).build(
//!     async |buf| sock.recv_from(buf).await,
//!     async |pkt, to| sock.send_to(pkt, to).await,
//!     async |at| sleep_until_precise(at).await,
//! )?;
//! # let _ = ep;
//! # Ok(()) }
//! ```
//!
//! A host with segmentation offload (`UDP_SEGMENT`) or coalesced receives (`UDP_GRO`) calls
//! [`build_batched`](Builder::build_batched) instead: its send closure gets a whole transmit and the segment size, and
//! its receive closure may return several datagrams and their segment size, so one system call moves many.
//!
//! # The shape
//!
//! - [`Vinc::builder`] sets the identity (a seed, or a key store), the protocols (ALPNs), relays, discovery, limits and
//!   the access hook, then [`build`](Builder::build) takes the closures and returns the [`Endpoint`].
//! - [`Endpoint::connect`] gives a [`Connection`]; [`Endpoint::accept`] gives an [`Incoming`] with its ALPN.
//! - A connection opens and accepts bidirectional and unidirectional streams and sends and reads datagrams.
//! - Every call is a future of the host's executor. A future that waits also runs the endpoint, one at a time; with no
//!   future being polled the endpoint makes no progress, so a host with nothing else to await on it awaits
//!   [`Endpoint::run`].
//! - A higher layer is a [`Protocol`]; [`Endpoint::register`] gives it an ALPN and returns the sessions to serve.
//! - Errors are one small [`Error`] with an [`ErrorKind`] to match on and a short plain message.
//!
//! # Thread per core
//!
//! One endpoint per core, each with its own socket and identity, and each polled on its core. The handles are `Rc`-based
//! and `!Send`: they stay on the thread that built the endpoint, and the host spawns the futures with its executor's local
//! spawn (`nuclei::spawn_local`, a tokio `LocalSet`, a smol `LocalExecutor`). Nothing in the crate is synchronised.
//!
//! ```compile_fail
//! fn needs_send<T: Send>(_: &T) {}
//! fn check<H: vinc::Hosted>(conn: vinc::Connection<H>) {
//!     needs_send(&conn);
//! }
//! ```
#![forbid(unsafe_code)]

/// The README's examples, compiled and run as doctests so they cannot drift.
#[cfg(doctest)]
#[doc = include_str!("../../../README.md")]
pub struct ReadmeDoctests;

mod addr;
pub mod carrier;
mod conn;
mod drive;
mod endpoint;
mod engine;
mod error;
mod host;
mod keys;
mod mem;
mod node;
mod protocol;
mod records;
mod standby;
mod start;
pub mod stream;

pub use addr::{NodeAddr, node_from_str, node_to_string};
pub use carrier::CarrierKind;
pub use conn::{ConnStats, Connection, Incoming};
pub use endpoint::{
    Admission, AllowAll, BatchBuilt, Builder, Built, Direction, Discovery, Endpoint, IoBuilt, LOOKUP_WAIT, NoDiscovery,
    Vinc,
};
pub use engine::{Admit, BUSY, DENIED, REVOKED_MAX};
pub use error::{Error, ErrorKind, Result};
pub use host::{BatchHost, Host, Hosted, Io, IoHost};
pub use keys::Identity;
pub use mem::{Limits, MAX_CONNECTIONS, RING, STREAMS};
pub use node::CAPACITIES;
pub use protocol::{MAX_TAG, Protocol, Registered, read_tag, write_tag};
pub use records::{KNOWN_MAX, MAX_HINTS, PeerRecord, Records, Rendezvous};
pub use stream::{RecvStream, SendStream};
pub use vinc_core::NodeStats;
pub use vinc_crypto::NodeId;
/// The urgency a stream starts with; see [`SendStream::set_urgency`].
pub use vinc_transport::stream::DEFAULT_URGENCY;
