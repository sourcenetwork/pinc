//! PINC for applications: one entry point, with no runtime, task, channel or thread of its own.
//!
//! The host passes its I/O as three async closures and calls async methods. Nothing runs in the background: the
//! futures of the handles drive the endpoint when the host polls them, on the host's executor and core, so tokio, smol
//! and nuclei all work. A host with no executor at all (a microcontroller, say) drives the SANS-IO `pinc-core` crate
//! directly.
//!
//! ```no_run
//! # async fn demo() -> pinc::Result<()> {
//! use nuclei::{Handle, time::sleep_until_precise};
//! use std::net::{SocketAddr, UdpSocket};
//!
//! const ALPN: &[u8] = b"app/1";
//! let sock = Handle::<UdpSocket>::bind(SocketAddr::from(([127, 0, 0, 1], 0))).await.expect("bind");
//! let ep = pinc::Pinc::builder().alpn(ALPN).local_addr(sock.local_addr().expect("addr")).build(
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
//! # Without `std`
//!
//! With the `std` feature (on by default) the standard library is the host's platform: `Pinc::builder` needs nothing
//! else. Without it the crate is `no_std` plus `alloc`: the host brings an allocator and a [`Platform`] (its clock, its
//! randomness and its error type) and starts from [`Pinc::builder_on`]; [`System`], `Pinc::builder` and
//! `Identity::from_seed` are the standard library's and exist only with `std`. `Limits::wasm` is the preset for a host
//! with a 32-bit address space (the default limits cannot be addressed there and the build refuses them), and
//! `examples/platform.rs` is a complete host on a platform of its own, in memory, to copy.
//!
//! The memory and the stack of such a host are measured on the 64-bit build host, not on a microcontroller, and a
//! 32-bit target is not measured yet. An endpoint with one session slot and 8 pool chunks holds about 0.8 MB with no
//! session; one connected session adds about 2.8 MB, the room reserved for its tables, which is written only as the
//! session uses it. Building, connecting, echoing 64 bytes and closing run on 1 MiB of stack and fail on 512 KiB. The
//! tests `pinc_nostd_memory` and `pinc_nostd_stack` hold them.
//!
//! # The shape
//!
//! - `Pinc::builder` (or [`Pinc::builder_on`]) sets the identity (a seed, or a key store), the protocols (ALPNs),
//!   relays, discovery, limits and the access hook, then [`build`](Builder::build) takes the closures and returns the
//!   [`Endpoint`].
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
//! spawn (`nuclei::spawn_local`, a tokio `LocalSet`, a smol `LocalExecutor`). An endpoint's futures stay on the thread
//! that built it also when the runtime moves that worker's reactor to another thread, so a runtime that hands a worker
//! off when a poll runs long has that turned off for the workers that run endpoints
//! (`nuclei::Builder::handoff_after(None)`). Nothing in the crate is synchronised.
//!
//! ```compile_fail
//! fn needs_send<T: Send>(_: &T) {}
//! fn check<H: pinc::Hosted>(conn: pinc::Connection<H>) {
//!     needs_send(&conn);
//! }
//! ```
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
// `System`, the default platform, is the standard library's; the tests use it also without the feature.
#[cfg(any(feature = "std", test))]
extern crate std;

/// The README's examples, compiled and run as doctests so they cannot drift.
#[cfg(doctest)]
#[doc = include_str!("../../../README.md")]
pub struct ReadmeDoctests;

mod addr;
mod body;
pub mod carrier;
mod carriers;
mod conn;
mod drive;
mod endpoint;
mod endpoint_state;
mod endpoint_topics;
mod engine;
mod error;
mod event;
mod host;
mod keys;
mod maps;
mod mem;
mod node;
mod platform;
mod protocol;
mod records;
pub mod relay;
mod reserved;
mod role;
mod standby;
mod start;
pub mod stream;
#[cfg(feature = "trace")]
#[doc(hidden)]
pub mod trace_waits;

pub use addr::{NodeAddr, node_from_str, node_to_string};
pub use body::Body;
pub use carrier::CarrierKind;
pub use carriers::{CarrierFns, Carriers, NoCarriers, Relay};
pub use conn::{ConnStats, Connection, Incoming};
pub use endpoint::{
    Admission, AllowAll, BatchBuilt, Builder, Built, Direction, Discovery, Endpoint, IoBuilt, LOOKUP_WAIT, NoDiscovery,
    Pinc,
};
pub use engine::{Admit, BUSY, DENIED, REVOKED_MAX, Restored};
pub use error::{Error, ErrorKind, Result};
pub use event::{Event, MessageId};
pub use host::{BatchHost, Host, Hosted, Io, IoHost};
pub use keys::Identity;
pub use mem::{Limits, MAX_CONNECTIONS, MAX_PROTOCOLS, RING, STREAMS};
pub use node::CAPACITIES;
pub use pinc_broadcast::{ReachStats, Reject, RejectStats};
pub use pinc_core::NodeStats;
pub use pinc_crypto::NodeId;
pub use pinc_node::{PortMapStats, Timed, TimerStats};
/// The urgency a stream starts with; see [`SendStream::set_urgency`].
pub use pinc_transport::stream::DEFAULT_URGENCY;
pub use platform::{HostError, HostInstant, Platform, System};
pub use protocol::{MAX_TAG, Protocol, Registered, read_tag, write_tag};
pub use records::{KNOWN_MAX, MAX_HINTS, PeerRecord, Records, Rendezvous};
pub use role::{RelayRole, Role, RoleSpec};
#[cfg(feature = "trace")]
pub use standby::trace::{StandbyProbe, StandbySlot};
pub use stream::{RecvStream, SendStream};
