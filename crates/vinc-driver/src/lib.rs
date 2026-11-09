//! The reference driver of the VINC endpoint: one thread, one UDP socket, no async runtime.
//!
//! The pieces, from the inside out:
//!
//! - [`Engine`]: the SANS-IO `vinc-core` endpoint with the host duties around it (key requests answered by a key store,
//!   access checks, dials, stream bytes moved between the endpoint and bounded channels). It reads no clock and opens
//!   no socket, so a different driver can run it the same way.
//! - [`Remote`] and [`Plane`]: the bounded request queue and the control queue between application handles on any
//!   thread and the engine thread, built on `kovan-channel`, with a [`Wake`] that rouses the driver loop.
//! - [`blocking`]: the loop over a `std::net::UdpSocket` that computes the next deadline, waits on the socket with a read
//!   timeout set to it, feeds the datagram or the timer, sends every datagram the endpoint produced (each segment on
//!   its own when the platform has no segmentation offload), and sleeps again. It never spins: it runs only for an
//!   input, a request or a deadline.
//!
//! A driver for another runtime builds the same [`Engine`] with [`run`], feeds it from its own sockets and timers, and
//! hands the application the [`Remote`] side.
//!
//! Invariants: after every input the engine is serviced to quiescence before the driver sleeps; every endpoint
//! deadline is honoured by the next wait (a wait may end late by the timer granularity of the operating system, never
//! early without a recheck); nothing is leaked when the loop stops.
#![forbid(unsafe_code)]
#![allow(clippy::needless_pass_by_value, reason = "reply senders are consumed by the answer")]

pub mod blocking;
mod engine;
mod error;
mod keys;
mod link;
mod mem;
mod plane;

pub use engine::{Admit, BUSY, CONNECTIONS, Direction, Engine, EngineConfig, run};
pub use error::{Error, ErrorKind, Result};
pub use keys::Identity;
pub use kovan_channel::bounded::{Receiver, Sender};
pub use link::{BLOCK, Item, NewStream, SessionShared, StreamShared, chan};
pub use mem::{Limits, MAX_CONNECTIONS, RING, STREAMS};
pub use plane::{Ctl, Plane, Remote, Request, Wake, WakeFlag, WeakRemote, plane};
pub use vinc_core::{NodeStats, SessionId, SessionStats};
