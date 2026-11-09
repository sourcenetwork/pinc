//! The reference driver of the VINC endpoint: the SANS-IO endpoint as a future the host runs, over the host's own
//! sockets and timers. It owns no executor, no thread and no socket loop.
//!
//! The pieces, from the inside out:
//!
//! - [`Engine`]: the SANS-IO `vinc-core` endpoint with the host duties around it (key requests answered by a key store,
//!   access checks, dials, stream bytes moved between the endpoint and bounded channels). It reads no clock and opens
//!   no socket, so any driver can run it the same way.
//! - [`Remote`] and [`Plane`]: the bounded request queue and the control queue between application handles and the
//!   engine, built on `kovan-channel`, with a wake that rouses the driver future through the host's executor.
//! - [`Datagrams`] and [`Timer`]: what the host implements, as async traits (a batched send, a receive into the
//!   driver's buffer, the local address; a clock and a sleep until an instant).
//! - [`open`] and [`Driver`]: the handles and the future. The host spawns [`Driver::run`] on the executor and the core
//!   that own the socket; while the endpoint is idle that future is parked on an await.
//!
//! Invariants: after every input the engine is serviced to quiescence before the driver awaits; every endpoint deadline
//! is honoured by the next wait; nothing is leaked when the future ends or is dropped.
#![forbid(unsafe_code)]
#![allow(clippy::needless_pass_by_value, reason = "reply senders are consumed by the answer")]

mod drive;
mod engine;
mod error;
mod io;
mod keys;
mod link;
mod mem;
mod node;
mod plane;
mod start;

pub use drive::{Driver, Handles, LoopCounts, LoopStats, Settings, open};
pub use engine::{Admit, AllowAll, BUSY, Direction, Engine, EngineConfig};
pub use error::{Error, ErrorKind, Result};
pub use io::{Datagrams, Timer};
pub use keys::Identity;
pub use kovan_channel::bounded::{Receiver, Sender};
pub use link::{BLOCK, Item, NewStream, SessionShared, StreamShared, chan};
pub use mem::{Limits, MAX_CONNECTIONS, RING, STREAMS};
pub use node::CAPACITIES;
pub use plane::{Ctl, Plane, Remote, Request, WakeFlag, WeakRemote, plane};
pub use start::run;
pub use vinc_core::{NodeStats, SessionId, SessionStats};
