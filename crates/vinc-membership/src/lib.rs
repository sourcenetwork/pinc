//! VINC membership: the hub stream codec, the hub lease roster and the member view, as SANS-IO state machines.
//!
//! Every node keeps a [`Membership`] machine. A hub also holds the lease roster of its members. The machines read no
//! clock and own no socket: the host reports sessions coming up and going down, frames, carrier events and timers,
//! and answers the machine's questions through the [`Host`] traits. The machine answers with frames sent through
//! [`Session::send`], [`Event`]s for the application and [`Trace`] records for the proofs.
//!
//! The codec ([`codec`]), the host interface ([`session`]) and the incarnation ([`incarnation`]) need no allocator.
//! The state machines keep bounded tables and need the `alloc` feature.
//!
//! The rules, in short:
//! - A hub's lease on a member lasts 80 s from its last renewal; transport evidence renews it as a frame does.
//! - A dropped carrier is probed, and the member is confirmed down only when it also stays silent on an independent
//!   path, so one lost probe or a slow member never confirms a live node down.
//! - Another hub's DOWN is accepted only while this hub's own lease for the member is stale.
//! - A returning carrier restores the entry, the held subscriptions and tells the member about itself.
//! - A member view takes snapshots as additions: a snapshot never removes a member on its own.
//! - Incarnations only go up, across restarts and clock jumps.
//!
//! Invariants: all tables are bounded; no input panics; the same inputs produce the same outputs.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod codec;
pub mod consts;
pub mod incarnation;
pub mod session;

#[cfg(feature = "alloc")]
pub mod event;
#[cfg(feature = "alloc")]
mod hub;
#[cfg(feature = "alloc")]
mod input;
#[cfg(feature = "alloc")]
mod node;
#[cfg(feature = "alloc")]
mod timers;
#[cfg(feature = "alloc")]
mod view;

pub use codec::{Frame, FrameError, NodeId, Record};
#[cfg(feature = "alloc")]
pub use event::{Event, Trace};
#[cfg(feature = "alloc")]
pub use input::MAX_FRAMES_PER_CALL;
#[cfg(feature = "alloc")]
pub use node::{Config, Membership, StartError, TableFull};
pub use session::{Broadcast, Carrier, CloseReason, Evidence, Host, Local, Nanos, Route, Session};
