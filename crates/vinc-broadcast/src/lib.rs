//! VINC topic broadcast with origin authentication, as a SANS-IO state machine.
//!
//! Every node keeps a [`Topics`] machine. Messages are signed by their origin over the topic, the message id and the
//! hash of the body, so a hub, a relay or a peer that alters a message is caught. The machine reads no clock and
//! owns no socket: the host passes the time and the frames in, carries the frames out through [`Host`], and hears
//! the results as [`Event`]s and [`Trace`] records.
//!
//! The wire format ([`wire`]), the signing ([`auth`]) and the host interface ([`host`]) need no allocator. The state
//! machine keeps bounded tables and the hub log, and needs the `alloc` feature.
//!
//! The rules, in short:
//! - A publisher hands a message to every hub at once when all are up (FANP to the primary, FAN to the others on a
//!   second stream), otherwise to its primary (PUB). It retries on the next hub every 3 s and gives up after 90 s.
//! - A hub logs 120 s or 2048 messages per topic, pushes to its subscribers, mirrors to the other hubs unless the
//!   message was fanned, and tells the other hubs the ids of the last 30 s every 5 s.
//! - A subscriber repairs gaps with SUB, HAVE, GET and MSG, repeats the question every 20 s while the topic had
//!   traffic in the last 60 s, and delivers each message at most once (ids are remembered for 600 s).
//! - A restarted member gathers the replay floors of the hubs for up to 15 s and holds messages meanwhile.
//! - A message from an origin the access-control layer has not answered for is held, at most 64, until it answers.
//! - With no hub reachable, a publisher sends the message straight to the topic's subscribers over member sessions.
//! - A hub keeps a member's subscriptions while it is held down and tells the member when they are live again.
//! - A member that names the peers it holds sessions with ([`Topics::set_adjacent`]) is reached through a hub only
//!   from its connected component, as on a gossip mesh: a hub hands it a message only when a chain of sessions that
//!   both ends reported links it to the origin, or the origin is a hub. The no-hub fallback is not scoped.
//!
//! Sizes are configuration ([`Limits`]): the body limit, the log ring, the topic count and the subscriber cap. Data
//! larger than the limit goes by reference: broadcast a root or CID and fetch the bytes with `vinc-values`.
//!
//! Invariants: all tables are bounded; no input panics; the same inputs produce the same outputs; a message is
//! delivered only after its signature over the exact body verified.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod auth;
pub mod consts;
pub mod event;
pub mod host;
pub mod wire;

#[cfg(feature = "alloc")]
mod behind;
#[cfg(feature = "alloc")]
mod floors;
#[cfg(feature = "alloc")]
mod frames;
#[cfg(feature = "alloc")]
mod gap;
#[cfg(feature = "alloc")]
mod log;
#[cfg(feature = "alloc")]
mod msg;
#[cfg(feature = "alloc")]
mod node;
#[cfg(feature = "alloc")]
mod publish;
#[cfg(feature = "alloc")]
mod reach;
#[cfg(feature = "alloc")]
mod subs;
#[cfg(feature = "alloc")]
mod table;
#[cfg(feature = "alloc")]
mod timers;

pub use event::{HoldWhy, PublishMode, Reject, SubsDrop, Tag, Trace, topic_tag};
pub use host::{Event, Host, Lane};
#[cfg(feature = "alloc")]
pub use node::{Config, Limits, Refused, StartError, Topics};
#[cfg(feature = "alloc")]
pub use reach::ReachStats;
