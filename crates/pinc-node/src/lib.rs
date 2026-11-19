//! The PINC node: the endpoint, the connectivity client, membership and broadcast, composed over real sessions as one
//! SANS-IO state machine.
//!
//! Each layer is a state machine over its own host interface. This crate implements those interfaces over the real
//! endpoint and the real connectivity client, so the algorithm runs as one system: membership and broadcast share one
//! hub stream per hub, found by a protocol id the node registers; their frames ride the endpoint's streams; the
//! evidence they judge by (last receive, smoothed round trip, probe timeouts, the give-up bound) is what the
//! transport knows; carrier drops and returns come from the relays.
//!
//! A [`Node`] mirrors the endpoint's shape: datagrams, time and commands go in; datagrams, the next deadline and
//! [`NodeEvent`]s come out. The application's own streams and datagrams pass through untouched. The host serves the
//! connectivity client's streams and key answers exactly as it does for the client alone.
//!
//! The host-side duties that the layers leave to their host live here:
//! - **Dialing.** Every hub is dialed, never inside its backoff window: 2 s doubling to 16 s for a hub (60 s for any
//!   other node), reset by a session that lived 5 s; a peer whose access check refused us waits 60 s doubling to 15
//!   min. A frame sent to a peer with no session waits for the dial (at most 256 frames).
//! - **Survivor adoption.** When a member's newer session closes at a hub and an older one was heard within 30 s, the
//!   hub adopts it: a fresh write stream, a snapshot, and the ids of the last 90 s of each subscribed topic. The
//!   same happens when a member writes on a session that is not the hub's current one.
//! - **Stream repair.** A hub session without our write stream gets a fresh one after 10 s, a member's toward a hub and a
//!   hub's toward a member alike (a stream the peer stopped or reset is forgotten, so the session is left without one).
//! - **No transport watchdog.** A hub session is closed for want of an answer only by membership, when its HELLO goes
//!   unanswered; probe timeouts alone do not close it, the transport gives up on a silent session by itself.
//! - **Heal detection.** A hub heard again after longer than the transport's give-up bound at the last round trip
//!   means a partition healed ([`bound::give_up`]); membership then opens its quiet window.
//! - **Independent probes.** A probe on [`Route::Via`](pinc_membership::session::Route) is a path challenge through
//!   the named hub's relay; the member's answer is evidence from the transport. A relayed probe for a member with no
//!   session, or with the probe queue full, is refused, so membership does not count it as sent.
//! - **Urgency.** A hub session's write stream goes first (1), the broadcast fan stream of a gossip session next (2,
//!   and its writes do not keep the session awake), then reconcile (2), the endpoint default (3) and the value
//!   requests (4).
//! - **`FLOOR_PUSH`.** A hub that accepted a member's session opens its own stream and sends the replay floor at once.
//! - **Relay duties.** A hub that runs a relay for its members gets the carrier evidence, the told-apart datagrams
//!   and the member notices from the node ([`relay_trace`](Node::relay_trace), [`is_relay_request`],
//!   [`member_at`](Node::member_at), [`poll_member`](Node::poll_member)).
//! - **Restart.** The host's bundle records bring held and partial bundles, with their copies and custody, back
//!   ([`dtn_restore`](Node::dtn_restore)).
//! - **A timer that moves.** A deadline that two timer calls in a row leave due where it was is counted against the
//!   layer that holds it ([`Node::timer_stats`]), and the node asks for the next call one [`TIMER_TICK`] later, so a
//!   host that serves due timers first does not spin on it.
//! - **Revocation and leave.** A revoked peer loses every session within the call; a leave closes every hub session
//!   with code 0x4C and then every other session.
//!
//! The crate is `no_std` with `alloc`, forbids unsafe code and uses no `dyn`. Every table is bounded.
//!
//! Invariants: the same inputs in the same order give the same outputs; no input panics; the streams of a
//! hub-protocol session never reach the application as events or bytes, nor do its datagram and room events (its
//! lifecycle events do); a frame the node cannot hand to a session reports failure to its layer,
//! which repairs it by its own rules.
#![no_std]
#![forbid(unsafe_code)]
#![allow(
    clippy::large_stack_arrays,
    clippy::too_many_lines,
    reason = "the connectivity layer holds its buffers inline; the node boxes it"
)]

extern crate alloc;

#[cfg(test)]
extern crate std;

mod apps;
pub mod bound;
mod config;
mod connect;
mod dtn;
mod dtn_rx;
mod dtn_save;
mod dtn_wire;
mod duties;
mod ep;
mod event;
mod events;
mod hosts;
mod io;
mod layer;
mod node;
mod portmap;
#[cfg(feature = "trace")]
mod probe;
mod reconcile;
mod relay;
mod timers;
pub mod trace;
mod values;
mod values_frames;
mod values_net;
mod values_provide;
mod values_types;

pub use apps::{Apps, DtnApp, Enabled, NoApps, NoDtn, NoIndex, NoSets, NoValues, Recipient, ServeSource, SetsApp};
pub use config::{
    BACKOFF_CAP, BACKOFF_FIRST, BACKOFF_HUB_CAP, Config, DENY_CAP, DENY_FIRST, DTN_ALPN, HUB_ALPN, HUB_URGENCY, Nanos,
    QUEUE_FRAMES, SESSION_LIVED, SETS_ALPN, SETS_URGENCY, STREAM_REPAIR, SURVIVOR, SURVIVOR_HAVE, Store, TIMER_TICK,
    VALUES_ALPN,
};
pub use dtn::{BUNDLES, DtnPlan, DtnSendError};
pub use dtn_save::DtnRestored;
pub use ep::Ep;
pub use event::{NodeEvent, ReconcileFailure};
pub use layer::Layer;
pub use node::{Node, StartError};
pub use pinc_broadcast::IdKey;
/// The two types [`ServeSource`] is written in, for a host that names its own stream source.
pub use pinc_values::{source::ValueSource, store::ValueRead};
pub use portmap::PortMapStats;
#[cfg(feature = "trace")]
pub use probe::BackoffProbe;
pub use reconcile::{ATTEMPTS, RESPONDERS, ROUNDS, SetsError};
pub use relay::{MemberNotice, is_relay_request};
pub use timers::{Timed, TimerStats};
pub use trace::{Body, NodeTrace, TRACE_VERSION, TraceItem};
#[cfg(feature = "trace")]
pub use values_frames::probe as values_frames_probe;
pub use values_provide::PROVIDED_MAX;
pub use values_types::{FETCHES, ValuesError, ValuesRequest, ValuesStats};
