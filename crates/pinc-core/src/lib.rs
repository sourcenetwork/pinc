//! PINC core: the SANS-IO endpoint that turns connections into a node.
//!
//! An [`Endpoint`] owns a bounded table of `pinc-transport` connections and everything that spans more than one of
//! them: demultiplexing by connection id (with a trial by keys when two sessions derive the same id), the
//! amplification [`Ledger`] on every outgoing datagram, the half-open cap and Initial size floors, the node round
//! trips ([`NodeRtt`]) fed to every connection, the access check with its gate, the optimistic report and the READY
//! hold, the shared ticket stores with export and restore across a restart, the protocol registry, sub-sessions that
//! open a second protocol without a round trip, the keepalive schedule by role, and one deadline heap for every
//! timer.
//!
//! The host drives it with a clock and datagrams in, and reads datagrams, events and deadlines out:
//!
//! ```text
//! handle_datagram(now, local, remote, buf)        command(now, Command) -> Reply { value, events }
//! poll_transmit(now, out) -> Option<Transmit>     poll_event() -> Option<Event>
//! poll_timeout() -> Option<u64>                   handle_timeout(now)        query(Query) -> Answer
//! ```
//!
//! After any input call `poll_transmit` until it returns `None`; there are no hidden wakeups.
//!
//! The crate is `no_std`, forbids unsafe code, uses no `dyn`, allocates nothing per packet, and never panics on input.
//! Every table has a fixed bound. Without the `alloc` feature it allocates nothing at all; with it the endpoint's tables
//! are allocated once, when it is built, and [`Endpoint::new_owned`] also allocates the slot table then and the memory
//! of a slot when the slot is first taken, all freed when the endpoint is dropped. With the `trace` feature every decision is also recorded as an
//! ndjson-ready [`TraceRecord`] for model checking and proof of the same rules.
#![no_std]
#![forbid(unsafe_code)]
#![allow(clippy::struct_excessive_bools, reason = "independent flags of one session")]
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    reason = "i, j and q index tables and queues; the names read well in the small loops"
)]
#![allow(clippy::too_many_lines, reason = "the command match has one arm per command")]
#![allow(
    clippy::cast_possible_truncation,
    reason = "table positions are below u32::MAX by construction, checked when a table is built"
)]
#![allow(
    clippy::large_stack_arrays,
    reason = "the endpoint holds its fixed tables inline by design; the caller places it in a box or a static"
)]
#![allow(
    clippy::large_enum_variant,
    reason = "answers are returned by value; boxing would allocate"
)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
extern crate std;

mod acp;
mod api;
mod commands;
mod endpoint;
mod events;
mod ext_in;
mod heap;
mod iface;
mod keepalive;
mod ledger;
mod orphan;
mod queue;
mod reach;
mod relay_net;
mod rtt;
mod rx;
mod slot;
mod state;
mod stateless;
mod store;
mod sub;
mod table;
mod timers;
mod trace;
mod tx;

pub use acp::{ACP_RECHECK, ACP_TTL};
pub use api::{
    Answer, Command, CommandError, ConnectFailure, EndReason, Event, Events, NodeStats, PathState, PeerInfo, Query,
    Reply, SendState, SessionId, SessionStats, Value,
};
pub use commands::{FAN_URGENCY, UDP_FRESH};
pub use endpoint::{CID_LEN, Endpoint, EndpointConfig, MAX_ALPNS, MAX_DATAGRAM, MAX_IFACES, PREKEY_PEERS, SUBS_SEEN};
pub use ext_in::EXT_BODY_MAX;
#[cfg(feature = "trace")]
pub use ext_in::trace::ExtInProbe;
pub use heap::DeadlineHeap;
pub use iface::{IfaceEvent, IfaceId};
pub use keepalive::{
    ACTIVE_KEEP, DIRECT_SILENCE, HOLD_WINDOW, IDLE_DROP, IDLE_KEEP, Inputs as KeepaliveInputs, LATE_START,
    MTU_PROBE_DELAY, PATH_KEEP, Plan as KeepalivePlan, QUIET_KEEP_ACCEPTOR, QUIET_KEEP_DIALER, RESUME_QUIET, Role,
    standby_due,
};
pub use ledger::{DATAGRAM_OVERHEAD, FACTOR, LEDGER_ENTRIES, Ledger, LedgerEntry};
#[cfg(feature = "trace")]
pub use orphan::trace::{OrphanEntry, OrphanProbe};
#[cfg(feature = "trace")]
pub use queue::trace::EventProbe;
pub use queue::{EVENT_BASE, event_headroom, event_queue};
pub use reach::REACH_BODY_MAX;
#[cfg(feature = "trace")]
pub use reach::trace::ReachProbe;
pub use relay_net::{RELAY_V4, is_relay_addr, relay_addr, relay_parts};
pub use rtt::{FIRST_RESEND, FLOOR_MAX, HUB_RESEND, NodeRtt, PEER_RTTS, SLOW_RTT};
#[cfg(feature = "trace")]
pub use rx::HalfOpenSlot;
pub use rx::{HALF_OPEN_HOLD, HALF_OPEN_LIFE, MAX_HALF_OPEN, Taken};
#[cfg(feature = "trace")]
pub use slot::trace::HeldProbe;
pub use slot::{HELD_EVENTS, Slot};
pub use state::{Restored, STATE_VERSION, StateError, state_len};
pub use table::Table;
#[cfg(feature = "trace")]
pub use timers::{SETTLE_CAPACITY, SettleRecord};
pub use trace::{TRACE_CAPACITY, TraceEvent, TraceRecord};
pub use tx::Transmit;
