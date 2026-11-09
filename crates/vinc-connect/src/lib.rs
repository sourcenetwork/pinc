//! VINC connectivity, relay side: the secured relay carrier and every relay-side state machine.
//!
//! A carrier is a byte stream (plain TCP, or WebSocket over TCP) between a node and a relay. It begins with a VINC
//! handshake to the relay's identity and then carries carrier frames inside record protection, so no TLS or QUIC
//! library is involved ([`carrier`]). The relay side ([`relay`]) keeps carrier sessions keyed by node id, forwards
//! packets, stores and replicates signed records ([`record`]), answers lookups and address discovery, delivers hub
//! tunnel packets, honours signed sleep notices and holds packets for sleeping members in a bounded [`mailbox`].
//!
//! The client side ([`client`]) is the other half: the carrier state machine with its lease, home relay selection and
//! reachability classification, the lookup client, hole punching, the member side of the hub tunnel, the first-flight
//! rules, local discovery ([`local`]) and tickets ([`ticket`]). All of it is driven by the `vinc-core` endpoint.
//!
//! The crate is `no_std`, never allocates, uses no `dyn`, reads no clock or randomness, keeps every table bounded
//! by a const generic, and never panics on any input. Every state machine is deterministic: the same inputs in the
//! same order give the same effects, and every transition is reported as a [`relay::Trace`] event through the
//! [`relay::Sink`] the host passes to each call.
#![no_std]
#![forbid(unsafe_code)]

pub mod carrier;
pub mod client;
pub mod local;
pub mod mailbox;
pub mod record;
pub mod relay;
pub mod ticket;
