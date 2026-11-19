//! The PINC hybrid post-quantum handshake as SANS-IO state machines, with the key schedule and record protection.
//!
//! [`Initiator`] and [`Responder`] run the full handshake (X25519 plus ML-KEM-768, mutual authentication with any
//! [`pinc_crypto::IdentityAlg`]), the prekey short Initial, and resumption with 0-RTT keys. They take received
//! bytes, the current time and a caller-owned [`pinc_crypto::Drbg`], and they hand out messages to send, key
//! operations for the host to perform ([`KeyRequest`], so a TPM or HSM can hold the long-term keys) and events. The
//! wire layout of every message is in [`message`]; the labels are in [`labels`].
//!
//! Around them: [`record`] (packet keys and header protection), [`keyroll`] (how a running session replaces its
//! keys with a fresh Diffie-Hellman value), the [`CreditRecord`] each side sends, the [`AmpBudget`] and the ticket
//! stores in [`tickets`].
//!
//! The crate is `no_std`, never allocates, uses no `dyn`, reads no clock or randomness, takes every primitive from
//! `pinc-crypto` through the [`pinc_crypto::Provider`] trait, and never panics on any input. Secrets are zeroizing
//! types.
#![no_std]
#![forbid(unsafe_code)]

pub mod amp;
pub mod cache;
pub mod credit;
pub mod error;
pub mod ids;
pub mod initiator;
pub mod keyroll;
pub mod keys;
pub mod labels;
pub mod message;
mod outbox;
pub mod record;
pub mod responder;
mod schedule;
pub mod session;
pub mod tickets;

pub use amp::AmpBudget;
pub use cache::PrekeyCache;
pub use credit::{CREDIT_RECORD_LEN, CreditRecord, WINDOW_UNIT};
pub use error::Failure;
pub use ids::{AeadSet, Alpn, AlpnList, ConnId, KeyHandle, LocalIdentity, VERSION};
pub use initiator::{Initiator, InitiatorParams};
pub use keyroll::{Answered, Completed, Rekey, Roll};
pub use keys::{KeyRequest, KeyResponse, PrekeyInfo, PrekeyPolicy, SoftKeys, SoftPrekeys, prekey_hash};
pub use message::{InitialForm, min_initial_len, reply_len};
#[cfg(feature = "trace")]
pub use outbox::{OutboxProbe, OutboxView};
pub use record::{HeaderKey, Limits, PacketKey, RecordError};
pub use responder::{Responder, ResponderConfig, ResponderStores};
pub use schedule::{roll_secret, sub_session_secret};
pub use session::{EarlyKeys, Env, Established, Event, Output, Protection, Traffic};
pub use tickets::{ClientTickets, ServerTickets, Ticket, TicketBatch, TicketEntry};
