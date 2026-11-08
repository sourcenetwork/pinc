//! The VINC hybrid post-quantum handshake as SANS-IO state machines, with the key schedule and record protection.
//!
//! [`Initiator`] and [`Responder`] run the full handshake (X25519 plus ML-KEM-768, mutual authentication with any
//! [`vinc_crypto::IdentityAlg`]), the prekey short Initial, and resumption with 0-RTT keys. They take received
//! bytes, the current time and a caller-owned [`vinc_crypto::Drbg`], and they hand out messages to send, key
//! operations for the host to perform ([`KeyRequest`], so a TPM or HSM can hold the long-term keys) and events. The
//! wire layout of every message is in [`message`]; the labels are in [`labels`].
//!
//! Around them: [`record`] (packet keys, header protection and key update), [`ReplayWindow`], address-validation
//! [`token`]s, the [`AmpBudget`] and the tickets stores in [`tickets`].
//!
//! The crate is `no_std`, never allocates, uses no `dyn`, reads no clock or randomness, takes every primitive from
//! `vinc-crypto` through the [`vinc_crypto::Provider`] trait, and never panics on any input. Secrets are zeroizing
//! types.
#![no_std]
#![forbid(unsafe_code)]

pub mod amp;
pub mod cache;
pub mod error;
pub mod ids;
pub mod initiator;
pub mod keys;
pub mod labels;
pub mod message;
mod outbox;
pub mod params;
pub mod record;
pub mod replay;
pub mod responder;
mod schedule;
pub mod session;
pub mod tickets;
pub mod token;

pub use amp::AmpBudget;
pub use cache::PrekeyCache;
pub use error::Failure;
pub use ids::{AeadSet, Alpn, AlpnList, ConnId, KeyHandle, LocalIdentity, VERSION};
pub use initiator::{Initiator, InitiatorParams};
pub use keys::{KeyRequest, KeyResponse, PrekeyInfo, PrekeyPolicy, SoftKeys, SoftPrekeys, prekey_hash};
pub use message::{InitialForm, min_initial_len, reply_len};
pub use params::{MAX_PARAMS_LEN, Params};
pub use record::{HeaderKey, Limits, PacketKey, RecordError};
pub use replay::{ReplayError, ReplayWindow};
pub use responder::{Responder, ResponderConfig, ResponderStores};
pub use schedule::sub_session_secret;
pub use session::{EarlyKeys, Env, Established, Event, Output, Protection, Traffic};
pub use tickets::{ClientTickets, ServerTickets, Ticket, TicketBatch, TicketEntry};
pub use token::{TokenError, TokenKey, TokenKind};
