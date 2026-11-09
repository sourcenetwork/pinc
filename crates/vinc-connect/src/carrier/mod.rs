//! The relay carrier: frames, aliases, the protected session and the WebSocket framing.
//!
//! A carrier is an ordered byte stream between a node and a relay. [`session::ProtectedCarrier`] runs a VINC handshake
//! to the relay's identity over it and then moves [`frame::Frame`]s inside record protection; [`ws`] frames the
//! stream when a WebSocket carries it. The default carrier ports are configuration (443 by default, TCP first and
//! WebSocket second after UDP).
//!
//! # Stream framing
//!
//! Every unit on the stream starts with a 2-byte big-endian length `n` of the bytes that follow.
//! - Before the handshake completes the units are handshake messages, in the clear, in the order the two
//!   state machines produce them.
//! - After it, each unit is a record: `n - 16` bytes of ciphertext and a 16-byte tag. The plaintext is one carrier
//!   frame (a batch counts as one). The record is sealed with the sender's packet key, the packet number is the
//!   count of records already sent on this direction starting at 0, and the two length bytes are the associated data.
//! - A unit longer than a record ([`session::MAX_UNIT_LEN`]) ends the carrier.
//!
//! Invariants: nothing is read or written outside the bounded buffers; a record that fails authentication ends the
//! carrier; plaintext is handed out in place, never copied.

pub mod alias;
pub mod frame;
pub mod node;
pub mod session;
pub mod ws;

pub use alias::{ALIAS_MAX, AliasTable, Assigned};
pub use frame::{
    BATCH_MAX_BYTES, BATCH_MAX_FRAMES, Batch, BatchBuilder, DnsAnswer, Frame, FrameError, MAX_FRAME_LEN,
    MAX_PACKET_LEN, Offer,
};
pub use node::NODE_ID_LEN;
pub use session::{CarrierError, Poll, ProtectedCarrier};
