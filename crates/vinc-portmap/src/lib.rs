//! VINC port mapping: a SANS-IO client that asks the home gateway for a UDP mapping of the node's socket, so a node
//! behind a home router can be reached directly (SYS-CON-03).
//!
//! The client ([`PortMap`]) talks PCP (RFC 6887), falls back to NAT-PMP (RFC 6886) and then to `UPnP`-IGD, renews the
//! lease half way, notices a gateway that restarted by its epoch, and deletes the mapping when stopped. It has no
//! clock, socket or thread: the host hands it time, the datagrams it [`owns`](PortMap::owns) and the answers to its
//! HTTP requests, and takes the datagrams and HTTP requests it wants sent ([`PortMap::poll_datagram`],
//! [`PortMap::poll_http`]) and the time it next wants to run ([`PortMap::poll_timeout`]).
//!
//! The codecs ([`pcp`], [`natpmp`], [`upnp`]) are length-checked, take one valid form, and never panic. The lease
//! arithmetic is in [`lease`].
#![no_std]
#![forbid(unsafe_code)]

pub mod addr;
pub mod client;
pub mod lease;
pub mod natpmp;
pub mod pcp;
mod text;
pub mod upnp;

pub use client::{Config, PortMap, Proto, Stats};

/// The most bytes of an HTTP answer the host hands over; a longer answer is cut there.
pub const MAX_RESPONSE: usize = 16 * 1024;
/// A buffer this large holds any datagram the client sends.
pub const MAX_DATAGRAM: usize = 256;
