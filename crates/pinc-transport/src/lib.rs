//! PINCER, the PINC transport: a SANS-IO connection over opaque datagram paths.
//!
//! Time, received datagrams and application calls go in; datagrams to send, timers and events come out. Nothing here
//! allocates per packet, blocks, or reads a clock: memory comes from a charged buffer pool, and every table is bounded.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod conn;
pub mod frame;
pub mod packet;
pub mod recovery;
pub mod stream;
