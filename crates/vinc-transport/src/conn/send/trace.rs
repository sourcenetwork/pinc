//! Test-only observation of the packet builder, for trace validation (cargo feature `trace`, off by default).
//!
//! Once [`Connection::trace_pack_enable`] was called, a connection records one [`PackRecord`] per packet it seals:
//! the frames `fill_frames` wrote, the place of the last STREAM frame it kept for an implicit length, the least
//! payload the packet must have, and the payload as it was sealed (after the padding or the dropped length). The
//! log is drained with [`Connection::trace_pack_take`]. [`PackProbe`] calls the two byte functions of the builder,
//! `implicit_stream_len` and `put_stream_header`, directly. Nothing here is compiled without the feature, and
//! nothing here feeds back into the connection.

use alloc::vec::Vec;

use vinc_crypto::Provider;

use crate::conn::Connection;
use crate::stream::{StreamChunk, StreamSource};

/// The header a packet was sealed under.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PackKind {
    /// A short (1-RTT) packet.
    Short,
    /// A long 0-RTT packet under the early keys.
    ZeroRtt,
}

/// What a packet was built for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PackMode {
    /// The ordinary fill: acknowledgement, control frames, path frames, stream data, datagrams.
    Normal,
    /// The probe timeout's packet: an acknowledgement, a WAKE and a PING.
    PingOnly,
    /// A path MTU probe: an acknowledgement and a PING, padded to the probe size.
    Probe,
    /// A tail repair: an acknowledgement and stream frames sent again.
    Repair,
    /// The packet that carries CLOSE.
    Close,
}

/// One sealed packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackRecord {
    /// The header.
    pub kind: PackKind,
    /// What it was built for.
    pub mode: PackMode,
    /// Whether the connection is a client.
    pub client: bool,
    /// The packet number.
    pub pn: u64,
    /// The width of the packet number.
    pub pn_len: usize,
    /// The frames as the fill wrote them, before the padding and the implicit length.
    pub frames: Vec<u8>,
    /// Where the last STREAM frame starts and the size of its header before the length, as the fill left it.
    pub hint: Option<(usize, usize)>,
    /// The least payload the packet must have.
    pub min_payload: usize,
    /// The payload as sealed.
    pub payload: Vec<u8>,
}

/// The log of the builder.
#[derive(Debug)]
pub(crate) struct PackLog {
    /// Whether packets are recorded; off until [`Connection::trace_pack_enable`], so a connection built with the
    /// feature still allocates nothing per packet.
    pub(crate) on: bool,
    pub(crate) log: Vec<PackRecord>,
}

impl PackLog {
    pub(crate) const fn new() -> Self {
        Self {
            on: false,
            log: Vec::new(),
        }
    }
}

impl PackMode {
    /// The mode of a fill, in the order `fill_frames` tests its switches.
    pub(crate) const fn of(ping_only: bool, probe: bool, repair: bool) -> Self {
        if ping_only {
            Self::PingOnly
        } else if probe {
            Self::Probe
        } else if repair {
            Self::Repair
        } else {
            Self::Normal
        }
    }
}

conn_impl! {
    /// Start recording the packets the builder seals (they are not recorded by default).
    pub fn trace_pack_enable(&mut self) {
        self.pack.on = true;
    }

    /// The packets sealed since the last call.
    pub fn trace_pack_take(&mut self) -> Vec<PackRecord> {
        core::mem::take(&mut self.pack.log)
    }
}

/// The byte functions of the builder.
#[derive(Debug, Clone, Copy)]
pub struct PackProbe;

impl PackProbe {
    /// `implicit_stream_len`: drop the length of the STREAM frame at `at` whose header before the length is `head`
    /// bytes, if its data runs to the end of `frames`; the bytes it shrank by.
    pub fn implicit_stream_len(frames: &mut [u8], at: usize, head: usize) -> Option<usize> {
        super::implicit_stream_len(frames, at, head)
    }

    /// `put_stream_header`: write the header of a STREAM frame with a length into exactly `dst`.
    pub fn put_stream_header(dst: &mut [u8], id: u64, offset: u64, len: usize, fin: bool) -> bool {
        super::put_stream_header(dst, &StreamChunk { id, offset, len, fin })
    }
}
