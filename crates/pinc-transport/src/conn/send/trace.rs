//! Test-only observation of the packet builder, for trace validation (cargo feature `trace`, off by default).
//!
//! Once [`Connection::trace_pack_enable`] was called, a connection records one [`PackRecord`] per packet it seals:
//! what it was built for, whether its fill took the pending tail repair and whether one is still pending, the frames
//! `fill_frames` wrote, the place of the last STREAM frame it kept for an implicit length, the least payload the
//! packet must have, and the payload as it was sealed (after the padding or the dropped length). The
//! log is drained with [`Connection::trace_pack_take`]. [`PackProbe`] calls the two byte functions of the builder,
//! `implicit_stream_len` and `put_stream_header`, directly. Nothing here is compiled without the feature, and
//! nothing here feeds back into the connection.

use alloc::vec::Vec;

use pinc_crypto::Provider;

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
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent observations of one packet, recorded as the code holds them"
)]
pub struct PackRecord {
    /// The header.
    pub kind: PackKind,
    /// What it was built for.
    pub mode: PackMode,
    /// Whether the connection is a client.
    pub client: bool,
    /// The fill took the pending tail repair (the packet is built as one).
    pub repair_taken: bool,
    /// A tail repair is still pending as the packet is sealed (one this packet's own data makes is set after).
    pub repair_left: bool,
    /// The packet goes on the active path.
    pub active: bool,
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

/// One call of `build_datagram`: its inputs and what it wrote (cargo feature `trace`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent observations of one datagram, recorded as the code holds them"
)]
pub struct DgramRecord {
    /// The path's datagram size (`path_mtu`).
    pub path_mtu: u16,
    /// The interface MTU of the path; 1228 when the path is gone (the code's room is then `MIN_MTU`).
    pub interface_mtu: u16,
    /// Whether the path is IPv6 (false when the path is gone).
    pub v6: bool,
    /// The caller's buffer (`out.len()`).
    pub out: usize,
    /// `amp_room(ti)`, saturated at 1_000_000.
    pub amp: usize,
    /// The probe size, 0 for none.
    pub probe: usize,
    /// `whole_len() + FLIGHT_OVERHEAD` when the flight may leave split and whole, else 0.
    pub flight: usize,
    /// The zero padding the handshake owed this datagram: `padding_owed()` when no fragment was written, else
    /// `pad_due(hs_len)`, read before the accounting.
    pub pad_owed: usize,
    /// The handshake fragment written.
    pub hs: usize,
    /// The application packet written.
    pub app: usize,
    /// The padding written.
    pub pad: usize,
    /// The length returned (0 for none).
    pub len: usize,
}

/// The log of `build_datagram`.
#[derive(Debug)]
pub(crate) struct DgramLog {
    /// Whether calls are recorded; off until [`Connection::trace_dgram_enable`].
    pub(crate) on: bool,
    pub(crate) log: Vec<DgramRecord>,
}

impl DgramLog {
    pub(crate) const fn new() -> Self {
        Self {
            on: false,
            log: Vec::new(),
        }
    }
}

conn_impl! {
    /// Start recording the datagrams `build_datagram` writes (they are not recorded by default).
    pub fn trace_dgram_enable(&mut self) {
        self.dgram.on = true;
    }

    /// The calls recorded since the last call.
    pub fn trace_dgram_take(&mut self) -> Vec<DgramRecord> {
        core::mem::take(&mut self.dgram.log)
    }

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
