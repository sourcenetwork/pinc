//! Transport parameters: what each endpoint tells the other about its limits, carried authenticated in the handshake.
//!
//! # Encoding
//!
//! A sequence of `id(varint) value(varint)` pairs, with ids strictly increasing (so sorted, no duplicates) and every
//! varint minimal. A value equal to the default is never written, and a decoder refuses one, so every parameter set has
//! exactly one encoding. An id the decoder does not know is skipped (its value must still be a varint, and ids must
//! still increase). The defaults are the minimum an endpoint can assume before it hears the peer: no data and no
//! streams, 1200-byte datagrams, a 25 ms ack delay, two connection ids, no datagram frames, no idle timeout.
//!
//! | Id | Parameter | Default |
//! |---|---|---|
//! | 1 | `initial_max_data` | 0 |
//! | 2 | `initial_max_stream_data_bidi_local` (streams the sender opened) | 0 |
//! | 3 | `initial_max_stream_data_bidi_remote` (streams the receiver opened) | 0 |
//! | 4 | `initial_max_stream_data_uni` | 0 |
//! | 5 | `initial_max_streams_bidi` | 0 |
//! | 6 | `initial_max_streams_uni` | 0 |
//! | 7 | `idle_timeout` in milliseconds (0: none) | 0 |
//! | 8 | `max_udp_payload_size` (at least 1200) | 1200 |
//! | 9 | `max_ack_delay` in milliseconds | 25 |
//! | 10 | `active_connection_id_limit` (at least 2) | 2 |
//! | 11 | `max_datagram_frame_size` (0: no datagrams) | 0 |
//! | 12 | `disable_active_migration` (the value 1) | 0 |
//!
//! Invariant: `decode(encode(p)) == p` for every valid `p`, and a decoded value re-encodes to the bytes it came from
//! (unknown parameters aside).

use core::fmt;

use vinc_wire::{Reader, Writer};

use crate::stream::{self, PeerLimits};

const INITIAL_MAX_DATA: u64 = 1;
const MAX_STREAM_DATA_BIDI_LOCAL: u64 = 2;
const MAX_STREAM_DATA_BIDI_REMOTE: u64 = 3;
const MAX_STREAM_DATA_UNI: u64 = 4;
const MAX_STREAMS_BIDI: u64 = 5;
const MAX_STREAMS_UNI: u64 = 6;
const IDLE_TIMEOUT: u64 = 7;
const MAX_UDP_PAYLOAD: u64 = 8;
const MAX_ACK_DELAY: u64 = 9;
const ACTIVE_CID_LIMIT: u64 = 10;
const MAX_DATAGRAM_FRAME: u64 = 11;
const DISABLE_MIGRATION: u64 = 12;

/// Why parameters were refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamsError {
    /// The bytes are not a sequence of well-formed pairs, or a value does not fit its parameter.
    Malformed,
    /// Ids are not strictly increasing, or a value is the default: not the canonical encoding.
    NotCanonical,
    /// A value is below the minimum its parameter allows.
    OutOfRange,
    /// The output buffer is too small.
    BufferTooSmall,
}

impl fmt::Display for ParamsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Malformed => "transport parameters are malformed",
            Self::NotCanonical => "transport parameters are not in canonical form",
            Self::OutOfRange => "a transport parameter is out of range",
            Self::BufferTooSmall => "no room for the transport parameters",
        })
    }
}

impl core::error::Error for ParamsError {}

/// The limits and options of one endpoint. `Default` is the minimum assumed before the peer is heard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "a flag of the wire format beside the numbers"
)]
pub struct TransportParams {
    /// The connection-level credit granted to the peer, in bytes.
    pub initial_max_data: u64,
    /// The credit per bidirectional stream the sender opened.
    pub max_stream_data_bidi_local: u64,
    /// The credit per bidirectional stream the receiver of the parameters opened.
    pub max_stream_data_bidi_remote: u64,
    /// The credit per unidirectional stream.
    pub max_stream_data_uni: u64,
    /// How many bidirectional streams the peer may open.
    pub max_streams_bidi: u64,
    /// How many unidirectional streams the peer may open.
    pub max_streams_uni: u64,
    /// The idle timeout in milliseconds; 0 means none.
    pub idle_timeout_ms: u64,
    /// The largest UDP payload the sender accepts, at least 1200.
    pub max_udp_payload: u64,
    /// The longest the sender delays an acknowledgement, in milliseconds.
    pub max_ack_delay_ms: u64,
    /// How many connection ids the sender keeps for the peer, at least 2.
    pub active_cid_limit: u64,
    /// The largest DATAGRAM frame the sender accepts; 0 means it accepts none.
    pub max_datagram_frame_size: u64,
    /// The sender will not move to another address, and asks the peer not to either.
    pub disable_active_migration: bool,
}

impl TransportParams {
    /// The minimum assumed before the peer's parameters are known.
    pub const MIN: Self = Self {
        initial_max_data: 0,
        max_stream_data_bidi_local: 0,
        max_stream_data_bidi_remote: 0,
        max_stream_data_uni: 0,
        max_streams_bidi: 0,
        max_streams_uni: 0,
        idle_timeout_ms: 0,
        max_udp_payload: 1200,
        max_ack_delay_ms: 25,
        active_cid_limit: 2,
        max_datagram_frame_size: 0,
        disable_active_migration: false,
    };

    /// The parameters that match a stream layer configured with `cfg`, with the other fields at generous defaults:
    /// 75 s idle, 65527-byte datagrams, 4 connection ids and 65535-byte datagram frames.
    pub const fn for_streams(cfg: &stream::Config) -> Self {
        Self {
            initial_max_data: cfg.initial_conn_window,
            max_stream_data_bidi_local: cfg.initial_stream_window,
            max_stream_data_bidi_remote: cfg.initial_stream_window,
            max_stream_data_uni: cfg.initial_stream_window,
            max_streams_bidi: cfg.max_streams_bidi,
            max_streams_uni: cfg.max_streams_uni,
            idle_timeout_ms: 75_000,
            max_udp_payload: 65_527,
            max_ack_delay_ms: 25,
            active_cid_limit: 4,
            max_datagram_frame_size: 65_535,
            disable_active_migration: false,
        }
    }

    /// What the peer lets us send, as the stream layer takes it.
    pub const fn peer_limits(&self) -> PeerLimits {
        PeerLimits {
            max_data: self.initial_max_data,
            max_stream_data_bidi_local: self.max_stream_data_bidi_local,
            max_stream_data_bidi_remote: self.max_stream_data_bidi_remote,
            max_stream_data_uni: self.max_stream_data_uni,
            max_streams_bidi: self.max_streams_bidi,
            max_streams_uni: self.max_streams_uni,
        }
    }

    /// Whether these limits are at least `other`'s: a server that remembered `other` for a ticket can still honour it.
    pub const fn covers(&self, other: &Self) -> bool {
        self.initial_max_data >= other.initial_max_data
            && self.max_stream_data_bidi_local >= other.max_stream_data_bidi_local
            && self.max_stream_data_bidi_remote >= other.max_stream_data_bidi_remote
            && self.max_stream_data_uni >= other.max_stream_data_uni
            && self.max_streams_bidi >= other.max_streams_bidi
            && self.max_streams_uni >= other.max_streams_uni
    }

    fn pairs(&self) -> [(u64, u64); 12] {
        [
            (INITIAL_MAX_DATA, self.initial_max_data),
            (MAX_STREAM_DATA_BIDI_LOCAL, self.max_stream_data_bidi_local),
            (MAX_STREAM_DATA_BIDI_REMOTE, self.max_stream_data_bidi_remote),
            (MAX_STREAM_DATA_UNI, self.max_stream_data_uni),
            (MAX_STREAMS_BIDI, self.max_streams_bidi),
            (MAX_STREAMS_UNI, self.max_streams_uni),
            (IDLE_TIMEOUT, self.idle_timeout_ms),
            (MAX_UDP_PAYLOAD, self.max_udp_payload),
            (MAX_ACK_DELAY, self.max_ack_delay_ms),
            (ACTIVE_CID_LIMIT, self.active_cid_limit),
            (MAX_DATAGRAM_FRAME, self.max_datagram_frame_size),
            (DISABLE_MIGRATION, u64::from(self.disable_active_migration)),
        ]
    }

    /// The canonical encoding into the start of `out`; returns its length.
    ///
    /// # Errors
    /// [`ParamsError::OutOfRange`] for a value the wire cannot carry (2^63 or more) or below its minimum,
    /// [`ParamsError::BufferTooSmall`] if `out` is too short.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, ParamsError> {
        if self.max_udp_payload < 1200 || self.active_cid_limit < 2 {
            return Err(ParamsError::OutOfRange);
        }
        let defaults = Self::MIN.pairs();
        let mut w = Writer::new(out);
        for ((id, v), (_, d)) in self.pairs().into_iter().zip(defaults) {
            if v == d {
                continue;
            }
            w.put_varint(id).map_err(|_| ParamsError::BufferTooSmall)?;
            w.put_varint(v).map_err(|_| ParamsError::OutOfRange)?;
        }
        Ok(w.written().len())
    }

    /// Parse canonical parameters. Unknown ids are skipped.
    ///
    /// # Errors
    /// [`ParamsError::Malformed`], [`ParamsError::NotCanonical`] or [`ParamsError::OutOfRange`].
    pub fn decode(bytes: &[u8]) -> Result<Self, ParamsError> {
        let mut p = Self::MIN;
        let mut r = Reader::new(bytes);
        let mut last = 0u64;
        while !r.is_empty() {
            let id = r.read_varint().map_err(|_| ParamsError::Malformed)?;
            let v = r.read_varint().map_err(|_| ParamsError::Malformed)?;
            if id <= last {
                return Err(ParamsError::NotCanonical);
            }
            last = id;
            let slot = match id {
                INITIAL_MAX_DATA => &mut p.initial_max_data,
                MAX_STREAM_DATA_BIDI_LOCAL => &mut p.max_stream_data_bidi_local,
                MAX_STREAM_DATA_BIDI_REMOTE => &mut p.max_stream_data_bidi_remote,
                MAX_STREAM_DATA_UNI => &mut p.max_stream_data_uni,
                MAX_STREAMS_BIDI => &mut p.max_streams_bidi,
                MAX_STREAMS_UNI => &mut p.max_streams_uni,
                IDLE_TIMEOUT => &mut p.idle_timeout_ms,
                MAX_UDP_PAYLOAD => &mut p.max_udp_payload,
                MAX_ACK_DELAY => &mut p.max_ack_delay_ms,
                ACTIVE_CID_LIMIT => &mut p.active_cid_limit,
                MAX_DATAGRAM_FRAME => &mut p.max_datagram_frame_size,
                DISABLE_MIGRATION => {
                    if v != 1 {
                        return Err(if v == 0 {
                            ParamsError::NotCanonical
                        } else {
                            ParamsError::OutOfRange
                        });
                    }
                    p.disable_active_migration = true;
                    continue;
                }
                _ => continue,
            };
            *slot = v;
        }
        // A value equal to the default would have been left out of the canonical form.
        let defaults = Self::MIN.pairs();
        let seen = p.pairs();
        let mut r = Reader::new(bytes);
        while !r.is_empty() {
            let id = r.read_varint().map_err(|_| ParamsError::Malformed)?;
            let v = r.read_varint().map_err(|_| ParamsError::Malformed)?;
            if let Some(i) = seen.iter().position(|(k, _)| *k == id)
                && defaults.get(i).is_some_and(|(_, d)| *d == v)
            {
                return Err(ParamsError::NotCanonical);
            }
        }
        if p.max_udp_payload < 1200 || p.active_cid_limit < 2 {
            return Err(ParamsError::OutOfRange);
        }
        Ok(p)
    }
}

impl Default for TransportParams {
    fn default() -> Self {
        Self::MIN
    }
}
