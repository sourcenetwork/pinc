//! Zero-copy frame decoding and the frame iterator.

use vinc_security::{Rekey, TicketBatch};
use vinc_wire::{Reader, WireError};

use super::{Ack, EXTENSION_BASE, Frame, FrameError, MAX_STREAM_END, ty};

/// A varint length, then that many bytes borrowed from the payload.
fn read_len_prefixed<'a>(r: &mut Reader<'a>) -> Result<&'a [u8], FrameError> {
    let len = usize::try_from(r.read_varint()?).map_err(|_| WireError::Truncated { needed: usize::MAX })?;
    Ok(r.read_bytes(len)?)
}

impl<'a> Frame<'a> {
    /// Decode one frame from the start of `r`, consuming at least one byte on success.
    ///
    /// # Errors
    /// [`FrameError::UnknownType`] for an unassigned type below `0x40`, [`FrameError::Wire`] for a truncated field
    /// or a bad varint, and the validation errors of the individual frames (see [`FrameError`]).
    pub fn decode(r: &mut Reader<'a>) -> Result<Self, FrameError> {
        let t = r.read_varint()?;
        Ok(match t {
            ty::PADDING => {
                // The rest of the payload, seen through a copy of the reader, scanned for the end of the zero run.
                let mut probe = *r;
                let rest = probe.read_bytes(probe.remaining())?;
                let more = rest.iter().position(|b| *b != 0).unwrap_or(rest.len());
                r.read_bytes(more)?;
                Self::Padding { len: more + 1 }
            }
            ty::PING => Self::Ping,
            ty::ACK => Self::Ack(Ack::parse(r)?),
            ty::RESET_STREAM => Self::ResetStream {
                id: r.read_varint()?,
                error: r.read_varint()?,
                final_size: r.read_varint()?,
            },
            ty::STOP_SENDING => Self::StopSending {
                id: r.read_varint()?,
                error: r.read_varint()?,
            },
            ty::STREAM..=ty::STREAM_LAST => Self::decode_stream(t, r)?,
            ty::MAX_STREAM_DATA => Self::MaxStreamData {
                id: r.read_varint()?,
                max: r.read_varint()?,
            },
            ty::PATH_CHALLENGE => Self::PathChallenge(r.read_array()?),
            ty::PATH_RESPONSE => Self::PathResponse(r.read_array()?),
            ty::CLOSE => Self::Close {
                error: r.read_varint()?,
            },
            ty::DATAGRAM => Self::Datagram {
                data: r.read_bytes(r.remaining())?,
                implicit_len: true,
            },
            ty::DATAGRAM_LEN => Self::Datagram {
                data: read_len_prefixed(r)?,
                implicit_len: false,
            },
            ty::MTU_PROBE_ECHO => Self::MtuProbeEcho { mtu: r.read_u16()? },
            ty::SLEEP => Self::Sleep,
            ty::WAKE => Self::Wake,
            ty::REKEY => Self::decode_rekey(r)?,
            ty::READY => Self::Ready,
            ty::NEW_TICKETS => Self::NewTickets(TicketBatch::read(r)?),
            t if t >= EXTENSION_BASE => Self::Extension {
                ty: t,
                body: read_len_prefixed(r)?,
            },
            t => return Err(FrameError::UnknownType(t)),
        })
    }

    fn decode_stream(t: u64, r: &mut Reader<'a>) -> Result<Self, FrameError> {
        let id = r.read_varint()?;
        let offset = if t & ty::STREAM_OFF != 0 { r.read_varint()? } else { 0 };
        let implicit_len = t & ty::STREAM_LEN == 0;
        let data = if implicit_len {
            r.read_bytes(r.remaining())?
        } else {
            read_len_prefixed(r)?
        };
        if offset
            .checked_add(data.len() as u64)
            .is_none_or(|end| end > MAX_STREAM_END)
        {
            return Err(FrameError::StreamEnd);
        }
        Ok(Self::Stream {
            id,
            offset,
            fin: t & ty::STREAM_FIN != 0,
            data,
            implicit_len,
        })
    }

    fn decode_rekey(r: &mut Reader<'a>) -> Result<Self, FrameError> {
        Rekey::read(r).map(Self::Rekey).map_err(|e| {
            if e == WireError::Unexpected("rekey kind") {
                FrameError::RekeyKind
            } else {
                e.into()
            }
        })
    }
}

/// An iterator over the frames of a decrypted payload. It yields each frame in order and stops after the first
/// error, so a malformed payload is never half-read past the fault.
#[derive(Debug, Clone)]
pub struct FrameIter<'a> {
    r: Reader<'a>,
}

impl<'a> FrameIter<'a> {
    /// Iterate over the frames of `payload`.
    pub const fn new(payload: &'a [u8]) -> Self {
        Self {
            r: Reader::new(payload),
        }
    }
}

impl<'a> Iterator for FrameIter<'a> {
    type Item = Result<Frame<'a>, FrameError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.r.is_empty() {
            return None;
        }
        let frame = Frame::decode(&mut self.r);
        if frame.is_err() {
            self.r = Reader::new(&[]);
        }
        Some(frame)
    }
}
