//! Frame encoding and the size functions the packet builder uses to fit frames.

use vinc_wire::{Writer, varint};

use super::{EXTENSION_BASE, Frame, FrameError, MAX_STREAM_END, ty};

/// The most a varint can hold: values from 2^63 are refused.
const VARINT_LIMIT: u64 = 1 << 63;

fn vlen(v: u64) -> usize {
    varint::encoded_len(v)
}

/// The bytes a STREAM frame spends besides its data: type, stream id, the offset when `offset` is not 0 and, unless
/// `implicit_len`, the length of `data_len` bytes of data.
pub fn stream_overhead(id: u64, offset: u64, data_len: usize, implicit_len: bool) -> usize {
    1 + vlen(id) + if offset == 0 { 0 } else { vlen(offset) } + if implicit_len { 0 } else { vlen(data_len as u64) }
}

/// The bytes a DATAGRAM frame spends besides its data: the type and, unless `implicit_len`, the length of
/// `data_len` bytes of data.
pub fn datagram_overhead(data_len: usize, implicit_len: bool) -> usize {
    1 + if implicit_len { 0 } else { vlen(data_len as u64) }
}

fn prefixed_len(bytes: &[u8]) -> usize {
    vlen(bytes.len() as u64) + bytes.len()
}

impl Frame<'_> {
    /// The varint fields of the frame, zero if unused: all must be below 2^63 to encode.
    fn varint_fields(&self) -> [u64; 3] {
        match *self {
            Self::ResetStream { id, error, final_size } => [id, error, final_size],
            Self::StopSending { id, error } | Self::MaxStreamData { id, max: error } => [id, error, 0],
            Self::Stream { id, offset, .. } => [id, offset, 0],
            Self::MaxData { max: v }
            | Self::MaxStreams { max: v, .. }
            | Self::DataBlocked { limit: v }
            | Self::StreamsBlocked { limit: v, .. }
            | Self::RetireConnectionId { seq: v }
            | Self::ApplicationClose { error: v, .. }
            | Self::Extension { ty: v, .. } => [v, 0, 0],
            Self::StreamDataBlocked { id, limit } => [id, limit, 0],
            Self::NewConnectionId {
                seq, retire_prior_to, ..
            } => [seq, retire_prior_to, 0],
            Self::Close { error, frame_type, .. } => [error, frame_type, 0],
            _ => [0; 3],
        }
    }

    /// The exact number of bytes [`write`](Self::write) writes for this frame.
    pub fn encoded_len(&self) -> usize {
        match *self {
            Self::Padding { len } => len,
            Self::Ping | Self::Sleep | Self::Wake | Self::Ready => 1,
            Self::Ack(ref ack) => 1 + ack.body_len(),
            Self::ResetStream { id, error, final_size } => 1 + vlen(id) + vlen(error) + vlen(final_size),
            Self::StopSending { id, error } => 1 + vlen(id) + vlen(error),
            Self::NewToken { token } => 1 + prefixed_len(token),
            Self::Stream {
                id,
                offset,
                data,
                implicit_len,
                ..
            } => stream_overhead(id, offset, data.len(), implicit_len) + data.len(),
            Self::MaxData { max: v }
            | Self::DataBlocked { limit: v }
            | Self::RetireConnectionId { seq: v }
            | Self::MaxStreams { max: v, .. }
            | Self::StreamsBlocked { limit: v, .. } => 1 + vlen(v),
            Self::MaxStreamData { id, max: v } | Self::StreamDataBlocked { id, limit: v } => 1 + vlen(id) + vlen(v),
            Self::NewConnectionId {
                seq,
                retire_prior_to,
                cid,
                ..
            } => 1 + vlen(seq) + vlen(retire_prior_to) + 1 + cid.as_bytes().len() + super::RESET_TOKEN_LEN,
            Self::PathChallenge(_) | Self::PathResponse(_) => 1 + 8,
            Self::Close {
                error,
                frame_type,
                reason,
            } => 1 + vlen(error) + vlen(frame_type) + prefixed_len(reason),
            Self::ApplicationClose { error, reason } => 1 + vlen(error) + prefixed_len(reason),
            Self::Datagram { data, implicit_len } => datagram_overhead(data.len(), implicit_len) + data.len(),
            Self::MtuProbeEcho { .. } => 1 + 2,
            Self::Extension { ty, body } => vlen(ty) + prefixed_len(body),
        }
    }

    /// Reject a frame that cannot be encoded, before any byte is written.
    fn validate(&self) -> Result<(), FrameError> {
        if self.varint_fields().iter().any(|v| *v >= VARINT_LIMIT) {
            return Err(vinc_wire::WireError::VarintOverflow.into());
        }
        match *self {
            Self::Stream { offset, data, .. } if offset.saturating_add(data.len() as u64) > MAX_STREAM_END => {
                Err(FrameError::StreamEnd)
            }
            Self::NewConnectionId { cid, .. } if cid.as_bytes().is_empty() => Err(FrameError::ConnId),
            Self::NewConnectionId {
                seq, retire_prior_to, ..
            } if retire_prior_to > seq => Err(FrameError::RetirePriorTo),
            Self::Extension { ty, .. } if ty < EXTENSION_BASE => Err(FrameError::UnknownType(ty)),
            _ => Ok(()),
        }
    }

    /// Encode the frame. A canonical encoding is chosen: the OFF bit is set exactly when the offset is not 0. The
    /// frame and the room are checked first, so nothing is written on an error.
    ///
    /// # Errors
    /// [`FrameError::Wire`] if the buffer is too small or a field is 2^63 or more, [`FrameError::StreamEnd`],
    /// [`FrameError::ConnId`], [`FrameError::RetirePriorTo`], or [`FrameError::UnknownType`] for an extension
    /// below `0x40`.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), FrameError> {
        self.validate()?;
        w.ensure(self.encoded_len())?;
        match *self {
            Self::Padding { len } => {
                const ZEROS: [u8; 64] = [0; 64];
                let mut left = len;
                while left > 0 {
                    let n = left.min(ZEROS.len());
                    w.put_slice(ZEROS.get(..n).unwrap_or_default())?;
                    left -= n;
                }
            }
            Self::Ping => w.put_varint(ty::PING)?,
            Self::Sleep => w.put_varint(ty::SLEEP)?,
            Self::Wake => w.put_varint(ty::WAKE)?,
            Self::Ready => w.put_varint(ty::READY)?,
            Self::Ack(ref ack) => {
                w.put_varint(ty::ACK)?;
                ack.write_body(w)?;
            }
            Self::ResetStream { id, error, final_size } => put(w, ty::RESET_STREAM, &[id, error, final_size])?,
            Self::StopSending { id, error } => put(w, ty::STOP_SENDING, &[id, error])?,
            Self::NewToken { token } => {
                w.put_varint(ty::NEW_TOKEN)?;
                put_bytes(w, token)?;
            }
            Self::Stream { .. } => self.write_stream(w)?,
            Self::MaxData { max } => put(w, ty::MAX_DATA, &[max])?,
            Self::MaxStreamData { id, max } => put(w, ty::MAX_STREAM_DATA, &[id, max])?,
            Self::MaxStreams { bidi, max } => put(
                w,
                if bidi {
                    ty::MAX_STREAMS_BIDI
                } else {
                    ty::MAX_STREAMS_UNI
                },
                &[max],
            )?,
            Self::DataBlocked { limit } => put(w, ty::DATA_BLOCKED, &[limit])?,
            Self::StreamDataBlocked { id, limit } => put(w, ty::STREAM_DATA_BLOCKED, &[id, limit])?,
            Self::StreamsBlocked { bidi, limit } => put(
                w,
                if bidi {
                    ty::STREAMS_BLOCKED_BIDI
                } else {
                    ty::STREAMS_BLOCKED_UNI
                },
                &[limit],
            )?,
            Self::NewConnectionId { .. } => self.write_new_cid(w)?,
            Self::RetireConnectionId { seq } => put(w, ty::RETIRE_CONNECTION_ID, &[seq])?,
            Self::PathChallenge(data) => {
                w.put_varint(ty::PATH_CHALLENGE)?;
                w.put_slice(&data)?;
            }
            Self::PathResponse(data) => {
                w.put_varint(ty::PATH_RESPONSE)?;
                w.put_slice(&data)?;
            }
            Self::Close {
                error,
                frame_type,
                reason,
            } => {
                put(w, ty::CLOSE, &[error, frame_type])?;
                put_bytes(w, reason)?;
            }
            Self::ApplicationClose { error, reason } => {
                put(w, ty::APPLICATION_CLOSE, &[error])?;
                put_bytes(w, reason)?;
            }
            Self::Datagram { data, implicit_len } => {
                if implicit_len {
                    w.put_varint(ty::DATAGRAM)?;
                    w.put_slice(data)?;
                } else {
                    w.put_varint(ty::DATAGRAM_LEN)?;
                    put_bytes(w, data)?;
                }
            }
            Self::MtuProbeEcho { mtu } => {
                w.put_varint(ty::MTU_PROBE_ECHO)?;
                w.put_u16(mtu)?;
            }
            Self::Extension { ty, body } => {
                w.put_varint(ty)?;
                put_bytes(w, body)?;
            }
        }
        Ok(())
    }

    fn write_stream(&self, w: &mut Writer<'_>) -> Result<(), FrameError> {
        let Self::Stream {
            id,
            offset,
            fin,
            data,
            implicit_len,
        } = *self
        else {
            return Ok(());
        };
        let flags = (if offset == 0 { 0 } else { ty::STREAM_OFF })
            | (if implicit_len { 0 } else { ty::STREAM_LEN })
            | u64::from(fin);
        put(w, ty::STREAM | flags, &[id])?;
        if offset != 0 {
            w.put_varint(offset)?;
        }
        if implicit_len {
            w.put_slice(data)?;
        } else {
            put_bytes(w, data)?;
        }
        Ok(())
    }

    fn write_new_cid(&self, w: &mut Writer<'_>) -> Result<(), FrameError> {
        let Self::NewConnectionId {
            seq,
            retire_prior_to,
            cid,
            token,
        } = *self
        else {
            return Ok(());
        };
        put(w, ty::NEW_CONNECTION_ID, &[seq, retire_prior_to])?;
        let bytes = cid.as_bytes();
        w.put_u8(u8::try_from(bytes.len()).map_err(|_| FrameError::ConnId)?)?;
        w.put_slice(bytes)?;
        w.put_slice(&token)?;
        Ok(())
    }
}

/// A type followed by varint fields.
fn put(w: &mut Writer<'_>, t: u64, fields: &[u64]) -> Result<(), FrameError> {
    w.put_varint(t)?;
    fields.iter().try_for_each(|f| w.put_varint(*f))?;
    Ok(())
}

/// A varint length and the bytes.
fn put_bytes(w: &mut Writer<'_>, bytes: &[u8]) -> Result<(), FrameError> {
    w.put_varint(bytes.len() as u64)?;
    w.put_slice(bytes)?;
    Ok(())
}
