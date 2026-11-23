//! Datagrams over a serial line: each one is byte-stuffed (COBS) and ends with a zero byte.
//!
//! No byte of an encoded datagram is zero, so a receiver that joins the line in mid-frame, or loses bytes, is in step
//! again at the next zero. A damaged frame decodes to bytes the endpoint's packet protection rejects, exactly as it
//! rejects a damaged datagram from a network.

/// The most bytes [`encode`] writes for `len` bytes of datagram, with the closing zero.
pub const fn encoded_max(len: usize) -> usize {
    len + len / 254 + 2
}

/// Write `src` as one frame into `out`, with its closing zero. Returns the frame's length, or `None` when `out` is
/// shorter than [`encoded_max`] of the datagram.
pub fn encode(src: &[u8], out: &mut [u8]) -> Option<usize> {
    if out.len() < encoded_max(src.len()) {
        return None;
    }
    let mut code_at = 0;
    let mut w = 1;
    let mut code = 1u8;
    for &b in src {
        if b == 0 {
            *out.get_mut(code_at)? = code;
            code_at = w;
            w += 1;
            code = 1;
        } else {
            *out.get_mut(w)? = b;
            w += 1;
            code += 1;
            if code == 0xff {
                *out.get_mut(code_at)? = code;
                code_at = w;
                w += 1;
                code = 1;
            }
        }
    }
    *out.get_mut(code_at)? = code;
    *out.get_mut(w)? = 0;
    Some(w + 1)
}

/// Undo the stuffing of one frame (without its closing zero) in place. Returns the datagram's length, or `None` for
/// bytes no encoder writes.
fn decode_in_place(buf: &mut [u8]) -> Option<usize> {
    let (mut r, mut w) = (0, 0);
    while r < buf.len() {
        let code = usize::from(*buf.get(r)?);
        if code == 0 || r + code > buf.len() {
            return None;
        }
        buf.copy_within(r + 1..r + code, w);
        w += code - 1;
        r += code;
        if code != 0xff && r < buf.len() {
            *buf.get_mut(w)? = 0;
            w += 1;
        }
    }
    Some(w)
}

/// Collects the bytes of the line into datagrams of up to `M` encoded bytes.
pub struct Deframer<const M: usize> {
    buf: [u8; M],
    len: usize,
    /// The frame under way is longer than the buffer: its bytes are dropped up to the next zero.
    overrun: bool,
}

impl<const M: usize> Deframer<M> {
    /// An empty deframer.
    pub const fn new() -> Self {
        Self {
            buf: [0; M],
            len: 0,
            overrun: false,
        }
    }

    /// Take one byte of the line. When it closes a frame, the datagram is returned; it is valid until the next call.
    pub fn push(&mut self, byte: u8) -> Option<&mut [u8]> {
        if byte != 0 {
            match self.buf.get_mut(self.len) {
                Some(slot) if !self.overrun => {
                    *slot = byte;
                    self.len += 1;
                }
                _ => self.overrun = true,
            }
            return None;
        }
        let (len, overrun) = (self.len, self.overrun);
        self.len = 0;
        self.overrun = false;
        if overrun || len == 0 {
            return None;
        }
        let frame = self.buf.get_mut(..len)?;
        let n = decode_in_place(frame)?;
        frame.get_mut(..n)
    }
}

impl<const M: usize> Default for Deframer<M> {
    fn default() -> Self {
        Self::new()
    }
}
