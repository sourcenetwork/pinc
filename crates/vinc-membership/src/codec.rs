//! The hub stream codec: `len32 | type | topic_len | topic | rest`.
//!
//! Membership owns six frame types (HELLO, ACK, DELTA, SNAP, PROBE, DOWN). Every other type, FLOOR and the topic
//! frames included, passes through as [`Other`] for the broadcast layer. Parsing is strict and zero-copy: a frame
//! with a wrong length, a stray byte, a reserved flag or an out-of-range value is an error, never a guess, and the
//! views borrow the input.
//!
//! Invariants: [`Frame::parse`] and [`Frame::read`] never panic and never read outside the input; a frame that
//! parses encodes back to the same bytes; the body of a frame is at most [`MAX_BODY`] bytes.

use vinc_wire::{Reader, WireError, Writer};

/// A node id: the 32-byte public identity of a member or hub.
pub type NodeId = [u8; 32];

/// The largest frame body (everything after the length prefix).
pub const MAX_BODY: usize = 262_144;
/// The size of one roster entry on the wire: member 32, incarnation 8, version 2, address hash 8, alive 1.
pub const ENTRY_LEN: usize = 51;
/// The size of a HELLO body after the header.
pub const HELLO_LEN: usize = 19;
/// The most entries one SNAP frame carries.
pub const SNAP_MAX: usize = 4096;
/// How many entries a sender puts in one SNAP frame before it sets the continuation bit.
pub const SNAP_CHUNK: usize = 64;
/// The most probes a DOWN proof lists.
pub const MAX_PROBES: usize = 4;

/// Frame type numbers.
pub mod ty {
    /// Lease renewal and attachment.
    pub const HELLO: u8 = 1;
    /// Answer to a HELLO that needs no snapshot.
    pub const ACK: u8 = 2;
    /// One roster change.
    pub const DELTA: u8 = 3;
    /// A roster snapshot.
    pub const SNAP: u8 = 4;
    /// A liveness probe.
    pub const PROBE: u8 = 12;
    /// A hub's report that a member is down, with proof.
    pub const DOWN: u8 = 13;
    /// The replay floor (carried opaquely for the broadcast layer).
    pub const FLOOR: u8 = 14;
}

/// Why bytes are not a frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameError {
    /// A read or write ran past the buffer.
    Wire(WireError),
    /// The length prefix names a body larger than [`MAX_BODY`].
    TooLarge,
    /// The frame violates the format, named by the reason.
    Malformed(&'static str),
}

impl From<WireError> for FrameError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl core::fmt::Display for FrameError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "frame cut short: {e}"),
            Self::TooLarge => f.write_str("frame is larger than the limit"),
            Self::Malformed(why) => write!(f, "malformed frame: {why}"),
        }
    }
}

impl core::error::Error for FrameError {}

/// What a node announces about itself: incarnation, stack version and address hash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Record {
    /// Incarnation word: 48-bit epoch in the high bits, 16-bit record sequence in the low bits.
    pub inc: u64,
    /// The stack version.
    pub ver: u16,
    /// The address hash (the identity ticket, folded with the move tag).
    pub thash: [u8; 8],
}

/// HELLO: a member renews its lease and says what it wants back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hello {
    /// The sender's record.
    pub rec: Record,
    /// Send a snapshot (flag bit 0).
    pub snap: bool,
    /// The receiving hub is the sender's primary, so the sender wants view deltas from it (flag bit 1).
    pub homed: bool,
}

/// The state a DELTA entry reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Alive {
    /// The member is down.
    Down = 0,
    /// The member is alive.
    Alive = 1,
    /// The member left gracefully.
    Left = 2,
}

/// One roster entry, borrowed from the frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Entry<'a> {
    /// The member.
    pub member: &'a NodeId,
    /// Its record.
    pub rec: Record,
    /// Its state.
    pub alive: Alive,
}

fn entry(b: &[u8]) -> Result<Entry<'_>, FrameError> {
    let mut r = Reader::new(b);
    let member = <&NodeId>::try_from(r.read_bytes(32)?).map_err(|_| FrameError::Malformed("member id"))?;
    let rec = Record {
        inc: r.read_u64()?,
        ver: r.read_u16()?,
        thash: r.read_array()?,
    };
    let alive = match r.read_u8()? {
        0 => Alive::Down,
        1 => Alive::Alive,
        2 => Alive::Left,
        _ => return Err(FrameError::Malformed("alive byte")),
    };
    Ok(Entry { member, rec, alive })
}

/// The bytes of one entry, as [`Snap`] and DELTA carry it.
pub fn entry_bytes(member: &NodeId, rec: &Record, alive: Alive) -> [u8; ENTRY_LEN] {
    let mut out = [0u8; ENTRY_LEN];
    let mut w = Writer::new(&mut out);
    // The buffer is exactly one entry long, so none of these writes can fail.
    let _ = w.put_slice(member);
    let _ = w.put_u64(rec.inc);
    let _ = w.put_u16(rec.ver);
    let _ = w.put_slice(&rec.thash);
    let _ = w.put_u8(alive as u8);
    out
}

/// A snapshot frame: a flag byte and entries, all alive, borrowed from the frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Snap<'a> {
    /// The sending hub is younger than a lease, so its roster may be incomplete (flag bit 0).
    pub partial: bool,
    /// More SNAP frames of the same snapshot follow (flag bit 1).
    pub more: bool,
    entries: &'a [u8],
}

impl<'a> Snap<'a> {
    /// A snapshot frame over `entries`, which must be whole alive entries (see [`entry_bytes`]).
    ///
    /// # Errors
    /// [`FrameError::Malformed`] if `entries` is not a whole number of alive entries, or is more than [`SNAP_MAX`].
    pub fn new(partial: bool, more: bool, entries: &'a [u8]) -> Result<Self, FrameError> {
        let (chunks, rest) = entries.as_chunks::<ENTRY_LEN>();
        if !rest.is_empty() || chunks.len() > SNAP_MAX {
            return Err(FrameError::Malformed("snapshot size"));
        }
        for c in chunks {
            if entry(c)?.alive != Alive::Alive {
                return Err(FrameError::Malformed("snapshot entry is not alive"));
            }
        }
        Ok(Self { partial, more, entries })
    }

    /// How many entries the frame carries.
    pub fn len(&self) -> usize {
        self.entries.len() / ENTRY_LEN
    }

    /// Whether the frame carries no entry.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The entries, in order.
    pub fn entries(&self) -> impl Iterator<Item = Entry<'a>> + use<'a> {
        self.entries
            .as_chunks::<ENTRY_LEN>()
            .0
            .iter()
            .filter_map(|c| entry(c).ok())
    }
}

/// Which path carried a probe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Path {
    /// The hub session as the transport routes it (through the member's carrier).
    Session = 0,
    /// The member's validated direct UDP path.
    Direct = 1,
    /// Another hub's relay.
    Relay = 2,
}

/// One unanswered probe in a DOWN proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Probe {
    /// How long before the DOWN was sent the probe went out, in milliseconds.
    pub age_ms: u32,
    /// The path it took.
    pub path: Path,
}

/// The evidence behind a DOWN: how long the sender heard nothing, and the probes that went unanswered.
///
/// Times are durations, never instants, so hubs need no common clock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Proof {
    /// How long the sender heard nothing from the member, in milliseconds.
    pub silence_ms: u32,
    probes: [Probe; MAX_PROBES],
    n: u8,
}

impl Proof {
    /// A proof of `silence_ms` and the given probes (one to [`MAX_PROBES`]).
    pub fn new(silence_ms: u32, probes: &[Probe]) -> Option<Self> {
        if probes.is_empty() || probes.len() > MAX_PROBES {
            return None;
        }
        let mut p = [Probe {
            age_ms: 0,
            path: Path::Session,
        }; MAX_PROBES];
        for (d, s) in p.iter_mut().zip(probes) {
            *d = *s;
        }
        Some(Self {
            silence_ms,
            probes: p,
            n: u8::try_from(probes.len()).ok()?,
        })
    }

    /// The probes, oldest first.
    pub fn probes(&self) -> &[Probe] {
        self.probes.get(..usize::from(self.n)).unwrap_or_default()
    }

    /// Whether probes went out on at least two different paths.
    pub fn independent(&self) -> bool {
        let ps = self.probes();
        ps.iter().any(|a| ps.iter().any(|b| a.path != b.path))
    }
}

/// DOWN: a hub reports a member down.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Down<'a> {
    /// The member.
    pub member: &'a NodeId,
    /// The incarnation the hub held for it.
    pub inc: u64,
    /// The evidence.
    pub proof: Proof,
}

/// A frame the broadcast layer owns, passed through untouched.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Other<'a> {
    /// The frame type.
    pub ty: u8,
    /// The topic (empty for frames that have none).
    pub topic: &'a [u8],
    /// The rest of the frame.
    pub rest: &'a [u8],
}

/// A hub stream frame, borrowing the bytes it was parsed from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Frame<'a> {
    /// See [`Hello`].
    Hello(Hello),
    /// An empty answer to a HELLO.
    Ack,
    /// One roster change.
    Delta(Entry<'a>),
    /// A roster snapshot.
    Snap(Snap<'a>),
    /// A liveness probe.
    Probe,
    /// See [`Down`].
    Down(Down<'a>),
    /// Any other type, for the broadcast layer.
    Other(Other<'a>),
}

fn only(r: &Reader<'_>, what: &'static str) -> Result<(), FrameError> {
    if r.is_empty() {
        Ok(())
    } else {
        Err(FrameError::Malformed(what))
    }
}

impl<'a> Frame<'a> {
    /// Parse one frame body (the bytes after the length prefix).
    ///
    /// # Errors
    /// [`FrameError`] for any deviation from the format.
    pub fn parse(body: &'a [u8]) -> Result<Self, FrameError> {
        let mut r = Reader::new(body);
        let ty = r.read_u8()?;
        let tl = usize::from(r.read_u8()?);
        let topic = r.read_bytes(tl)?;
        if !topic.is_empty() && matches!(ty, ty::HELLO | ty::ACK | ty::DELTA | ty::SNAP | ty::PROBE | ty::DOWN) {
            return Err(FrameError::Malformed("membership frame with a topic"));
        }
        match ty {
            ty::HELLO => {
                let rec = Record {
                    inc: r.read_u64()?,
                    ver: r.read_u16()?,
                    thash: r.read_array()?,
                };
                let flags = r.read_u8()?;
                if flags & !3 != 0 {
                    return Err(FrameError::Malformed("reserved HELLO flag"));
                }
                only(&r, "HELLO length")?;
                Ok(Self::Hello(Hello {
                    rec,
                    snap: flags & 1 != 0,
                    homed: flags & 2 != 0,
                }))
            }
            ty::ACK => only(&r, "ACK is empty").map(|()| Self::Ack),
            ty::PROBE => only(&r, "PROBE is empty").map(|()| Self::Probe),
            ty::DELTA => {
                let e = entry(r.read_bytes(ENTRY_LEN)?)?;
                only(&r, "DELTA length")?;
                Ok(Self::Delta(e))
            }
            ty::SNAP => {
                let flags = r.read_u8()?;
                if flags & !3 != 0 {
                    return Err(FrameError::Malformed("reserved SNAP flag"));
                }
                let n = r.remaining();
                Ok(Self::Snap(Snap::new(flags & 1 != 0, flags & 2 != 0, r.read_bytes(n)?)?))
            }
            ty::DOWN => {
                let member = <&NodeId>::try_from(r.read_bytes(32)?).map_err(|_| FrameError::Malformed("member id"))?;
                let inc = r.read_u64()?;
                let silence_ms = r.read_u32()?;
                let n = usize::from(r.read_u8()?);
                let mut probes = [Probe {
                    age_ms: 0,
                    path: Path::Session,
                }; MAX_PROBES];
                if n == 0 || n > MAX_PROBES {
                    return Err(FrameError::Malformed("probe count"));
                }
                for p in probes.iter_mut().take(n) {
                    p.age_ms = r.read_u32()?;
                    p.path = match r.read_u8()? {
                        0 => Path::Session,
                        1 => Path::Direct,
                        2 => Path::Relay,
                        _ => return Err(FrameError::Malformed("probe path")),
                    };
                }
                only(&r, "DOWN length")?;
                let proof = Proof::new(silence_ms, probes.get(..n).unwrap_or_default())
                    .ok_or(FrameError::Malformed("probe count"))?;
                Ok(Self::Down(Down { member, inc, proof }))
            }
            _ => {
                let n = r.remaining();
                Ok(Self::Other(Other {
                    ty,
                    topic,
                    rest: r.read_bytes(n)?,
                }))
            }
        }
    }

    /// Read the next frame from a stream buffer. `Ok(None)` means more bytes are needed; on success the second value
    /// is how many bytes of `buf` the frame used, length prefix included.
    ///
    /// # Errors
    /// [`FrameError::TooLarge`] for a length over [`MAX_BODY`], or any [`Frame::parse`] error.
    pub fn read(buf: &'a [u8]) -> Result<Option<(Self, usize)>, FrameError> {
        Self::read_with(buf, MAX_BODY)
    }

    /// As [`Frame::read`], with a body limit of `max_body` bytes in place of [`MAX_BODY`]. A host whose broadcast layer
    /// is configured for larger messages raises the limit to the largest frame that layer can build.
    ///
    /// # Errors
    /// [`FrameError::TooLarge`] for a length over `max_body`, or any [`Frame::parse`] error.
    pub fn read_with(buf: &'a [u8], max_body: usize) -> Result<Option<(Self, usize)>, FrameError> {
        let Some((head, rest)) = buf.split_first_chunk::<4>() else {
            return Ok(None);
        };
        let len = usize::try_from(u32::from_be_bytes(*head)).map_err(|_| FrameError::TooLarge)?;
        if len > max_body {
            return Err(FrameError::TooLarge);
        }
        let Some(body) = rest.get(..len) else {
            return Ok(None);
        };
        Ok(Some((Self::parse(body)?, 4 + len)))
    }

    /// The frame type number.
    pub const fn ty(&self) -> u8 {
        match self {
            Self::Hello(_) => ty::HELLO,
            Self::Ack => ty::ACK,
            Self::Delta(_) => ty::DELTA,
            Self::Snap(_) => ty::SNAP,
            Self::Probe => ty::PROBE,
            Self::Down(_) => ty::DOWN,
            Self::Other(o) => o.ty,
        }
    }

    fn body_len(&self) -> usize {
        2 + match self {
            Self::Hello(_) => HELLO_LEN,
            Self::Ack | Self::Probe => 0,
            Self::Delta(_) => ENTRY_LEN,
            Self::Snap(s) => 1 + s.entries.len(),
            Self::Down(d) => 32 + 8 + 4 + 1 + 5 * d.proof.probes().len(),
            Self::Other(o) => o.topic.len() + o.rest.len(),
        }
    }

    /// Encode the frame, length prefix included, into `out`; returns the written bytes.
    ///
    /// # Errors
    /// [`FrameError::Wire`] if `out` is too small, [`FrameError::TooLarge`] or [`FrameError::Malformed`] for a body
    /// that cannot be framed (a topic over 255 bytes).
    pub fn encode<'b>(&self, out: &'b mut [u8]) -> Result<&'b [u8], FrameError> {
        let len = self.body_len();
        if len > MAX_BODY {
            return Err(FrameError::TooLarge);
        }
        let mut w = Writer::new(&mut *out);
        w.put_u32(u32::try_from(len).map_err(|_| FrameError::TooLarge)?)?;
        let topic: &[u8] = if let Self::Other(o) = self { o.topic } else { &[] };
        w.put_u8(self.ty())?;
        w.put_u8(u8::try_from(topic.len()).map_err(|_| FrameError::Malformed("topic longer than 255 bytes"))?)?;
        w.put_slice(topic)?;
        match self {
            Self::Hello(h) => {
                w.put_u64(h.rec.inc)?;
                w.put_u16(h.rec.ver)?;
                w.put_slice(&h.rec.thash)?;
                w.put_u8(u8::from(h.snap) | (u8::from(h.homed) << 1))?;
            }
            Self::Ack | Self::Probe => {}
            Self::Delta(e) => w.put_slice(&entry_bytes(e.member, &e.rec, e.alive))?,
            Self::Snap(s) => {
                w.put_u8(u8::from(s.partial) | (u8::from(s.more) << 1))?;
                w.put_slice(s.entries)?;
            }
            Self::Down(d) => {
                w.put_slice(d.member)?;
                w.put_u64(d.inc)?;
                w.put_u32(d.proof.silence_ms)?;
                w.put_u8(u8::try_from(d.proof.probes().len()).map_err(|_| FrameError::Malformed("probe count"))?)?;
                for p in d.proof.probes() {
                    w.put_u32(p.age_ms)?;
                    w.put_u8(p.path as u8)?;
                }
            }
            Self::Other(o) => w.put_slice(o.rest)?,
        }
        let n = w.written().len();
        out.get(..n).ok_or(FrameError::Malformed("encoded length"))
    }
}
