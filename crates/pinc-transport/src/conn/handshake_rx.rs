//! What a handshake does with the fragments it receives: which reassembly takes a fragment, how a responder compares the
//! repeats of its first message with it, and the hand-over of a complete message to the state machine.
//!
//! A responder before it has a first message reassembles one message, and a fragment that disagrees with it is refused
//! as [`Failure::DifferentFirst`] (the endpoint then gives a first flight that no holder of the id agrees with a
//! half-open session of its own). Once the first message is accepted the responder keeps it, in the spare region of the
//! handshake chunk, and a fragment of a message of the same length is compared with it byte for byte: equal is a part
//! of a repeat, different is refused as [`Failure::DifferentFirst`], so nothing forged can mix into a repeat.
//!
//! A message that only one session receives (a dialing side's Reply, a responder's Finish) is reassembled by two
//! candidates. A fragment goes to every candidate that holds something and agrees with it; when none does, to an empty
//! one, else it starts over the one written least recently. A candidate whose message completes and does not authenticate
//! goes back to the runs it held before that fragment (the bytes need no undo: agreement means only bytes no run covered
//! were written), so a damaged copy racing a genuine fragment costs at most one resend. A message longer than a classical
//! Reply gets its second candidate in a chunk of its own, taken on the first conflict.
//!
//! Invariants: a candidate never holds bytes of two messages; a refused fragment changes nothing; the buffers of the
//! candidates and the first message lie inside the chunk and do not overlap.

use core::ops::Range;

use pinc_crypto::Provider;
use pinc_security::{Env, Failure, ResponderStores};
use pinc_wire::Reader;

use super::{ALT_MAX, FIRST_MAX, FIRST_OFF, Handshake, MAX_MESSAGE_LEN, Machine, machine_of};
use crate::conn::config::{MIN_MTU, PathId};
use crate::conn::reasm::{Added, Reassembly};
use crate::stream::pool::{BufferPool, Chunk};

/// The header of a held fragment: body length (u16), path id (u64), arrival instant (u64), datagram length (u32).
const HOLD_HEAD: usize = 22;

/// What the reassembly made of one fragment.
#[allow(clippy::large_enum_variant, reason = "a value that lives for one call, on the stack")]
pub(crate) enum Frag {
    /// A fragment of a message that is not complete (or one that was ignored).
    Part,
    /// A fragment that disagrees with what is held; nothing changed.
    Conflict,
    /// A fragment that completed a message.
    Whole(Done),
}

/// The messages one fragment completed (by candidate), and the state of each candidate before the fragment, to go back
/// to when the message does not authenticate.
#[derive(Default)]
pub(crate) struct Done {
    len: [Option<usize>; 2],
    undo: [Option<Reassembly>; 2],
}

/// What [`Handshake::receive`] did with the body of a Handshake packet.
#[derive(Clone, Copy)]
pub(crate) enum Got {
    /// Only a part of a message: nothing was decided.
    Part,
    /// A fragment that disagrees with what the session holds.
    Conflict,
    /// A message completed and the machine answered `r`. `owed`: a responder took its first message, or the same one
    /// again, so the path of the datagram is owed its flight.
    Fed { r: Result<(), Failure>, owed: bool },
}

/// The body of a Handshake packet: the message length, the offset of the fragment and its bytes.
fn parse(body: &[u8]) -> Option<(usize, usize, &[u8])> {
    let mut r = Reader::new(body);
    let total = usize::try_from(r.read_varint().ok()?).ok()?;
    let off = usize::try_from(r.read_varint().ok()?).ok()?;
    Some((total, off, r.read_bytes(r.remaining()).ok()?))
}

/// Where candidate `k` keeps a message of `total` bytes: in the spill chunk or in the handshake chunk, and the range.
fn place(client: bool, k: usize, total: usize) -> (bool, Range<usize>) {
    if k == 0 {
        return (false, MAX_MESSAGE_LEN..2 * MAX_MESSAGE_LEN);
    }
    if total > ALT_MAX {
        return (true, 0..MAX_MESSAGE_LEN);
    }
    let from = FIRST_OFF + if client { 0 } else { FIRST_MAX };
    (false, from..from + ALT_MAX)
}

/// The buffer of candidate `k` for a message of `total` bytes.
fn region<'p>(
    chunks: (Option<&Chunk>, Option<&Chunk>),
    pool: &'p mut BufferPool<'_>,
    client: bool,
    k: usize,
    total: usize,
) -> Option<&'p mut [u8]> {
    let (spill, range) = place(client, k, total);
    let chunk = if spill { chunks.1 } else { chunks.0 };
    pool.bytes_mut(chunk?).get_mut(range)
}

impl Handshake {
    fn cand(&mut self, k: usize) -> &mut Reassembly {
        if k == 0 { &mut self.rx } else { &mut self.alt }
    }

    /// Whether the fragment `data` at `off` of a message of the first message's length is a part of it.
    fn part_of_first(&self, pool: &BufferPool<'_>, off: usize, data: &[u8]) -> bool {
        let n = self.first_len.saturating_sub(off).min(data.len());
        if n == 0 {
            return true;
        }
        let first = self
            .chunk
            .as_ref()
            .and_then(|c| pool.bytes(c).get(FIRST_OFF..FIRST_OFF + self.first_len));
        first.and_then(|f| f.get(off..off + n)) == data.get(..n)
    }

    /// Hand a fragment to the reassembly: parse the packet body and keep it where the rules above say.
    pub(crate) fn take_fragment(&mut self, pool: &mut BufferPool<'_>, body: &[u8]) -> Frag {
        self.repeat = false;
        if !self.rx_live {
            self.repeat = true;
            return Frag::Part;
        }
        let Some((total, off, data)) = parse(body) else {
            self.repeat = true;
            return Frag::Part;
        };
        if self.first_len > 0 && total == self.first_len {
            if !self.part_of_first(pool, off, data) {
                return Frag::Conflict;
            }
            self.repeat = true;
        }
        if self.client || self.first_len > 0 {
            let f = self.add_pair(pool, total, off, data);
            if matches!(f, Frag::Part) {
                self.repeat = true;
            }
            return f;
        }
        let buf = region((self.chunk.as_ref(), None), pool, self.client, 0, total);
        let had = self.rx.covered();
        match self.rx.add(buf, total, off, data) {
            Added::Part => {
                self.repeat = self.rx.covered() <= had;
                Frag::Part
            }
            Added::Conflict => Frag::Conflict,
            Added::Whole(n) => Frag::Whole(Done {
                len: [Some(n), None],
                undo: [None, None],
            }),
        }
    }

    /// The two candidates of a message only this session receives.
    fn add_pair(&mut self, pool: &mut BufferPool<'_>, total: usize, off: usize, data: &[u8]) -> Frag {
        let mut done = Done::default();
        let mut took = [false; 2];
        let client = self.client;
        for (k, (cand, (tk, (dl, du)))) in [&mut self.rx, &mut self.alt]
            .into_iter()
            .zip(took.iter_mut().zip(done.len.iter_mut().zip(done.undo.iter_mut())))
            .enumerate()
        {
            if !cand.busy() {
                continue;
            }
            let undo = *cand;
            let chunks = (self.chunk.as_ref(), self.spill.as_ref());
            let Some(buf) = region(chunks, pool, client, k, cand.total()) else {
                continue;
            };
            match cand.add(Some(buf), total, off, data) {
                Added::Conflict => {}
                Added::Part => *tk = true,
                Added::Whole(n) => {
                    *tk = true;
                    *dl = Some(n);
                    *du = Some(undo);
                }
            }
        }
        if took[0] || took[1] {
            if took[0] != took[1] {
                self.alt_lru = took[0];
            }
            return Self::outcome(done);
        }
        // Nothing agrees: an empty candidate takes the fragment, else the one written least recently starts over.
        let k = usize::from(self.rx.busy() && (!self.alt.busy() || self.alt_lru));
        if k == 1 && total > ALT_MAX && self.spill.is_none() {
            match pool.alloc_chunk() {
                Ok(c) => self.spill = Some(c),
                Err(_) => return Frag::Conflict,
            }
        }
        self.alt_lru = k == 0;
        let client = self.client;
        let chunks = (self.chunk.as_ref(), self.spill.as_ref());
        let cand = if k == 0 { &mut self.rx } else { &mut self.alt };
        cand.clear();
        let Some(buf) = region(chunks, pool, client, k, total) else {
            return Frag::Conflict;
        };
        match cand.add(Some(buf), total, off, data) {
            Added::Part => Frag::Part,
            Added::Conflict => Frag::Conflict,
            Added::Whole(n) => {
                if let (Some(l), Some(u)) = (done.len.get_mut(k), done.undo.get_mut(k)) {
                    *l = Some(n);
                    *u = Some(Reassembly::new());
                }
                Self::outcome(done)
            }
        }
    }

    fn outcome(done: Done) -> Frag {
        if done.len.iter().any(Option::is_some) {
            Frag::Whole(done)
        } else {
            Frag::Part
        }
    }

    /// The bytes of the message of `len` bytes candidate `k` completed.
    fn message<'p>(&self, pool: &'p BufferPool<'_>, k: usize, len: usize) -> Option<&'p [u8]> {
        let (spill, range) = place(self.client, k, len);
        let chunk = if spill {
            self.spill.as_ref()
        } else {
            self.chunk.as_ref()
        }?;
        pool.bytes(chunk).get(range)?.get(..len)
    }

    /// A fragment arrived, in any order: keep it, and hand a message it completed to the state machine. A server needs
    /// the shared `stores`. A message that does not authenticate puts its candidate back as it was before the fragment,
    /// and the next candidate that completed gets its turn.
    ///
    /// The message taken last, if the first flight went unrepeated, gives the handshake round trip, offered only once
    /// the session is established: the message that leads there is the one that authenticated, so a forged one gives
    /// no sample. The reference model seeds its estimate the same way, only after the reply's checks:
    /// `if c.hs_tries == 1 and c.srtt == 0 and c.hs_sent:` then `c.srtt = max(1000000, now - c.hs_sent)`.
    pub(crate) fn receive<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        pool: &mut BufferPool<'_>,
        env: &mut Env<'_, P>,
        mut stores: Option<&mut ResponderStores<PK, TK>>,
        body: &[u8],
    ) -> Got {
        let done = match self.take_fragment(pool, body) {
            Frag::Part => return Got::Part,
            Frag::Conflict => return Got::Conflict,
            Frag::Whole(done) => done,
        };
        let mut first_err = None;
        for k in 0..2 {
            let Some(len) = done.len.get(k).copied().flatten() else {
                continue;
            };
            match self.feed(pool, env, stores.as_deref_mut(), k, len) {
                Ok(()) => {
                    let taken = self.keep_first(pool, k, len);
                    if self.awaiting() {
                        // The verdict on this message comes later (the machine holds its copy): both candidates go back
                        // to what they held, and a message the other one completed waits to be fed if the verdict fails.
                        for (j, u) in done.undo.iter().enumerate() {
                            if let Some(u) = *u {
                                *self.cand(j) = u;
                            }
                        }
                        if k == 0 {
                            self.ready = done.len.get(1).copied().flatten().and_then(|n| u16::try_from(n).ok());
                        }
                    }
                    return Got::Fed {
                        r: Ok(()),
                        owed: !self.client && (taken || self.repeat),
                    };
                }
                Err(e) => {
                    if let Some(u) = done.undo.get(k).copied().flatten() {
                        *self.cand(k) = u;
                    }
                    first_err.get_or_insert(e);
                }
            }
        }
        Got::Fed {
            r: Err(first_err.unwrap_or(Failure::Closed)),
            owed: false,
        }
    }

    /// Keep the fragment `body` that arrived on `from` (path, instant, datagram length) while the verdict on a Reply is
    /// awaited, in arrival order, for [`Self::take_held`]. Returns whether it was kept: not when it is longer than the
    /// smallest datagram (an honest one before the session is established is not), or the chunk is full or cannot be
    /// taken.
    pub(crate) fn hold(&mut self, pool: &mut BufferPool<'_>, from: (PathId, u64, usize), body: &[u8]) -> bool {
        let used = usize::from(self.hold_len);
        let need = HOLD_HEAD + body.len();
        let (Ok(blen), Ok(dlen)) = (u16::try_from(body.len()), u32::try_from(from.2)) else {
            return false;
        };
        if body.len() > usize::from(MIN_MTU) {
            return false;
        }
        if self.hold.is_none() {
            match pool.alloc_chunk() {
                Ok(c) => self.hold = Some(c),
                Err(_) => return false,
            }
        }
        let Some(buf) = self.hold.as_ref().map(|c| pool.bytes_mut(c)) else {
            return false;
        };
        // The one guard for the room: the record must fit what the chunk has left after the fragments already held.
        let Some(end) = used.checked_add(need) else {
            return false;
        };
        let Some(mut rest) = buf.get_mut(used..end) else {
            return false;
        };
        let (id, at) = (from.0.0.to_le_bytes(), from.1.to_le_bytes());
        for part in [&blen.to_le_bytes()[..], &id, &at, &dlen.to_le_bytes(), body] {
            let Some((dst, tail)) = rest.split_at_mut_checked(part.len()) else {
                return false;
            };
            dst.copy_from_slice(part);
            rest = tail;
        }
        let Ok(len) = u16::try_from(end) else {
            return false;
        };
        self.hold_len = len;
        true
    }

    /// Take the first held fragment: its body is copied into `out` (it cannot be borrowed from the pool while the
    /// caller hands it to [`Self::receive`]), with where it arrived and its length.
    pub(crate) fn take_held(
        &mut self,
        pool: &mut BufferPool<'_>,
        out: &mut [u8; MIN_MTU as usize],
    ) -> Option<((PathId, u64, usize), usize)> {
        let used = usize::from(self.hold_len);
        let buf = pool.bytes_mut(self.hold.as_ref()?);
        let (blen, rest) = buf.split_first_chunk::<2>()?;
        let (id, rest) = rest.split_first_chunk::<8>()?;
        let (at, rest) = rest.split_first_chunk::<8>()?;
        let (dlen, rest) = rest.split_first_chunk::<4>()?;
        let blen = usize::from(u16::from_le_bytes(*blen));
        let from = (
            PathId(u64::from_le_bytes(*id)),
            u64::from_le_bytes(*at),
            u32::from_le_bytes(*dlen) as usize,
        );
        out.get_mut(..blen)?.copy_from_slice(rest.get(..blen)?);
        let end = HOLD_HEAD + blen;
        // `hold` writes whole records, so a record never ends past the held bytes; if one did, the store is dropped
        // rather than read past its end (no test reaches this branch).
        let Some(left) = used.checked_sub(end) else {
            self.hold_len = 0;
            if let Some(c) = self.hold.take() {
                pool.free_chunk(c);
            }
            return None;
        };
        buf.copy_within(end..used, 0);
        self.hold_len = u16::try_from(left).unwrap_or(0);
        if self.hold_len == 0
            && let Some(c) = self.hold.take()
        {
            pool.free_chunk(c);
        }
        Some((from, blen))
    }

    /// A responder without a first message that has just accepted one keeps it, to compare its repeats with. Returns
    /// whether it did.
    fn keep_first(&mut self, pool: &mut BufferPool<'_>, k: usize, len: usize) -> bool {
        if self.client || self.first_len > 0 || k != 0 || len > FIRST_MAX {
            return false;
        }
        let Some(buf) = self.chunk.as_ref().map(|c| pool.bytes_mut(c)) else {
            return false;
        };
        if buf.len() < FIRST_OFF + FIRST_MAX || buf.len() < MAX_MESSAGE_LEN + len {
            return false;
        }
        buf.copy_within(MAX_MESSAGE_LEN..MAX_MESSAGE_LEN + len, FIRST_OFF);
        self.first_len = len;
        true
    }

    /// Hand the complete message of `len` bytes of candidate `k` to the state machine.
    pub(crate) fn feed<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        pool: &BufferPool<'_>,
        env: &mut Env<'_, P>,
        stores: Option<&mut ResponderStores<PK, TK>>,
        k: usize,
        len: usize,
    ) -> Result<(), Failure> {
        self.clock = env.now;
        if !self.rx_live || self.chunk.is_none() {
            return Err(Failure::Closed);
        }
        let msg = self.message(pool, k, len).ok_or(Failure::InvalidParameter)?;
        // A prekey reject is answered with the full Initial at most once per `max(500 ms, node round trip)`.
        let gap = pinc_security::initiator::REJECT_GAP.max(self.timing.node_rtt.unwrap_or(0));
        let r = match (machine_of(&mut self.machine).ok_or(Failure::Closed)?, stores) {
            (Machine::Client(m), _) => {
                m.set_reject_gap(gap);
                m.handle(env, msg)
            }
            (Machine::Server(m), Some(stores)) => m.handle(env, stores, msg),
            (Machine::Server(_), None) => Err(Failure::InvalidParameter),
        };
        if r.is_ok() && self.client {
            // The peer answered (a reject too): only flights sent after this count towards the early end.
            self.unheard = 0;
            self.sample = (self.sends == 1).then_some(env.now.saturating_sub(self.first_sent).max(super::MIN_SAMPLE));
        }
        r
    }

    /// The id the dialer named for itself in the first message the responder accepted.
    pub(crate) fn client_cid(&mut self) -> Option<pinc_security::ConnId> {
        match machine_of(&mut self.machine) {
            Some(Machine::Server(m)) => m.client_cid(),
            _ => None,
        }
    }

    /// Whether the fragment last taken was a part of the responder's first message again, or a part that added no
    /// byte to the first message being assembled.
    pub(crate) const fn was_repeat(&self) -> bool {
        self.repeat
    }

    /// [`Self::take_fragment`] with the state of the first reassembly around it and the message buffer after it
    /// (trace validation: the real parse of the two varints and the real reassembly, without the state machine).
    #[cfg(feature = "trace")]
    pub(crate) fn trace_fragment(
        &mut self,
        pool: &mut BufferPool<'_>,
        body: &[u8],
    ) -> crate::conn::reasm::trace::FragmentView {
        let before = self.rx.trace_view();
        let ret = match self.take_fragment(pool, body) {
            Frag::Whole(d) => d.len[0],
            Frag::Part | Frag::Conflict => None,
        };
        let after = self.rx.trace_view();
        let n = ret.unwrap_or(0).max(after.total);
        let message = self
            .chunk
            .as_ref()
            .and_then(|c| pool.bytes(c).get(MAX_MESSAGE_LEN..))
            .and_then(|b| b.get(..n))
            .map(<[u8]>::to_vec)
            .unwrap_or_default();
        crate::conn::reasm::trace::FragmentView {
            before,
            after,
            ret,
            message,
        }
    }
}
