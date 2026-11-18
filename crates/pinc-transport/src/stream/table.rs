//! The stream table: ids, limits, the control-frame queue and the glue between the halves of each stream.
//!
//! Invariants: `ids[i]` is the id held by slot `i` (or `NONE`) and `hot[i]` is a superset of what slot `i` can emit
//! (a stale bit costs one failed attempt, a missing bit would starve the slot, so every mutator refreshes it); a slot
//! is freed only when both halves are done, which returns all of its chunks to the pool; every slot at or above
//! `top` is blank and, unless the table is empty, slot `top - 1` holds a stream; `buffered` is the sum over
//! slots of the written-and-unacknowledged bytes; `local_live` counts the streams we opened that hold a slot and
//! `remote_live` the peer's streams that count against its limit (a peer stream stops counting when its data is
//! whole and read and our answer has left, though its slot is held until the answer is acknowledged); a peer stream
//! the table has no room for is stored nowhere, answers nothing and is never acknowledged, so
//! its opener holds and retransmits it until there is room;
//! stream ids of a class are opened in order and never reused.

use super::credit::Admit;
use super::lazy::{Blank, Lazy};
use super::pool::{BufferPool, CHUNK_SIZE};
use super::recv::Recv;
use super::send::Send;
use super::spill::SpillArena;
use super::{
    Config, DEFAULT_URGENCY, FIRST_CHARGE, NoSource, PeerLimits, RecvStatus, StreamError, StreamId, StreamSource,
    StreamStats, is_uni,
};

mod giving_up;
mod pick;
#[cfg(feature = "trace")]
mod view;

const NONE: u64 = u64::MAX;
const HOT_RETX: u8 = 1;
const HOT_NEW: u8 = 2;
const HOT_CTL: u8 = 4;

#[derive(Debug)]
struct Slot<S, const C: usize> {
    recv: Recv<C>,
    send: Send<S, C>,
    urgency: u8,
    /// The stream counts against its opener's limit (`local_live` or `remote_live`).
    counted: bool,
    /// For a stream we opened: how many we had opened in all, itself included; its first frame waits until the peer's
    /// limit covers it. 0 for a stream the peer opened.
    ordinal: u64,
}

/// How many of `fit` first charges the credit may promise: half of them, but never more than leave three for the
/// streams already open (their windows slide through whole chunks) and for our own, and one when a charge fits at all.
/// A pool of 4 promises 1, one of 6 promises 3, one of 25 promises 12.
const fn admit_fit(fit: u64) -> u64 {
    let spare = fit.saturating_sub(3);
    let half = fit / 2;
    let most = if spare < half { spare } else { half };
    let one = if fit < 1 { fit } else { 1 };
    if most > one { most } else { one }
}

impl<S: StreamSource, const C: usize> Slot<S, C> {
    const NEW: Self = Self {
        recv: Recv::NEW,
        send: Send::NEW,
        urgency: DEFAULT_URGENCY,
        counted: false,
        ordinal: 0,
    };
}

impl<S: StreamSource, const C: usize> Blank for Slot<S, C> {
    const BLANK: Self = Self::NEW;
}

/// The class index of a stream id: 0 for bidirectional, 1 for unidirectional.
const fn class(id: StreamId) -> usize {
    if is_uni(id) { 1 } else { 0 }
}

/// The stream table of a connection: `N` slots, each with receive and send chunk rings of `C` entries.
///
/// All bytes live in the [`BufferPool`] passed to the mutating calls. A slot is about `8 * C` bytes plus a few hundred.
/// Without `alloc` the table is a fixed-size value that never allocates, so a large `C` wants it boxed or static; with
/// `alloc` the room for the `N` slots is allocated once, when the table is made, and a slot's memory is written only when
/// a stream first takes it, so a table costs the most streams it held at once, not `N`.
pub struct Streams<S: StreamSource = NoSource, const N: usize = 100, const C: usize = 1025> {
    is_client: bool,
    ids: [u64; N],
    hot: [u8; N],
    slots: Lazy<Slot<S, C>, N>,
    stream_window: u64,
    max_stream_window: u64,
    peer: PeerLimits,
    max_remote: u64,
    local_opened: [u64; 2],
    remote_next: [u64; 2],
    local_live: u64,
    remote_live: u64,
    /// A peer stream stopped counting against its limit since [`Streams::take_released`] last asked.
    released: bool,
    open: usize,
    /// One past the highest slot a stream holds, 0 with none (see [`Streams::used`]).
    top: usize,
    buffered: u64,
    stats: StreamStats,
    admit: Admit,
    /// The least ordinal among the streams whose first frame or control frame waits for the peer's limit, 0 with none: a raise of the
    /// limit looks again once it reaches this.
    held_from: u64,
    /// Some slot's grant was deferred at the last pass; a stale `true` costs one pass that clears it.
    stalled: bool,
}

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// The bytes a table holds on the heap at most: the table itself and the room reserved for its `N` slots, all of
    /// them written. The memory of a slot's chunks is the pool's, not counted here.
    #[doc(hidden)]
    #[cfg(feature = "alloc")]
    pub const BYTES: usize = core::mem::size_of::<Self>() + N * core::mem::size_of::<Slot<S, C>>();

    /// A table for `config`. The window ceiling is clamped to what the chunk rings and half of the pool's budget can
    /// hold, and the peer-opened stream cap to the table size.
    pub fn new(config: &Config, pool: &BufferPool<'_>) -> Self {
        const { assert!(C >= 2 && N >= 1) };
        let (max_stream, stream_window) = Self::windows(config, pool);
        let mut streams = Self {
            is_client: config.is_client,
            ids: [NONE; N],
            hot: [0; N],
            slots: Lazy::new(),
            stream_window,
            max_stream_window: max_stream,
            peer: PeerLimits::default(),
            max_remote: config.max_streams.min(N as u64),
            local_opened: [0; 2],
            remote_next: [0; 2],
            local_live: 0,
            remote_live: 0,
            released: false,
            open: 0,
            top: 0,
            buffered: 0,
            stats: StreamStats::default(),
            admit: Admit {
                on: config.credit,
                ..Admit::NEW
            },
            held_from: 0,
            stalled: false,
        };
        streams.set_peer_limits(&config.peer);
        streams.set_advertised(streams.admit_cap(pool));
        streams
    }

    /// The streams this table tells the peer it admits at the start: the room an empty table has.
    pub fn admit_cap(&self, pool: &BufferPool<'_>) -> u64 {
        if self.admit.on { self.admit_room(pool) } else { 0 }
    }

    /// What the ledger counts for a stream that has carried no data, and keeps for each stream inside the credit: its
    /// initial window or [`FIRST_CHARGE`], whichever is less, in whole chunks, at least one.
    fn first_charge(&self) -> u64 {
        let chunk = CHUNK_SIZE as u64;
        self.stream_window.min(FIRST_CHARGE).div_ceil(chunk).max(1) * chunk
    }

    /// The streams admitted in all, of both kinds.
    fn admitted(&self) -> u64 {
        self.remote_next.iter().sum()
    }

    /// The streams the peer may open in all, as last advertised: the handshake value until a raise is sent.
    pub const fn advertised_streams(&self) -> u64 {
        self.admit.adv
    }

    /// Record the stream credit the handshake gave the peer (the connection may lower it to its own cap).
    pub fn set_advertised(&mut self, streams: u64) {
        self.admit.adv = streams;
        self.admit.pend = false;
    }

    /// The window ceiling and the initial window `config` gives against `pool`.
    fn windows(config: &Config, pool: &BufferPool<'_>) -> (u64, u64) {
        let chunk = CHUNK_SIZE as u64;
        let half = pool.budget_bytes() / 2 / chunk * chunk;
        let max_stream = config.max_stream_window.min((C as u64 - 1) * chunk).min(half);
        (max_stream, config.initial_stream_window.min(max_stream))
    }

    /// Make this table the one [`Streams::new`] builds for `config`, in place. For reuse by a new connection: the
    /// pool must be fresh (every chunk the old streams held is gone), so no chunk is released here.
    pub fn reinit(&mut self, config: &Config, pool: &BufferPool<'_>) {
        let (max_stream, stream_window) = Self::windows(config, pool);
        self.slots.clear();
        self.is_client = config.is_client;
        self.ids = [NONE; N];
        self.hot = [0; N];
        self.stream_window = stream_window;
        self.max_stream_window = max_stream;
        self.peer = PeerLimits::default();
        self.max_remote = config.max_streams.min(N as u64);
        self.local_opened = [0; 2];
        self.remote_next = [0; 2];
        self.local_live = 0;
        self.remote_live = 0;
        self.released = false;
        self.open = 0;
        self.top = 0;
        self.buffered = 0;
        self.stats = StreamStats::default();
        self.admit = Admit {
            on: config.credit,
            ..Admit::NEW
        };
        self.held_from = 0;
        self.stalled = false;
        self.set_peer_limits(&config.peer);
        self.set_advertised(self.admit_cap(pool));
    }

    /// Counters of absorbed events.
    pub const fn stats(&self) -> StreamStats {
        self.stats
    }

    /// The number of streams currently in the table.
    pub const fn open_streams(&self) -> usize {
        self.open
    }

    /// The initial receive window of a stream, which the connection advertises.
    pub const fn recv_window(&self) -> u64 {
        self.stream_window
    }

    /// Run with the limits the connection advertises to its peer, for a table with no stream open yet: `window` as the
    /// receive window every stream starts with (at most the ceiling the table was made with) and `streams` as the most
    /// peer streams live at once (at most the cap it was made with). The stream credit is derived again from them.
    pub fn adopt(&mut self, pool: &BufferPool<'_>, window: u64, streams: u64) {
        self.stream_window = window.min(self.max_stream_window);
        self.max_remote = self.max_remote.min(streams);
        self.set_advertised(self.admit_cap(pool));
    }

    /// The receive window size and advertised limit of a stream.
    pub fn stream_recv_window(&self, id: StreamId) -> Option<(u64, u64)> {
        let win = &self.slot(self.find(id)?)?.recv.win;
        Some((win.size, win.limit))
    }

    /// The receive credit granted to the peer and not yet received, summed over the open streams. It is recomputed by
    /// a scan of the slots up to the highest one a stream holds.
    pub fn granted_unreceived(&self) -> u64 {
        self.slots
            .written()
            .iter()
            .take(self.used())
            .fold(0, |sum, s| sum.saturating_add(s.recv.unreceived()))
    }

    /// The slots no stream holds.
    const fn free(&self) -> u64 {
        N.saturating_sub(self.open) as u64
    }

    /// One past the highest slot a stream holds (a new stream takes the lowest free slot): no slot beyond it holds a
    /// stream or has anything to send, so the scans the connection makes for each packet stop here. It falls when the
    /// top stream ends, so a session back to one stream after a burst of many scans one slot again, not every slot the
    /// burst wrote (whose memory a scan would read, a cache miss a slot).
    pub(super) const fn used(&self) -> usize {
        self.top
    }

    /// The pool bytes promised to the peer: the credit granted and not yet received, plus the first charges kept for the
    /// streams it may still open. Admitting a stream inside the credit moves a first charge from the second part to the
    /// first and leaves the sum alone; a window grant, a stream beyond the credit and a local stream are the only things
    /// that raise it, and each of them first checks that the sum with the new part fits the pool. Other users of the pool
    /// (the send buffers, the datagram queues) take chunks without asking, so the sum can pass what the pool has left
    /// without any promise having grown; it falls again as those chunks come back or the peer's credit is received.
    pub fn promised(&self) -> u64 {
        self.granted_unreceived().saturating_add(self.reserved())
    }

    /// The bytes written and not yet acknowledged, over all buffered streams.
    pub const fn buffered(&self) -> u64 {
        self.buffered
    }

    /// Apply the peer's limits (its credit record, or later raises). Limits only grow.
    pub fn set_peer_limits(&mut self, limits: &PeerLimits) {
        self.peer.window = self.peer.window.max(limits.window);
        self.peer.max_streams = self.peer.max_streams.max(limits.max_streams);
        self.admit.raise_limit(limits.max_streams);
        self.regate();
        let window = self.peer.window;
        for slot in self.slots.written_iter_mut() {
            if slot.send.open {
                slot.send.raise_limit(window);
            }
        }
        for i in 0..self.used() {
            self.refresh(i);
        }
    }

    fn is_local(&self, id: StreamId) -> bool {
        (id & 1 == 0) == self.is_client
    }

    fn find(&self, id: StreamId) -> Option<usize> {
        // The first free slot may be the one after the used ones.
        let within = if id == NONE { N } else { self.used() };
        self.ids.iter().take(within).position(|&x| x == id)
    }

    fn slot(&self, i: usize) -> Option<&Slot<S, C>> {
        self.slots.get(i)
    }

    fn refresh(&mut self, i: usize) {
        let Some(slot) = self.slots.get(i) else { return };
        let (retx, mut new) = slot.send.wants();
        let ordinal = slot.ordinal;
        let past = ordinal > self.admit.limit;
        let mut ctl =
            (slot.recv.win.pending && slot.recv.open) || slot.recv.stop_pending() || slot.send.control_pending();
        // Past the peer's limit the peer does not know the stream yet: neither its data nor its control frames go.
        if (new || ctl) && past {
            new = false;
            ctl = false;
            self.held_from = if self.held_from == 0 {
                ordinal
            } else {
                self.held_from.min(ordinal)
            };
        }
        let hot = (u8::from(retx) * HOT_RETX) | (u8::from(new) * HOT_NEW) | (u8::from(ctl) * HOT_CTL);
        if let Some(h) = self.hot.get_mut(i) {
            *h = hot;
        }
    }

    /// Run `f` on the send half of slot `i`, keeping the `buffered` counter in step with what it did.
    fn with_send<R>(&mut self, i: usize, f: impl FnOnce(&mut Send<S, C>) -> R) -> Option<R> {
        let slot = self.slots.get_mut(i)?;
        let before = slot.send.buffered();
        let out = f(&mut slot.send);
        let after = slot.send.buffered();
        self.buffered = self.buffered.saturating_add(after).saturating_sub(before);
        Some(out)
    }

    /// Refresh the slot, and free it when both halves are done.
    fn settle(&mut self, pool: &mut BufferPool<'_>, i: usize) {
        let done = self.slots.get(i).is_some_and(|s| s.recv.is_done() && s.send.is_done());
        if !done {
            self.refresh(i);
            self.release_limit(i);
            self.regrant(pool);
            return;
        }
        let id = self.ids.get(i).copied().unwrap_or(NONE);
        let counted = self.slots.get(i).is_some_and(|s| s.counted);
        if let Some(slot) = self.slots.get_mut(i) {
            self.buffered = self.buffered.saturating_sub(slot.send.buffered());
            slot.recv.release_all(pool);
            slot.send.release_all(pool);
            slot.send.release_sets(pool);
            *slot = Slot::NEW;
        }
        if let Some(x) = self.ids.get_mut(i) {
            *x = NONE;
        }
        if let Some(h) = self.hot.get_mut(i) {
            *h = 0;
        }
        self.open = self.open.saturating_sub(1);
        // The top stream ended: walk the mark down past the free slots below it, each passed once per free.
        while self.top > 0 && self.ids.get(self.top - 1) == Some(&NONE) {
            self.top -= 1;
        }
        if id != NONE && counted {
            let live = if self.is_local(id) {
                &mut self.local_live
            } else {
                &mut self.remote_live
            };
            *live = live.saturating_sub(1);
        }
        // The last stream ended: the session is quiet, so its pool lets go of the chunks its busiest moment took.
        if self.open == 0 {
            pool.trim();
        }
        self.regrant(pool);
    }

    /// Try the window grants that were deferred for want of pool room again. Every release of pool chunks and every
    /// change of the credit ledger calls it (the end of `settle`, and the connection before it writes control
    /// frames, which covers chunks the datagram queues and the early-data buffer gave back), so a grant is never
    /// left waiting for the application to read something: with nothing readable it never would.
    // vertexia: one pass of the table per call while a grant is deferred; gate on the pool's free bytes if a long
    // shortage with many streams shows up in a profile.
    pub fn regrant(&mut self, pool: &BufferPool<'_>) {
        self.refresh_admit(pool);
        if self.stalled {
            self.grant(pool, N);
        }
    }

    /// How many more peer streams could be admitted now, counting the credit already given: the live-stream cap (at
    /// most half the slots, so the rest stay free for the streams we open) less the live ones, the free slots, and as
    /// many first charges as [`admit_fit`] allows of those that fit in the pool bytes left beside a first charge for
    /// each open stream ([`Streams::admitted_charge`]).
    fn admit_room(&self, pool: &BufferPool<'_>) -> u64 {
        let free = self.free();
        let fit = pool.available_bytes().saturating_sub(self.admitted_charge()) / self.first_charge();
        let cap = self.max_remote.min((N as u64 / 2).max(1));
        cap.saturating_sub(self.remote_live).min(free).min(admit_fit(fit))
    }

    /// Queue a raise of the stream credit when the room grew enough (see [`Admit::update`]).
    // vertexia: one scan of the used slots per call, which the connection makes once per packet it writes; gate on a
    // changed pool or slot count if a profile shows it with many streams.
    fn refresh_admit(&mut self, pool: &BufferPool<'_>) {
        let (admitted, room) = (self.admitted(), self.admit_room(pool));
        self.admit.update(admitted, room);
    }

    fn alloc_slot(&mut self, id: StreamId) -> Result<usize, StreamError> {
        let i = self.find(NONE).ok_or(StreamError::TableFull)?;
        let local = self.is_local(id);
        let (window, limit) = (self.stream_window, self.peer.window);
        let slot = self.slots.get_mut(i).ok_or(StreamError::TableFull)?;
        if !is_uni(id) || !local {
            slot.recv.init(window);
        }
        if !is_uni(id) || local {
            slot.send.init(limit);
        }
        if let Some(x) = self.ids.get_mut(i) {
            *x = id;
        }
        slot.counted = true;
        self.open += 1;
        self.top = self.top.max(i + 1);
        if local {
            self.local_live += 1;
        } else {
            self.remote_live += 1;
        }
        self.refresh(i);
        Ok(i)
    }

    /// A peer stream stops counting against the peer's limit once what it sent is whole and read and our answer has
    /// left with nothing queued to be sent again ([`Send::flushed`]): the peer may open another while this one's
    /// last bytes wait for their acknowledgement. A stream that carries one request and its reply so frees its place
    /// when the reply is sent, not a round trip later. The slot is kept until both halves are done.
    pub(super) fn release_limit(&mut self, i: usize) {
        let local = self.ids.get(i).is_none_or(|id| *id == NONE || self.is_local(*id));
        if local {
            return;
        }
        if let Some(slot) = self.slots.written_mut(i)
            && slot.counted
            && slot.recv.is_done()
            && slot.send.flushed()
        {
            slot.counted = false;
            self.remote_live = self.remote_live.saturating_sub(1);
            self.released = true;
        }
    }

    /// Whether a peer stream gave its place back since the last call, so the stream credit may have room to grow.
    pub fn take_released(&mut self) -> bool {
        core::mem::take(&mut self.released)
    }

    /// The pool bytes reserved for the stream credit given to the peer and not yet used: the first charges of the
    /// streams it may still open. Window grants and local streams leave them alone.
    fn reserved(&self) -> u64 {
        self.admit
            .adv
            .saturating_sub(self.admitted())
            .saturating_mul(self.first_charge())
    }

    /// The streams the peer may still open inside the credit.
    fn credit_left(&self) -> u64 {
        self.admit.adv.saturating_sub(self.admitted())
    }

    /// What the open streams count for when one more stream is admitted: for each, the credit it may still claim, but
    /// no more than one first charge. A window grant counts whole windows ([`Streams::granted_unreceived`]); admitting
    /// a stream asks only that every stream, old and new, has room for a first step, so streams that carry data and
    /// stay open do not shut out new ones for the size of their windows.
    fn admitted_charge(&self) -> u64 {
        let first = self.first_charge();
        self.slots
            .written()
            .iter()
            .take(self.used())
            .fold(0, |sum, s| sum.saturating_add(s.recv.unreceived().min(first)))
    }

    /// Whether the first charges of `streams` new streams fit in the pool bytes left beside a first charge for each
    /// open stream. The one test for a peer stream beyond the credit and for a local one, so they cannot differ.
    fn windows_fit(&self, pool: &BufferPool<'_>, streams: u64) -> bool {
        self.admitted_charge()
            .saturating_add(streams.saturating_mul(self.first_charge()))
            <= pool.available_bytes()
    }

    /// Whether `count` more peer streams can be admitted: under the cap and with slots. Inside the credit no pool test
    /// is made (a new stream takes no chunk, and the credit kept its first charge), so a frame that opens many skipped
    /// streams at once is never held back for them; beyond it their first charges must fit beside the credit left.
    fn admits(&self, pool: &BufferPool<'_>, count: u64) -> bool {
        let free = self.free();
        let inside = self.admitted().saturating_add(count) <= self.admit.adv;
        self.remote_live + count <= self.max_remote
            && free >= count
            && (inside || self.windows_fit(pool, count.max(self.credit_left())))
    }

    /// The slot of `id`, opening peer streams implicitly; `None` if it was already closed.
    fn locate(&mut self, pool: &BufferPool<'_>, id: StreamId) -> Result<Option<usize>, StreamError> {
        let (c, index) = (class(id), id >> 2);
        if self.is_local(id) {
            if index >= self.local_opened.get(c).copied().unwrap_or(0) {
                return Err(StreamError::StreamState);
            }
            return Ok(self.find(id));
        }
        let next = self.remote_next.get(c).copied().unwrap_or(0);
        if index < next {
            return Ok(self.find(id));
        }
        if index >= next.saturating_add(self.max_remote) {
            return Err(StreamError::StreamLimit);
        }
        if !self.admits(pool, index - next + 1) {
            self.stats.held_back += 1;
            return Err(StreamError::Exhausted);
        }
        let mut last = None;
        for n in next..=index {
            let low = (n << 2) | (id & 3);
            last = Some(self.alloc_slot(low)?);
            if let Some(r) = self.remote_next.get_mut(c) {
                *r = n + 1;
            }
        }
        Ok(last)
    }

    /// How many streams of `id`'s kind and initiator the peer has opened so far: the index the next one will have.
    /// An arriving stream opens every lower one implicitly, so the ids from here up to the arriving one are all new.
    pub fn peer_opened(&self, id: StreamId) -> u64 {
        self.remote_next.get(class(id)).copied().unwrap_or(0)
    }

    fn require(&self, id: StreamId) -> Result<usize, StreamError> {
        self.find(id).ok_or(StreamError::UnknownStream)
    }

    /// Whether a stream we initiate could open now, by the same test [`Streams::open_stream`] applies: a host that got
    /// [`StreamError::StreamLimit`] or [`StreamError::Exhausted`] asks again after each input until this is `Ok`.
    ///
    /// # Errors
    /// The error `open_stream` would return.
    pub fn can_open(&self, pool: &BufferPool<'_>, bidi: bool) -> Result<(), StreamError> {
        if !self.admit.early && !self.admit.allows(self.local_opened.iter().sum()) {
            return Err(StreamError::StreamLimit);
        }
        // The slot and the first charge of every stream inside the credit given to the peer stay free.
        let left = self.credit_left();
        let free = self.free();
        if (free > 0 && free <= left) || (bidi && !self.windows_fit(pool, left + 1)) {
            return Err(StreamError::Exhausted);
        }
        Ok(())
    }

    /// Open a stream we initiate. A bidirectional stream's receive window is the one the connection advertised, so it
    /// cannot be made smaller: it is charged to the credit ledger like a peer stream's (its first charge now, the whole
    /// window from its first byte), and the stream opens only when the first charge fits in `pool`.
    ///
    /// # Errors
    /// [`StreamError::StreamLimit`] when the peer has not given credit for one more stream yet (it says how many it
    /// admits in the handshake and raises that as its streams end),
    /// [`StreamError::TableFull`] when the table has no slot, [`StreamError::Exhausted`] when the first charge of a
    /// bidirectional stream's receive window does not fit in the pool beside the credit granted yet; try again once the
    /// application has read or chunks were released.
    pub fn open_stream(&mut self, pool: &BufferPool<'_>, bidi: bool) -> Result<StreamId, StreamError> {
        self.can_open(pool, bidi)?;
        let c = usize::from(!bidi);
        let opened = self.local_opened.get(c).copied().unwrap_or(0);
        let id = (opened << 2) | if bidi { 0 } else { 2 } | u64::from(!self.is_client);
        let ordinal = self.local_opened.iter().sum::<u64>() + 1;
        let i = self.alloc_slot(id)?;
        if let Some(slot) = self.slots.get_mut(i) {
            slot.ordinal = ordinal;
        }
        self.refresh(i);
        if let Some(o) = self.local_opened.get_mut(c) {
            *o += 1;
        }
        Ok(id)
    }

    /// An open was refused for want of credit: show the peer the newest stream of each kind we opened and sent
    /// nothing on, so it counts every stream below it and can give the credit back. Each stream is shown once.
    pub fn announce_top(&mut self) {
        for c in 0..2 {
            let Some(top) = self.local_opened.get(c).copied().unwrap_or(0).checked_sub(1) else {
                continue;
            };
            let id = (top << 2) | ((c as u64) << 1) | u64::from(!self.is_client);
            let Some(i) = self.find(id) else { continue };
            if self.slots.get_mut(i).is_some_and(|s| s.send.announce()) {
                self.refresh(i);
            }
        }
    }

    /// Set the urgency of a stream; a lower number is served first (the default is [`DEFAULT_URGENCY`]).
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`].
    pub fn set_urgency(&mut self, id: StreamId, urgency: u8) -> Result<(), StreamError> {
        let i = self.require(id)?;
        self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?.urgency = urgency;
        Ok(())
    }

    // ---- receive ----------------------------------------------------------------------------------------------

    /// A stream data frame arrived.
    ///
    /// # Errors
    /// A violation by the peer ([`StreamError::StreamLimit`], [`StreamError::StreamState`], [`StreamError::FlowControl`],
    /// [`StreamError::FinalSize`], [`StreamError::Conflict`]) or a local shortage ([`StreamError::Exhausted`], including a new
    /// peer stream the table has no room for yet, and [`StreamError::Fragmented`]); on a local shortage nothing was
    /// stored and the packet should go unacknowledged.
    pub fn on_stream_frame(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        offset: u64,
        data: &[u8],
        fin: bool,
    ) -> Result<(), StreamError> {
        if is_uni(id) && self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(pool, id)? else { return Ok(()) };
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.recv.on_data(pool, offset, data, fin);
        self.stats.range_spills += slot.recv.take_spills();
        self.stats.held_back += u64::from(result == Err(StreamError::Exhausted));
        self.stats.range_overflows += u64::from(result == Err(StreamError::Fragmented));
        self.settle(pool, i);
        result
    }

    /// The contiguous readable bytes of a stream (up to the end of one chunk), borrowed from the pool.
    pub fn read_chunk<'a>(&self, pool: &'a BufferPool<'_>, id: StreamId) -> Option<&'a [u8]> {
        self.slot(self.find(id)?)?.recv.read_chunk(pool)
    }

    /// The stored bytes of a stream from absolute offset `at` (up to the end of one chunk), borrowed from the pool.
    /// They may lie beyond a hole: the stream's readable bytes are only the contiguous prefix. `arena` is the
    /// endpoint's spill arena, which holds the stream's received ranges if they spilled.
    pub fn read_at<'a>(
        &self,
        pool: &'a BufferPool<'_>,
        arena: &SpillArena<'_>,
        id: StreamId,
        at: u64,
    ) -> Option<&'a [u8]> {
        self.slot(self.find(id)?)?.recv.read_at(pool, arena, at)
    }

    /// The first run of stored bytes of a stream that reaches past `from` (and the read position), cut to begin at
    /// `from` or later. Bytes beyond the first hole show up here before they are readable.
    pub fn stored_after(&self, arena: &SpillArena<'_>, id: StreamId, from: u64) -> Option<core::ops::Range<u64>> {
        self.slot(self.find(id)?)?.recv.stored_after(arena, from)
    }

    /// The state of a stream's send half; `None` if the stream is unknown or closed.
    pub fn send_view(&self, id: StreamId) -> Option<super::SendView> {
        Some(self.slot(self.find(id)?)?.send.view())
    }

    /// The urgency of a stream; `None` if it is unknown.
    pub fn urgency(&self, id: StreamId) -> Option<u8> {
        Some(self.slot(self.find(id)?)?.urgency)
    }

    /// Release `n` readable bytes of a stream, freeing the chunks they filled and moving the peer's window forward.
    /// `now` and `srtt` are the monotonic time and smoothed round trip in the same unit; they feed the stream's own
    /// delivery-rate meter, which sizes its window. Consuming zero bytes after the end (or a reset) was seen lets the
    /// stream close.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], or [`StreamError::InvalidConsume`] if `n` exceeds the readable bytes.
    pub fn consume(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        n: usize,
        now: u64,
        srtt: u64,
    ) -> Result<RecvStatus, StreamError> {
        let i = self.require(id)?;
        let (floor, ceiling) = (self.stream_window, self.max_stream_window);
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        slot.recv.consume(pool, n as u64)?;
        let status = slot.recv.status();
        // Each window grows only with what its own reader drains: a stream asks for the larger of the initial window
        // and twice its own rate, so the windows together ask for at most the initial windows plus about twice the
        // connection's rate, however many streams share it. A stream that has not drained fast asks for no more than
        // the initial window; a window never shrinks.
        let rate = slot.recv.meter.consumed(n as u64, now, srtt);
        slot.recv.win.size = slot.recv.win.size.max(rate.saturating_mul(2).max(floor).min(ceiling));
        self.grant(pool, i);
        self.settle(pool, i);
        Ok(status)
    }

    /// Move the limit of slot `first`, and of every slot whose grant was deferred, to a window ahead of its read position
    /// (the window its own reader's rate sized in `consume`). A grant is
    /// queued only while the credit already granted and not yet received, plus the increase, fits in the pool;
    /// otherwise the slot stays deferred and is tried again after a later consume.
    fn grant(&mut self, pool: &BufferPool<'_>, first: usize) {
        let mut granted: Option<u64> = None;
        let reserve = self.reserved();
        for i in 0..self.used() {
            let Some(slot) = self.slots.written_mut(i) else {
                continue;
            };
            if !slot.recv.open || !(i == first || slot.recv.win.deferred) {
                continue;
            }
            let Some(candidate) = slot.recv.due() else {
                slot.recv.win.deferred = false;
                continue;
            };
            let sum = *granted.get_or_insert_with(|| self.granted_unreceived());
            let Some(slot) = self.slots.get_mut(i) else { continue };
            let demand = sum
                .saturating_sub(slot.recv.unreceived())
                .saturating_add(slot.recv.charged_demand(candidate));
            if demand.saturating_add(reserve) <= pool.available_bytes() {
                slot.recv.win.limit = candidate;
                slot.recv.win.pending = true;
                slot.recv.win.deferred = false;
                granted = Some(demand);
            } else {
                slot.recv.win.deferred = true;
            }
            self.refresh(i);
        }
        self.stalled = self
            .slots
            .written()
            .iter()
            .take(self.used())
            .any(|s| s.recv.win.deferred);
    }

    /// Whether the bytes `offset..offset + len` of a stream are acknowledged (an empty range asks about the end
    /// marker). A stream that is gone counts as acknowledged.
    pub fn is_acked(&self, pool: &BufferPool<'_>, id: StreamId, offset: u64, len: u64) -> bool {
        self.find(id)
            .and_then(|i| self.slot(i))
            .is_none_or(|s| s.send.is_acked(pool, offset, len))
    }

    /// The lowest offset at or after `offset` of a stream that is not acknowledged for good, so a frame sent again can
    /// be cut to the bytes still held. A stream that is gone returns `offset`.
    pub fn resend_from(&self, id: StreamId, offset: u64) -> u64 {
        self.find(id)
            .and_then(|i| self.slot(i))
            .map_or(offset, |s| s.send.clip(offset))
    }

    /// Whether a stream sends from application storage instead of a buffer.
    pub fn is_source(&self, id: StreamId) -> bool {
        self.find(id)
            .and_then(|i| self.slot(i))
            .is_some_and(|s| s.send.is_source())
    }

    /// The state of a stream's receive side; `None` if it is unknown or closed.
    pub fn recv_status(&self, id: StreamId) -> Option<RecvStatus> {
        Some(self.slot(self.find(id)?)?.recv.status())
    }

    // ---- frames from the peer that move limits -----------------------------------------------------------------

    /// A send limit update for a stream arrived.
    ///
    /// # Errors
    /// [`StreamError::StreamState`] for a stream we cannot send on or never opened; the errors of opening a peer
    /// stream as in [`Streams::on_stream_frame`].
    pub fn on_max_stream_data(&mut self, pool: &BufferPool<'_>, id: StreamId, max: u64) -> Result<(), StreamError> {
        if is_uni(id) && !self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(pool, id)? else { return Ok(()) };
        if let Some(slot) = self.slots.get_mut(i) {
            slot.send.raise_limit(max);
        }
        self.refresh(i);
        Ok(())
    }

    // ---- send ---------------------------------------------------------------------------------------------------

    /// Buffer up to `data.len()` bytes for sending (one copy into pool chunks); returns how many were accepted. The
    /// write is bounded by the stream's send window, the ring, the pool and `buffer_cap - buffered()`, the room the
    /// connection leaves in its send buffer. Zero means one of those is full; a write cut short by the cap is woken
    /// through [`Streams::poll_writable`], one cut by the window by the next window update.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`] on a source-backed
    /// stream, [`StreamError::Finished`] after `finish` or `reset`.
    pub fn write(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        data: &[u8],
        buffer_cap: u64,
    ) -> Result<usize, StreamError> {
        let i = self.require(id)?;
        let room = buffer_cap.saturating_sub(self.buffered);
        let result = self
            .with_send(i, |send| send.write(pool, data, room))
            .unwrap_or(Err(StreamError::UnknownStream));
        self.refresh(i);
        result
    }

    /// A stream whose write was cut short by the send buffer cap, once `buffered() < buffer_cap`; one stream per call,
    /// and its mark is cleared.
    pub fn poll_writable(&mut self, buffer_cap: u64) -> Option<StreamId> {
        if self.buffered >= buffer_cap {
            return None;
        }
        let i = self
            .slots
            .written()
            .iter()
            .take(self.used())
            .position(|s| s.send.cap_cut)?;
        if let Some(slot) = self.slots.get_mut(i) {
            slot.send.cap_cut = false;
        }
        self.ids.get(i).copied()
    }

    /// Back a stream with application storage of `len_hint` bytes: nothing is buffered, bytes are read from `source`
    /// when a frame is built and again when a range is lost, and the end is sent after byte `len_hint`.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`] if data was already
    /// written or a source set.
    pub fn open_source(&mut self, id: StreamId, source: S, len_hint: u64) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.open_source(source, len_hint);
        self.refresh(i);
        result
    }

    /// End a buffered stream after the bytes written so far.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`], [`StreamError::Finished`].
    pub fn finish(&mut self, id: StreamId) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.finish();
        self.refresh(i);
        result
    }

    /// Close every stream and return all their chunks to the pool (the connection is going away).
    pub fn close_all(&mut self, pool: &mut BufferPool<'_>) {
        for slot in self.slots.written_iter_mut() {
            slot.recv.release_all(pool);
            slot.send.release_all(pool);
            slot.send.release_sets(pool);
        }
        self.slots.clear();
        self.ids = [NONE; N];
        self.hot = [0; N];
        self.open = 0;
        self.top = 0;
        self.buffered = 0;
        self.local_live = 0;
        self.remote_live = 0;
        self.released = false;
        self.stalled = false;
    }

    /// Return every spill slot the streams' range sets hold to the endpoint's arena, leaving their chunks to the pool's
    /// reset: the connection is handing its memory back, closed or not.
    pub fn release_spills(&mut self, pool: &mut BufferPool<'_>) {
        for slot in self.slots.written_iter_mut() {
            slot.recv.release_sets(pool);
            slot.send.release_sets(pool);
        }
    }

    /// The peer raised the number of streams we may have opened in all (`MAX_STREAMS`).
    pub fn on_max_streams(&mut self, limit: u64) {
        self.admit.raise_limit(limit);
        self.regate();
    }

    /// Let streams open past the peer's limit while it is unknown (`on`), or end that when its record arrived. A stream
    /// opened past the limit sends nothing until the limit covers it, in the order the streams were opened.
    pub fn set_early(&mut self, on: bool) {
        self.admit.early = on;
    }

    /// Look again at the streams whose first frame waited for the peer's limit.
    fn regate(&mut self) {
        if self.held_from == 0 || self.admit.limit < self.held_from {
            return;
        }
        self.held_from = 0;
        for i in 0..self.used() {
            self.refresh(i);
        }
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests;

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod spill_tests;
