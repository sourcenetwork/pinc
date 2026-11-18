//! The stream table's credit ledger: what the peer was promised, what the pool reserved for it, and the grants and
//! stream credit held back for want of room and tried again.

use super::super::pool::{BufferPool, Mem};
use super::{Streams, admit_fit};
use crate::stream::StreamSource;

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// Try the window grants that were deferred for want of pool room again. Every release of pool chunks and every
    /// change of the credit ledger calls it (the end of `settle`, and the connection before it writes control
    /// frames, which covers chunks the datagram queues and the early-data buffer gave back), so a grant is never
    /// left waiting for the application to read something: with nothing readable it never would.
    // vertexia: one pass of the table per call while a grant is deferred; gate on the pool's free bytes if a long
    // shortage with many streams shows up in a profile.
    pub fn regrant(&mut self, pool: &mut BufferPool<'_>) {
        self.refresh_admit(pool);
        if self.stalled {
            self.grant(pool, N);
        }
    }

    /// How many more peer streams could be admitted now, counting the credit already given: the live-stream cap (at
    /// most half the slots, so the rest stay free for the streams we open) less the live ones, the free slots, and as
    /// many first charges as [`admit_fit`] allows of those that fit in the pool bytes left beside a first charge for
    /// each open stream ([`Streams::admitted_charge`]).
    pub(super) fn admit_room(&self, mem: Mem<'_, '_>) -> u64 {
        let free = self.free();
        let cap = self.max_remote.min((N as u64 / 2).max(1));
        // The credit is a soft promise, measured against what the store could still give: a credited stream takes no
        // chunk until its data arrives, and data that finds none is held back and sent again, so a quiet session
        // reserves only its floor and leaves the rest of the store to others.
        let fit = mem.room_bytes().saturating_sub(self.admitted_charge()) / self.first_charge();
        cap.saturating_sub(self.remote_live).min(free).min(admit_fit(fit))
    }

    /// Queue a raise of the stream credit when the room grew enough (see [`Admit::update`]).
    // vertexia: one scan of the used slots per call, which the connection makes once per packet it writes; gate on a
    // changed pool or slot count if a profile shows it with many streams.
    pub(super) fn refresh_admit(&mut self, pool: &mut BufferPool<'_>) {
        // The open streams' first charges are reserved; the credit beside them is only measured (`admit_room`).
        pool.make_room(self.admitted_charge());
        let (admitted, room) = (self.admitted(), self.admit_room(pool.mem()));
        self.admit.update(admitted, room);
    }

    /// The pool bytes reserved for the stream credit given to the peer and not yet used: the first charges of the
    /// streams it may still open. Window grants and local streams leave them alone.
    pub(super) fn reserved(&self) -> u64 {
        self.admit
            .adv
            .saturating_sub(self.admitted())
            .saturating_mul(self.first_charge())
    }

    /// The streams the peer may still open inside the credit.
    pub(super) fn credit_left(&self) -> u64 {
        self.admit.adv.saturating_sub(self.admitted())
    }

    /// What the open streams count for when one more stream is admitted: for each, the credit it may still claim, but
    /// no more than one first charge. A window grant counts whole windows ([`Streams::granted_unreceived`]); admitting
    /// a stream asks only that every stream, old and new, has room for a first step, so streams that carry data and
    /// stay open do not shut out new ones for the size of their windows.
    pub(super) fn admitted_charge(&self) -> u64 {
        let first = self.first_charge();
        self.slots
            .written()
            .iter()
            .take(self.used())
            .fold(0, |sum, s| sum.saturating_add(s.recv.unreceived().min(first)))
    }

    /// Whether the first charges of `streams` new streams fit in the pool bytes left beside a first charge for each
    /// open stream. The one test for a peer stream beyond the credit and for a local one, so they cannot differ.
    pub(super) fn windows_fit(&self, mem: Mem<'_, '_>, streams: u64) -> bool {
        let need = self
            .admitted_charge()
            .saturating_add(streams.saturating_mul(self.first_charge()));
        // Growing the reservation moves room from the burst room into it, so it leaves the room this measures alone.
        need <= mem.room_bytes()
    }

    /// Whether `count` more peer streams can be admitted: under the cap and with slots. Inside the credit no pool test
    /// is made (a new stream takes no chunk, and the credit kept its first charge), so a frame that opens many skipped
    /// streams at once is never held back for them; beyond it their first charges must fit beside the credit left.
    pub(super) fn admits(&self, pool: &BufferPool<'_>, count: u64) -> bool {
        let free = self.free();
        let inside = self.admitted().saturating_add(count) <= self.admit.adv;
        self.remote_live + count <= self.max_remote
            && free >= count
            && (inside || self.windows_fit(pool.mem(), count.max(self.credit_left())))
    }

    /// Move the limit of slot `first`, and of every slot whose grant was deferred, to a window ahead of its read position
    /// (the window its own reader's rate sized in `consume`). A grant is
    /// queued only while the credit already granted and not yet received, plus the increase, fits in the pool;
    /// otherwise the slot stays deferred and is tried again after a later consume.
    pub(super) fn grant(&mut self, pool: &mut BufferPool<'_>, first: usize) {
        let mut granted: Option<u64> = None;
        let reserve = self.reserved();
        // The smallest window a deferred grant waits for, with the credit kept beside it: the store queues the slot for
        // both, so the room it reserves passes the check below.
        let mut short: Option<u64> = None;
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
            // The window is reserved; the credit beside it is a soft promise (see `admit_room`).
            pool.make_room(demand);
            if demand <= pool.available_bytes() && demand.saturating_add(reserve) <= pool.room_bytes() {
                slot.recv.win.limit = candidate;
                slot.recv.win.pending = true;
                slot.recv.win.deferred = false;
                granted = Some(demand);
            } else {
                slot.recv.win.deferred = true;
                short.get_or_insert(demand.saturating_add(reserve));
            }
            self.refresh(i);
        }
        self.stalled = self
            .slots
            .written()
            .iter()
            .take(self.used())
            .any(|s| s.recv.win.deferred);
        match short {
            Some(d) => pool.wait_for(d),
            None => pool.stop_waiting(),
        }
    }
}
