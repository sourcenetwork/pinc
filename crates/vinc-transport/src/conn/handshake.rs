//! The handshake driver: carries `vinc-security` messages in long Handshake packets and runs its timers.
//!
//! A handshake message can be longer than a datagram, so a Handshake packet body is
//! `total(varint) offset(varint) fragment`: the message length, where the fragment starts and its bytes. The sender
//! cuts the message into datagram-sized fragments; the receiver keeps every fragment that arrives, in any order, in a
//! buffer of the largest message size with a bounded set of received runs, so a lost fragment costs only the
//! retransmission, which sends the flight again and completes the message.
//!
//! The send and receive buffers are one chunk of the connection's buffer pool, held only while the handshake needs
//! them: the receive buffer is released when the session is established (a resumed responder keeps it, with the send
//! buffer, to answer a repeated Hello), the send buffer when the peer has shown it holds the session (the first
//! 1-RTT packet), and at once for a responder of a full handshake. Nothing here allocates per packet.
//!
//! # Timers
//!
//! - A dialing side resends its first flight after `max(500 ms, 2 x RTT)`, where the RTT is the one remembered for
//!   this peer, else the node's average; the delay then doubles up to `max(16 s, 4 x node RTT)`, and on a thin node
//!   no further than `max(8 s, 2 x the node's largest RTT)`. A Hello that stayed unanswered for its third send gives
//!   way to a full handshake (see `vinc-security`), and a rejected ticket restarts the schedule.
//! - A prekey reject (the peer does not hold the prekey a short Initial named) is answered at once with the full
//!   Initial, then at most once per `max(500 ms, node RTT)`; the resends that follow are short as before.
//! - A responder resends its flight after 999 ms, then after 1.998 s, 3.996 s and every 4 s.
//! - A dialing side resends its Finish after 999 ms whatever the round trip it measured, then after `999 ms << n`
//!   (n the sends so far, at most 3) up to 2 s, until the first 1-RTT packet arrives. On a thin node each wait after
//!   the first is at least `min(20 s, 2 x max(srtt, node RTTs))`. The Finish and each resend go on the path the reply
//!   came on, not on the other paths the first flight was copied to.
//! - A handshake still not established more than 30 s after it began (60 s on a thin node) ends; the connection then
//!   closes.
//!   The limit follows the node's round trips as they change, so a dial begun before the node measured itself slow
//!   keeps 60 s.
//! - A dial the layer above told to end early (one it reported before its handshake) also ends when the resend timer
//!   fires after 4 first flights went out with nothing heard from the peer: 15 first delays for a full handshake
//!   (7.5 s at the 500 ms floor), 6 for a resume, whose fallback at the third send restarts the schedule (3 s). A held
//!   flight is not sent and does not count, a message from the peer (a rejected ticket too) starts the count again,
//!   and a thin node keeps its 60 s. It closes as [`CloseReason::Unanswered`](super::CloseReason::Unanswered), which
//!   the node's handshake floor does not count.
//! - When the link returns, a dialing side's pending flight is resent at once.
//! - The round trip of the first flight, if it was answered without a resend, is offered once as an RTT sample.
//!
//! The state machine is large and needed only until the peer shows it holds the session. With the `alloc` feature it is
//! boxed, and the box comes from a [`Machines`] pool that the connections of a node share and goes back to it when the
//! handshake is over or the connection ends, so an established session holds no machine and a new handshake takes a box
//! that exists already. Without `alloc` the machine stays in place and sheds its secrets.
//!
//! Invariants: the reassembly buffer never holds more than [`MAX_MESSAGE_LEN`] bytes and a message is handed to the
//! state machine only when complete; a timer is reported only while it can still act; a box returned to the pool holds
//! no secrets.

use vinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use vinc_crypto::{IdentityAlg, Provider};
use vinc_security::initiator::REJECT_GAP;
use vinc_security::message::MAX_MESSAGE_LEN;
use vinc_security::{
    Env, Event as SecEvent, Failure, Initiator, KeyHandle, KeyRequest, Output, Responder, ResponderStores,
};
use vinc_wire::{Reader, varint};

use super::reasm::Reassembly;
use crate::recovery::{MS, SECOND};
use crate::stream::pool::{BufferPool, CHUNK_SIZE, Chunk};

/// The first resend delay of a dialing side when no round trip is known (the algorithm's 500 ms).
const FIRST: u64 = 500 * MS;
/// The shift limit of the doubling.
const MAX_SHIFT: u32 = 5;
/// The longest resend delay of a dialing side, unless 4 node round trips are longer.
const CAP: u64 = 16 * SECOND;
/// The longest resend delay of a thin node, unless twice its largest round trip is longer.
const CAP_THIN: u64 = 8 * SECOND;
/// A node whose round trip is at least this is thin whatever its configuration says.
const THIN_RTT: u64 = 250 * MS;
/// How often a held flight is looked at again.
const HELD_RECHECK: u64 = 500 * MS;
/// How long an unestablished handshake lasts.
const CONNECT_TIMEOUT: u64 = 30 * SECOND;
/// The first flights a dial told to end early sends; the wait after the last of them ends it.
const EARLY_FLIGHTS: u32 = 4;
/// The first resend delay of a responder: three times the 333 ms initial round trip.
const SERVER_FIRST: u64 = 999 * MS;
/// The longest resend delay of a responder.
const SERVER_CAP: u64 = 4 * SECOND;
/// The shift limit of a responder's doubling.
const SERVER_SHIFT: u32 = 4;
/// The first resend delay of the Finish: three times the 333 ms initial round trip.
const FINISH_FIRST: u64 = 999 * MS;
/// The longest delay between resends of the Finish.
const FINISH_CAP: u64 = 2 * SECOND;
/// The longest extra wait before a thin node resends its Finish.
const THIN_FINISH_MAX: u64 = 20 * SECOND;
/// The shift limit of the Finish backoff.
const FINISH_SHIFT: u32 = 3;
/// The shortest round trip a handshake sample may be.
const MIN_SAMPLE: u64 = MS;

/// The longest message a key request signs.
const SIGN_MAX: usize = 64;

const _: () = assert!(
    2 * MAX_MESSAGE_LEN <= CHUNK_SIZE,
    "both handshake buffers fit one pool chunk"
);

/// What the timers know about the node: how long round trips take. All durations in nanoseconds.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Timing {
    /// A node on a constrained link (a thin node).
    pub(crate) thin: bool,
    /// The round trip remembered for this peer.
    pub(crate) remembered_rtt: Option<u64>,
    /// The node's average handshake round trip.
    pub(crate) node_rtt: Option<u64>,
    /// The node's largest recent round trip.
    pub(crate) node_peak_rtt: Option<u64>,
}

impl Timing {
    /// Replace what the node knows about its round trips.
    pub(crate) const fn set_node(&mut self, thin: bool, node_rtt: Option<u64>, node_peak_rtt: Option<u64>) {
        self.thin = thin;
        self.node_rtt = node_rtt;
        self.node_peak_rtt = node_peak_rtt;
    }

    fn is_thin(&self) -> bool {
        self.thin || self.node_rtt.unwrap_or(0).max(self.node_peak_rtt.unwrap_or(0)) >= THIN_RTT
    }

    /// The first resend delay of a dialing side.
    fn first(&self) -> u64 {
        let r = self.remembered_rtt.or(self.node_rtt).unwrap_or(0);
        FIRST.max(r.saturating_mul(2))
    }

    /// The longest resend delay of a dialing side.
    fn cap(&self) -> u64 {
        let cap = CAP.max(self.node_rtt.unwrap_or(0).saturating_mul(4));
        if self.is_thin() {
            cap.min(CAP_THIN.max(self.node_peak_rtt.unwrap_or(0).saturating_mul(2)))
        } else {
            cap
        }
    }

    /// How long an unestablished handshake lasts.
    fn connect_timeout(&self) -> u64 {
        if self.is_thin() {
            CONNECT_TIMEOUT * 2
        } else {
            CONNECT_TIMEOUT
        }
    }

    /// The first instant at which a handshake begun at `created` has run out: the limit is exceeded, not reached.
    fn connect_deadline(&self, created: u64) -> u64 {
        created.saturating_add(self.connect_timeout()).saturating_add(1)
    }
}

/// One of the two state machines.
#[allow(
    clippy::large_enum_variant,
    reason = "one per connection, held inline so nothing allocates"
)]
pub(crate) enum Machine {
    Client(Initiator),
    Server(Responder),
}

/// The boxes of the handshake state machines a node's connections share, so that an established session holds none and
/// a new handshake takes one that exists already. A handle: cloning it shares the pool. Without the `alloc` feature it
/// holds nothing and the machine stays in the connection.
#[derive(Clone)]
pub struct Machines {
    #[cfg(feature = "alloc")]
    free: alloc::rc::Rc<[core::cell::Cell<Option<alloc::boxed::Box<Machine>>>; MACHINE_BOXES]>,
}

/// The most idle boxes a [`Machines`] pool keeps; a handshake that finds it empty allocates, and a box that finds it
/// full is freed.
#[cfg(feature = "alloc")]
const MACHINE_BOXES: usize = 64;

impl core::fmt::Debug for Machines {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Machines").finish_non_exhaustive()
    }
}

impl Default for Machines {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "alloc")]
impl Machines {
    /// An empty pool.
    pub fn new() -> Self {
        Self {
            free: alloc::rc::Rc::new(core::array::from_fn(|_| core::cell::Cell::new(None))),
        }
    }

    fn take(&self) -> Option<alloc::boxed::Box<Machine>> {
        self.free.iter().find_map(core::cell::Cell::take)
    }

    fn put(&self, b: alloc::boxed::Box<Machine>) {
        let empty = self.free.iter().find(|cell| {
            let held = cell.take();
            let vacant = held.is_none();
            cell.set(held);
            vacant
        });
        if let Some(cell) = empty {
            cell.set(Some(b));
        }
    }
}

#[cfg(not(feature = "alloc"))]
impl Machines {
    /// An empty pool.
    pub const fn new() -> Self {
        Self {}
    }
}

#[cfg(feature = "alloc")]
type MachineBox = alloc::boxed::Box<Machine>;
#[cfg(not(feature = "alloc"))]
type MachineBox = Machine;

#[cfg(feature = "alloc")]
fn boxed(machines: &Machines, machine: Machine) -> MachineBox {
    match machines.take() {
        Some(mut b) => {
            *b = machine;
            b
        }
        None => alloc::boxed::Box::new(machine),
    }
}

#[cfg(not(feature = "alloc"))]
fn boxed(_: &Machines, machine: Machine) -> MachineBox {
    machine
}

/// The machine a slot holds. A function of the slot alone, so a caller can keep its other fields borrowed.
#[cfg(feature = "alloc")]
fn machine_of(slot: &mut Option<MachineBox>) -> Option<&mut Machine> {
    slot.as_deref_mut()
}

/// The machine a slot holds.
#[cfg(not(feature = "alloc"))]
fn machine_of(slot: &mut Option<MachineBox>) -> Option<&mut Machine> {
    slot.as_mut()
}

impl Drop for Handshake {
    fn drop(&mut self) {
        self.retire_machine();
    }
}

/// An owned copy of a key request, so it can be shown as an event after the machine's borrow ended.
#[allow(clippy::large_enum_variant, reason = "held inline so nothing allocates")]
pub(crate) enum OwnedRequest {
    Sign {
        key: KeyHandle,
        alg: IdentityAlg,
        msg: [u8; SIGN_MAX],
        len: usize,
    },
    Decap {
        key: KeyHandle,
        ct: [u8; KEM_CIPHERTEXT_LEN],
    },
}

impl OwnedRequest {
    pub(crate) fn as_request(&self) -> KeyRequest<'_> {
        match self {
            Self::Sign { key, alg, msg, len } => KeyRequest::Sign {
                key: *key,
                alg: *alg,
                message: msg.get(..*len).unwrap_or_default(),
            },
            Self::Decap { key, ct } => KeyRequest::Decapsulate { key: *key, ct },
        }
    }
}

/// Where the dialing side or the responder is in its timers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Stage {
    /// The first flight is out and unanswered, or the responder waits for the Finish.
    Open,
    /// A dialing side established the session and resends its Finish until the peer shows it holds the session.
    Finish,
    /// The timers are done.
    Done,
}

/// The handshake state of a connection.
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent flags of the buffers and timers"
)]
pub(crate) struct Handshake {
    /// The state machine, until the peer shows it holds the session (see [`Machines`]).
    machine: Option<MachineBox>,
    machines: Machines,
    client: bool,
    timing: Timing,
    chunk: Option<Chunk>,
    tx_live: bool,
    rx_live: bool,
    tx_len: usize,
    tx_min: usize,
    tx_off: usize,
    /// Where the segment being sent ends, and where a second segment (from 0) ends once the first is out: a
    /// retransmission of a flight that never went out whole starts at the first byte never sent.
    tx_seg_end: usize,
    tx_wrap: Option<usize>,
    /// The highest offset ever sent of the flight.
    tx_high: usize,
    tx_total_sent: usize,
    tx_active: bool,
    /// The flight in the buffer is a retransmission.
    tx_retx: bool,
    retransmitting: bool,
    rx: Reassembly,
    pub(crate) request: Option<OwnedRequest>,
    pub(crate) request_announced: bool,
    stage: Stage,
    retx_at: Option<u64>,
    /// The resends wait: the peer's address is still being looked up.
    held: bool,
    sends: u32,
    srtt: u64,
    /// The first instant at which the unestablished handshake has run out (see [`Timing::connect_deadline`]).
    connect_at: Option<u64>,
    timed_out: bool,
    /// End once [`EARLY_FLIGHTS`] first flights went unanswered.
    early: bool,
    /// First flights queued since the peer was last heard.
    unheard: u32,
    /// The handshake ended that way.
    unanswered: bool,
    /// When the handshake began.
    created: u64,
    first_sent: u64,
    sample: Option<u64>,
    sampled: bool,
    clock: u64,
    /// A new flight was queued since the connection last asked.
    fresh: bool,
}

impl Handshake {
    /// The handshake of `machine` starting at `now`. Its buffers are one chunk of `pool`.
    ///
    /// # Errors
    /// [`Failure::OutOfMemory`] if the pool has no free chunk.
    pub(crate) fn new(
        machine: Machine,
        machines: Machines,
        pool: &mut BufferPool<'_>,
        now: u64,
        timing: Timing,
    ) -> Result<Self, Failure> {
        let client = matches!(machine, Machine::Client(_));
        let chunk = pool.alloc_chunk().map_err(|_| Failure::OutOfMemory)?;
        let (first, sends) = if client { (timing.first(), 1) } else { (SERVER_FIRST, 0) };
        Ok(Self {
            machine: Some(boxed(&machines, machine)),
            machines,
            client,
            timing,
            chunk: Some(chunk),
            tx_live: true,
            rx_live: true,
            tx_len: 0,
            tx_min: 0,
            tx_off: 0,
            tx_seg_end: 0,
            tx_wrap: None,
            tx_high: 0,
            tx_total_sent: 0,
            tx_active: false,
            tx_retx: false,
            retransmitting: false,
            rx: Reassembly::new(),
            request: None,
            request_announced: false,
            stage: Stage::Open,
            retx_at: client.then(|| now.saturating_add(first)),
            held: false,
            sends,
            srtt: 0,
            connect_at: Some(timing.connect_deadline(now)),
            timed_out: false,
            early: false,
            unheard: 0,
            unanswered: false,
            created: now,
            first_sent: now,
            sample: None,
            sampled: false,
            clock: now,
            fresh: false,
        })
    }

    /// The pool the machine came from.
    pub(crate) const fn machines(&self) -> &Machines {
        &self.machines
    }

    /// The state machine, while the peer has not shown it holds the session.
    pub(crate) fn machine_mut(&mut self) -> Option<&mut Machine> {
        machine_of(&mut self.machine)
    }

    /// Drain the machine until it reports an event. Messages and key requests are copied out; the event is returned.
    pub(crate) fn step(&mut self, pool: &mut BufferPool<'_>) -> Option<SecEvent> {
        loop {
            let out = match machine_of(&mut self.machine)? {
                Machine::Client(m) => m.poll_output(),
                Machine::Server(m) => m.poll_output(),
            };
            match out? {
                Output::Send { data, min_len } => {
                    let dst = self
                        .chunk
                        .as_ref()
                        .filter(|_| self.tx_live)
                        .and_then(|c| pool.bytes_mut(c).get_mut(..data.len()));
                    if let Some(dst) = dst {
                        // The same flight again, after part of it never went out (the amplification limit stopped
                        // it): start at the first byte never sent, then wrap to the start.
                        let same = self.tx_active && data.len() == self.tx_len && dst.get(..data.len()) == Some(data);
                        dst.copy_from_slice(data);
                        let resume = if same && self.tx_high < data.len() {
                            self.tx_high
                        } else {
                            0
                        };
                        if resume == 0 {
                            self.tx_high = 0;
                        }
                        self.tx_len = data.len();
                        self.tx_min = min_len;
                        self.tx_off = resume;
                        self.tx_seg_end = data.len();
                        self.tx_wrap = (resume > 0).then_some(resume);
                        self.tx_total_sent = 0;
                        self.tx_active = true;
                        self.fresh = true;
                        self.tx_retx = self.retransmitting;
                        self.retransmitting = false;
                        if self.client && self.stage == Stage::Open {
                            self.unheard = self.unheard.saturating_add(1);
                        }
                        // A responder's resend schedule starts when its flight first goes out.
                        if !self.client && self.stage == Stage::Open && self.retx_at.is_none() {
                            self.retx_at = Some(self.clock.saturating_add(SERVER_FIRST));
                        }
                    }
                }
                Output::Key(req) => {
                    self.request = Some(match req {
                        KeyRequest::Sign { key, alg, message } => {
                            let mut msg = [0u8; SIGN_MAX];
                            let len = message.len().min(SIGN_MAX);
                            if let (Some(d), Some(s)) = (msg.get_mut(..len), message.get(..len)) {
                                d.copy_from_slice(s);
                            }
                            OwnedRequest::Sign { key, alg, msg, len }
                        }
                        KeyRequest::Decapsulate { key, ct } => OwnedRequest::Decap { key, ct: *ct },
                    });
                    self.request_announced = false;
                }
                Output::Event(e) => {
                    self.on_event(pool, &e);
                    return Some(e);
                }
            }
        }
    }

    /// React to an event of the machine: a rejected or abandoned ticket restarts the dialing schedule, and an
    /// established session lets go of the buffers it no longer needs.
    pub(crate) fn on_event(&mut self, pool: &mut BufferPool<'_>, e: &SecEvent) {
        match e {
            SecEvent::ResumeRejected => {
                self.sends = 1;
                self.first_sent = self.clock;
                self.retx_at = Some(self.clock.saturating_add(self.timing.first()));
            }
            SecEvent::Established(est) => {
                self.connect_at = None;
                if self.client {
                    self.stage = Stage::Finish;
                    self.retx_at = None;
                    self.rx_live = false;
                    if est.resumed {
                        self.tx_live = false;
                        self.tx_active = false;
                    }
                } else {
                    self.stage = Stage::Done;
                    self.retx_at = None;
                    if !est.resumed {
                        self.rx_live = false;
                        self.tx_live = false;
                        self.tx_active = false;
                    }
                }
                self.release(pool);
            }
            SecEvent::EarlyKeys(_) | SecEvent::Failed(_) => {}
        }
    }

    /// Return the chunk to the pool once neither buffer is wanted.
    fn release(&mut self, pool: &mut BufferPool<'_>) {
        if !self.tx_live && !self.rx_live {
            if let Some(c) = self.chunk.take() {
                pool.free_chunk(c);
            }
            self.rx.clear();
        }
    }

    /// A dialing side established its session at `now`: resend the Finish after [`FINISH_FIRST`] until the first
    /// 1-RTT packet arrives. The sends so far (the first flight and its resends) keep counting.
    pub(crate) fn finish_sent(&mut self, now: u64, srtt: u64) {
        if self.client && self.stage == Stage::Finish {
            self.srtt = srtt;
            self.retx_at = Some(now.saturating_add(FINISH_FIRST));
        }
    }

    /// Update the node-level timing inputs. An unestablished handshake takes the connect limit they give, counted
    /// from its start.
    pub(crate) fn set_node_timing(&mut self, thin: bool, node_rtt: Option<u64>, node_peak_rtt: Option<u64>) {
        self.timing.set_node(thin, node_rtt, node_peak_rtt);
        if self.connect_at.is_some() {
            self.connect_at = Some(self.timing.connect_deadline(self.created));
        }
    }

    /// Whether a flight was queued since the last call (the connection copies it onto its fan-out paths).
    pub(crate) const fn take_fresh(&mut self) -> bool {
        let f = self.fresh;
        self.fresh = false;
        f
    }

    /// Queue the flight in the buffer again from its first byte, for another path. Returns whether there is one.
    pub(crate) const fn replay(&mut self) -> bool {
        if !self.tx_live || self.tx_len == 0 {
            return false;
        }
        self.tx_off = 0;
        self.tx_seg_end = self.tx_len;
        self.tx_wrap = None;
        self.tx_high = 0;
        self.tx_total_sent = 0;
        self.tx_retx = true;
        self.tx_active = true;
        true
    }

    /// Allow short Initials in a dialing side's resends while the clock is below `until`.
    pub(crate) fn set_short_until(&mut self, until: u64) {
        if let Some(Machine::Client(m)) = machine_of(&mut self.machine) {
            m.set_short_until(until);
        }
    }

    /// Whether the dialing side took a prekey reject since the last call (the peer does not hold its prekey).
    pub(crate) fn take_prekey_rejected(&mut self) -> bool {
        match machine_of(&mut self.machine) {
            Some(Machine::Client(m)) => m.take_prekey_rejected(),
            _ => false,
        }
    }

    /// Hold the resends of a dialing side, or let them go on.
    pub(crate) const fn set_held(&mut self, held: bool) {
        self.held = held;
    }

    /// End a dialing side once [`EARLY_FLIGHTS`] first flights went unanswered, unless the node is thin.
    pub(crate) const fn end_unanswered(&mut self) {
        self.early = true;
    }

    /// Whether the handshake ended because its first flights went unanswered (see [`Self::end_unanswered`]).
    pub(crate) const fn unanswered(&self) -> bool {
        self.unanswered
    }

    /// Move the pending resend of a dialing side to `at`; ignored once the handshake is past its first flight.
    pub(crate) const fn set_retransmit_at(&mut self, at: u64) {
        if self.client && matches!(self.stage, Stage::Open) && self.retx_at.is_some() {
            self.retx_at = Some(at);
        }
    }

    /// Whether there are fragments or padding left to send.
    pub(crate) const fn has_tx(&self) -> bool {
        self.tx_active
    }

    /// The length of the flight in the buffer if none of it has gone out yet and it is not a retransmission: only
    /// such a flight may leave whole in one datagram.
    pub(crate) const fn whole_len(&self) -> Option<usize> {
        if self.tx_active && self.tx_off == 0 && self.tx_high == 0 && !self.tx_retx {
            Some(if self.tx_len > self.tx_min {
                self.tx_len
            } else {
                self.tx_min
            })
        } else {
            None
        }
    }

    /// The next fragment of at most `room` bytes after the two varints, as `(total, offset, bytes)`.
    pub(crate) fn next_fragment<'p>(
        &mut self,
        pool: &'p BufferPool<'_>,
        room: usize,
    ) -> Option<(usize, usize, &'p [u8])> {
        if !self.tx_active {
            return None;
        }
        if self.tx_off >= self.tx_seg_end
            && let Some(e) = self.tx_wrap.take()
        {
            self.tx_off = 0;
            self.tx_seg_end = e;
        }
        if self.tx_off >= self.tx_seg_end {
            return None;
        }
        let end = self.tx_seg_end.min(self.tx_off + room);
        let off = self.tx_off;
        self.tx_off = end;
        self.tx_high = self.tx_high.max(end);
        let bytes = pool.bytes(self.chunk.as_ref()?).get(off..end)?;
        Some((self.tx_len, off, bytes))
    }

    /// The fixed bytes a fragment header spends: both varints at their current size.
    pub(crate) fn fragment_overhead(&self) -> usize {
        varint::encoded_len(self.tx_len as u64) + varint::encoded_len(self.tx_off as u64)
    }

    /// Record that a datagram of `len` bytes carried this flight; returns how many zero bytes it should be padded
    /// with so the flight totals at least the message's minimum, within `room`.
    pub(crate) fn account(&mut self, len: usize, room: usize) -> usize {
        let done = self.tx_off >= self.tx_seg_end && self.tx_wrap.is_none();
        let before = self.tx_total_sent;
        let pad = if done {
            self.tx_min.saturating_sub(before + len).min(room)
        } else {
            0
        };
        self.tx_total_sent = before + len + pad;
        if done && self.tx_total_sent >= self.tx_min {
            self.tx_active = false;
        }
        pad
    }

    /// Zero bytes still owed after the last fragment went out (a flight padded across datagrams).
    pub(crate) fn padding_owed(&self) -> usize {
        if self.tx_active && self.tx_off >= self.tx_seg_end && self.tx_wrap.is_none() {
            self.tx_min.saturating_sub(self.tx_total_sent)
        } else {
            0
        }
    }

    /// A fragment arrived, in any order. Returns the length of the complete message once every byte is in;
    /// [`Self::feed`] hands it to the state machine.
    pub(crate) fn on_fragment(&mut self, pool: &mut BufferPool<'_>, body: &[u8]) -> Option<usize> {
        if !self.rx_live {
            return None;
        }
        let mut r = Reader::new(body);
        let total = usize::try_from(r.read_varint().ok()?).ok()?;
        let off = usize::try_from(r.read_varint().ok()?).ok()?;
        let data = r.read_bytes(r.remaining()).ok()?;
        let buf = self
            .chunk
            .as_ref()
            .and_then(|c| pool.bytes_mut(c).get_mut(MAX_MESSAGE_LEN..));
        self.rx.add(buf, total, off, data)
    }

    /// [`Self::on_fragment`] with the state of the reassembly around it and the message buffer after it.
    #[cfg(feature = "trace")]
    pub(crate) fn trace_fragment(
        &mut self,
        pool: &mut BufferPool<'_>,
        body: &[u8],
    ) -> super::reasm::trace::FragmentView {
        let before = self.rx.trace_view();
        let ret = self.on_fragment(pool, body);
        let after = self.rx.trace_view();
        let n = ret.unwrap_or(0).max(after.total);
        let message = self
            .chunk
            .as_ref()
            .and_then(|c| pool.bytes(c).get(MAX_MESSAGE_LEN..))
            .and_then(|b| b.get(..n))
            .map(<[u8]>::to_vec)
            .unwrap_or_default();
        super::reasm::trace::FragmentView {
            before,
            after,
            ret,
            message,
        }
    }

    /// Hand the complete message of `len` bytes to the state machine. A server needs the shared `stores`.
    ///
    /// The first message that is taken, if the first flight went unrepeated, gives the handshake round trip.
    pub(crate) fn feed<P: Provider, const PK: usize, const TK: usize>(
        &mut self,
        pool: &BufferPool<'_>,
        env: &mut Env<'_, P>,
        stores: Option<&mut ResponderStores<PK, TK>>,
        len: usize,
    ) -> Result<(), Failure> {
        self.clock = env.now;
        let chunk = self.chunk.as_ref().filter(|_| self.rx_live).ok_or(Failure::Closed)?;
        let msg = pool
            .bytes(chunk)
            .get(MAX_MESSAGE_LEN..)
            .and_then(|b| b.get(..len))
            .ok_or(Failure::InvalidParameter)?;
        // A prekey reject is answered with the full Initial at most once per `max(500 ms, node round trip)`.
        let gap = REJECT_GAP.max(self.timing.node_rtt.unwrap_or(0));
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
        }
        if r.is_ok() && self.client && !self.sampled && self.sends == 1 {
            self.sampled = true;
            self.sample = Some(env.now.saturating_sub(self.first_sent).max(MIN_SAMPLE));
        }
        r
    }

    /// The handshake round trip, once: offered when the first flight was answered without a resend.
    pub(crate) const fn take_rtt_sample(&mut self) -> Option<u64> {
        self.sample.take()
    }

    /// When the next timer fires, if one runs: the resend, or the end of an unestablished handshake.
    pub(crate) fn retransmit_at(&self) -> Option<u64> {
        match (self.retx_at, self.connect_at) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// Whether the handshake ran out of time; the connection then closes.
    pub(crate) const fn timed_out(&self) -> bool {
        self.timed_out
    }

    /// Run the timers if due: the machine queues its flight again and the delay grows, or an unestablished
    /// handshake ends ([`Self::timed_out`]). Returns whether a timer fired.
    pub(crate) fn on_timer<P: Provider>(&mut self, env: &mut Env<'_, P>, now: u64) -> bool {
        self.clock = now;
        if self.connect_at.is_some_and(|t| t <= now) {
            self.connect_at = None;
            self.retx_at = None;
            self.timed_out = true;
            return true;
        }
        if self.retx_at.is_none_or(|t| t > now) {
            return false;
        }
        if self.held && self.client && self.stage == Stage::Open {
            self.retx_at = Some(now.saturating_add(HELD_RECHECK));
            return false;
        }
        if self.early
            && self.client
            && self.stage == Stage::Open
            && self.unheard >= EARLY_FLIGHTS
            && !self.timing.is_thin()
        {
            self.connect_at = None;
            self.retx_at = None;
            self.timed_out = true;
            self.unanswered = true;
            return true;
        }
        let sent = self.sends;
        self.sends = self.sends.saturating_add(1);
        let delay = match (self.stage, self.client) {
            (Stage::Finish, _) => {
                let backoff = FINISH_FIRST.saturating_mul(1 << sent.min(FINISH_SHIFT)).min(FINISH_CAP);
                if self.timing.is_thin() {
                    // On a thin uplink the Finish is resent only after its answer could have arrived.
                    let rtt = self
                        .srtt
                        .max(self.timing.node_peak_rtt.unwrap_or(0))
                        .max(self.timing.node_rtt.unwrap_or(0));
                    backoff.max(THIN_FINISH_MAX.min(rtt.saturating_mul(2)))
                } else {
                    backoff
                }
            }
            (_, true) => self
                .timing
                .cap()
                .min(self.timing.first().saturating_mul(1 << (self.sends - 1).min(MAX_SHIFT))),
            (_, false) => SERVER_CAP.min(SERVER_FIRST.saturating_mul(1 << self.sends.min(SERVER_SHIFT))),
        };
        match machine_of(&mut self.machine) {
            Some(Machine::Client(m)) => {
                // The machine's own failure (a fallback that cannot get randomness) stops it and surfaces as its
                // event; there is nothing to do here.
                let _ = m.retransmit(env);
            }
            Some(Machine::Server(m)) => m.retransmit(),
            None => {}
        }
        self.retransmitting = true;
        // A fallback or a reject restarts the schedule when its event is drained; otherwise the delay stands.
        self.retx_at = Some(now.saturating_add(delay));
        true
    }

    /// The link came back: a dialing side that still waits for the answer to its first flight sends it again now.
    pub(crate) fn link_return(&mut self, now: u64) {
        if self.client && self.stage == Stage::Open && self.retx_at.is_some() {
            self.retx_at = Some(now);
        }
    }

    /// The peer shows it holds the session (a 1-RTT packet arrived): stop the timers and let go of what the
    /// handshake kept to answer a repeat.
    pub(crate) fn confirm(&mut self, pool: &mut BufferPool<'_>) {
        self.retx_at = None;
        self.stage = Stage::Done;
        self.retire_machine();
        self.tx_live = false;
        self.rx_live = false;
        self.tx_active = false;
        self.release(pool);
    }

    /// Shed what the machine holds and, with `alloc`, give its box back to the pool.
    pub(crate) fn retire_machine(&mut self) {
        match machine_of(&mut self.machine) {
            Some(Machine::Client(m)) => m.shed(),
            Some(Machine::Server(m)) => m.shed(),
            None => return,
        }
        #[cfg(feature = "alloc")]
        if let Some(b) = self.machine.take() {
            self.machines.put(b);
        }
    }

    /// Whether a responder still holds its Reply to answer a repeated Hello.
    pub(crate) const fn keeps_reply(&self) -> bool {
        !self.client && (self.tx_live || self.rx_live)
    }
}
