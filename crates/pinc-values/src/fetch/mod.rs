//! The multi-provider fetcher: one sans-IO machine per value fetch.
//!
//! A [`Fetch`] pulls the missing bytes of a value from up to four providers and puts only verified bytes in the store.
//! Time, session events and application calls go in; session operations, store writes and [`Out`] events come out.
//! The rules and numbers are the reference design's (see [`crate::knobs`]):
//!
//! - DEADLINE_STRIPE / ARRIVAL_CURVE / TAIL_SHRINK: work comes from one offset-ordered queue and each provider is
//!   topped up to its verified rate times one second (64 KiB to 1.5 MiB, 768 KiB before 500 ms of samples); near the
//!   end a top-up takes only a share of what is left (`sched`).
//! - STEAL: an idle provider takes the tail of the provider that would finish last, or all of a stalled one (`sched`).
//! - LIAR_EVICT: a provider whose bytes fail verification is cut off, its share goes back to the queue (`sched`).
//! - HEAD_HOLD: the first granule is delivered once 96 KiB stand behind it, after 40 more granules, or after 2 s
//!   (`recv`).
//! - STALL_REDIAL: no verified granule for 4 s (doubling to 16 s, adjusted by ARK_PACE, BYTE_LIVE, STALL_RTT and
//!   STALL_LIVE) drops the sessions and dials afresh (`stall`).
//! - WRITE_THROUGH: out-of-order groups are verified against range proofs and written at once (`wt`).
//! - Resume: a fetch asks only for the bytes the store has not verified.
//!
//! # Invariants
//!
//! - Only bytes that hashed to the value's root are written to the store, and a range is committed only after its
//!   bytes are written: a crash leaves the verified set a subset of the truth.
//! - All state is in fixed arrays: 4 providers, 16 request streams, 255 wanted ranges, a 64-span queue. A full range
//!   list widens a span over a gap, which asks twice and never skips a byte.
//! - The machine never reads a clock, allocates or blocks; every input carries `now`.

mod recv;
mod rx;
mod sched;
mod stall;
mod wt;

use pinc_transport::stream::StreamId;

use crate::knobs::{GROUP, MAX_PROVIDERS, MAX_REQ_RANGES, STALL_WAIT};
use crate::session::{Outbound, Provider};
use crate::span::{RangeList, Span, align};
use crate::store::ValueStore;
use crate::trace::{Event, FailReason, Out, Trace};
use rx::Rx;
pub use stall::Timers;
use wt::ProofCache;

/// The most request streams a fetch has open at once, over all providers: the size of its table. One provider may use
/// any number of them; the session's own stream limit and credit decide how many it admits.
pub const MAX_STREAMS: usize = 16;
/// The wanted ranges of a fetch.
const WANT: usize = MAX_REQ_RANGES;
/// The spans a provider's assigned work holds.
const ASSIGN: usize = 64;
/// The spans the stripe queue holds.
const QUEUE: usize = 64;

/// The borrowed host a fetch calls into: its session, store and sink.
#[derive(Debug)]
pub struct Io<'a, Se, St, Ob> {
    /// The connection layer.
    pub session: &'a mut Se,
    /// The value store.
    pub store: &'a mut St,
    /// The sink of events and trace records.
    pub out: &'a mut Ob,
}

/// The three parts of an [`Io`], so the fetch code is generic over one type.
pub trait Env {
    /// The session type.
    type Se: Outbound;
    /// The store type.
    type St: ValueStore;
    /// The sink type.
    type Ob: Out;
    /// Borrow the session, the store and the sink at once.
    fn split(&mut self) -> (&mut Self::Se, &mut Self::St, &mut Self::Ob);
}

impl<Se: Outbound, St: ValueStore, Ob: Out> Env for Io<'_, Se, St, Ob> {
    type Se = Se;
    type St = St;
    type Ob = Ob;
    fn split(&mut self) -> (&mut Se, &mut St, &mut Ob) {
        (&mut *self.session, &mut *self.store, &mut *self.out)
    }
}

/// What a fetch is asked to get.
#[derive(Debug, Clone, Copy)]
pub struct FetchSpec<'a> {
    /// The root of the value.
    pub root: [u8; 32],
    /// The value length in bytes. It is authenticated by the last group, so a wrong length fails verification there.
    pub length: u64,
    /// The byte ranges wanted; empty means the whole value.
    pub ranges: &'a [Span],
    /// The providers to use; the first four count.
    pub providers: &'a [Provider],
    /// The time after which the fetch fails, if any. Nothing else ends a fetch whose providers stop answering: a
    /// provider whose session closed is dialled again for as long as the fetch runs, and one that is connected and
    /// sends nothing is waited for with no timer. A fetch that must not wait gives a deadline.
    pub deadline: Option<u64>,
}

/// Why a fetch could not start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartError {
    /// A fetch is already running on this machine.
    Busy,
    /// More than 255 ranges were asked for.
    TooManyRanges,
    /// A range runs past the end of the value.
    OutOfBounds,
}

/// The inputs a fetch takes from the session.
#[derive(Debug, Clone, Copy)]
pub enum In<'a> {
    /// A session to a provider is up.
    Connected(Provider),
    /// A session to a provider could not be set up.
    ConnectFailed(Provider),
    /// A session to a provider closed.
    Closed(Provider),
    /// In-order bytes arrived on a request stream.
    Readable {
        /// The stream.
        stream: StreamId,
        /// How many new in-order bytes.
        bytes: usize,
    },
    /// Bytes arrived beyond a hole on a request stream, held by the session for the value layer.
    Ahead {
        /// The stream.
        stream: StreamId,
        /// The absolute stream offset of the first byte.
        offset: u64,
        /// The number of bytes.
        len: u64,
    },
    /// The peer ended the stream after every byte was consumed.
    Finished(StreamId),
    /// The stream was reset.
    Reset {
        /// The stream.
        stream: StreamId,
        /// The reset code.
        code: u64,
    },
    /// An extension frame arrived (a range proof).
    Ext {
        /// The frame type.
        ty: u64,
        /// The frame body.
        body: &'a [u8],
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Idle,
    Running,
    Done,
}

/// One provider's share of a fetch.
#[derive(Debug, Clone)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent membership and session flags, read one at a time"
)]
struct Prov {
    id: Provider,
    /// Still a candidate (not evicted).
    in_provs: bool,
    /// Holds a share of the work.
    in_assign: bool,
    assign: RangeList<ASSIGN>,
    conn: bool,
    dialing: bool,
    retry: Option<u64>,
    /// The time of its last verified group.
    lp: Option<u64>,
    /// Verified bytes it delivered.
    pb: u64,
    /// The time of its first verified group.
    pt: Option<u64>,
}

impl Prov {
    const fn new(id: Provider) -> Self {
        Self {
            id,
            in_provs: false,
            in_assign: false,
            assign: RangeList::new(),
            conn: false,
            dialing: false,
            retry: None,
            lp: None,
            pb: 0,
            pt: None,
        }
    }
}

/// The first granule, verified and written but not yet announced.
#[derive(Debug, Clone, Copy)]
struct Head {
    off: u64,
    len: u64,
    t0: u64,
}

/// A multi-provider fetch of one value.
#[derive(Debug)]
pub struct Fetch {
    root: [u8; 32],
    length: u64,
    want: RangeList<WANT>,
    o0: u64,
    deadline: Option<u64>,
    provs: [Prov; MAX_PROVIDERS],
    nprov: usize,
    queue: RangeList<QUEUE>,
    striped: bool,
    t0: u64,
    rx: [Option<Rx>; MAX_STREAMS],
    proofs: ProofCache,
    head: Option<Head>,
    released: bool,
    nv: u32,
    lastp: u64,
    lastb: u64,
    treq: u64,
    sw: u64,
    tw: u64,
    state: State,
}

impl Default for Fetch {
    fn default() -> Self {
        Self::new()
    }
}

impl Fetch {
    /// An idle machine; call [`Fetch::start`].
    pub fn new() -> Self {
        Self {
            root: [0; 32],
            length: 0,
            want: RangeList::new(),
            o0: 0,
            deadline: None,
            provs: core::array::from_fn(|_| Prov::new(Provider(0))),
            nprov: 0,
            queue: RangeList::new(),
            striped: false,
            t0: 0,
            rx: core::array::from_fn(|_| None),
            proofs: ProofCache::new(),
            head: None,
            released: false,
            nv: 0,
            lastp: 0,
            lastb: 0,
            treq: 0,
            sw: STALL_WAIT,
            tw: 0,
            state: State::Idle,
        }
    }

    /// Whether a fetch is running.
    pub fn is_running(&self) -> bool {
        self.state == State::Running
    }

    /// Whether the fetch finished, successfully or not.
    pub fn is_done(&self) -> bool {
        self.state == State::Done
    }

    /// Start fetching `spec`. Bytes the store has verified are not asked for again.
    ///
    /// # Errors
    /// [`StartError`] for a bad spec or a machine that is already running; nothing else changes.
    pub fn start<E: Env>(&mut self, io: &mut E, now: u64, spec: &FetchSpec<'_>) -> Result<(), StartError> {
        if self.state == State::Running {
            return Err(StartError::Busy);
        }
        if spec.ranges.len() > WANT {
            return Err(StartError::TooManyRanges);
        }
        if spec.ranges.iter().any(|r| r.end() > spec.length) {
            return Err(StartError::OutOfBounds);
        }
        *self = Self::new();
        let whole = [Span {
            off: 0,
            len: spec.length,
        }];
        let asked = if spec.ranges.is_empty() {
            &whole[..]
        } else {
            spec.ranges
        };
        for s in asked {
            if let Some(a) = align(*s, spec.length) {
                self.want.push_new(a);
            }
        }
        self.root = spec.root;
        self.length = spec.length;
        self.o0 = asked.first().map_or(0, |s| s.off);
        self.deadline = spec.deadline;
        self.t0 = now;
        self.state = State::Running;
        let (_, st, ob) = io.split();
        if spec.length == 0 && spec.root != *blake3::hash(b"").as_bytes() {
            self.finish(ob, now, Event::Failed(FailReason::BadRoot));
            return Ok(());
        }
        let need = self.want.missing(&*st, &self.root);
        if need.is_empty() {
            self.finish(ob, now, Event::Complete);
            return Ok(());
        }
        for id in spec.providers {
            if self.nprov < MAX_PROVIDERS
                && self.provs_unique(*id)
                && let Some(slot) = self.provs.get_mut(self.nprov)
            {
                slot.id = *id;
                slot.in_provs = true;
                self.nprov += 1;
            }
        }
        if self.nprov == 0 {
            self.finish(ob, now, Event::Failed(FailReason::NoProvider));
            return Ok(());
        }
        self.striped = self.nprov > 1;
        ob.trace(
            now,
            Trace::FetchStart {
                wanted: need.total(),
                providers: u8::try_from(self.nprov).unwrap_or(u8::MAX),
                striped: self.striped,
            },
        );
        self.begin(io, now, &need);
        Ok(())
    }

    /// Whether `id` is not yet among the candidates.
    fn provs_unique(&self, id: Provider) -> bool {
        !self.provs.iter().any(|p| p.in_provs && p.id == id)
    }

    /// Tell the application how the fetch ended and stop.
    fn finish<Ob: Out>(&mut self, ob: &mut Ob, now: u64, ev: Event) {
        self.state = State::Done;
        ob.event(now, ev);
    }

    fn prov_index(&self, id: Provider) -> Option<usize> {
        self.provs.iter().position(|p| p.in_provs && p.id == id)
    }

    fn rx_index(&self, stream: StreamId) -> Option<usize> {
        self.rx
            .iter()
            .position(|r| r.as_ref().is_some_and(|r| r.stream == stream))
    }

    /// The least group-aligned size of `len` bytes, at least one group.
    pub(crate) const fn group_floor(len: u64) -> u64 {
        let g = len / GROUP * GROUP;
        if g == 0 { GROUP } else { g }
    }

    /// Feed one input from the session at time `now`.
    pub fn on_event<E: Env>(&mut self, io: &mut E, now: u64, ev: &In<'_>) {
        if self.state != State::Running {
            return;
        }
        match *ev {
            In::Connected(p) => self.on_connected(io, now, p),
            In::ConnectFailed(p) | In::Closed(p) => self.on_down(io, now, p, matches!(ev, In::Closed(_))),
            In::Readable { stream, bytes } => self.on_readable(io, now, stream, bytes),
            In::Ahead { stream, offset, len } => self.on_ahead(io, now, stream, offset, len),
            In::Finished(stream) | In::Reset { stream, .. } => self.on_stream_end(io, now, stream),
            In::Ext { ty, body } => self.on_ext(io, now, ty, body),
        }
    }

    fn on_connected<E: Env>(&mut self, io: &mut E, now: u64, p: Provider) {
        let Some(pi) = self.prov_index(p) else { return };
        let assigned = self.provs.get_mut(pi).is_some_and(|s| {
            s.dialing = false;
            s.conn = true;
            s.in_assign
        });
        if assigned {
            self.request(io, now, pi, None);
            // A provider that holds nothing (it finished, or its work was stolen) must try to take work or steal
            // again now that it is back: no other event will top it up.
            if self.striped {
                self.top_up(io, now, pi);
            }
        }
    }

    /// A session failed to come up or closed: forget its streams and dial again after a delay.
    fn on_down<E: Env>(&mut self, io: &mut E, now: u64, p: Provider, closed: bool) {
        let Some(pi) = self.prov_index(p) else { return };
        if closed {
            self.drop_streams(pi);
        }
        let assigned = self.provs.get_mut(pi).is_some_and(|s| {
            s.dialing = false;
            s.conn = false;
            if s.in_assign {
                s.retry = Some(now + crate::knobs::REDIAL_DELAY);
            }
            s.in_assign
        });
        if assigned {
            io.split().2.trace(now, Trace::Retry(p));
        }
    }

    /// Forget every request stream of provider `pi` (the session is gone or they were reset by us).
    fn drop_streams(&mut self, pi: usize) {
        for slot in &mut self.rx {
            if slot.as_ref().is_some_and(|r| r.provider == pi) {
                *slot = None;
            }
        }
    }

    fn streams_of(&self, pi: usize) -> usize {
        self.rx.iter().flatten().filter(|r| r.provider == pi).count()
    }
}
