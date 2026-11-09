//! The initiator and responder state machines.
//!
//! Both are sans-IO: [`Initiator::handle`] and [`Responder::handle`] take one framed message and write at most one
//! framed message, and a [`Step`] says what the caller does next. The drivers in [`crate::drive`] run them over a
//! [`Channel`](crate::Channel).
//!
//! Invariants: only the initiator ends with a report. Every message is answered by one message, so at most one side
//! sends at a time. A reply holds as many parts as fit the message limit; the rest of the answer waits in the replier
//! and its `more` flag says so (see [`wire`](crate::wire)). The exchange ends when a side sends or receives the empty
//! count while neither side holds more.
//! If any leaf part was exchanged, the initiator first sends one check: the fingerprint the responder's whole set
//! must have if the reported difference is exact. A disagreement (an id collision) restarts the session from the root
//! with items in place of ids, which cannot collide; a second disagreement is [`Error::Mismatch`]. So a finished
//! session is exact, not probable, under the keyed-hash assumption on the range fingerprints.

use alloc::vec::Vec;

use vinc_wire::{Reader, varint};

use crate::core::{Arena, Core};
use crate::error::{Error, Reason};
use crate::index::ItemIndex;
use crate::limits::Limits;
use crate::wire::{count, read_parts};

/// What the caller does after a handler wrote (or did not write) a message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Send the message, then receive the next one.
    Send,
    /// Send the message, then call [`Responder::resume`] for the next chunk of the stream.
    Chunk,
    /// Send the message and finish the stream; the session is over.
    Last,
    /// Nothing to send; receive the next message.
    Wait,
    /// Nothing to send; the session is over (a responder finishes the stream).
    Done,
}

/// The items of one side of a finished session, in arrival order.
#[derive(Debug, Clone)]
pub struct Entries<'a> {
    rest: &'a [u8],
}

impl<'a> Iterator for Entries<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        let (len, used) = varint::decode(self.rest).ok()?;
        let end = used.checked_add(usize::try_from(len).ok()?)?;
        let item = self.rest.get(used..end)?;
        self.rest = self.rest.get(end..)?;
        Some(item)
    }
}

/// The exact difference between the two sets, as seen by the initiator.
#[derive(Debug, Clone, Copy)]
pub struct Report<'a> {
    here: &'a Arena,
    there: &'a Arena,
}

impl<'a> Report<'a> {
    /// The items the peer has and the initiator lacks.
    pub fn missing_here(&self) -> Entries<'a> {
        Entries { rest: &self.here.data }
    }

    /// The items the initiator has and the peer lacks.
    pub fn missing_there(&self) -> Entries<'a> {
        Entries { rest: &self.there.data }
    }

    /// How many items [`missing_here`](Self::missing_here) yields.
    pub const fn here_count(&self) -> usize {
        self.here.n
    }

    /// How many items [`missing_there`](Self::missing_there) yields.
    pub const fn there_count(&self) -> usize {
        self.there.n
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    Idle,
    Open,
    Checking,
    Done,
}

/// The side that opens a session and reports the difference.
pub struct Initiator {
    pub(crate) core: Core,
    phase: Phase,
    pub(crate) tx: Vec<u8>,
    pub(crate) rx: Vec<u8>,
}

impl Initiator {
    /// An initiator with its buffers sized from `limits`.
    pub fn new(limits: Limits) -> Self {
        Self {
            core: Core::new(limits, true),
            phase: Phase::Idle,
            tx: Vec::new(),
            rx: Vec::new(),
        }
    }

    /// Begin a session for the set named `set_ref`: write the first message to `out`.
    ///
    /// # Errors
    /// An index failure, or `set_ref` longer than the item limit.
    pub fn start<I: ItemIndex>(&mut self, idx: &I, set_ref: &[u8], out: &mut Vec<u8>) -> Result<(), Error<I::Error>> {
        self.phase = Phase::Idle;
        self.core.start(idx, set_ref, out)?;
        self.phase = Phase::Open;
        Ok(())
    }

    /// Process the peer's message and write the reply, if any, to `out`.
    ///
    /// # Errors
    /// A malformed message, an exceeded limit, an index failure, or [`Error::Mismatch`].
    pub fn handle<I: ItemIndex>(&mut self, idx: &I, msg: &[u8], out: &mut Vec<u8>) -> Result<Step, Error<I::Error>> {
        if !matches!(self.phase, Phase::Open | Phase::Checking) {
            return Err(Reason::State.into());
        }
        self.core.round()?;
        let body = self.core.body(msg)?;
        let mut r = Reader::new(body);
        let (np, more) = read_parts(&mut r)?;
        let ans = self.core.turn(idx, body, &mut r, np)?;
        if ans.cold {
            return Ok(if ans.cold_end {
                self.phase = Phase::Done;
                Step::Done
            } else {
                Step::Wait
            });
        }
        if self.phase == Phase::Checking && np > 0 && !ans.miss {
            return Err(Reason::State.into());
        }
        if ans.miss {
            if self.core.exact {
                return Err(Error::Mismatch);
            }
            self.core.restart_exact(idx, out)?;
            self.phase = Phase::Open;
            return Ok(Step::Send);
        }
        if ans.cnt > 0 || self.core.holds() {
            self.core.reply(out, ans.cnt, self.core.holds())?;
            return Ok(Step::Send);
        }
        if more {
            self.core.end_msg(out)?;
            return Ok(Step::Send);
        }
        self.close(idx, out, np == 0)
    }

    /// The exchange has nothing left to say: verify if leaves were exchanged, else end.
    fn close<I: ItemIndex>(&mut self, idx: &I, out: &mut Vec<u8>, peer_done: bool) -> Result<Step, Error<I::Error>> {
        if self.phase == Phase::Checking {
            self.phase = Phase::Done;
            return Ok(Step::Done);
        }
        if self.core.leafed {
            self.core.check_msg(idx, out)?;
            self.phase = Phase::Checking;
            return Ok(Step::Send);
        }
        self.phase = Phase::Done;
        if peer_done {
            return Ok(Step::Done);
        }
        self.core.end_msg(out)?;
        Ok(Step::Last)
    }

    /// The difference, once a session has finished.
    pub fn report(&self) -> Option<Report<'_>> {
        (self.phase == Phase::Done).then_some(Report {
            here: &self.core.here,
            there: &self.core.there,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    Fresh,
    Open,
    Cold,
    Done,
}

/// The side that answers a session and learns nothing; the initiator reports.
pub struct Responder {
    pub(crate) core: Core,
    side: Side,
    pub(crate) tx: Vec<u8>,
    pub(crate) rx: Vec<u8>,
}

impl Responder {
    /// A responder with its buffers sized from `limits`.
    pub fn new(limits: Limits) -> Self {
        Self {
            core: Core::new(limits, false),
            side: Side::Fresh,
            tx: Vec::new(),
            rx: Vec::new(),
        }
    }

    /// Forget the current session so the next message is read as the first of a new one.
    pub fn reset(&mut self) {
        self.side = Side::Fresh;
    }

    /// Process the initiator's message and write the reply, if any, to `out`.
    ///
    /// The first message of a session names the set; the caller reads it with [`crate::first_set_ref`] to pick the
    /// index.
    ///
    /// # Errors
    /// A malformed message, an exceeded limit, or an index failure.
    pub fn handle<I: ItemIndex>(&mut self, idx: &I, msg: &[u8], out: &mut Vec<u8>) -> Result<Step, Error<I::Error>> {
        let fresh = self.side == Side::Fresh;
        if !fresh && self.side != Side::Open {
            return Err(Reason::State.into());
        }
        let body = self.core.body(msg)?;
        let mut r = Reader::new(body);
        if fresh {
            self.core.clear();
            let l = count(&mut r)?;
            if l > self.core.lim.max_item {
                return Err(Error::ItemTooLarge);
            }
            r.read_bytes(l).map_err(|_| Reason::Truncated)?;
            let na = r.read_varint().map_err(|_| Reason::Truncated)?;
            self.core.n = idx.count().map_err(Error::Index)?;
            if Core::is_cold(na, self.core.n) {
                self.core.begin_cold();
                self.side = Side::Cold;
                return self.resume(idx, out);
            }
            self.side = Side::Open;
        }
        self.core.round()?;
        let (np, more) = read_parts(&mut r)?;
        let ans = self.core.turn(idx, body, &mut r, np)?;
        if ans.cnt > 0 || self.core.holds() {
            self.core.reply(out, ans.cnt, self.core.holds())?;
            return Ok(Step::Send);
        }
        if more {
            self.core.end_msg(out)?;
            return Ok(Step::Send);
        }
        self.side = Side::Done;
        if np == 0 {
            return Ok(Step::Done);
        }
        self.core.end_msg(out)?;
        Ok(Step::Last)
    }

    /// Write the next chunk of a cold stream to `out`.
    ///
    /// # Errors
    /// An index failure, or [`Reason::State`] if no cold stream is running.
    pub fn resume<I: ItemIndex>(&mut self, idx: &I, out: &mut Vec<u8>) -> Result<Step, Error<I::Error>> {
        if self.side != Side::Cold {
            return Err(Reason::State.into());
        }
        if self.core.cold_chunk(idx, out)? {
            self.side = Side::Done;
            Ok(Step::Last)
        } else {
            Ok(Step::Chunk)
        }
    }
}
