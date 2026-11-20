//! The ordered log of a traced endpoint's drive turns (feature `trace`), as `tests/trace_facade_turn.rs` records them
//! for the TLA+ trace check `TraceFacadeTurn.tla`.
//!
//! Each mark is one step of the model `FacadeTurn.tla`: a call of the facade entering the drive loop, ending a poll in
//! one of its three ways, finishing a flush, or leaving it (the guard's `Drop`), and the endpoint notifying a ticket.
//! A mark names no future: the test knows which task it polled. Invariant: a probe only reads state and appends a
//! mark, and an endpoint that was not asked to trace (`Endpoint::trace_waits`) pushes nothing.

use alloc::vec::Vec;
use core::cell::{Cell, RefCell};

use crate::standby::Standby;

/// A ticket as a slot and a generation.
pub type Code = (u32, u32);

/// One step of the drive's turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[doc(hidden)]
pub enum Kind {
    /// A call entered the drive loop.
    Start,
    /// A poll served something or queued packets: the call flushes and polls again.
    Io,
    /// The attempt finished: the call flushes and returns.
    Done,
    /// The attempt waits.
    Wait {
        /// The call's ticket after the poll.
        tk: Code,
        /// Whether the call drives after the poll.
        drv: bool,
        /// How many datagrams the burst took from the host.
        took: u32,
        /// Whether the call goes on to flush (something moved) rather than return `Pending`.
        flush: bool,
    },
    /// A flush ended and the call polls again.
    Flush,
    /// The call returned: its flush ended after its guard's `Drop`.
    Return,
    /// The host dropped the call's future (after its guard's `Drop`).
    Drop,
    /// The endpoint notified this ticket.
    Notify(Code),
    /// The endpoint woke every armed ticket.
    NotifyAll,
}

/// A step, and the turn's flag and the core's driver ticket after it (none for a notification, which changes neither).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[doc(hidden)]
pub struct Mark {
    /// The step.
    pub kind: Kind,
    /// The flag and the driver ticket after the step.
    pub state: Option<(bool, Option<Code>)>,
}

std::thread_local! {
    static LOG: RefCell<Vec<Mark>> = const { RefCell::new(Vec::new()) };
    static TOOK: Cell<u32> = const { Cell::new(0) };
}

/// Append `m` to this thread's log.
#[doc(hidden)]
pub fn push(m: Mark) {
    // A log torn down at thread exit, or borrowed by a re-entrant call, drops the mark: nothing reads it then.
    let _ = LOG.try_with(|l| {
        if let Ok(mut l) = l.try_borrow_mut() {
            l.push(m);
        }
    });
}

/// Drain this thread's log.
#[doc(hidden)]
pub fn take() -> Vec<Mark> {
    LOG.try_with(|l| {
        l.try_borrow_mut()
            .map(|mut l| core::mem::take(&mut *l))
            .unwrap_or_default()
    })
    .unwrap_or_default()
}

/// One datagram of the host was handed to the core in the burst now running.
pub(crate) fn took() {
    let _ = TOOK.try_with(|t| t.set(t.get().saturating_add(1)));
}

/// The datagrams the burst took since the last call.
pub(crate) fn take_took() -> u32 {
    TOOK.try_with(|t| t.replace(0)).unwrap_or(0)
}

impl Standby {
    /// Log a notification, which carries no state.
    pub(crate) fn turn_mark(&self, kind: Kind) {
        if self.traced {
            push(Mark { kind, state: None });
        }
    }
}
