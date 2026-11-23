//! The ordered log of a traced endpoint's waiters (feature `trace`): events, wakes and attempts, as
//! `tests/trace_facade_waits.rs` records them.
//!
//! Invariant: a probe only reads state and appends a mark; a core that was not asked to trace pushes nothing.

use alloc::vec::Vec;
use core::cell::RefCell;

use crate::error::{Error, ErrorKind};
use crate::standby::Standby;

/// One thing the waiters did, in the order it happened.
#[derive(Debug, Clone, PartialEq, Eq)]
#[doc(hidden)]
pub enum Mark {
    /// `Core::on_event` begins on an event naming a session: its variant code and its stream (0 if none).
    EvStart {
        /// The variant's code.
        k: u32,
        /// The stream the event names, or 0.
        s: u64,
    },
    /// `Core::on_event` ended: the session's accept queues and the streams of its `send_fail`, in order.
    EvEnd {
        /// The bidirectional accept queue.
        acc: Vec<u64>,
        /// The unidirectional accept queue.
        accu: Vec<u64>,
        /// The streams whose writer sees an error.
        fail: Vec<u64>,
    },
    /// `Core::service` is about to notify every waiter.
    All,
    /// A session record is about to end, with the kind code of its reason.
    End {
        /// The reason's code (see [`kind_code`]).
        e: u32,
    },
    /// The send half of a stream was dropped and its failure forgotten.
    SendDrop {
        /// The stream.
        s: u64,
    },
    /// An attempt ended (key 0) or registered a wait on `key` and stream `s`.
    Try {
        /// The wait's key code, 0 when the attempt ended.
        key: u32,
        /// The wait's stream, or 0.
        s: u64,
    },
    /// `Core::kick` is about to notify the driver.
    Kick,
    /// A future's turn ended and the baton is about to be offered.
    Pass,
    /// The test's waker of future `f` was woken.
    Woke(u32),
}

std::thread_local! {
    static LOG: RefCell<Vec<Mark>> = const { RefCell::new(Vec::new()) };
}

/// Append `m` to this thread's log.
#[doc(hidden)]
pub fn push(m: Mark) {
    // A log being torn down at thread exit, or borrowed by a re-entrant call, drops the mark: nothing reads it then.
    let _ = LOG.try_with(|l| {
        if let Ok(mut l) = l.try_borrow_mut() {
            l.push(m);
        }
    });
}

/// Drain this thread's log.
#[doc(hidden)]
pub fn take() -> Vec<Mark> {
    LOG.try_with(|l| l.try_borrow_mut().map_or_default(|mut l| core::mem::take(&mut *l)))
        .unwrap_or_default()
}

/// The test's waker of future `f` was woken.
#[doc(hidden)]
pub fn woke(f: u32) {
    push(Mark::Woke(f));
}

/// The code of an error kind in the trace: Stopped 1, Reset 2, Closed by the peer 3, Closed by this side 4, TooLarge 5,
/// TimedOut 6, Refused 7, Unreachable 8, Busy 9, Config 10, Shutdown 11.
#[doc(hidden)]
pub const fn kind_code(k: ErrorKind) -> u32 {
    match k {
        ErrorKind::Stopped(_) => 1,
        ErrorKind::Reset(_) => 2,
        ErrorKind::Closed { by_peer: true, .. } => 3,
        ErrorKind::Closed { by_peer: false, .. } => 4,
        ErrorKind::TooLarge => 5,
        ErrorKind::TimedOut => 6,
        ErrorKind::Refused => 7,
        ErrorKind::Unreachable => 8,
        ErrorKind::Busy => 9,
        ErrorKind::Config => 10,
        ErrorKind::Shutdown => 11,
    }
}

impl Standby {
    /// Log `m` if this core was asked to trace.
    pub(crate) fn mark(&self, m: Mark) {
        if self.traced {
            push(m);
        }
    }

    /// Log the end of a session with reason `err`.
    pub(crate) fn mark_end(&self, err: &Error) {
        self.mark(Mark::End {
            e: kind_code(err.kind()),
        });
    }
}
