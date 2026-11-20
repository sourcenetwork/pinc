//! The marks of the drive turn (`trace_turn`): they read the turn's flag and the core's driver ticket, which live in
//! [`Shared`], so they are written here. Each call site in `drive.rs` is one line behind the `trace` feature.

use super::Shared;
use crate::engine::Core;
use crate::host::Hosted;
use crate::standby::Ticket;
use crate::trace_turn::{Kind, Mark, push, take_took};

/// A mark of a core already borrowed by the caller.
pub(super) fn mark<H: Hosted>(sh: &Shared<H>, core: &Core<H::Keys, H::Access>, kind: Kind) {
    if core.standby.traced {
        push(Mark {
            kind,
            state: Some((sh.driving.get(), core.driver.map(Ticket::code))),
        });
    }
}

/// A mark of a core the caller does not hold.
pub(super) fn mark_free<H: Hosted>(sh: &Shared<H>, kind: Kind) {
    if let Some(core) = sh.lock() {
        mark(sh, &core, kind);
    }
}

/// The attempt waits: the call's ticket after the poll (`core` when the caller holds it), whether it drives, and how it
/// ends the poll.
pub(super) fn wait<H: Hosted>(
    sh: &Shared<H>,
    core: Option<&Core<H::Keys, H::Access>>,
    ticket: Option<Ticket>,
    drv: bool,
    flush: bool,
) {
    let Some(t) = ticket else { return };
    let kind = Kind::Wait {
        tk: t.code(),
        drv,
        took: take_took(),
        flush,
    };
    match core {
        Some(c) => mark(sh, c, kind),
        None => mark_free(sh, kind),
    }
}

/// The end of a call, after its guard released what it held: a return in the poll that took the value (`taken`), a
/// return after the flush (`returned`), or a drop if the host dropped the call.
pub(super) fn end<H: Hosted>(sh: &Shared<H>, returned: bool, taken: bool) {
    let kind = if taken {
        Kind::Taken
    } else if returned {
        Kind::Return
    } else {
        Kind::Drop
    };
    mark_free(sh, kind);
}
