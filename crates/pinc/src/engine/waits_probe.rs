//! The entry of the core's events and the probe of the waiters on it: with the `trace` feature, a core that was asked
//! to trace logs each event handled for a session with the session's queues after it, and the codes of the waits.

use pinc_core::Event;
use pinc_keystore::KeyStore;

use super::{Admit, Core};
#[cfg(feature = "trace")]
use super::{GKey, SKey, Wait};
#[cfg(feature = "trace")]
use crate::trace_waits::{Mark, push};

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// One event of the endpoint, handled; a traced core logs it when it names a session.
    pub(super) fn on_event(&mut self, now: u64, ev: Event) {
        #[cfg(feature = "trace")]
        {
            if self.standby.traced
                && let Some(sid) = ev.session()
            {
                push(Mark::EvStart {
                    k: event_code(&ev),
                    s: event_stream(&ev),
                });
                self.on_event_body(now, ev);
                let (acc, accu, fail) = self.sessions.get(&sid).map_or_else(Default::default, |s| {
                    (
                        s.accept_bi.iter().copied().collect(),
                        s.accept_uni.iter().copied().collect(),
                        s.send_fail.iter().map(|(id, _)| *id).collect(),
                    )
                });
                push(Mark::EvEnd { acc, accu, fail });
                return;
            }
        }
        self.on_event_body(now, ev);
    }
}

/// Marks that cost nothing and exist only with the `trace` feature, so a call site needs no `cfg` of its own.
#[cfg_attr(
    not(feature = "trace"),
    allow(clippy::unused_self, reason = "the marks exist only with `trace`")
)]
impl crate::standby::Standby {
    /// Log a kick of the driver.
    pub(super) fn trace_kick(&self) {
        #[cfg(feature = "trace")]
        self.mark(Mark::Kick);
    }

    /// Log the wake of every waiter.
    pub(super) fn trace_all(&self) {
        #[cfg(feature = "trace")]
        self.mark(Mark::All);
    }

    /// Log the drop of the send half of `stream`, which forgets its failure.
    pub(super) fn trace_send_drop(&self, stream: u64) {
        #[cfg(feature = "trace")]
        self.mark(Mark::SendDrop { s: stream });
        #[cfg(not(feature = "trace"))]
        let _ = stream;
    }

    /// Log the end of a session with reason `err`.
    pub(super) fn trace_end(&self, err: &crate::error::Error) {
        #[cfg(feature = "trace")]
        self.mark_end(err);
        #[cfg(not(feature = "trace"))]
        let _ = err;
    }
}

/// The code of an event's variant in the trace.
#[cfg(feature = "trace")]
const fn event_code(ev: &Event) -> u32 {
    match ev {
        Event::Connected { .. } => 1,
        Event::Incoming { .. } => 2,
        Event::Closed { .. } => 4,
        Event::StreamOpened { .. } => 5,
        Event::StreamReadable { .. } => 6,
        Event::StreamReset { .. } => 7,
        Event::StreamWritable { .. } => 8,
        Event::OpenReady { .. } => 9,
        Event::Answered { .. } => 10,
        Event::StreamStopped { .. } => 12,
        Event::DatagramReceived { .. } => 14,
        _ => 0,
    }
}

/// The stream an event names, 0 if none.
#[cfg(feature = "trace")]
const fn event_stream(ev: &Event) -> u64 {
    match *ev {
        Event::StreamOpened { stream, .. }
        | Event::StreamReadable { stream, .. }
        | Event::StreamReset { stream, .. }
        | Event::StreamWritable { stream, .. }
        | Event::StreamStopped { stream, .. } => stream,
        _ => 0,
    }
}

/// The key code and stream of a wait in the trace: session keys 1 to 9, endpoint-wide keys from 16.
#[cfg(feature = "trace")]
pub(crate) const fn wait_code(w: &Wait) -> (u32, u64) {
    match *w {
        Wait::S(_, SKey::AcceptBi) => (1, 0),
        Wait::S(_, SKey::AcceptUni) => (2, 0),
        Wait::S(_, SKey::Datagram) => (3, 0),
        Wait::S(_, SKey::Closed) => (4, 0),
        Wait::S(_, SKey::Open(true)) => (5, 0),
        Wait::S(_, SKey::Open(false)) => (6, 0),
        Wait::S(_, SKey::Read(id)) => (7, id),
        Wait::S(_, SKey::Write(id)) => (8, id),
        Wait::S(_, SKey::Answered) => (9, 0),
        Wait::G(GKey::Dial(_)) => (16, 0),
        Wait::G(GKey::Route(_)) => (17, 0),
        Wait::G(GKey::Shutdown) => (18, 0),
        Wait::G(GKey::Idle) => (19, 0),
        Wait::G(GKey::Events) => (20, 0),
        Wait::G(GKey::Lookup) => (21, 0),
        Wait::G(GKey::Topic) => (22, 0),
        Wait::G(GKey::Publish) => (23, 0),
    }
}
