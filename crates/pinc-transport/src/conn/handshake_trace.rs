//! Test-only views of the handshake for trace validation (cargo feature `trace`; the machine boxes also need `alloc`).

#[cfg(feature = "alloc")]
use pinc_crypto::Provider;

#[cfg(feature = "alloc")]
use super::super::Connection;
use super::Handshake;
#[cfg(feature = "alloc")]
use super::Machines;
#[cfg(feature = "alloc")]
use crate::stream::StreamSource;

#[cfg(feature = "alloc")]
impl Machines {
    /// The address of the box in each of the pool's cells, 0 for an empty cell, for trace validation. Each cell is
    /// taken and set back, as `put` reads it.
    #[must_use]
    pub fn trace_cells(&self) -> alloc::vec::Vec<usize> {
        self.free
            .iter()
            .map(|cell| {
                let held = cell.take();
                let addr = held.as_deref().map_or(0, |m| core::ptr::from_ref(m).addr());
                cell.set(held);
                addr
            })
            .collect()
    }
}

impl Handshake {
    /// The Finish resend state, for trace validation.
    pub(crate) fn finish_view(&self) -> super::super::timer::trace::FinishView {
        super::super::timer::trace::FinishView {
            finish: self.client && self.stage == super::Stage::Finish,
            sends: self.sends,
            first: self.finish_first,
            retx_at: self.retx_at,
            thin: self.timing.is_thin(),
            rtt: self.finish_rtt(),
            pto: self.finish_pto,
        }
    }

    /// The address of the machine box this handshake holds, 0 for none.
    #[cfg(feature = "alloc")]
    pub(crate) fn trace_machine(&self) -> usize {
        self.machine.as_deref().map_or(0, |m| core::ptr::from_ref(m).addr())
    }
}

#[cfg(feature = "alloc")]
conn_impl! {
    /// The address of the handshake machine box this connection holds, 0 for none, for trace validation.
    pub fn trace_machine(&self) -> usize {
        self.hs.trace_machine()
    }
}
