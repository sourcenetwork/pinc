//! Test-only views of the handshake machine boxes for trace validation (cargo features `trace` and `alloc`).

use pinc_crypto::Provider;

use super::super::Connection;
use super::{Handshake, Machines};
use crate::stream::StreamSource;

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
    /// The address of the machine box this handshake holds, 0 for none.
    pub(crate) fn trace_machine(&self) -> usize {
        self.machine.as_deref().map_or(0, |m| core::ptr::from_ref(m).addr())
    }
}

conn_impl! {
    /// The address of the handshake machine box this connection holds, 0 for none, for trace validation.
    pub fn trace_machine(&self) -> usize {
        self.hs.trace_machine()
    }
}
