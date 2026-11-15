//! The state the receive and credit path works on, shown for trace validation (cargo feature `trace`).
//!
//! A child of the table so it reaches the table's private slots; it only reads them.

use super::Streams;
use crate::stream::StreamSource;
use crate::stream::pool::BufferPool;
use crate::stream::trace::TableView;

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// The state the receive and credit path works on, for trace validation.
    pub fn trace_view(&self, pool: &BufferPool<'_>) -> TableView {
        let slots: alloc::vec::Vec<_> = self
            .slots
            .iter()
            .zip(&self.ids)
            .map(|(s, &id)| {
                let mut v = s.recv.trace_view(pool);
                let (done, reset, code) = s.send.trace_state();
                v.id = id;
                v.send_done = done;
                v.send_reset = reset;
                v.send_code = code;
                v.ordinal = s.ordinal;
                v
            })
            .collect();
        // A receive half whose ranges spilled holds one more chunk; a send half's spill counts with the others.
        let held: u64 = slots.iter().map(|v| v.held.len() as u64 + u64::from(v.spilled)).sum();
        TableView {
            slots,
            remote_next: self.remote_next,
            local_opened: self.local_opened,
            remote_live: self.remote_live,
            local_live: self.local_live,
            ext: (pool.used_chunks() as u64).saturating_sub(held),
            high_water: self.used() as u64,
            admit: [self.admit.limit, self.admit.adv, self.admit.adv_at],
            admit_pend: self.admit.pend,
            early: self.admit.early,
        }
    }
}
