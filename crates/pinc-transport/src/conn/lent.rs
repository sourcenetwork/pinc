//! What an endpoint lends a connection for the length of one call.

use crate::stream::spill::SpillArena;

/// What an endpoint lends a connection for one call: the memory every session of the endpoint shares and none owns.
/// The endpoint keeps it beside its connection table and passes it to each call that can spill a range set, read a
/// spilled one or return its slot; between calls a connection holds only the indices of its slots.
#[derive(Debug)]
pub struct Lent<'l, 'a> {
    /// The endpoint's spill arena.
    pub spill: &'l mut SpillArena<'a>,
}

impl<'a, P, S, const N: usize, const C: usize, const F: usize, const NP: usize> super::Connection<'a, P, S, N, C, F, NP>
where
    P: pinc_crypto::Provider,
    S: crate::stream::StreamSource,
{
    /// Run `f` with the arena moved into the connection's pool, and move it back after.
    pub(super) fn with_lent<R>(&mut self, lent: &mut Lent<'_, 'a>, f: impl FnOnce(&mut Self) -> R) -> R {
        self.pool.lend_spill(core::mem::take(lent.spill));
        let r = f(self);
        *lent.spill = self.pool.return_spill();
        r
    }
}
