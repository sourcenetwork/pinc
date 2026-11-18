//! What an endpoint lends a connection for the length of one call.

use crate::stream::spill::SpillArena;
use crate::stream::store::ChunkStore;

/// What an endpoint lends a connection for one call: the memory every session of the endpoint shares and none owns.
/// The endpoint keeps it beside its connection table and passes it to each call that can spill a range set, read a
/// spilled one or return its slot, or take, give or count a chunk; between calls a connection holds only the indices of
/// its slots and the numbers of its chunks.
#[derive(Debug)]
pub struct Lent<'l, 'a> {
    /// The endpoint's spill arena.
    pub spill: &'l mut SpillArena<'a>,
    /// The endpoint's chunk store: an empty one for an endpoint whose pools have memory of their own.
    pub store: &'l mut ChunkStore,
}

impl<'a, P, S, const N: usize, const C: usize, const F: usize, const NP: usize> super::Connection<'a, P, S, N, C, F, NP>
where
    P: pinc_crypto::Provider,
    S: crate::stream::StreamSource,
{
    /// Run `f` with the arena and the store moved into the connection's pool, and move them back after.
    pub(super) fn with_lent<R>(&mut self, lent: &mut Lent<'_, 'a>, f: impl FnOnce(&mut Self) -> R) -> R {
        self.pool.lend_spill(core::mem::take(lent.spill));
        self.pool.lend_store(core::mem::take(lent.store));
        let r = f(self);
        *lent.spill = self.pool.return_spill();
        *lent.store = self.pool.return_store();
        r
    }
}
