//! Whether the endpoint's ledger holds a path's address. The ledger holds an address to three times what it received
//! from it until it proves that it receives what we sent, and the endpoint says so on every datagram it delivers from
//! that address; the connection keeps it as the path's `held` flag.
//!
//! Invariants: `Paths::held` equals the number of tracked paths whose flag is set, so a session with none is known by
//! one read; a flag for a path the connection does not track is ignored; the flag stops the size probe and, in a
//! validated session, sends past the path's own budget; nothing else of what the connection builds.

use pinc_crypto::Provider;

use super::Connection;
use super::config::PathId;
use super::path::Paths;
use crate::stream::StreamSource;

impl<const NP: usize> Paths<NP> {
    /// Count the held paths again, after a flag changed or a slot was emptied or replaced.
    pub(crate) fn recount(&mut self) {
        self.held = self.slots.iter().flatten().filter(|p| p.held).count();
    }
}

conn_impl! {
    /// The endpoint's ledger holds the address of path `id` (`held`) or no longer does. No size probe is offered for a
    /// held path: the ledger would refuse it, and a lost probe is not retried for 10 minutes. Ignored for a path the
    /// connection does not track.
    pub fn set_path_held(&mut self, id: PathId, held: bool) {
        if let Some(p) = self.paths.find(id).and_then(|i| self.paths.get_mut(i)) {
            let changed = p.held != held;
            p.held = held;
            if changed {
                self.paths.recount();
            }
        }
    }

    /// Whether the ledger holds the address of any path (one read).
    pub fn has_held_paths(&self) -> bool {
        self.paths.held > 0
    }
}

#[cfg(feature = "trace")]
conn_impl! {
    /// The count of held paths and every path slot as `(id, held)`, for trace validation.
    pub fn trace_held_paths(&self) -> (usize, alloc::vec::Vec<Option<(u64, bool)>>) {
        let slots = self.paths.slots.iter().map(|s| s.as_ref().map(|p| (p.id.0, p.held))).collect();
        (self.paths.held, slots)
    }
}
