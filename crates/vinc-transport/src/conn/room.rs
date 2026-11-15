//! What the endpoint's ledger still lets a path's address be sent. While the ledger holds an address to three times
//! what it received from it, the endpoint tells the connection the bytes that are left (`Path::room`), and the
//! connection builds nothing for the path beyond them, so the ledger holds back nothing the connection counts as sent
//! (the datagram would be declared lost and the congestion window would shrink for a path that only waits for
//! evidence).
//!
//! Invariants: a room is counted as the ledger counts a datagram, its size and
//! [`DATAGRAM_HEADERS`](super::DATAGRAM_HEADERS); `Paths::held` equals the number of tracked paths whose room is
//! `Some`, so a session with none is known by one read; the room of a path the connection does not track is ignored.

use vinc_crypto::Provider;

use super::Connection;
use super::config::PathId;
use super::path::Paths;
use crate::stream::StreamSource;

impl<const NP: usize> Paths<NP> {
    /// Count the paths that have a room again, after a slot was emptied or replaced.
    pub(crate) fn recount(&mut self) {
        self.held = self.slots.iter().flatten().filter(|p| p.room.is_some()).count();
    }
}

conn_impl! {
    /// The endpoint's ledger holds the address of path `id` to three times what it sent and `room` bytes of that are
    /// left, or no longer holds it (`None`). The connection builds nothing for the path that does not fit, and no size
    /// probe while the path's challenge is unanswered, so the ledger never holds back a datagram the connection counts
    /// as sent (it would be declared lost and the congestion window would shrink for it): a path the peer moved to
    /// carries its challenge at once and waits for the answer instead. Ignored for a path the connection does not
    /// track.
    pub fn set_path_room(&mut self, id: PathId, room: Option<u64>) {
        if let Some(p) = self.paths.find(id).and_then(|i| self.paths.get_mut(i)) {
            let changed = p.room.is_some() != room.is_some();
            p.room = room;
            if changed {
                self.paths.recount();
            }
        }
    }

    /// Whether the ledger holds the address of any path (one read; see [`Connection::held_paths`]).
    pub fn has_held_paths(&self) -> bool {
        self.paths.held > 0
    }

    /// The paths whose address the endpoint's ledger holds (see [`Connection::set_path_room`]): their room is to be
    /// brought up to date before the connection is asked for a datagram.
    pub fn held_paths(&self) -> impl Iterator<Item = PathId> + '_ {
        self.paths.iter().filter(|(_, p)| p.room.is_some()).map(|(_, p)| p.id)
    }
}
