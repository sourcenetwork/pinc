//! The notes `build_datagram` leaves for trace validation (cargo feature `trace`): the inputs of a call and what it
//! wrote, pushed to the log of [`DgramRecord`](super::trace::DgramRecord) when the call ends. Without the feature
//! the note is empty and every method returns what it is given, so the builder reads the same either way.

use pinc_crypto::Provider;

use super::{Connection, StreamSource};

#[cfg(feature = "trace")]
pub(super) type Note = super::trace::DgramRecord;

/// The note of a call, empty without the feature.
#[cfg(not(feature = "trace"))]
pub(super) struct Note;

#[cfg(feature = "trace")]
conn_impl! {
    /// The inputs of a call of `build_datagram` for path `ti`, read before the handshake writes anything.
    pub(super) fn dgram_note(&self, ti: usize, out: usize, probe: Option<usize>, path_mtu: u16) -> Note {
        use super::super::config::{HEADERS_V4, MIN_MTU};
        let (interface_mtu, v6) = self.paths.get(ti).map_or((MIN_MTU + HEADERS_V4, false), |p| (p.info.interface_mtu, p.info.v6));
        let flight = if self.cfg.flight_split {
            self.hs.whole_len().map_or(0, |n| n + super::FLIGHT_OVERHEAD)
        } else {
            0
        };
        Note {
            path_mtu,
            interface_mtu,
            v6,
            out,
            amp: self.amp_room(ti).min(1_000_000),
            probe: probe.unwrap_or(0),
            flight,
            pad_owed: self.hs.padding_owed(),
            hs: 0,
            app: 0,
            pad: 0,
            len: 0,
        }
    }

    /// The padding the handshake owes a datagram that carried `hs_len` bytes of the flight, read before it is
    /// accounted.
    pub(super) fn dgram_owed(&self, note: &mut Note, hs_len: usize) {
        note.pad_owed = self.hs.pad_due(hs_len);
    }

    /// Record the call, which wrote `[hs, app, pad]` bytes and returned `r`, and pass `r` on.
    pub(super) fn dgram_end(&mut self, mut note: Note, parts: [usize; 3], r: Option<usize>) -> Option<usize> {
        if self.dgram.on {
            [note.hs, note.app, note.pad] = parts;
            note.len = r.unwrap_or(0);
            self.dgram.log.push(note);
        }
        r
    }
}

#[cfg(not(feature = "trace"))]
conn_impl! {
    #[allow(clippy::unused_self, reason = "the same call as with the trace feature, which reads the connection")]
    pub(super) fn dgram_note(&self, _ti: usize, _out: usize, _probe: Option<usize>, _path_mtu: u16) -> Note {
        Note
    }

    #[allow(clippy::unused_self, reason = "the same call as with the trace feature, which reads the connection")]
    pub(super) fn dgram_owed(&self, _note: &mut Note, _hs_len: usize) {}

    #[allow(clippy::unused_self, reason = "the same call as with the trace feature, which reads the connection")]
    pub(super) fn dgram_end(&mut self, _note: Note, _parts: [usize; 3], r: Option<usize>) -> Option<usize> {
        r
    }
}
