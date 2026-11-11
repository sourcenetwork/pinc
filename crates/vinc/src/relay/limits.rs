//! The relay's limits and the shape of its state machine.

use vinc_connect::relay::Quota;

use crate::error::{Error, Result};

/// The most member sessions the relay holds: the table size of the state machine.
pub const CARRIERS: usize = 1024;
/// The most signed records the relay stores.
pub const RECORDS: usize = 1024;
/// The most sleeping members whose packets the mailbox holds.
pub const MAILBOX_MEMBERS: usize = 256;
/// The bytes the mailbox holds for each sleeping member.
pub const MAILBOX_BYTES: usize = 16_384;

/// The state machine, in the shape the relay runs. Its tables live on the heap (the `alloc` feature of `vinc-connect`),
/// so a relay of any of these sizes builds on a 1 MiB stack (see the test below).
pub(crate) type Machine = vinc_connect::relay::Relay<CARRIERS, RECORDS, MAILBOX_MEMBERS, MAILBOX_BYTES>;

/// The sizes and rates a relay runs with; each has a default.
///
/// The tables of the state machine have a fixed shape ([`CARRIERS`], [`RECORDS`], [`MAILBOX_MEMBERS`],
/// [`MAILBOX_BYTES`]); these limits lower what a host allows within it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most authenticated carriers at once (at most [`CARRIERS`]). A carrier past it is closed after its
    /// handshake; the carriers that are up keep working. A node that reconnects replaces its own older carrier and
    /// is never counted twice.
    pub carriers: usize,
    /// The most carriers still in their handshake. A stream past it is closed as it is accepted.
    pub handshaking: usize,
    /// How long a carrier may take to finish its handshake, in nanoseconds.
    pub handshake_ns: u64,
    /// A carrier that sends nothing for this long is closed, in nanoseconds. The relay pings every 10 minutes, so a
    /// live peer answers well within the default.
    pub idle_ns: u64,
    /// The most bytes queued for one carrier that is not draining. A carrier past it is closed, so one slow reader
    /// never holds memory or time of the others.
    pub write_backlog: usize,
    /// The most members with a UDP session to the relay's hub, when a hub is configured. Memory for all of them is
    /// reserved when the relay is built: about 360 KiB each plus their buffers.
    pub hub_sessions: usize,
    /// The 16 KiB buffers each hub session may hold (at least 8).
    pub hub_pool_chunks: usize,
    /// The bytes, window and session time each node may use ([`Quota`]).
    pub quota: Quota,
    /// How long the mailbox holds a packet for a sleeping member, in nanoseconds.
    pub mailbox_max_age_ns: u64,
    /// The most operator events kept for [`Relay::next_event`](super::Relay::next_event); the oldest are dropped
    /// and counted.
    pub events: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            carriers: CARRIERS,
            handshaking: 64,
            handshake_ns: 10_000_000_000,
            idle_ns: 1_260_000_000_000,
            write_backlog: 1 << 20,
            hub_sessions: 64,
            hub_pool_chunks: 16,
            quota: Quota::DEFAULT,
            mailbox_max_age_ns: 86_400_000_000_000,
            events: 256,
        }
    }
}

impl Limits {
    /// Check the limits against the shape of the tables.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) naming the limit that is out of range.
    pub fn check(&self) -> Result<()> {
        let ok = (1..=CARRIERS).contains(&self.carriers)
            && self.handshaking >= 1
            && self.handshake_ns > 0
            && self.idle_ns > 0
            && self.write_backlog >= 64 * 1024
            && self.quota.window_ns > 0
            && self.quota.session_ns > 0
            && self.events >= 1
            && (1..=CARRIERS).contains(&self.hub_sessions)
            && self.hub_pool_chunks >= 8;
        if ok {
            Ok(())
        } else {
            Err(Error::config("a relay limit is out of range"))
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// The machine is built by value before it moves to the heap: a 1 MiB stack builds and drops a relay with a hub.
    #[test]
    fn a_relay_builds_and_drops_on_a_one_mebibyte_stack() {
        use vinc_keystore::SoftwareStore;

        use super::super::state::Core;
        use crate::keys::Identity;

        std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let id = Identity::from_seed(&[3; 32]).unwrap();
                let hub = Some(("127.0.0.1:1".parse().unwrap(), vec![b"t".to_vec()]));
                drop(Core::<(), SoftwareStore>::new(id, Vec::new(), Limits::default(), hub, 1).unwrap());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn the_defaults_pass_and_each_bound_is_checked() {
        assert!(Limits::default().check().is_ok());
        let bad = [
            Limits {
                carriers: 0,
                ..Limits::default()
            },
            Limits {
                carriers: CARRIERS + 1,
                ..Limits::default()
            },
            Limits {
                handshaking: 0,
                ..Limits::default()
            },
            Limits {
                write_backlog: 1,
                ..Limits::default()
            },
            Limits {
                events: 0,
                ..Limits::default()
            },
        ];
        for l in bad {
            assert!(l.check().is_err(), "{l:?}");
        }
    }
}
