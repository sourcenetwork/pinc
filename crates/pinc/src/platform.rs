//! The platform: what the facade needs from the host beyond its I/O closures.
//!
//! The builder holds a [`Platform`]: the monotonic clock every deadline reads, the wall clock the relay role and the
//! sleep notices sign with, and the random bytes a software key store without the operating system seeds itself from.
//! The platform also names the two types of the host's world the facade sees: the instant its sleep closure takes
//! ([`HostInstant`]) and the error its receive, send and carrier closures return ([`HostError`]).
//!
//! [`System`], the platform of a `std` host, is the default everywhere, so today's signatures hold: its instant is
//! [`std::time::Instant`] and its error [`std::io::Error`]. A host without `std` calls
//! [`Pinc::builder_on`](crate::Pinc::builder_on) with a platform of its own; without one a build does not type-check,
//! because there is no clock to read.

use core::time::Duration;

use crate::error::Result;
#[cfg(feature = "std")]
use crate::error::{Error, ErrorKind};

/// The host's instant: what the sleep closure takes, and what the platform's clock reads.
pub trait HostInstant: Copy {
    /// The instant `d` later (saturating).
    #[must_use]
    fn add(self, d: Duration) -> Self;

    /// The time from `earlier` to this instant; zero if `earlier` is later.
    #[must_use]
    fn since(self, earlier: Self) -> Duration;
}

impl HostInstant for u64 {
    /// A nanosecond count.
    fn add(self, d: Duration) -> Self {
        self.saturating_add(u64::try_from(d.as_nanos()).unwrap_or(u64::MAX))
    }

    fn since(self, earlier: Self) -> Duration {
        Duration::from_nanos(self.saturating_sub(earlier))
    }
}

#[cfg(feature = "std")]
impl HostInstant for std::time::Instant {
    fn add(self, d: Duration) -> Self {
        self + d
    }

    fn since(self, earlier: Self) -> Duration {
        self.saturating_duration_since(earlier)
    }
}

/// The one thing the facade ever asks a host I/O error: whether it loses one datagram and nothing else.
pub trait HostError {
    /// A transient error loses the one datagram it was carrying: the transport sends it again. Anything else ends
    /// the endpoint.
    fn is_transient(&self) -> bool;
}

#[cfg(feature = "std")]
impl HostError for std::io::Error {
    fn is_transient(&self) -> bool {
        matches!(
            self.kind(),
            std::io::ErrorKind::Interrupted
                | std::io::ErrorKind::ConnectionReset
                | std::io::ErrorKind::ConnectionRefused
        )
    }
}

/// What the facade needs from the host beyond its I/O closures: the clocks, and random bytes.
pub trait Platform {
    /// The instant the host's sleep closure takes, and its clock reads.
    type Instant: HostInstant;
    /// The error the host's receive, send and carrier closures return.
    type Error: HostError;

    /// The monotonic clock now.
    fn now(&self) -> Self::Instant;

    /// The wall clock in nanoseconds since the Unix epoch; `None` when the host has no wall clock, which refuses the
    /// relay role and signs the sleep notices with a count of sleeps instead.
    fn wall_ns(&self) -> Option<u64>;

    /// Fill `out` with random bytes.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] when the host has no randomness.
    fn random(&self, out: &mut [u8]) -> Result<()>;
}

/// The platform of a `std` host: the operating system's clocks and randomness, `std::time::Instant` and
/// `std::io::Error`. The default everywhere, so a host of today changes nothing. The type exists without the `std`
/// feature (the defaults name it); its [`Platform`] impl does not, so a build without `std` does not type-check until
/// the host names a platform of its own.
#[derive(Debug, Clone, Copy, Default)]
pub struct System;

/// The wall clock in nanoseconds since the Unix epoch; zero if the system clock is before it.
#[cfg(feature = "std")]
fn wall_ns() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_nanos()).unwrap_or(u64::MAX))
}

#[cfg(feature = "std")]
impl Platform for System {
    type Instant = std::time::Instant;
    type Error = std::io::Error;

    fn now(&self) -> Self::Instant {
        std::time::Instant::now()
    }

    fn wall_ns(&self) -> Option<u64> {
        Some(wall_ns())
    }

    fn random(&self, out: &mut [u8]) -> Result<()> {
        pinc_keystore::os_random(out).map_err(|_| Error::new(ErrorKind::Config, "the system has no randomness"))
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// The `u64` instant is always there, without std: it adds and subtracts saturating.
    #[test]
    fn a_nanosecond_count_adds_and_measures_saturating() {
        let at = 10_000_000_000u64;
        assert_eq!(at.add(Duration::from_nanos(5)), 10_000_000_005);
        assert_eq!(at.add(Duration::from_secs(10)), 20_000_000_000);
        assert_eq!(at.since(at), Duration::ZERO);
        assert_eq!(at.since(at.add(Duration::from_secs(1))), Duration::ZERO);
        assert_eq!(u64::MAX.add(Duration::from_secs(1)), u64::MAX);
    }

    /// A no-std platform of the test kind: the clock a `Cell<u64>` holds, errors of the crate's own type.
    pub(crate) struct TestClock(pub core::cell::Cell<u64>);

    pub(crate) struct TestError(pub bool);

    impl HostError for TestError {
        fn is_transient(&self) -> bool {
            self.0
        }
    }

    impl Platform for TestClock {
        type Instant = u64;
        type Error = TestError;

        fn now(&self) -> u64 {
            self.0.get()
        }

        fn wall_ns(&self) -> Option<u64> {
            None
        }

        fn random(&self, out: &mut [u8]) -> Result<()> {
            for b in out.iter_mut() {
                *b = 7;
            }
            Ok(())
        }
    }

    #[test]
    fn a_platform_without_std_builds_and_reads_its_clock() {
        let p = TestClock(core::cell::Cell::new(1_000));
        assert_eq!(p.now(), 1_000);
        assert!(p.wall_ns().is_none());
        let mut b = [0u8; 4];
        p.random(&mut b).unwrap();
        assert_eq!(b, [7; 4]);
    }
}
