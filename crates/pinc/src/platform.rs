//! What the host provides besides I/O: the monotonic clock, the wall clock, randomness, and the types of the instant
//! and of the I/O error. One [`Platform`] value lives inside the host; [`System`] is the standard library's and is
//! the default everywhere a platform is a type parameter, so a host on `std` names none.
//!
//! What an implementation must guarantee:
//!
//! - [`Platform::now`] is monotonic: it never goes backward.
//! - [`HostInstant::add`] never panics; an instant that cannot be represented saturates to the latest one.
//! - [`HostInstant::since`] is zero when `earlier` is later.
//! - [`Platform::wall_ns`] is zero when the wall clock is not known; a relay role needs it and refuses to build
//!   without it.
//!
//! Invariants: nothing here allocates; `now`, `add`, `since` and `is_transient` are arithmetic on the host's own types.

use core::convert::Infallible;
use core::time::Duration;

use pinc_keystore::SoftwareStore;
use zeroize::Zeroizing;

use crate::error::{Error, ErrorKind};

/// A point of the host's monotonic clock.
pub trait HostInstant: Copy {
    /// The instant `d` after this one; it never panics, and an instant that cannot be represented is the latest one.
    #[must_use]
    fn add(self, d: Duration) -> Self;

    /// The time from `earlier` to this instant; zero if `earlier` is later.
    fn since(self, earlier: Self) -> Duration;
}

/// Nanoseconds of the host's monotonic clock.
impl HostInstant for u64 {
    #[inline]
    fn add(self, d: Duration) -> Self {
        self.saturating_add(u64::try_from(d.as_nanos()).unwrap_or(Self::MAX))
    }

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        Duration::from_nanos(self.saturating_sub(earlier))
    }
}

/// The error type of a host's I/O.
pub trait HostError {
    /// The receive lost one datagram and nothing else; any other receive error stops the endpoint.
    fn is_transient(&self) -> bool;
}

/// A host that cannot fail.
impl HostError for Infallible {
    #[inline]
    fn is_transient(&self) -> bool {
        match *self {}
    }
}

/// Only a busy host is transient.
impl HostError for Error {
    #[inline]
    fn is_transient(&self) -> bool {
        matches!(self.kind(), ErrorKind::Busy)
    }
}

/// The host's clock, randomness and the types of its instant and I/O error.
pub trait Platform {
    /// The type of a point of the monotonic clock.
    type Instant: HostInstant;
    /// The type of an I/O error of the host.
    type Error: HostError;

    /// The monotonic clock, which never goes backward.
    fn now(&self) -> Self::Instant;

    /// Nanoseconds since the Unix epoch by the wall clock; zero if the host does not know it.
    fn wall_ns(&self) -> u64;

    /// Fill `out` with unpredictable bytes.
    ///
    /// # Errors
    /// The host's error when it has no randomness to give. An error at a prekey rotation leaves the generator on the
    /// entropy it has.
    fn random(&self, out: &mut [u8]) -> Result<(), Self::Error>;

    /// The key store the facade makes for this host: a generator seeded with 32 bytes of [`Platform::random`], which
    /// a host without an operating system has no other source for. [`System`] draws from the operating system.
    ///
    /// # Errors
    /// The host's error when it has no randomness to give.
    #[doc(hidden)]
    fn key_store(&self) -> Result<SoftwareStore, Self::Error> {
        let mut entropy = Zeroizing::new([0u8; 32]);
        self.random(entropy.as_mut_slice())?;
        Ok(SoftwareStore::from_entropy(*entropy))
    }
}

/// Whole milliseconds of `ns` nanoseconds: the unit of the records' sequence numbers and of the suspend call.
#[inline]
pub(crate) const fn ns_to_ms(ns: u64) -> u64 {
    ns / 1_000_000
}

// The standard library's platform: kept together so that the part that needs `std` is one block.

/// The standard library's platform: `Instant` and `SystemTime`, `io::Error`, and the operating system's randomness.
#[derive(Debug, Clone, Copy, Default)]
pub struct System;

/// The latest instant `self + d` can reach: the step is halved until it fits.
impl HostInstant for std::time::Instant {
    #[inline]
    fn add(self, d: Duration) -> Self {
        let mut step = d;
        while !step.is_zero() {
            if let Some(t) = self.checked_add(step) {
                return t;
            }
            step /= 2;
        }
        self
    }

    #[inline]
    fn since(self, earlier: Self) -> Duration {
        self.saturating_duration_since(earlier)
    }
}

/// Interrupted, reset and refused receives lose one datagram; any other error is the socket's failure.
impl HostError for std::io::Error {
    #[inline]
    fn is_transient(&self) -> bool {
        use std::io::ErrorKind as K;
        matches!(self.kind(), K::Interrupted | K::ConnectionReset | K::ConnectionRefused)
    }
}

impl Platform for System {
    type Instant = std::time::Instant;
    type Error = std::io::Error;

    #[inline]
    fn now(&self) -> std::time::Instant {
        std::time::Instant::now()
    }

    #[inline]
    fn wall_ns(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| u64::try_from(d.as_nanos()).unwrap_or(u64::MAX))
    }

    fn random(&self, out: &mut [u8]) -> Result<(), std::io::Error> {
        // From a kind: no message, so no allocation.
        pinc_keystore::os_random(out).map_err(|_| std::io::ErrorKind::Other.into())
    }

    fn key_store(&self) -> Result<SoftwareStore, std::io::Error> {
        SoftwareStore::new().map_err(|_| std::io::ErrorKind::Other.into())
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use std::io::ErrorKind as K;
    use std::time::Instant;

    use super::*;

    #[test]
    fn a_nanosecond_instant_saturates_at_both_ends() {
        assert_eq!(u64::MAX.add(Duration::from_nanos(1)), u64::MAX);
        assert_eq!(5u64.add(Duration::MAX), u64::MAX);
        assert_eq!(5u64.add(Duration::from_nanos(7)), 12);
        assert_eq!(3u64.since(9), Duration::ZERO);
        assert_eq!(9u64.since(3), Duration::from_nanos(6));
        assert_eq!(0u64.since(u64::MAX), Duration::ZERO);
    }

    #[test]
    fn a_std_instant_add_never_panics_and_never_goes_back() {
        let t = Instant::now();
        let far = t.add(Duration::MAX);
        assert!(far >= t);
        assert_eq!(t.add(Duration::ZERO), t);
        assert_eq!(t.add(Duration::from_secs(2)).since(t), Duration::from_secs(2));
        assert_eq!(t.since(far), Duration::ZERO);
    }

    #[test]
    fn the_system_gives_random_bytes_and_a_wall_clock() {
        let mut out = [0u8; 32];
        System.random(&mut out).unwrap();
        assert_ne!(out, [0u8; 32]);
        assert_ne!(System.wall_ns(), 0);
    }

    #[test]
    fn each_error_type_decides_what_is_transient() {
        for (kind, transient) in [
            (K::Interrupted, true),
            (K::ConnectionReset, true),
            (K::ConnectionRefused, true),
            (K::WouldBlock, false),
            (K::BrokenPipe, false),
            (K::Other, false),
        ] {
            assert_eq!(std::io::Error::from(kind).is_transient(), transient, "{kind:?}");
        }
        assert!(Error::new(ErrorKind::Busy, "busy").is_transient());
        assert!(!Error::new(ErrorKind::Unreachable, "gone").is_transient());
        assert!(!Error::new(ErrorKind::Shutdown, "stopped").is_transient());
    }

    #[test]
    fn milliseconds_truncate_like_a_duration() {
        for ns in [0, 999_999, 1_000_000, 1_700_000_000_123_456_789, u64::MAX] {
            assert_eq!(u128::from(ns_to_ms(ns)), Duration::from_nanos(ns).as_millis());
        }
    }
}
