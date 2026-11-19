//! The host's clocks, in one place.
//!
//! The endpoint's time is nanoseconds from a fixed origin ([`T0`](crate::drive::T0)); the node also wants the wall
//! clock in milliseconds since the Unix epoch for the records it signs.

/// The wall clock in milliseconds since the Unix epoch; zero if the system clock is before it.
pub(crate) fn wall_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

/// The wall clock in nanoseconds since the Unix epoch; zero if the system clock is before it.
pub(crate) fn wall_ns() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_nanos()).unwrap_or(u64::MAX))
}
