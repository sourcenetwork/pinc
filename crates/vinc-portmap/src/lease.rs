//! The arithmetic of a lease: when to renew it, when it ends, and whether the gateway lost its mappings in between
//! (its epoch went back, or ran at another pace than the client's clock).
//!
//! Times are the client's nanoseconds; lifetimes and epochs are the gateway's seconds.
//!
//! Invariants: [`renew_at`] of a lease of at least one second is strictly before its [`expiry`]; nothing overflows
//! (every sum saturates).

/// Nanoseconds in a second.
pub const SEC: u64 = 1_000_000_000;
/// The longest lease taken: a longer grant is renewed as if it were this long, so a gateway that forgot it is noticed.
pub const MAX_LIFETIME: u32 = 86_400;

/// When to renew a lease of `lifetime` seconds whose request first left at `sent`: half way.
pub const fn renew_at(sent: u64, lifetime: u32) -> u64 {
    sent.saturating_add(clamp(lifetime) as u64 * (SEC / 2))
}

/// When a lease of `lifetime` seconds whose request first left at `sent` ends on the client's clock. The request left
/// before the gateway granted it, so the gateway's own end is no earlier.
pub const fn expiry(sent: u64, lifetime: u32) -> u64 {
    sent.saturating_add(clamp(lifetime) as u64 * SEC)
}

/// The lifetime a lease is scheduled with.
pub const fn clamp(lifetime: u32) -> u32 {
    if lifetime > MAX_LIFETIME {
        MAX_LIFETIME
    } else {
        lifetime
    }
}

/// What the client last heard of the gateway's epoch: its own time and the gateway's seconds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Epoch {
    /// The client's time, in nanoseconds.
    pub at: u64,
    /// The gateway's epoch, in seconds.
    pub server: u32,
}

/// Whether hearing epoch `server` at `now` shows that the gateway lost its mappings since `prev` (RFC 6887 section
/// 8.5, which NAT-PMP's rule is a looser form of): the epoch went back by more than a second, or the two clocks
/// advanced at paces more than a sixteenth and two seconds apart.
pub const fn restarted(prev: Epoch, now: u64, server: u32) -> bool {
    if (server as u64) + 1 < prev.server as u64 {
        return true;
    }
    let client = now.saturating_sub(prev.at) / SEC;
    let gateway = server.saturating_sub(prev.server) as u64;
    client + 2 < gateway - gateway / 16 || gateway + 2 < client - client / 16
}
