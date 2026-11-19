//! Helpers shared by the grading tests.

use std::net::SocketAddr;

use pinc_sim::suite::rec::NS;

pub const DUR: u64 = 600 * NS;

pub fn sec(x: u64) -> u64 {
    x * NS
}

pub fn ms(x: u64) -> u64 {
    x * 1_000_000
}

pub fn addr(n: u8) -> SocketAddr {
    SocketAddr::from(([10, 0, 0, n], 4000))
}

pub fn close(a: f64, b: f64) -> bool {
    (a - b).abs() <= 1e-9 * b.abs().max(1.0)
}
