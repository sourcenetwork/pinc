//! The reference random source: a bit-exact port of `CPython`'s `random` and of the reference harness's seed
//! derivation, behind the simulator's [`Random`] trait.
//!
//! The harness seeds each component stream with `random.Random(int_from_blake2b(repr((seed, tag, index))))`. This
//! module reproduces the whole chain: [`seed`] hashes the `repr` text of a tuple, [`PyRandom`] is the generator, and
//! [`RefRng`] makes the generator a [`Random`] so that a [`crate::Sim`] draws exactly the numbers the reference
//! harness draws. Needs the `reference` feature (it brings in the `BLAKE2b` hash).
//!
//! Invariant: every function here is a pure function of its arguments (the loss-realization switch, read once per
//! process, is the one input beyond them), and the test vectors in `tests/data/reference_rng.txt` were produced by
//! `CPython` itself.

mod mt;
mod repr;

use std::sync::OnceLock;

use blake2::digest::consts::{U8, U16, U32};
use blake2::{Blake2b, Digest};

pub use mt::PyRandom;
pub use repr::Py;

use crate::rng::{Random, Stream};

/// The reference `_seed(*parts)`: the little-endian integer of the 8-byte `BLAKE2b` of `repr(parts)`, where `parts` is
/// the tuple of the given values.
pub fn seed(parts: &[Py<'_>]) -> u64 {
    let d = Blake2b::<U8>::digest(Py::Tuple(parts).repr().as_bytes());
    let mut out = [0u8; 8];
    out.copy_from_slice(&d);
    u64::from_le_bytes(out)
}

/// `blake2b(repr(parts).encode(), digest_size=32)`, the digest of a workload item.
pub fn digest32(parts: &[Py<'_>]) -> [u8; 32] {
    Blake2b::<U32>::digest(Py::Tuple(parts).repr().as_bytes()).into()
}

/// `blake2b(data, digest_size=16)`, the digest the trace hash and the test vectors use.
pub fn blake2b_128(data: &[u8]) -> [u8; 16] {
    Blake2b::<U16>::digest(data).into()
}

/// The environment variable that selects the realization of every LAN's packet loss.
pub const LOSS_SALT_ENV: &str = "PINC_SUITE_LOSS_SALT";

/// Parses the value of [`LOSS_SALT_ENV`]: unset or `0` is the world's own realization, a whole number of 1 or more is
/// another one.
///
/// # Errors
///
/// A value that is not a whole number, with a message that says what the variable takes.
pub fn parse_loss_salt(value: Option<&str>) -> Result<u64, String> {
    value.map_or(Ok(0), |v| {
        v.trim().parse().map_err(|_| {
            format!("{LOSS_SALT_ENV} takes a whole number: 0 for the world's own link loss, 1 or more for another realization of it (got {v:?})")
        })
    })
}

/// The realization of the link loss this process runs in, read from [`LOSS_SALT_ENV`] on the first call and kept (the
/// streams are derived by the thousand, so the environment is not read for each).
///
/// # Panics
///
/// When the variable holds a value that does not parse, with the message of [`parse_loss_salt`]: the run stops
/// rather than measure a realization nobody asked for.
#[allow(clippy::panic)] // a test-suite switch fails loudly on a bad value, `derive` has no error channel
pub fn loss_salt() -> u64 {
    static SALT: OnceLock<u64> = OnceLock::new();
    *SALT.get_or_init(|| {
        let v = std::env::var_os(LOSS_SALT_ENV).map(|v| v.to_string_lossy().into_owned());
        parse_loss_salt(v.as_deref()).unwrap_or_else(|m| panic!("{m}"))
    })
}

/// The random source of the reference harness: `CPython`'s generator seeded the way the harness seeds each stream.
#[derive(Clone, Debug)]
pub struct RefRng(PyRandom);

impl RefRng {
    /// `random.Random(seed)`, as the harness seeds its scenario generator.
    pub fn python(seed: u64) -> Self {
        Self(PyRandom::from_seed(u128::from(seed)))
    }

    /// `random.Random(_seed(*parts))`, as the harness seeds a node, an adversary or a link.
    pub fn from_parts(parts: &[Py<'_>]) -> Self {
        Self::python(seed(parts))
    }

    /// A LAN loss stream: the harness's own seeding when `salt` is 0, else another realization of the same process,
    /// the seed becoming `(seed * 1_000_003 + salt * 7919) mod 2^63` (the arithmetic of the reference runner's switch).
    #[allow(clippy::cast_possible_truncation)] // the remainder is below 2^63
    fn lan(parts: &[Py<'_>], salt: u64) -> Self {
        let s = seed(parts);
        if salt == 0 {
            return Self::python(s);
        }
        Self::python(((u128::from(s) * 1_000_003 + u128::from(salt) * 7919) % (1u128 << 63)) as u64)
    }

    /// [`Random::derive`] in the realization `salt` of every LAN's loss process: 0 is the world's own, and for 1 or
    /// more each LAN stream is another deterministic one. The streams that are not a LAN's are the same for every
    /// `salt`. `derive` itself takes `salt` from [`loss_salt`].
    pub fn derive_salted(run_seed: u64, stream: Stream, salt: u64) -> Self {
        let s = Py::Int(i128::from(run_seed));
        match stream {
            Stream::LanUp(i) => Self::lan(&[s, Py::Str("ge-up"), Py::Int(i128::from(i))], salt),
            Stream::LanDown(i) => Self::lan(&[s, Py::Str("ge-down"), Py::Int(i128::from(i))], salt),
            Stream::Nat(i) => Self::from_parts(&[s, Py::Str("nat"), Py::Int(i128::from(i))]),
            Stream::Link { from, to } => {
                Self::from_parts(&[s, Py::Str("link"), Py::Int(i128::from(from)), Py::Int(i128::from(to))])
            }
            Stream::Flood(i) => Self::from_parts(&[s, Py::Str("flood"), Py::Int(i128::from(i))]),
            Stream::Adversary => Self::from_parts(&[s, Py::Str("adversary")]),
        }
    }

    /// The generator, for the calls beyond the [`Random`] trait (`choice`, `shuffle`, `sample`, `uniform`, ...).
    pub fn py(&mut self) -> &mut PyRandom {
        &mut self.0
    }
}

impl Random for RefRng {
    /// Streams the reference harness has are seeded as it seeds them: `("ge-up", site)`, `("ge-down", site)` and
    /// `("nat", nat)` after the run seed. The two that it does not have get `("link", from, to)` and
    /// `("flood", index)`; the inbound adversary is seeded `("adversary")` after the run seed, as the harness seeds it.
    fn derive(run_seed: u64, stream: Stream) -> Self {
        Self::derive_salted(run_seed, stream, loss_salt())
    }

    fn random(&mut self) -> f64 {
        self.0.random()
    }

    fn below(&mut self, n: u64) -> u64 {
        self.0.randbelow(n)
    }

    /// One `getrandbits(8)` per byte, as the harness builds its garbage datagrams.
    fn fill(&mut self, buf: &mut [u8]) {
        for b in buf {
            *b = (self.0.next_u32() >> 24) as u8;
        }
    }
}
