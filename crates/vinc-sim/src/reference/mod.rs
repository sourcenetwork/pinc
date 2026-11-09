//! The reference random source: a bit-exact port of CPython's `random` and of the reference harness's seed
//! derivation, behind the simulator's [`Random`] trait.
//!
//! The harness seeds each component stream with `random.Random(int_from_blake2b(repr((seed, tag, index))))`. This
//! module reproduces the whole chain: [`seed`] hashes the `repr` text of a tuple, [`PyRandom`] is the generator, and
//! [`RefRng`] makes the generator a [`Random`] so that a [`crate::Sim`] draws exactly the numbers the reference
//! harness draws. Needs the `reference` feature (it brings in the BLAKE2b hash).
//!
//! Invariant: every function here is a pure function of its arguments, and the test vectors in
//! `tests/data/reference_rng.txt` were produced by CPython itself.

mod mt;
mod repr;

use blake2::digest::consts::{U8, U16, U32};
use blake2::{Blake2b, Digest};

pub use mt::PyRandom;
pub use repr::Py;

use crate::rng::{Random, Stream};

/// The reference `_seed(*parts)`: the little-endian integer of the 8-byte BLAKE2b of `repr(parts)`, where `parts` is
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

/// The random source of the reference harness: CPython's generator seeded the way the harness seeds each stream.
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

    /// The generator, for the calls beyond the [`Random`] trait (`choice`, `shuffle`, `sample`, `uniform`, ...).
    pub fn py(&mut self) -> &mut PyRandom {
        &mut self.0
    }
}

impl Random for RefRng {
    /// Streams the reference harness has are seeded as it seeds them: `("ge-up", site)`, `("ge-down", site)` and
    /// `("nat", nat)` after the run seed. The two that it does not have get `("link", from, to)` and
    /// `("flood", index)`.
    fn derive(run_seed: u64, stream: Stream) -> Self {
        let s = Py::Int(i128::from(run_seed));
        match stream {
            Stream::LanUp(i) => Self::from_parts(&[s, Py::Str("ge-up"), Py::Int(i128::from(i))]),
            Stream::LanDown(i) => Self::from_parts(&[s, Py::Str("ge-down"), Py::Int(i128::from(i))]),
            Stream::Nat(i) => Self::from_parts(&[s, Py::Str("nat"), Py::Int(i128::from(i))]),
            Stream::Link { from, to } => {
                Self::from_parts(&[s, Py::Str("link"), Py::Int(i128::from(from)), Py::Int(i128::from(to))])
            }
            Stream::Flood(i) => Self::from_parts(&[s, Py::Str("flood"), Py::Int(i128::from(i))]),
        }
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
