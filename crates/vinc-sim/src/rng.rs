//! The simulator's random source: a trait the engine is generic over, and `SplitMix64`, its default implementation.
//!
//! Invariant: a source is a pure function of the run seed and the stream it serves, so a run replays byte for byte.
//! A scenario port that must match another implementation draw for draw implements [`Random`] (including how a
//! stream's seed is derived from the run seed) and passes it as the `R` parameter of [`crate::Sim`].

/// The independent random streams of a run. The engine asks [`Random::derive`] for one source per stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    /// The link between two sites, by site index.
    Link {
        /// Sending site.
        from: u32,
        /// Receiving site.
        to: u32,
    },
    /// The uplink of a LAN.
    LanUp(u32),
    /// The downlink of a LAN.
    LanDown(u32),
    /// A NAT's port allocation.
    Nat(u32),
    /// A flood's payloads.
    Flood(u32),
    /// The inbound adversary's choices (captures, replays, bit flips).
    Adversary,
}

/// A source of random numbers with the operations the engine needs. Implement it to replace [`Rng`].
pub trait Random: Sized {
    /// The source for `stream` of the run seeded with `seed`.
    fn derive(seed: u64, stream: Stream) -> Self;
    /// A uniform float in `[0, 1)`.
    fn random(&mut self) -> f64;
    /// A uniform integer in `[0, n)` (like `randrange(n)`); 0 when `n` is 0.
    fn below(&mut self, n: u64) -> u64;
    /// Fills `buf` with random bytes.
    fn fill(&mut self, buf: &mut [u8]);
    /// True with probability `p`. Draws nothing when `p` is at or below 0, or at or above 1.
    fn chance(&mut self, p: f64) -> bool {
        if p <= 0.0 {
            false
        } else if p >= 1.0 {
            true
        } else {
            self.random() < p
        }
    }
    /// An exponential variate with the given rate (like `expovariate`).
    fn expovariate(&mut self, rate: f64) -> f64 {
        -(1.0 - self.random()).ln() / rate
    }
}

/// A seeded `SplitMix64` generator. Cheap to copy; every stream of the simulator owns one.
#[derive(Clone, Debug)]
pub struct Rng(u64);

const GAMMA: u64 = 0x9E37_79B9_7F4A_7C15;

const fn mix(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

impl Rng {
    /// A generator that starts from `seed`.
    pub const fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// An independent generator derived from `seed` and a stream number (not from the current state).
    pub const fn stream(seed: u64, stream: u64) -> Self {
        Self(mix(seed ^ mix(stream.wrapping_add(GAMMA))))
    }

    /// The next 64 random bits.
    pub const fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(GAMMA);
        mix(self.0)
    }
}

impl Random for Rng {
    fn derive(seed: u64, stream: Stream) -> Self {
        let tag = match stream {
            Stream::Link { from, to } => (u64::from(from) << 32) | u64::from(to),
            Stream::LanUp(i) => 0x1_0000_0000_0000 | u64::from(i),
            Stream::LanDown(i) => 0x2_0000_0000_0000 | u64::from(i),
            Stream::Nat(i) => 0x3_0000_0000_0000 | u64::from(i),
            Stream::Flood(i) => 0x4_0000_0000_0000 | u64::from(i),
            Stream::Adversary => 0x5_0000_0000_0000,
        };
        Self::stream(seed, tag)
    }

    fn random(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / (1u64 << 53) as f64)
    }

    fn below(&mut self, n: u64) -> u64 {
        ((u128::from(self.next_u64()) * u128::from(n)) >> 64) as u64
    }

    fn fill(&mut self, buf: &mut [u8]) {
        for chunk in buf.chunks_mut(8) {
            let bytes = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&bytes[..chunk.len()]);
        }
    }
}
