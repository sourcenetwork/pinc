//! A bit-exact port of CPython's `random.Random`: MT19937 with `init_by_array` seeding, the 53-bit `random()`,
//! `getrandbits`, `_randbelow` by rejection sampling, and the methods built on them.
//!
//! Invariant: for the same seed every method returns exactly what the CPython method of the same name returns, and
//! consumes the same 32-bit words, so a mixed sequence of calls stays in step with CPython. The float methods use
//! the platform logarithm like `math.log` does; the tests compare them bit for bit.

use std::collections::BTreeSet;

const N: usize = 624;
const M: usize = 397;

/// CPython's Mersenne Twister generator and the `random.Random` methods the reference harness calls.
#[derive(Clone, Debug)]
pub struct PyRandom {
    mt: [u32; N],
    idx: usize,
}

impl PyRandom {
    /// `random.Random(seed)` for a non-negative integer seed.
    pub fn from_seed(seed: u128) -> Self {
        let mut key = [0u32; 4];
        for (i, w) in key.iter_mut().enumerate() {
            *w = (seed >> (32 * i)) as u32;
        }
        let used = key.iter().rposition(|w| *w != 0).map_or(1, |p| p + 1);
        Self::from_words(&key[..used])
    }

    /// `random.Random(seed)` for a seed given as 32-bit words, least significant first (the key of
    /// `init_by_array`). An empty key is the key `[0]`, which is also what the seed 0 gives.
    pub fn from_words(key: &[u32]) -> Self {
        let key: &[u32] = if key.is_empty() { &[0] } else { key };
        let mut mt = [0u32; N];
        mt[0] = 19_650_218;
        for i in 1..N {
            mt[i] = 1_812_433_253u32
                .wrapping_mul(mt[i - 1] ^ (mt[i - 1] >> 30))
                .wrapping_add(i as u32);
        }
        let (mut i, mut j) = (1usize, 0usize);
        for _ in 0..N.max(key.len()) {
            mt[i] = (mt[i] ^ (mt[i - 1] ^ (mt[i - 1] >> 30)).wrapping_mul(1_664_525))
                .wrapping_add(key[j])
                .wrapping_add(j as u32);
            i += 1;
            j += 1;
            if i >= N {
                mt[0] = mt[N - 1];
                i = 1;
            }
            if j >= key.len() {
                j = 0;
            }
        }
        for _ in 0..N - 1 {
            mt[i] = (mt[i] ^ (mt[i - 1] ^ (mt[i - 1] >> 30)).wrapping_mul(1_566_083_941)).wrapping_sub(i as u32);
            i += 1;
            if i >= N {
                mt[0] = mt[N - 1];
                i = 1;
            }
        }
        mt[0] = 0x8000_0000;
        Self { mt, idx: N }
    }

    fn refill(&mut self) {
        let twist = |u: u32, v: u32| {
            let y = (u & 0x8000_0000) | (v & 0x7fff_ffff);
            (y >> 1) ^ if v & 1 == 1 { 0x9908_b0df } else { 0 }
        };
        for k in 0..N - M {
            self.mt[k] = self.mt[k + M] ^ twist(self.mt[k], self.mt[k + 1]);
        }
        for k in N - M..N - 1 {
            self.mt[k] = self.mt[k + M - N] ^ twist(self.mt[k], self.mt[k + 1]);
        }
        self.mt[N - 1] = self.mt[M - 1] ^ twist(self.mt[N - 1], self.mt[0]);
        self.idx = 0;
    }

    /// The next 32 random bits (`genrand_uint32`).
    pub fn next_u32(&mut self) -> u32 {
        if self.idx >= N {
            self.refill();
        }
        let mut y = self.mt[self.idx];
        self.idx += 1;
        y ^= y >> 11;
        y ^= (y << 7) & 0x9d2c_5680;
        y ^= (y << 15) & 0xefc6_0000;
        y ^ (y >> 18)
    }

    /// `random()`: a float in `[0, 1)` from 53 random bits (`genrand_res53`).
    pub fn random(&mut self) -> f64 {
        let a = f64::from(self.next_u32() >> 5);
        let b = f64::from(self.next_u32() >> 6);
        (a * 67_108_864.0 + b) * (1.0 / 9_007_199_254_740_992.0)
    }

    /// `getrandbits(k)` for `k` up to 128; a larger `k` is clamped to 128. Word 0 is the least significant.
    pub fn getrandbits(&mut self, k: u32) -> u128 {
        let mut k = k.min(128);
        if k <= 32 {
            return if k == 0 {
                0
            } else {
                u128::from(self.next_u32() >> (32 - k))
            };
        }
        let mut v = 0u128;
        let mut shift = 0;
        while k > 0 {
            let mut r = self.next_u32();
            if k < 32 {
                r >>= 32 - k;
            }
            v |= u128::from(r) << shift;
            shift += 32;
            k = k.saturating_sub(32);
        }
        v
    }

    /// `getrandbits(8 * n).to_bytes(n, "little")`: `n` random bytes taken word by word.
    pub fn getrandbytes(&mut self, n: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(n + 4);
        let mut left = n;
        while left > 0 {
            let w = self.next_u32();
            let take = left.min(4);
            let shifted = if take < 4 { w >> (32 - 8 * take) } else { w };
            out.extend_from_slice(&shifted.to_le_bytes()[..take]);
            left -= take;
        }
        out
    }

    /// `_randbelow(n)` (and `randrange(n)`): a uniform integer in `[0, n)` by rejection sampling on
    /// `getrandbits(n.bit_length())`. Returns 0 without drawing when `n` is 0 (CPython raises there).
    pub fn randbelow(&mut self, n: u64) -> u64 {
        if n == 0 {
            return 0;
        }
        let k = 64 - n.leading_zeros();
        loop {
            let r = self.getrandbits(k) as u64;
            if r < n {
                return r;
            }
        }
    }

    /// `randrange(start, stop)` with step 1; `start` when the range is empty (CPython raises there).
    pub fn randrange(&mut self, start: i64, stop: i64) -> i64 {
        let width = i128::from(stop) - i128::from(start);
        if width <= 0 {
            return start;
        }
        (i128::from(start) + i128::from(self.randbelow(width as u64))) as i64
    }

    /// `randint(a, b)`: a uniform integer in `[a, b]`; `a` when `b < a` (CPython raises there).
    pub fn randint(&mut self, a: i64, b: i64) -> i64 {
        self.randrange(a, b.saturating_add(1))
    }

    /// `choice(seq)` as an index: a uniform index below `len`, or `None` for an empty sequence.
    pub fn choice_index(&mut self, len: usize) -> Option<usize> {
        (len > 0).then(|| self.randbelow(len as u64) as usize)
    }

    /// `shuffle(x)`: the Fisher-Yates shuffle CPython uses, from the back.
    pub fn shuffle<T>(&mut self, x: &mut [T]) {
        for i in (1..x.len()).rev() {
            let j = self.randbelow(i as u64 + 1) as usize;
            x.swap(i, j);
        }
    }

    /// `sample(range(n), k)`: `k` distinct indices below `n` in selection order, or `None` when `k > n`. Uses the
    /// pool method for small populations and a selected-set method otherwise, exactly as CPython chooses.
    pub fn sample_indices(&mut self, n: usize, k: usize) -> Option<Vec<usize>> {
        if k > n {
            return None;
        }
        let mut setsize = 21usize;
        if k > 5 {
            let exp = ((k * 3) as f64).ln() / 4f64.ln();
            setsize = setsize.saturating_add(4usize.saturating_pow(exp.ceil() as u32));
        }
        let mut result = Vec::with_capacity(k);
        if n <= setsize {
            let mut pool: Vec<usize> = (0..n).collect();
            for i in 0..k {
                let j = self.randbelow((n - i) as u64) as usize;
                result.push(pool[j]);
                pool[j] = pool[n - i - 1];
            }
        } else {
            let mut selected = BTreeSet::new();
            for _ in 0..k {
                let mut j = self.randbelow(n as u64) as usize;
                while selected.contains(&j) {
                    j = self.randbelow(n as u64) as usize;
                }
                selected.insert(j);
                result.push(j);
            }
        }
        Some(result)
    }

    /// `uniform(a, b)`: `a + (b - a) * random()`.
    pub fn uniform(&mut self, a: f64, b: f64) -> f64 {
        a + (b - a) * self.random()
    }

    /// `expovariate(lambd)`: `-log(1.0 - random()) / lambd`.
    pub fn expovariate(&mut self, lambd: f64) -> f64 {
        -(1.0 - self.random()).ln() / lambd
    }
}
