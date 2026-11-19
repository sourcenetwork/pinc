//! Arithmetic in GF(2^8) with the primitive polynomial `x^8 + x^4 + x^3 + x^2 + 1` (0x11d) and generator 2.
//!
//! Invariants: addition is XOR; the exp, log and full multiplication tables are built at compile time, so there is
//! no start-up cost and no mutable state; `mul(a, b)` is a single table load and `inv(0)` is defined as 0 (never
//! used by the callers, which only invert nonzero field elements). The slice kernels [`mul_add`] and [`scale`] are
//! table-driven, portable, SIMD-free and allocation-free.
#![allow(
    clippy::indexing_slicing,
    reason = "every index is a u8 into a 256-entry table or a loop counter bounded by the table size"
)]

const POLY: u16 = 0x11d;

struct Tables {
    exp: [u8; 512],
    log: [u8; 256],
}

#[allow(
    clippy::cast_possible_truncation,
    reason = "values are reduced below 256 before the cast"
)]
const fn build_tables() -> Tables {
    let mut exp = [0u8; 512];
    let mut log = [0u8; 256];
    let mut x: u16 = 1;
    let mut i = 0;
    while i < 255 {
        exp[i] = x as u8;
        exp[i + 255] = x as u8;
        log[x as usize] = i as u8;
        x <<= 1;
        if x & 0x100 != 0 {
            x ^= POLY;
        }
        i += 1;
    }
    Tables { exp, log }
}

#[allow(clippy::cast_possible_truncation, reason = "a and b are below 256")]
#[allow(clippy::large_stack_arrays, reason = "evaluated at compile time into a static")]
const fn build_mul(t: &Tables) -> [[u8; 256]; 256] {
    let mut mul = [[0u8; 256]; 256];
    let mut a = 1;
    while a < 256 {
        let mut b = 1;
        while b < 256 {
            mul[a][b] = t.exp[t.log[a] as usize + t.log[b] as usize];
            b += 1;
        }
        a += 1;
    }
    mul
}

static TABLES: Tables = build_tables();
static MUL: [[u8; 256]; 256] = build_mul(&TABLES);

/// The product of `a` and `b`.
pub fn mul(a: u8, b: u8) -> u8 {
    MUL[usize::from(a)][usize::from(b)]
}

/// The multiplicative inverse of `a`; 0 for 0.
pub fn inv(a: u8) -> u8 {
    if a == 0 {
        0
    } else {
        TABLES.exp[255 - usize::from(TABLES.log[usize::from(a)])]
    }
}

/// `dst ^= src` for the common length of the two slices.
pub fn xor_into(dst: &mut [u8], src: &[u8]) {
    for (d, s) in dst.iter_mut().zip(src) {
        *d ^= *s;
    }
}

/// `dst ^= c * src` for the common length of the two slices.
pub fn mul_add(dst: &mut [u8], src: &[u8], c: u8) {
    match c {
        0 => {}
        1 => xor_into(dst, src),
        _ => {
            let table = &MUL[usize::from(c)];
            let n = dst.len().min(src.len());
            let (Some(dst), Some(src)) = (dst.get_mut(..n), src.get(..n)) else {
                return;
            };
            let (dw, dr) = dst.as_chunks_mut::<8>();
            let (sw, sr) = src.as_chunks::<8>();
            // Eight lookups per word: one load and one store of `dst` per eight bytes instead of per byte.
            for (d, s) in dw.iter_mut().zip(sw) {
                let looked = s.map(|x| table[usize::from(x)]);
                *d = (u64::from_le_bytes(*d) ^ u64::from_le_bytes(looked)).to_le_bytes();
            }
            for (d, s) in dr.iter_mut().zip(sr) {
                *d ^= table[usize::from(*s)];
            }
        }
    }
}

/// `buf = c * buf`, in place.
pub fn scale(buf: &mut [u8], c: u8) {
    match c {
        1 => {}
        0 => buf.fill(0),
        _ => {
            let table = &MUL[usize::from(c)];
            for b in buf {
                *b = table[usize::from(*b)];
            }
        }
    }
}
