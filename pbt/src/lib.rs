//! Helpers shared by the PINC property tests (`tests/*.rs`, one file per area under test).
//!
//! Every property runs through ephyra's runner, so a failure shrinks, prints an `EPHYRA_REPLAY=<seed>:<iteration>`
//! line and replays exactly. Generators build valid inputs from the types; byte-level mutation is added on top only
//! where the code under test parses untrusted bytes.

use ephyra::{Gen, GenExt, Source, gens};

/// Bytes of a length in `0..=max`, each byte uniform. Shrinks toward shorter and smaller.
pub fn bytes(max: usize) -> impl Gen<Value = Vec<u8>> + Clone {
    gens::vec(gens::int(0u8..=255)).len(0..=max)
}

/// One edit of an encoding, for decoders of untrusted bytes: what a hostile or broken peer could send in place of
/// `valid`. The edits are the ones that reach past a decoder's first length check: a flipped bit, a replaced byte, a
/// cut, a doubled run, an inserted byte, and a length-like byte pushed to an extreme.
pub fn mangle(g: &mut Source, valid: &[u8]) -> Vec<u8> {
    let mut out = valid.to_vec();
    if out.is_empty() {
        return g.draw(&bytes(8));
    }
    let at = g.index(out.len());
    match g.int(0u8..=6) {
        0 => {
            if let Some(b) = out.get_mut(at) {
                *b ^= 1 << g.int(0u8..=7);
            }
        },
        1 => {
            if let Some(b) = out.get_mut(at) {
                *b = g.int(0u8..=255);
            }
        },
        2 => out.truncate(at),
        3 => {
            let end = (at + g.int(1usize..=8)).min(out.len());
            let run: Vec<u8> = out.get(at..end).map(<[u8]>::to_vec).unwrap_or_default();
            out.splice(at..at, run);
        },
        4 => out.insert(at, g.int(0u8..=255)),
        5 => {
            if let Some(b) = out.get_mut(at) {
                *b = *g.pick(&[0x00, 0x01, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x3f, 0x40, 0x7f, 0x80, 0xbf, 0xc0, 0xfe, 0xff]);
            }
        },
        _ => out.extend(g.draw(&bytes(8))),
    }
    out
}

/// A generator of encodings that are valid most of the time and mangled once or a few times otherwise: `encode`
/// draws one valid encoding. The valid share keeps the decoder's deep paths reached; the mangled share is the oracle
/// for "no input makes the decoder panic".
pub fn mostly_valid<F>(encode: F) -> ephyra::BoxGen<Vec<u8>>
where
    F: Fn(&mut Source) -> Vec<u8> + Send + Sync + Clone + 'static,
{
    (move |g: &mut Source| {
        let mut out = encode(g);
        if g.bool_with(0.6) {
            for _ in 0..g.int(1u8..=3) {
                out = mangle(g, &out);
            }
        }
        out
    })
    .with_shrink(shrink_bytes)
    .boxed()
}

/// Shrinks a byte string: drop the tail half, drop one byte, zero one byte.
#[allow(clippy::ptr_arg)]
pub fn shrink_bytes(
    v: &Vec<u8>,
    visit: &mut dyn FnMut(Vec<u8>) -> std::ops::ControlFlow<()>,
) -> std::ops::ControlFlow<()> {
    if v.len() > 1 {
        visit(v.get(..v.len() / 2).map(<[u8]>::to_vec).unwrap_or_default())?;
    }
    for i in 0..v.len() {
        let mut shorter = v.clone();
        shorter.remove(i);
        visit(shorter)?;
    }
    for (i, b) in v.iter().enumerate() {
        if *b != 0 {
            let mut zeroed = v.clone();
            if let Some(z) = zeroed.get_mut(i) {
                *z = 0;
            }
            visit(zeroed)?;
        }
    }
    std::ops::ControlFlow::Continue(())
}
