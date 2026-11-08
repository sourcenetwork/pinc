//! Encoded sizes of the DAG-CBOR pieces that blocks and CAR headers are made of.
//!
//! Invariants: each function returns exactly the byte count the canonical [`vinc_wire::cbor::Encoder`] writes for the
//! same piece, so a caller can size its buffer before encoding and check the result afterwards.

/// The size of a header (initial byte plus argument) for `arg`.
pub(crate) const fn head_len(arg: u64) -> usize {
    match arg {
        0..=23 => 1,
        24..=0xff => 2,
        0x100..=0xffff => 3,
        0x1_0000..=0xffff_ffff => 5,
        _ => 9,
    }
}

/// The size of a text string of `n` bytes.
pub(crate) const fn text_len(n: usize) -> usize {
    head_len(n as u64).saturating_add(n)
}

/// The size of a CID of `n` bytes as tag 42 over a byte string of `0x00` and the CID.
pub(crate) const fn cid_len(n: usize) -> usize {
    // Tag 42 is two bytes (0xd8 0x2a); the byte string holds the zero prefix and the CID.
    2usize
        .saturating_add(head_len(n as u64 + 1))
        .saturating_add(1)
        .saturating_add(n)
}
