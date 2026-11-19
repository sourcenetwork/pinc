//! The request rule of a receiving transfer, for trace validation (cargo feature `trace`).

use alloc::vec::Vec;

use pinc_dtn::layout::SliceLayout;

use crate::dtn::{CHUNK_BYTES, Dtn, Want, no_symbols};

/// What `Dtn::want` answered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answer {
    /// Ask for the symbols `first..end`.
    Ask(u64, u64),
    /// Every block holds enough symbols.
    Decodable,
    /// A block cannot reach `k` symbols from this holder.
    Stuck,
}

/// The layout of a bundle and what `Dtn::want` answered for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Probe {
    /// The blocks of the bundle.
    pub blocks: u64,
    /// `(block_k, block_n)` of each block.
    pub shape: Vec<(usize, usize)>,
    /// The longest run one ask takes.
    pub max: u64,
    /// The answer.
    pub answer: Answer,
}

/// `Dtn::want` for a bundle of `k`, `m`, `slice_log` and `payload_len`, holding `held`, with `lost` lost from this
/// holder and the receiver's cursor at `cursor`. `None` for a layout `SliceLayout::new` refuses or a symbol `held`
/// names outside the bundle.
#[must_use]
pub fn want(k: u8, m: u8, slice_log: u8, payload_len: u64, cursor: u64, held: &[u64], lost: &[u64]) -> Option<Probe> {
    let layout = SliceLayout::new(k, m, slice_log, payload_len).ok()?;
    let mut have = no_symbols(&layout)?;
    for s in held {
        if !have.insert_symbol(*s) {
            return None;
        }
    }
    let (mut cursor, mut lost) = (cursor, lost.to_vec());
    let answer = match Dtn::want_held(&layout, &have, &mut cursor, &mut lost) {
        Want::Ask(a, e) => Answer::Ask(a, e),
        Want::Decodable => Answer::Decodable,
        Want::Stuck => Answer::Stuck,
    };
    Some(Probe {
        blocks: layout.blocks(),
        shape: (0..layout.blocks())
            .map(|b| (layout.block_k(b), layout.block_n(b)))
            .collect(),
        max: (CHUNK_BYTES / layout.slice_len()).max(1),
        answer,
    })
}
