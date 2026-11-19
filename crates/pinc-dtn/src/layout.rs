//! The geometry of a bundle: how a payload becomes numbered symbols in erasure blocks.
//!
//! A payload is cut into data slices of `slice_len - 16` bytes (the last one zero-padded); each is sealed into a
//! symbol of exactly `slice_len = 1024 << slice_log` bytes. Data symbols are grouped `k` to a block (the last block
//! may hold fewer) and each block gets `m` parity symbols, so block `b` occupies symbols `b * (k + m)` onward: its
//! data first, its parity last. One symbol is one tree group, so a symbol is exactly the unit a range proof releases.
//!
//! Invariants: the layout is a pure function of `(k, m, slice_log, payload_len)`; every count uses checked
//! arithmetic and a layout whose symbol count or byte length does not fit `u64` is refused with
//! [`DtnError::Params`]; `k >= 1`, `k + m <= 255`, `slice_log <= 4`, `payload_len >= 1`.

use core::ops::Range;

use pinc_dag::tree::{CHUNK_LEN, Layout};

use crate::error::DtnError;
use crate::rs::MAX_SYMBOLS;

/// The largest supported slice size log: slices of 16 KiB.
pub const MAX_SLICE_LOG: u8 = 4;
/// The AEAD tag appended to every sealed slice.
pub const TAG_LEN: usize = 16;

/// Where one symbol sits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    /// The erasure block.
    pub block: u64,
    /// The index inside the block, data first.
    pub index: usize,
    /// The number of data symbols in this block.
    pub block_k: usize,
}

impl Position {
    /// Whether the symbol is parity.
    pub const fn is_parity(&self) -> bool {
        self.index >= self.block_k
    }
}

/// The validated geometry of a bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SliceLayout {
    k: u8,
    m: u8,
    log: u8,
    payload_len: u64,
}

impl SliceLayout {
    /// The layout of `payload_len` bytes cut into `1024 << slice_log` byte symbols, `k` data and `m` parity per block.
    ///
    /// # Errors
    /// [`DtnError::Params`] for `k == 0`, `k + m > 255`, `slice_log > 4`, an empty payload, or a payload whose sealed
    /// size does not fit in `u64`.
    pub fn new(k: u8, m: u8, slice_log: u8, payload_len: u64) -> Result<Self, DtnError> {
        let valid = k >= 1 && usize::from(k) + usize::from(m) <= MAX_SYMBOLS && slice_log <= MAX_SLICE_LOG;
        let this = Self {
            k,
            m,
            log: slice_log,
            payload_len,
        };
        if !valid || payload_len == 0 || this.try_total_len().is_none() {
            return Err(DtnError::Params);
        }
        Ok(this)
    }

    fn try_total_len(&self) -> Option<u64> {
        let data = self.payload_len.div_ceil(self.plain_len());
        let parity = data.div_ceil(u64::from(self.k)).checked_mul(u64::from(self.m))?;
        data.checked_add(parity)?.checked_mul(self.slice_len())
    }

    /// Data symbols per full block.
    pub const fn k(&self) -> u8 {
        self.k
    }

    /// Parity symbols per block.
    pub const fn m(&self) -> u8 {
        self.m
    }

    /// The slice size log.
    pub const fn slice_log(&self) -> u8 {
        self.log
    }

    /// The payload length in bytes.
    pub const fn payload_len(&self) -> u64 {
        self.payload_len
    }

    /// The bytes of one symbol: plaintext, then the tag.
    pub const fn slice_len(&self) -> u64 {
        CHUNK_LEN << self.log
    }

    /// The plaintext bytes of one data slice.
    pub const fn plain_len(&self) -> u64 {
        self.slice_len() - TAG_LEN as u64
    }

    /// The number of data symbols.
    pub const fn data_symbols(&self) -> u64 {
        self.payload_len.div_ceil(self.plain_len())
    }

    /// The size a plaintext output buffer needs: every data slice in full, padding included.
    pub const fn padded_len(&self) -> u64 {
        self.data_symbols() * self.plain_len()
    }

    /// The number of erasure blocks.
    pub const fn blocks(&self) -> u64 {
        self.data_symbols().div_ceil(self.k as u64)
    }

    /// The number of data symbols in block `b` (`k` except possibly in the last block); 0 past the last block.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the value is below k, which is at most 255"
    )]
    pub const fn block_k(&self, b: u64) -> usize {
        let d = self.data_symbols();
        let first = b.saturating_mul(self.k as u64);
        if first >= d {
            0
        } else if d - first < self.k as u64 {
            (d - first) as usize
        } else {
            self.k as usize
        }
    }

    /// The number of symbols in block `b`.
    pub const fn block_n(&self, b: u64) -> usize {
        match self.block_k(b) {
            0 => 0,
            k => k + self.m as usize,
        }
    }

    /// The index of the first symbol of block `b`.
    pub const fn block_start(&self, b: u64) -> u64 {
        b.saturating_mul(self.k as u64 + self.m as u64)
    }

    /// The number of symbols in the whole bundle.
    pub const fn total_symbols(&self) -> u64 {
        self.data_symbols() + self.blocks() * self.m as u64
    }

    /// The length of the sealed bundle in bytes: what the tree commits to.
    pub const fn total_len(&self) -> u64 {
        self.total_symbols() * self.slice_len()
    }

    /// The size of the tree outboard of the sealed bundle.
    ///
    /// # Errors
    /// [`DtnError::Tree`] if the tree cannot be laid out.
    pub fn outboard_len(&self) -> Result<u64, DtnError> {
        Ok(Layout::new(self.total_len(), u32::from(self.log))?.outboard_size())
    }

    /// Where symbol `s` sits, or `None` past the last symbol.
    pub fn locate(&self, s: u64) -> Option<Position> {
        let per_block = u64::from(self.k) + u64::from(self.m);
        let block = s / per_block;
        let index = usize::try_from(s % per_block).ok()?;
        let block_k = self.block_k(block);
        (block_k > 0 && index < block_k + usize::from(self.m)).then_some(Position { block, index, block_k })
    }

    /// The position of data slice `d` (counting data slices only) as a symbol index.
    pub fn data_symbol(&self, d: u64) -> Option<u64> {
        (d < self.data_symbols()).then(|| self.block_start(d / u64::from(self.k)) + d % u64::from(self.k))
    }

    /// The byte range of symbols `symbols` (end exclusive) in the sealed bundle.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] if the range is reversed or ends past the last symbol.
    pub fn byte_range(&self, symbols: &Range<u64>) -> Result<Range<u64>, DtnError> {
        if symbols.start > symbols.end || symbols.end > self.total_symbols() {
            return Err(DtnError::Buffer);
        }
        Ok(symbols.start * self.slice_len()..symbols.end * self.slice_len())
    }
}
