//! The block of bytes a table lives in: a caller's `'static` slice, or with the `alloc` feature one zeroed block the
//! storage makes itself. It is the only owner of the bytes; a table holds one `Storage` and no lifetime or type
//! parameter, so the table types stay plain. Nothing here allocates after the block exists.

use core::fmt;

#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use crate::error::{Error, Refused};

/// One block of bytes, either borrowed for the whole program or owned. Its `Debug` prints the length only, so a
/// table in a log line or a panic message never prints a block.
pub struct Storage(Inner);

enum Inner {
    Static(&'static mut [u8]),
    #[cfg(feature = "alloc")]
    Owned(Box<[u8]>),
}

impl Storage {
    /// A caller's block, for example a `static` array. A table writes its own bookkeeping bytes when it is made, so
    /// the block need not be zeroed.
    pub fn from_static(block: &'static mut [u8]) -> Self {
        Self(Inner::Static(block))
    }

    /// One zeroed block of `len` bytes, allocated once. The crate writes only the bytes a table writes; whether
    /// the untouched pages of a zeroed block stay unbacked is the allocator's and the system's to decide. A failed
    /// allocation ends the process, as any allocation of the standard library does (a fallible zeroed allocation in
    /// safe code would write every byte).
    ///
    /// # Errors
    ///
    /// [`Error::Capacity`] for a `len` above `isize::MAX`, which no allocation can hold.
    #[cfg(feature = "alloc")]
    pub fn zeroed(len: usize) -> Result<Self, Error> {
        if no_block_holds(len) {
            return Err(Error::Capacity);
        }
        Ok(Self(Inner::Owned(alloc::vec![0u8; len].into_boxed_slice())))
    }

    /// The length of the block in bytes.
    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    /// Whether the block has no bytes.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn as_slice(&self) -> &[u8] {
        match &self.0 {
            Inner::Static(b) => b,
            #[cfg(feature = "alloc")]
            Inner::Owned(b) => b,
        }
    }

    pub(crate) fn as_mut_slice(&mut self) -> &mut [u8] {
        match &mut self.0 {
            Inner::Static(b) => b,
            #[cfg(feature = "alloc")]
            Inner::Owned(b) => b,
        }
    }
}

impl fmt::Debug for Storage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Storage").field("len", &self.len()).finish()
    }
}

impl From<&'static mut [u8]> for Storage {
    fn from(block: &'static mut [u8]) -> Self {
        Self::from_static(block)
    }
}

/// Whether no block can be `len` bytes long: a slice holds at most `isize::MAX` bytes.
fn no_block_holds(len: usize) -> bool {
    isize::try_from(len).is_err()
}

/// Checks that `mem` holds `need` bytes and gives it back, or refuses with it. A `need` above `isize::MAX`, a
/// saturated one included, is a capacity no block can satisfy, not a size.
pub(crate) fn fit(mem: Storage, need: usize) -> Result<Storage, Refused> {
    if no_block_holds(need) {
        Err(Refused {
            error: Error::Capacity,
            storage: mem,
        })
    } else if mem.len() < need {
        Err(Refused {
            error: Error::Storage { need },
            storage: mem,
        })
    } else {
        Ok(mem)
    }
}

// The readers below are total: a table checks its block's size when it is made, so an out-of-range read cannot
// happen, and a short slice reads as zero instead of panicking.

pub(crate) fn rd16(b: &[u8], i: usize) -> u16 {
    i.checked_mul(2)
        .and_then(|o| b.get(o..o.checked_add(2)?))
        .and_then(|s| <[u8; 2]>::try_from(s).ok())
        .map_or(0, u16::from_le_bytes)
}

pub(crate) fn wr16(b: &mut [u8], i: usize, v: u16) {
    if let Some(s) = i.checked_mul(2).and_then(|o| b.get_mut(o..o.checked_add(2)?)) {
        s.copy_from_slice(&v.to_le_bytes());
    }
}

pub(crate) fn rd32(b: &[u8], i: usize) -> u32 {
    i.checked_mul(4)
        .and_then(|o| b.get(o..o.checked_add(4)?))
        .and_then(|s| <[u8; 4]>::try_from(s).ok())
        .map_or(0, u32::from_le_bytes)
}

pub(crate) fn wr32(b: &mut [u8], i: usize, v: u32) {
    if let Some(s) = i.checked_mul(4).and_then(|o| b.get_mut(o..o.checked_add(4)?)) {
        s.copy_from_slice(&v.to_le_bytes());
    }
}

/// Entry `i` of an index of `w`-byte entries (2 or 4).
pub(crate) fn rd_w(b: &[u8], i: usize, w: usize) -> usize {
    if w == 2 {
        usize::from(rd16(b, i))
    } else {
        rd32(b, i) as usize
    }
}

pub(crate) fn wr_w(b: &mut [u8], i: usize, w: usize, v: usize) {
    if w == 2 {
        wr16(b, i, u16::try_from(v).unwrap_or(u16::MAX));
    } else {
        wr32(b, i, u32::try_from(v).unwrap_or(u32::MAX));
    }
}

/// The bytes of record `i` of `size` bytes each.
pub(crate) fn rec(b: &[u8], i: usize, size: usize) -> &[u8] {
    i.checked_mul(size)
        .and_then(|o| b.get(o..o.checked_add(size)?))
        .unwrap_or(&[])
}

pub(crate) fn rec_mut(b: &mut [u8], i: usize, size: usize) -> Option<&mut [u8]> {
    let o = i.checked_mul(size)?;
    b.get_mut(o..o.checked_add(size)?)
}
