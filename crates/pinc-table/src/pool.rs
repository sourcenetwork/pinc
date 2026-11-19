//! The slot pool: one fixed-size slot per message a limit allows. A free stack of slot numbers hands slots out; a
//! [`Slot`] handle carries a generation, so a handle that was given back (or given back and taken by another) reads
//! and writes nothing and is refused a second give-back.
//! The generation is 32 bits and goes up by 2 each time the slot is taken and given back, so it wraps after 2^31
//! takes of one slot, and a handle kept that long could match again: with one message in flight the free stack hands
//! out the same slot every time, which at 100,000 takes a second is about 6 hours (calculated, not measured). Each
//! slot keeps the length written to it since it was taken: `take` sets it to 0 and writes no byte, `write` raises
//! it, and `read` returns the written prefix only, so a new owner never sees the last one's bytes and a slot's
//! memory is touched only where it is written. A pool and its handles carry a zero-sized kind `K` the holder
//! chooses: a handle of a pool of another kind does not compile.
//! A handle of another pool of the same kind is not detected, so a holder with two pools gives each its own kind.
//! Invariants: a slot is on the free stack exactly when its generation is even; the stack holds `free` slots; the
//! taken slots are `capacity - free`; a slot's written length is at most the slot size.

use core::fmt;
use core::marker::PhantomData;

use crate::error::Error;
use crate::storage::{Storage, fit, rd32, rec, rec_mut, wr32};

/// The bytes a slot costs beside its own: its place on the free stack, its generation and its written length.
const OVERHEAD: usize = 12;

/// A taken slot: its number and the generation it was taken in, of a pool of kind `K`. Plain data; it carries no
/// borrow, and nothing is asked of `K`.
pub struct Slot<K = ()> {
    index: u32,
    generation: u32,
    kind: PhantomData<fn() -> K>,
}

impl<K> Slot<K> {
    /// The slot's number, below the pool's capacity.
    pub fn index(self) -> usize {
        self.index as usize
    }

    /// The handle as 8 bytes (the number, then the generation, little-endian), for a table that keeps handles in
    /// bytes. The kind is the type's, not stored.
    pub fn to_bytes(self) -> [u8; 8] {
        let mut out = [0; 8];
        let (i, g) = out.split_at_mut(4);
        i.copy_from_slice(&self.index.to_le_bytes());
        g.copy_from_slice(&self.generation.to_le_bytes());
        out
    }

    /// The handle `bytes` hold. Bytes no `take` produced give a handle the pool refuses: it reads `None` and is
    /// `Stale` on `write` and `give`.
    /// The bytes are for use inside one process and one run: they name no pool, kind or run, and every pool's
    /// generations start again at 0, so a layer that stores or sends them adds its own run counter.
    pub fn from_bytes(bytes: [u8; 8]) -> Self {
        let (i, g) = bytes.split_at(4);
        Self {
            index: u32::from_le_bytes(<[u8; 4]>::try_from(i).unwrap_or_default()),
            generation: u32::from_le_bytes(<[u8; 4]>::try_from(g).unwrap_or_default()),
            kind: PhantomData,
        }
    }
}

// By hand, so none of these asks anything of `K`.
impl<K> Clone for Slot<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for Slot<K> {}

impl<K> PartialEq for Slot<K> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.generation == other.generation
    }
}

impl<K> Eq for Slot<K> {}

impl<K> fmt::Debug for Slot<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Slot")
            .field("index", &self.index)
            .field("generation", &self.generation)
            .finish()
    }
}

/// A pool of fixed-size slots of kind `K`. See the module comment.
///
/// A handle of a pool of another kind is refused by the compiler:
///
/// ```compile_fail
/// use pinc_table::{Pool, Storage};
/// struct A;
/// struct B;
/// fn f(ma: &'static mut [u8], mb: &'static mut [u8]) {
///     let mut a = Pool::<A>::new(Storage::from_static(ma), 2, 4).unwrap();
///     let mut b = Pool::<B>::new(Storage::from_static(mb), 2, 4).unwrap();
///     let sb = b.take().unwrap();
///     let _ = a.give(sb);
/// }
/// ```
///
/// The same code with one kind compiles, and its handles are the holder's to keep apart:
///
/// ```
/// use pinc_table::{Pool, Storage};
/// struct A;
/// fn f(ma: &'static mut [u8], mb: &'static mut [u8]) {
///     let mut a = Pool::<A>::new(Storage::from_static(ma), 2, 4).unwrap();
///     let mut b = Pool::<A>::new(Storage::from_static(mb), 2, 4).unwrap();
///     let sb = b.take().unwrap();
///     let _ = a.give(sb);
/// }
/// # fn main() {}
/// ```
pub struct Pool<K = ()> {
    mem: Storage,
    slots: usize,
    size: usize,
    free: usize,
    kind: PhantomData<fn() -> K>,
}

impl<K> fmt::Debug for Pool<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pool")
            .field("mem", &self.mem)
            .field("slots", &self.slots)
            .field("size", &self.size)
            .field("free", &self.free)
            .finish()
    }
}

impl<K> Pool<K> {
    /// The bytes of block a pool of `slots` slots of `slot_size` bytes needs: 12 bytes a slot (its place on the
    /// free stack, its generation and its written length) plus the slot. Saturates at `usize::MAX`.
    pub const fn bytes(slots: usize, slot_size: usize) -> usize {
        slots.saturating_mul(slot_size.saturating_add(OVERHEAD))
    }

    /// Makes a pool with every slot free over `mem`. Refuses a block smaller than [`Self::bytes`], more slots than
    /// a slot number holds, and a slot of more than `u32::MAX` bytes.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn new(mut mem: Storage, slots: usize, slot_size: usize) -> Result<Self, Error> {
        // The written length is a u32, so a slot is at most u32::MAX bytes.
        if u32::try_from(slots).is_err() || u32::try_from(slot_size).is_err() {
            return Err(Error::Capacity);
        }
        fit(&mem, Self::bytes(slots, slot_size))?;
        let b = mem.as_mut_slice();
        for i in 0..slots {
            // The stack pops from the top, so slot 0 is handed out first.
            wr32(b, i, u32::try_from(slots - 1 - i).unwrap_or(0));
            wr32(b, slots + i, 0);
            wr32(b, 2 * slots + i, 0);
        }
        Ok(Self {
            mem,
            slots,
            size: slot_size,
            free: slots,
            kind: PhantomData,
        })
    }

    /// The slots the pool has.
    pub fn capacity(&self) -> usize {
        self.slots
    }

    /// The slots free to take.
    pub fn free(&self) -> usize {
        self.free
    }

    /// The slots taken.
    pub fn taken(&self) -> usize {
        self.slots - self.free
    }

    /// The bytes of one slot.
    pub fn slot_size(&self) -> usize {
        self.size
    }

    fn gen_of(&self, i: usize) -> u32 {
        rd32(self.mem.as_slice(), self.slots + i)
    }

    fn written(&self, i: usize) -> usize {
        rd32(self.mem.as_slice(), 2 * self.slots + i) as usize
    }

    fn data(&self) -> &[u8] {
        self.mem.as_slice().get(self.slots * OVERHEAD..).unwrap_or(&[])
    }

    fn live(&self, s: Slot<K>) -> bool {
        s.generation & 1 == 1 && s.index() < self.slots && self.gen_of(s.index()) == s.generation
    }

    /// Takes a free slot with nothing written to it. `None` when every slot is taken.
    pub fn take(&mut self) -> Option<Slot<K>> {
        // Everything that can refuse is above the first write, so a refusal leaves the pool unchanged.
        let top = self.free.checked_sub(1)?;
        let b = self.mem.as_mut_slice();
        let index = rd32(b, top);
        let i = index as usize;
        // vertexia: the generation wraps after 2^31 takes of one slot and a handle held that long could match
        // again; a u64 generation (a 12-byte handle) if a handle can outlive 2^31 reuses of its slot
        let generation = rd32(b, self.slots + i).wrapping_add(1);
        wr32(b, self.slots + i, generation);
        wr32(b, 2 * self.slots + i, 0);
        self.free = top;
        Some(Slot {
            index,
            generation,
            kind: PhantomData,
        })
    }

    /// Gives a slot back. Refuses a slot already given back, or one given back and taken again since. An old handle
    /// is refused until its slot has been taken 2^31 times since.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn give(&mut self, slot: Slot<K>) -> Result<(), Error> {
        if !self.live(slot) {
            return Err(Error::Stale);
        }
        let b = self.mem.as_mut_slice();
        wr32(b, self.slots + slot.index(), slot.generation.wrapping_add(1));
        wr32(b, self.free, slot.index);
        self.free += 1;
        Ok(())
    }

    /// The bytes written to the slot since it was taken (the written prefix), or `None` for a slot not taken.
    pub fn read(&self, slot: Slot<K>) -> Option<&[u8]> {
        if !self.live(slot) {
            return None;
        }
        rec(self.data(), slot.index(), self.size).get(..self.written(slot.index()))
    }

    /// Writes `data` at the start of the slot and raises the written length to cover it; bytes already written
    /// past `data` stay.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn write(&mut self, slot: Slot<K>, data: &[u8]) -> Result<(), Error> {
        if !self.live(slot) {
            return Err(Error::Stale);
        }
        if data.len() > self.size {
            return Err(Error::Length);
        }
        let (at, size, written) = (self.slots * OVERHEAD, self.size, self.written(slot.index()));
        let b = self.mem.as_mut_slice();
        let r = rec_mut(b.get_mut(at..).ok_or(Error::Position)?, slot.index(), size).ok_or(Error::Position)?;
        r.get_mut(..data.len()).ok_or(Error::Length)?.copy_from_slice(data);
        // The length is at most the slot size, which `new` checked fits a u32.
        let raised = u32::try_from(written.max(data.len())).unwrap_or(u32::MAX);
        wr32(b, 2 * self.slots + slot.index(), raised);
        Ok(())
    }
}

/// Views of the pool's block, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
impl<K> Pool<K> {
    /// The slot number in entry `k` of the free stack (entry 0 at the bottom), for `k` below [`Self::free`].
    #[must_use]
    pub fn trace_stack(&self, k: usize) -> Option<usize> {
        (k < self.free).then(|| rd32(self.mem.as_slice(), k) as usize)
    }

    /// The generation of slot `i`, for `i` below the capacity.
    #[must_use]
    pub fn trace_generation(&self, i: usize) -> Option<u32> {
        (i < self.slots).then(|| self.gen_of(i))
    }

    /// The written length of slot `i`, for `i` below the capacity.
    #[must_use]
    pub fn trace_written(&self, i: usize) -> Option<usize> {
        (i < self.slots).then(|| self.written(i))
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn a_generation_at_the_top_of_its_range_wraps_to_free_and_stays_refused() {
        let mut p: Pool = Pool::new(Storage::zeroed(Pool::<()>::bytes(1, 4)).unwrap(), 1, 4).unwrap();
        wr32(p.mem.as_mut_slice(), p.slots, u32::MAX - 1);
        let a = p.take().unwrap();
        assert_eq!(p.give(a), Ok(()));
        assert_eq!(p.give(a), Err(Error::Stale), "a second give-back of the wrapped slot");
        let b = p.take().unwrap();
        assert_eq!(p.read(a), None);
        assert_eq!(p.read(b), Some(&[][..]));
    }
}
