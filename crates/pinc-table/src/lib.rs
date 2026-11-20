//! Fixed tables over one block of bytes made once. Four shapes: a sorted slab (a keyed table that walks in key
//! order), an array by position, a ring and a slot pool. Each owns a [`Storage`] block, reads and writes its
//! fixed-size records with `from_le_bytes` and `to_le_bytes`, refuses when full, allocates nothing after it is made,
//! hashes nothing and reads neither a clock nor a random source.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod array;
mod error;
mod pool;
mod ring;
mod slab;
mod storage;

pub use array::Array;
pub use error::{Error, Refused};
pub use pool::{Pool, Slot};
pub use ring::Ring;
pub use slab::SortedSlab;
pub use storage::Storage;

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn sizes_are_constants_a_static_block_can_use() {
        const A: usize = SortedSlab::bytes(8, 4, 4);
        const B: usize = Ring::bytes(8, 4);
        const C: usize = Array::bytes(8, 4);
        const D: usize = Pool::<()>::bytes(8, 4);
        assert_eq!((A, B, C, D), (8 * 10, 32, 56, 8 * 16));
        assert_eq!(SortedSlab::bytes(65_535, 4, 0), 65_535 * 6);
        assert_eq!(SortedSlab::bytes(65_536, 4, 0), 65_536 * 8);
        assert_eq!(Ring::bytes(usize::MAX, 2), usize::MAX);
    }

    #[test]
    fn a_static_block_and_an_owned_one_serve_the_same_type() {
        let leaked: &'static mut [u8] = alloc::boxed::Box::leak(alloc::vec![0u8; 8].into_boxed_slice());
        for mem in [Storage::from(leaked), Storage::zeroed(8).unwrap()] {
            assert_eq!(mem.len(), 8);
            let mut r = Ring::new(mem, 2, 4).unwrap();
            r.push(&[1; 4]).unwrap();
            assert_eq!(r.pop(), Some(&[1u8; 4][..]));
        }
    }

    #[test]
    fn a_block_is_refused_past_what_an_allocation_holds_and_no_table_prints_its_bytes() {
        assert_eq!(Storage::zeroed(usize::MAX).unwrap_err(), Error::Capacity);
        assert_eq!(Storage::zeroed(usize::MAX / 2 + 1).unwrap_err(), Error::Capacity);
        let leaked: &'static mut [u8] = alloc::boxed::Box::leak(alloc::vec![0xa5u8; 4].into_boxed_slice());
        let mem = Storage::from(leaked);
        assert_eq!(alloc::format!("{mem:?}"), "Storage { len: 4 }");
        let mut r = Ring::new(mem, 1, 4).unwrap();
        r.push(&[0xa5; 4]).unwrap();
        assert!(!alloc::format!("{r:?}").contains("165"));
        let mut p: Pool = Pool::new(Storage::zeroed(Pool::<()>::bytes(1, 4)).unwrap(), 1, 4).unwrap();
        let s = p.take().unwrap();
        p.write(s, &[0xa5; 4]).unwrap();
        assert!(!alloc::format!("{p:?}").contains("165"));
    }

    #[test]
    fn a_record_size_past_usize_max_is_refused_at_capacity_zero() {
        let new = |k, v| SortedSlab::new(Storage::zeroed(0).unwrap(), 0, k, v);
        assert_eq!(new(usize::MAX, 1).unwrap_err().error, Error::Capacity);
        assert_eq!(new(1, usize::MAX).unwrap_err().error, Error::Capacity);
        assert_eq!(new(usize::MAX, 0).unwrap().retain(|_, _| true), 0);
    }

    #[test]
    fn a_size_past_isize_max_is_a_capacity_as_zeroed_says() {
        let n = usize::MAX / 4 + 1;
        assert_eq!(Ring::bytes(n, 2), usize::MAX / 2 + 1);
        assert_eq!(Storage::zeroed(Ring::bytes(n, 2)).unwrap_err(), Error::Capacity);
        assert_eq!(
            Ring::new(Storage::zeroed(0).unwrap(), n, 2).unwrap_err().error,
            Error::Capacity
        );
    }
}
