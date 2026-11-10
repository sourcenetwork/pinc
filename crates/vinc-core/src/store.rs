//! Fixed-size storage that is built without forming a large value on the stack.
//!
//! Without the `alloc` feature a [`Store`] is an inline array and everything is as before. With it the same storage is a
//! boxed array filled element by element, so an endpoint for thousands of sessions never has a table of megabytes in
//! a stack frame, and the endpoint's inline part stays the same few tens of kilobytes whatever the table sizes.
//!
//! Invariants: a store always holds exactly `N` elements; the two forms index, iterate and borrow alike.

/// `N` elements of `T`: an array, or with `alloc` a boxed array.
#[cfg(feature = "alloc")]
pub(crate) type Store<T, const N: usize> = alloc::boxed::Box<[T; N]>;
/// `N` elements of `T`: an array, or with `alloc` a boxed array.
#[cfg(not(feature = "alloc"))]
pub(crate) type Store<T, const N: usize> = [T; N];

/// A store of `N` copies of `v`.
#[cfg(feature = "alloc")]
pub(crate) fn filled<T: Copy, const N: usize>(v: T) -> Store<T, N> {
    match alloc::vec![v; N].into_boxed_slice().try_into() {
        Ok(b) => b,
        Err(_) => unreachable!("a vector of N elements converts to an array of N"),
    }
}

/// A store of `N` copies of `v`.
#[cfg(not(feature = "alloc"))]
pub(crate) const fn filled<T: Copy, const N: usize>(v: T) -> Store<T, N> {
    [v; N]
}

/// Declares a function that is `const` without `alloc` (the arrays are built at compile time) and a plain function with
/// it (the arrays are built on the heap).
macro_rules! store_fn {
    ($(#[$m:meta])* $vis:vis fn $name:ident $($rest:tt)*) => {
        #[cfg(feature = "alloc")]
        $(#[$m])* $vis fn $name $($rest)*
        #[cfg(not(feature = "alloc"))]
        $(#[$m])* $vis const fn $name $($rest)*
    };
}
pub(crate) use store_fn;
