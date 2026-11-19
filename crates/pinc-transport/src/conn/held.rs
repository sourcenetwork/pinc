//! The two memory-holding forms of a connection's shared resources: borrowed from the host, or (with `alloc`) owned.
//!
//! A connection works on a stream table of its own and reads a loss estimate the whole node shares. A host with a fixed
//! region lends both (`Borrowed`); a host that has an allocator can hand over a boxed table and a counted estimate, so
//! the node that owns its connections needs no memory that outlives it and no leak to make a borrow last.
//!
//! Invariants: both forms read and write through the same operations; the form changes nothing the connection does.

use core::ops::{Deref, DerefMut};

/// A value the connection works on mutably: lent by the host, or owned.
pub enum Held<'a, T> {
    /// Lent by the host for `'a`.
    Borrowed(&'a mut T),
    /// Owned by the connection and handed back with its resources.
    #[cfg(feature = "alloc")]
    Owned(alloc::boxed::Box<T>),
}

impl<T> Deref for Held<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::Borrowed(r) => r,
            #[cfg(feature = "alloc")]
            Self::Owned(b) => b,
        }
    }
}

impl<T> DerefMut for Held<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        match self {
            Self::Borrowed(r) => r,
            #[cfg(feature = "alloc")]
            Self::Owned(b) => b,
        }
    }
}

impl<'a, T> From<&'a mut T> for Held<'a, T> {
    fn from(r: &'a mut T) -> Self {
        Self::Borrowed(r)
    }
}

/// A value the connection only reads and the node shares: lent by the host, or counted.
pub enum Shared<'a, T> {
    /// Lent by the host for `'a`.
    Borrowed(&'a T),
    /// Shared by reference count among the node's connections.
    #[cfg(feature = "alloc")]
    Counted(alloc::rc::Rc<T>),
}

impl<T> Deref for Shared<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            Self::Borrowed(r) => r,
            #[cfg(feature = "alloc")]
            Self::Counted(r) => r,
        }
    }
}

impl<'a, T> From<&'a T> for Shared<'a, T> {
    fn from(r: &'a T) -> Self {
        Self::Borrowed(r)
    }
}
