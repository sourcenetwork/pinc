//! A buffer the application hands to a stream whole, so the endpoint sends from it instead of copying it first.
//!
//! [`SendStream::send_owned`](crate::stream::SendStream::send_owned) takes a [`Body`]: the endpoint keeps it and reads
//! its bytes into each packet as the packet is built, and again for a range that was lost. The bytes are copied once,
//! into the datagram, and the stream's send buffer is never filled: a body of a gigabyte costs the gigabyte the
//! application already holds.
//!
//! Invariants: a body never changes once made; cloning one is a reference count, never a copy of its bytes.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use pinc_node::{ServeSource, ValueRead, ValueSource};
use pinc_transport::stream::StreamSource;

/// The whole content of a stream, owned: see [`SendStream::send_owned`](crate::stream::SendStream::send_owned).
/// Made from a `Vec<u8>`, a `Box<[u8]>`, a `String`, an `Rc<[u8]>` or a `&'static [u8]`, none of which is copied.
#[derive(Debug, Clone)]
pub struct Body(Kind);

#[derive(Debug, Clone)]
enum Kind {
    Vec(Rc<Vec<u8>>),
    Shared(Rc<[u8]>),
    Static(&'static [u8]),
}

impl Body {
    /// The bytes.
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        match &self.0 {
            Kind::Vec(v) => v,
            Kind::Shared(s) => s,
            Kind::Static(s) => s,
        }
    }

    /// How many bytes it holds.
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    /// Whether it holds none.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_slice().is_empty()
    }
}

impl From<Vec<u8>> for Body {
    fn from(v: Vec<u8>) -> Self {
        Self(Kind::Vec(Rc::new(v)))
    }
}

impl From<Box<[u8]>> for Body {
    fn from(b: Box<[u8]>) -> Self {
        Self::from(b.into_vec())
    }
}

impl From<String> for Body {
    fn from(s: String) -> Self {
        Self::from(s.into_bytes())
    }
}

impl From<Rc<[u8]>> for Body {
    fn from(s: Rc<[u8]>) -> Self {
        Self(Kind::Shared(s))
    }
}

impl From<&'static [u8]> for Body {
    fn from(s: &'static [u8]) -> Self {
        Self(Kind::Static(s))
    }
}

impl StreamSource for Body {
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
        let from = usize::try_from(offset)
            .ok()
            .and_then(|o| self.as_slice().get(o..))
            .unwrap_or_default();
        let n = from.len().min(dst.len());
        if let (Some(d), Some(s)) = (dst.get_mut(..n), from.get(..n)) {
            d.copy_from_slice(s);
        }
        n
    }
}

/// The facade does not serve values from a store through its streams: a body is only ever the application's.
impl<H: ValueRead> ServeSource<H> for Body {
    fn from_source(_source: ValueSource<H>) -> Option<Self> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_body_reads_any_range_of_its_bytes_and_nothing_past_its_end() {
        let bytes: Vec<u8> = (0..=255).collect();
        let shared: Rc<[u8]> = Rc::from(bytes.clone());
        let fixed: &'static [u8] = b"0123456789";
        for mut body in [
            Body::from(bytes.clone()),
            Body::from(shared),
            Body::from(bytes.clone().into_boxed_slice()),
        ] {
            assert_eq!((body.len(), body.is_empty()), (256, false));
            let mut out = [0u8; 100];
            assert_eq!(body.read_at(0, &mut out), 100);
            assert_eq!(out.as_slice(), bytes.get(..100).unwrap_or_default());
            assert_eq!(body.read_at(200, &mut out), 56, "the last bytes, fewer than asked");
            assert_eq!(out.get(..56), bytes.get(200..));
            assert_eq!(body.read_at(256, &mut out), 0);
            assert_eq!(body.read_at(u64::MAX, &mut out), 0);
            // A clone is the same bytes, not a copy of them.
            assert!(core::ptr::eq(body.clone().as_slice(), body.as_slice()));
        }
        let mut body = Body::from(fixed);
        let mut out = [0u8; 4];
        assert_eq!((body.read_at(8, &mut out), out.get(..2)), (2, Some(&b"89"[..])));
        assert!(Body::from(String::new()).is_empty());
    }
}
