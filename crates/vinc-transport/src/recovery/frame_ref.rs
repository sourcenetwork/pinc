//! Compact descriptors of the frames a sent packet carried, so loss can requeue them and acknowledgement can free them.

/// The most frame descriptors one sent packet records.
pub const MAX_FRAME_REFS: usize = 8;

/// One frame a sent packet carried, by what is needed to retransmit or release it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameRef {
    /// A range of stream bytes.
    Stream {
        /// The stream id.
        id: u64,
        /// The offset of the first byte.
        offset: u64,
        /// The number of bytes.
        len: u32,
        /// Whether the range ends the stream.
        fin: bool,
    },
    /// A control frame, by kind and id (for example a stream id or a sequence number).
    Control {
        /// The frame kind, as numbered by the caller.
        kind: u8,
        /// The id inside the kind.
        id: u64,
    },
}

/// The list already holds [`MAX_FRAME_REFS`] descriptors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameRefsFull;

/// A fixed-capacity list of at most [`MAX_FRAME_REFS`] [`FrameRef`]s. It never allocates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameRefs {
    items: [FrameRef; MAX_FRAME_REFS],
    len: u8,
}

impl Default for FrameRefs {
    fn default() -> Self {
        Self::new()
    }
}

impl FrameRefs {
    /// An empty list.
    pub const fn new() -> Self {
        Self {
            items: [FrameRef::Control { kind: 0, id: 0 }; MAX_FRAME_REFS],
            len: 0,
        }
    }

    /// Append a descriptor.
    ///
    /// # Errors
    /// [`FrameRefsFull`] if the list already holds [`MAX_FRAME_REFS`] entries.
    pub fn push(&mut self, frame: FrameRef) -> Result<(), FrameRefsFull> {
        let slot = self.items.get_mut(usize::from(self.len)).ok_or(FrameRefsFull)?;
        *slot = frame;
        self.len += 1;
        Ok(())
    }

    /// The descriptors in the order they were pushed.
    pub fn as_slice(&self) -> &[FrameRef] {
        self.items.get(..usize::from(self.len)).unwrap_or(&[])
    }

    /// The number of descriptors.
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// The descriptors in the order they were pushed.
    pub fn iter(&self) -> core::slice::Iter<'_, FrameRef> {
        self.as_slice().iter()
    }

    /// Whether the list is empty.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'a> IntoIterator for &'a FrameRefs {
    type Item = &'a FrameRef;
    type IntoIter = core::slice::Iter<'a, FrameRef>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}
