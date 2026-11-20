//! Datagram queues and the early-data buffer, both packed into pool chunks.
//!
//! Invariants: entries are stored back to back in a ring of pool chunks and never straddle a chunk; a chunk is
//! returned to the pool as soon as its last entry is removed, and an empty queue holds no chunk. The queues are bounded
//! in entries and in chunks, so memory stays within the pool charge. Datagrams are never retransmitted. A full
//! datagram queue drops its oldest entry; the early-data buffer drops the newest instead.

use core::fmt;

use super::pool::{BufferPool, CHUNK_SIZE, Chunk, PoolExhausted};

/// Why a queue refused an entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueueError {
    /// The entry is larger than one pool chunk.
    TooLarge,
    /// The queue holds as many entries or chunks as it may.
    Full,
    /// The pool has no chunk left.
    Exhausted,
}

/// Where one queued datagram sits: its chunk slot, and its offset and length in the chunk (a chunk is 16 KiB, so both
/// fit 16 bits). Six bytes, because a queue holds many.
#[derive(Debug, Clone, Copy)]
struct Entry {
    slot: u8,
    at: u16,
    len: u16,
}

/// A bounded FIFO of byte strings packed into pool chunks: at most `Q` entries in at most `C` chunks.
#[derive(Debug)]
struct PackedQueue<const Q: usize, const C: usize> {
    entries: [Entry; Q],
    head: usize,
    len: usize,
    chunks: [Option<Chunk>; C],
    chunk_head: usize,
    chunk_len: usize,
    tail_at: usize,
}

impl<const Q: usize, const C: usize> PackedQueue<Q, C> {
    const NEW: Self = Self {
        entries: [Entry { slot: 0, at: 0, len: 0 }; Q],
        head: 0,
        len: 0,
        chunks: [const { None }; C],
        chunk_head: 0,
        chunk_len: 0,
        tail_at: 0,
    };

    fn push(&mut self, pool: &mut BufferPool<'_>, data: &[u8]) -> Result<(), QueueError> {
        if data.len() > CHUNK_SIZE {
            return Err(QueueError::TooLarge);
        }
        if self.len == Q {
            return Err(QueueError::Full);
        }
        if self.chunk_len == 0 || self.tail_at + data.len() > CHUNK_SIZE {
            if self.chunk_len == C {
                return Err(QueueError::Full);
            }
            let chunk = pool.alloc_chunk().map_err(|PoolExhausted| QueueError::Exhausted)?;
            let slot = (self.chunk_head + self.chunk_len) % C;
            if let Some(s) = self.chunks.get_mut(slot) {
                *s = Some(chunk);
            }
            self.chunk_len += 1;
            self.tail_at = 0;
        }
        let slot = (self.chunk_head + self.chunk_len + C - 1) % C;
        let at = self.tail_at;
        let dst = self
            .chunks
            .get(slot)
            .and_then(Option::as_ref)
            .and_then(|chunk| pool.bytes_mut(chunk).get_mut(at..at + data.len()));
        let Some(dst) = dst else {
            return Err(QueueError::Exhausted);
        };
        dst.copy_from_slice(data);
        let at_entry = (self.head + self.len) % Q;
        let (Ok(slot8), Ok(at16), Ok(len16)) = (u8::try_from(slot), u16::try_from(at), u16::try_from(data.len()))
        else {
            return Err(QueueError::TooLarge);
        };
        if let Some(e) = self.entries.get_mut(at_entry) {
            *e = Entry {
                slot: slot8,
                at: at16,
                len: len16,
            };
        }
        self.tail_at += data.len();
        self.len += 1;
        Ok(())
    }

    /// Push, dropping the oldest entries until it fits; every entry dropped is added to `dropped`, also when the push
    /// is refused in the end.
    fn push_drop_oldest(
        &mut self,
        pool: &mut BufferPool<'_>,
        data: &[u8],
        dropped: &mut u64,
    ) -> Result<(), QueueError> {
        loop {
            match self.push(pool, data) {
                Ok(()) => return Ok(()),
                Err(QueueError::TooLarge) => return Err(QueueError::TooLarge),
                Err(e) if self.len == 0 => return Err(e),
                Err(_) => {
                    self.pop(pool);
                    *dropped += 1;
                }
            }
        }
    }

    fn front<'a>(&self, pool: &'a BufferPool<'_>) -> Option<&'a [u8]> {
        if self.len == 0 {
            return None;
        }
        let e = self.entries.get(self.head)?;
        let chunk = self.chunks.get(usize::from(e.slot))?.as_ref()?;
        pool.bytes(chunk)
            .get(usize::from(e.at)..usize::from(e.at) + usize::from(e.len))
    }

    /// Remove the oldest entry; returns whether there was one.
    fn pop(&mut self, pool: &mut BufferPool<'_>) -> bool {
        let Some(e) = (self.len > 0).then(|| self.entries.get(self.head).copied()).flatten() else {
            return false;
        };
        self.head = (self.head + 1) % Q;
        self.len -= 1;
        let next_slot = (self.len > 0)
            .then(|| self.entries.get(self.head).map(|n| n.slot))
            .flatten();
        if self.len == 0 {
            self.clear(pool);
        } else if next_slot != Some(e.slot)
            && let Some(chunk) = self.chunks.get_mut(self.chunk_head).and_then(Option::take)
        {
            pool.free_chunk(chunk);
            self.chunk_head = (self.chunk_head + 1) % C;
            self.chunk_len -= 1;
        }
        true
    }

    fn clear(&mut self, pool: &mut BufferPool<'_>) {
        for chunk in self.chunks.iter_mut().filter_map(Option::take) {
            pool.free_chunk(chunk);
        }
        self.head = 0;
        self.len = 0;
        self.chunk_head = 0;
        self.chunk_len = 0;
        self.tail_at = 0;
    }
}

/// Why a datagram could not be queued.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatagramError {
    /// The datagram exceeds the largest the connection can send.
    TooLarge {
        /// The limit it exceeded.
        max_size: usize,
    },
    /// The pool has no chunk left and nothing older could be dropped to make room.
    Exhausted,
}

impl fmt::Display for DatagramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge { .. } => f.write_str("datagram larger than the maximum size"),
            Self::Exhausted => f.write_str("buffer pool exhausted"),
        }
    }
}

impl core::error::Error for DatagramError {}

/// The send and receive datagram queues, each holding at most `Q` datagrams in at most `C` pool chunks.
#[derive(Debug)]
pub struct Datagrams<const Q: usize = 64, const C: usize = 16> {
    send: PackedQueue<Q, C>,
    recv: PackedQueue<Q, C>,
    send_dropped: u64,
    recv_dropped: u64,
}

impl<const Q: usize, const C: usize> Default for Datagrams<Q, C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const Q: usize, const C: usize> Datagrams<Q, C> {
    /// Empty queues.
    pub const fn new() -> Self {
        const { assert!(Q >= 1 && C >= 1 && C <= 255) };
        Self {
            send: PackedQueue::NEW,
            recv: PackedQueue::NEW,
            send_dropped: 0,
            recv_dropped: 0,
        }
    }

    /// Queue a datagram for sending, dropping the oldest queued ones if the queue is full.
    ///
    /// # Errors
    /// [`DatagramError::TooLarge`] if `data` is longer than `max_size`; [`DatagramError::Exhausted`] if the pool is empty
    /// and the queue has nothing left to drop.
    pub fn send_datagram(
        &mut self,
        pool: &mut BufferPool<'_>,
        data: &[u8],
        max_size: usize,
    ) -> Result<(), DatagramError> {
        if data.len() > max_size {
            return Err(DatagramError::TooLarge { max_size });
        }
        match self.send.push_drop_oldest(pool, data, &mut self.send_dropped) {
            Ok(()) => Ok(()),
            Err(QueueError::TooLarge) => Err(DatagramError::TooLarge { max_size: CHUNK_SIZE }),
            Err(_) => {
                self.send_dropped += 1;
                Err(DatagramError::Exhausted)
            }
        }
    }

    /// The oldest datagram waiting to be sent. Remove it with [`Datagrams::pop_send`] once it is in a packet.
    pub fn peek_send<'a>(&self, pool: &'a BufferPool<'_>) -> Option<&'a [u8]> {
        self.send.front(pool)
    }

    /// Remove the datagram [`Datagrams::peek_send`] returned.
    pub fn pop_send(&mut self, pool: &mut BufferPool<'_>) {
        self.send.pop(pool);
    }

    /// A DATAGRAM frame arrived: queue it for the application, dropping the oldest unread ones if the queue is full.
    /// A datagram that cannot be stored at all is counted as dropped.
    pub fn on_datagram_frame(&mut self, pool: &mut BufferPool<'_>, data: &[u8]) {
        if self.recv.push_drop_oldest(pool, data, &mut self.recv_dropped).is_err() {
            self.recv_dropped += 1;
        }
    }

    /// The oldest received datagram. Call [`Datagrams::release`] once it is handled.
    pub fn recv_datagram<'a>(&self, pool: &'a BufferPool<'_>) -> Option<&'a [u8]> {
        self.recv.front(pool)
    }

    /// Remove the datagram [`Datagrams::recv_datagram`] returned.
    pub fn release(&mut self, pool: &mut BufferPool<'_>) {
        self.recv.pop(pool);
    }

    /// Datagrams dropped from the send queue to make room (or refused by an empty pool).
    pub const fn send_dropped(&self) -> u64 {
        self.send_dropped
    }

    /// Received datagrams dropped to make room (or that could not be stored).
    pub const fn recv_dropped(&self) -> u64 {
        self.recv_dropped
    }

    /// Return every chunk to the pool (the connection is going away).
    pub fn clear(&mut self, pool: &mut BufferPool<'_>) {
        self.send.clear(pool);
        self.recv.clear(pool);
    }
}

/// The most packets a connection holds that arrived before the keys to open them (early 1-RTT and 0-RTT packets).
pub const MAX_EARLY_PACKETS: usize = 8;

/// Packets held, as received, until the handshake gives the keys that open them. At most
/// [`MAX_EARLY_PACKETS`] are held; further ones are dropped and counted.
#[derive(Debug)]
pub struct EarlyData {
    queue: PackedQueue<MAX_EARLY_PACKETS, MAX_EARLY_PACKETS>,
    dropped: u64,
}

impl Default for EarlyData {
    fn default() -> Self {
        Self::new()
    }
}

impl EarlyData {
    /// An empty buffer.
    pub const fn new() -> Self {
        Self {
            queue: PackedQueue::NEW,
            dropped: 0,
        }
    }

    /// Hold a packet. Returns whether it was kept; a dropped packet is counted.
    pub fn push(&mut self, pool: &mut BufferPool<'_>, packet: &[u8]) -> bool {
        let kept = self.queue.push(pool, packet).is_ok();
        self.dropped += u64::from(!kept);
        kept
    }

    /// How many packets are held.
    pub const fn len(&self) -> usize {
        self.queue.len
    }

    /// Whether no packet is held.
    pub const fn is_empty(&self) -> bool {
        self.queue.len == 0
    }

    /// The oldest held packet.
    pub fn front<'a>(&self, pool: &'a BufferPool<'_>) -> Option<&'a [u8]> {
        self.queue.front(pool)
    }

    /// Remove the packet [`EarlyData::front`] returned.
    pub fn pop(&mut self, pool: &mut BufferPool<'_>) {
        self.queue.pop(pool);
    }

    /// Packets dropped because the buffer was full, the pool empty or the packet oversized.
    pub const fn dropped(&self) -> u64 {
        self.dropped
    }

    /// Drop every held packet: the connection closed, whatever the reason.
    pub fn clear(&mut self, pool: &mut BufferPool<'_>) {
        self.queue.clear(pool);
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// A pool whose budget fell below its use refuses the new datagram after the queue gave up its old ones: every
    /// one of them, and the refused one, is counted.
    #[test]
    fn drops_are_counted_when_the_pool_refuses_after_making_room() {
        let data = [7u8; CHUNK_SIZE / 2 + 1];
        let mut pool = BufferPool::new_boxed(4);
        let mut q: Datagrams = Datagrams::new();
        for _ in 0..2 {
            q.send_datagram(&mut pool, &data, CHUNK_SIZE).unwrap();
            q.on_datagram_frame(&mut pool, &data);
        }
        assert_eq!(pool.used_chunks(), 4);
        pool.set_budget_bytes(0);
        assert_eq!(
            q.send_datagram(&mut pool, &data, CHUNK_SIZE),
            Err(DatagramError::Exhausted)
        );
        assert_eq!(q.send_dropped(), 3, "two popped and the refused one");
        q.on_datagram_frame(&mut pool, &data);
        assert_eq!(q.recv_dropped(), 3, "two popped and the refused one");
    }
}
