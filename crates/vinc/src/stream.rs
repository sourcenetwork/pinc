//! Streams: a [`SendStream`] and a [`RecvStream`].
//!
//! Bytes cross between the caller's buffer and the endpoint directly: a write hands the caller's slice to the
//! endpoint and a read copies out of the endpoint's chunk into the caller's buffer, so a stream holds nothing of its
//! own and an established stream allocates nothing per message. Every wait is woken by the stream's own events, and
//! the waiting future drives the endpoint when no other future does.
//!
//! # Cancel safety
//!
//! - [`SendStream::write`], [`SendStream::finish`], [`RecvStream::read`] and [`RecvStream::read_chunk`]: dropping the
//!   future before it returns something changes nothing, except that the bytes of a write the endpoint already took
//!   stay written when the future is dropped while the packets they caused are still being sent by the host.
//! - [`SendStream::write_all`], [`RecvStream::read_exact`] and [`RecvStream::read_to_end`]: dropping the future leaves
//!   the stream consistent, with the bytes moved so far moved, as for any loop of reads or writes.
//!
//! Dropping a [`SendStream`] without finishing it finishes it after the bytes already written (a clean end). Dropping a
//! [`RecvStream`] discards what the peer still sends.

use std::sync::Arc;

use crate::conn::ConnInner;
use crate::engine::Try;
use crate::error::{Error, ErrorKind, Result};
use crate::host::Hosted;

/// The most bytes one [`RecvStream::read_chunk`] allocates and one [`RecvStream::read_to_end`] step reads.
pub const BLOCK: usize = 16 * 1024;

/// The sending half of a stream.
pub struct SendStream<H: Hosted> {
    conn: Arc<ConnInner<H>>,
    id: u64,
    finished: bool,
}

/// The receiving half of a stream.
pub struct RecvStream<H: Hosted> {
    conn: Arc<ConnInner<H>>,
    id: u64,
    /// How the stream ended for this reader: `Ok` for the end of the data, else why not.
    end: Option<Result<()>>,
    stopped: Option<u64>,
}

impl<H: Hosted> core::fmt::Debug for SendStream<H> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SendStream")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

impl<H: Hosted> core::fmt::Debug for RecvStream<H> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RecvStream")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

impl<H: Hosted> SendStream<H> {
    pub(crate) fn new(conn: &Arc<ConnInner<H>>, id: u64) -> Self {
        Self {
            conn: Arc::clone(conn),
            id,
            finished: false,
        }
    }

    /// The stream id.
    pub const fn id(&self) -> u64 {
        self.id
    }

    /// Write some of `buf`; returns how many bytes were taken. Waits while the stream has no room.
    ///
    /// # Errors
    /// The error that ended the stream: a reset, or a closed connection.
    pub async fn write(&mut self, buf: &[u8]) -> Result<usize> {
        if self.finished {
            return Err(Error::new(ErrorKind::Stopped(0), "the stream is finished"));
        }
        let (c, id) = (&self.conn, self.id);
        c.sh.run(|core, now| core.write(now, &c.info, id, buf)).await
    }

    /// Write all of `buf`.
    ///
    /// # Errors
    /// As [`write`](Self::write).
    pub async fn write_all(&mut self, mut buf: &[u8]) -> Result<()> {
        while !buf.is_empty() {
            let n = self.write(buf).await?;
            buf = buf.get(n..).unwrap_or_default();
        }
        Ok(())
    }

    /// End the stream after the bytes written: the peer reads them and then the end.
    ///
    /// # Errors
    /// The error that ended the stream.
    pub async fn finish(&mut self) -> Result<()> {
        if self.finished {
            return Ok(());
        }
        let (c, id) = (&self.conn, self.id);
        let fin = &mut self.finished;
        c.sh.run(|core, now| {
            let r = core.finish(now, &c.info, id);
            *fin |= r.is_ok();
            Try::Done(r)
        })
        .await
    }

    /// Abandon the stream: bytes not yet sent are dropped and the peer sees a reset with `code`.
    pub async fn reset(&mut self, code: u64) {
        self.finished = true;
        let (c, id) = (&self.conn, self.id);
        c.sh.run(|core, now| {
            core.reset(now, &c.info, id, code);
            Try::Done(())
        })
        .await;
    }
}

impl<H: Hosted> Drop for SendStream<H> {
    fn drop(&mut self) {
        let now = self.conn.sh.now();
        self.conn
            .sh
            .lock()
            .drop_send(now, &self.conn.info, self.id, self.finished);
    }
}

impl<H: Hosted> RecvStream<H> {
    pub(crate) fn new(conn: &Arc<ConnInner<H>>, id: u64) -> Self {
        Self {
            conn: Arc::clone(conn),
            id,
            end: None,
            stopped: None,
        }
    }

    /// The stream id.
    pub const fn id(&self) -> u64 {
        self.id
    }

    /// Read some bytes into `buf`; `Ok(None)` at the end of the stream. Waits while the stream has none.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Reset`] if the peer reset the stream, or the error that closed the connection.
    pub async fn read(&mut self, buf: &mut [u8]) -> Result<Option<usize>> {
        if let Some(code) = self.stopped {
            return Err(Error::new(ErrorKind::Stopped(code), "the stream was stopped"));
        }
        if let Some(end) = self.end {
            return end.map(|()| None);
        }
        let (c, id) = (&self.conn, self.id);
        let (n, end) = c.sh.run(|core, now| core.read(now, &c.info, id, buf)).await?;
        if end.is_some() {
            self.end = end;
        }
        if n > 0 || buf.is_empty() {
            return Ok(Some(n));
        }
        // The read saw the end and no bytes: the end is the answer.
        self.end.map_or(Ok(Some(0)), |e| e.map(|()| None))
    }

    /// Read the next bytes the stream has, at most `max`; `Ok(None)` at the end. Allocates the chunk.
    ///
    /// # Errors
    /// As [`read`](Self::read).
    pub async fn read_chunk(&mut self, max: usize) -> Result<Option<Vec<u8>>> {
        let mut buf = vec![0u8; max.min(BLOCK)];
        Ok(self.read(&mut buf).await?.map(|n| {
            buf.truncate(n);
            buf
        }))
    }

    /// Fill `buf` exactly.
    ///
    /// # Errors
    /// As [`read`](Self::read), or [`crate::ErrorKind::Closed`] if the stream ends first.
    pub async fn read_exact(&mut self, mut buf: &mut [u8]) -> Result<()> {
        while !buf.is_empty() {
            match self.read(buf).await? {
                Some(n) => buf = buf.split_at_mut(n).1,
                None => {
                    return Err(Error::new(
                        ErrorKind::Closed { code: 0, by_peer: true },
                        "the stream ended early",
                    ));
                }
            }
        }
        Ok(())
    }

    /// Read to the end of the stream, at most `limit` bytes.
    ///
    /// # Errors
    /// As [`read`](Self::read), or [`crate::ErrorKind::TooLarge`] if the stream is longer than `limit`.
    pub async fn read_to_end(&mut self, limit: usize) -> Result<Vec<u8>> {
        let mut out = Vec::new();
        let mut buf = vec![0u8; BLOCK];
        while let Some(n) = self.read(&mut buf).await? {
            if out.len() + n > limit {
                return Err(Error::new(ErrorKind::TooLarge, "the stream is longer than the limit"));
            }
            out.extend_from_slice(buf.get(..n).unwrap_or_default());
        }
        Ok(out)
    }

    /// Stop reading: what the peer still sends is discarded and later reads fail with [`crate::ErrorKind::Stopped`].
    /// The peer is told with `code`: it resets the stream and its writer sees [`crate::ErrorKind::Stopped`] with the code.
    pub async fn stop(&mut self, code: u64) {
        self.stopped = Some(code);
        let (c, id) = (&self.conn, self.id);
        c.sh.run(|core, now| {
            core.stop_recv(now, &c.info, id, code);
            Try::Done(())
        })
        .await;
    }
}

impl<H: Hosted> Drop for RecvStream<H> {
    fn drop(&mut self) {
        if self.end.is_none() && self.stopped.is_none() {
            let now = self.conn.sh.now();
            self.conn.sh.lock().drop_recv(now, &self.conn.info, self.id);
        }
    }
}
