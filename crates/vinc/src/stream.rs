//! Streams: a [`SendStream`] and a [`RecvStream`] that implement the `futures-io` traits.
//!
//! Bytes cross to the driver in blocks of at most 16 KiB through bounded channels, so a stream holds at most
//! `Limits::stream_blocks` blocks per direction outside the endpoint. Every wait registers the task's waker on a signal
//! of the stream and checks again, so a dropped future never loses bytes and never leaves the stream half updated.
//!
//! # Cancel safety
//!
//! - [`SendStream::write`], [`SendStream::finish`], [`RecvStream::read`], [`RecvStream::read_chunk`] and
//!   [`poll_write`](futures_io::AsyncWrite::poll_write) / [`poll_read`](futures_io::AsyncRead::poll_read): dropping the
//!   future after it was polled changes nothing the stream did not already report; a write that returned `Pending`
//!   accepted no bytes.
//! - [`SendStream::write_all`], [`RecvStream::read_exact`] and [`RecvStream::read_to_end`]: dropping the future leaves
//!   the stream consistent, with the bytes moved so far moved (the write is partial, the read consumed what it
//!   filled), as for any loop of reads or writes.
//!
//! Dropping a [`SendStream`] without finishing it finishes it after the bytes already written (a clean end). Dropping a
//! [`RecvStream`] discards what the peer still sends.

use std::future::poll_fn;
use std::io;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::task::{Context, Poll};

use futures_io::{AsyncRead, AsyncWrite};
use vinc_driver::{BLOCK, Ctl, Error, ErrorKind, Item, NewStream, Receiver, Result, Sender, StreamShared};

use crate::conn::ConnInner;

fn io_err(e: Error) -> io::Error {
    e.into()
}

/// The sending half of a stream.
pub struct SendStream {
    conn: Arc<ConnInner>,
    shared: Arc<StreamShared>,
    tx: Sender<Item>,
    finished: bool,
}

/// The receiving half of a stream.
pub struct RecvStream {
    conn: Arc<ConnInner>,
    shared: Arc<StreamShared>,
    rx: Option<Receiver<Vec<u8>>>,
    cur: Vec<u8>,
    pos: usize,
    done: bool,
    stopped: u64,
}

impl core::fmt::Debug for SendStream {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SendStream")
            .field("id", &self.shared.id)
            .finish_non_exhaustive()
    }
}

impl core::fmt::Debug for RecvStream {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("RecvStream")
            .field("id", &self.shared.id)
            .finish_non_exhaustive()
    }
}

/// The stream ends of a new stream, as the two halves (either may be absent for a one-way stream).
pub(crate) fn halves(conn: &Arc<ConnInner>, n: NewStream) -> (Option<SendStream>, Option<RecvStream>) {
    let send = n.tx.map(|tx| SendStream {
        conn: Arc::clone(conn),
        shared: Arc::clone(&n.shared),
        tx,
        finished: false,
    });
    let recv = n.rx.map(|rx| RecvStream {
        conn: Arc::clone(conn),
        shared: n.shared,
        rx: Some(rx),
        cur: Vec::new(),
        pos: 0,
        done: false,
        stopped: 0,
    });
    (send, recv)
}

impl SendStream {
    /// The stream id.
    pub fn id(&self) -> u64 {
        self.shared.id
    }

    fn failed(&self) -> Option<Error> {
        self.shared.tx_err.get().copied()
    }

    /// Wait until the channel has room for one more item, or the stream has failed (the caller looks).
    fn poll_room(&self, cx: &mut Context<'_>) -> Poll<()> {
        let ready = || !self.tx.is_full() || self.shared.tx_err.get().is_some();
        if ready() {
            return Poll::Ready(());
        }
        self.shared.writable.register(cx.waker());
        if ready() {
            return Poll::Ready(());
        }
        // The driver may be idle with a full channel: make sure it looks.
        self.conn.remote.nudge(&self.shared);
        Poll::Pending
    }

    fn poll_write_inner(&mut self, cx: &mut Context<'_>, buf: &[u8]) -> Poll<Result<usize>> {
        if let Some(e) = self.failed() {
            return Poll::Ready(Err(e));
        }
        if self.finished {
            return Poll::Ready(Err(Error::new(ErrorKind::Stopped(0), "the stream is finished")));
        }
        if buf.is_empty() {
            return Poll::Ready(Ok(0));
        }
        if self.poll_room(cx).is_pending() {
            return Poll::Pending;
        }
        if let Some(e) = self.failed() {
            return Poll::Ready(Err(e));
        }
        let n = buf.len().min(BLOCK);
        self.tx.send(Item::Data(buf.get(..n).unwrap_or_default().to_vec()));
        self.conn.remote.nudge(&self.shared);
        Poll::Ready(self.failed().map_or(Ok(n), Err))
    }

    fn poll_close_inner(&mut self, cx: &mut Context<'_>) -> Poll<Result<()>> {
        if let Some(e) = self.failed() {
            return Poll::Ready(Err(e));
        }
        if !self.finished {
            if self.poll_room(cx).is_pending() {
                return Poll::Pending;
            }
            if let Some(e) = self.failed() {
                return Poll::Ready(Err(e));
            }
            self.finished = true;
            self.tx.send(Item::Fin);
            self.conn.remote.nudge(&self.shared);
        }
        Poll::Ready(self.failed().map_or(Ok(()), Err))
    }

    /// Write some of `buf`; returns how many bytes were taken (at most 16 KiB). Cancel safe.
    ///
    /// # Errors
    /// The error that ended the stream: a reset, or a closed connection.
    pub async fn write(&mut self, buf: &[u8]) -> Result<usize> {
        poll_fn(|cx| self.poll_write_inner(cx, buf)).await
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

    /// End the stream after the bytes written: the peer reads them and then the end. Cancel safe.
    ///
    /// # Errors
    /// The error that ended the stream.
    pub async fn finish(&mut self) -> Result<()> {
        poll_fn(|cx| self.poll_close_inner(cx)).await
    }

    /// Abandon the stream: bytes not yet sent are dropped and the peer sees a reset with `code`.
    pub fn reset(&mut self, code: u64) {
        self.finished = true;
        self.conn
            .remote
            .ctl(Ctl::Reset(self.shared.session, self.shared.id, code));
    }
}

impl RecvStream {
    /// The stream id.
    pub fn id(&self) -> u64 {
        self.shared.id
    }

    fn end(&self) -> Result<Option<usize>> {
        match self.shared.rx_end.get() {
            Some(Ok(())) => Ok(None),
            Some(Err(e)) => Err(*e),
            None => Err(Error::shutdown()),
        }
    }

    /// Take the next block into `cur`; `Ready(false)` at the end of the stream. The end is the stream's reason, set
    /// after the last block was sent, so blocks are drained once more after it is seen.
    fn poll_block(&mut self, cx: &mut Context<'_>) -> Poll<Result<bool>> {
        let Some(rx) = self.rx.as_ref() else {
            return Poll::Ready(Err(Error::new(
                ErrorKind::Stopped(self.stopped),
                "the stream was stopped",
            )));
        };
        let mut registered = false;
        loop {
            let ended = self.shared.rx_end.get().is_some();
            if let Some(b) = rx.try_recv() {
                self.cur = b;
                self.pos = 0;
                // The channel has room again: wake the engine if it stopped for lack of it.
                if self.shared.starved.swap(false, Ordering::SeqCst) {
                    self.conn.remote.nudge(&self.shared);
                }
                return Poll::Ready(Ok(true));
            }
            if ended {
                self.done = true;
                return self.end().map(|_| false).into();
            }
            if registered {
                return Poll::Pending;
            }
            self.shared.readable.register(cx.waker());
            registered = true;
        }
    }

    fn poll_read_inner(&mut self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<Option<usize>>> {
        loop {
            if let Some(avail) = self.cur.get(self.pos..).filter(|a| !a.is_empty()) {
                let n = avail.len().min(buf.len());
                if let (Some(d), Some(s)) = (buf.get_mut(..n), avail.get(..n)) {
                    d.copy_from_slice(s);
                }
                self.pos += n;
                return Poll::Ready(Ok(Some(n)));
            }
            if self.done {
                return Poll::Ready(self.end());
            }
            if buf.is_empty() {
                return Poll::Ready(Ok(Some(0)));
            }
            match self.poll_block(cx) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
                Poll::Ready(Ok(_)) => {}
            }
        }
    }

    /// Read some bytes into `buf`; `Ok(None)` at the end of the stream. Cancel safe.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Reset`] if the peer reset the stream, or the error that closed the connection.
    pub async fn read(&mut self, buf: &mut [u8]) -> Result<Option<usize>> {
        poll_fn(|cx| self.poll_read_inner(cx, buf)).await
    }

    /// Read the next bytes the stream has, at most `max`; `Ok(None)` at the end. Cancel safe.
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
        while let Some(chunk) = self.read_chunk(BLOCK).await? {
            if out.len() + chunk.len() > limit {
                return Err(Error::new(ErrorKind::TooLarge, "the stream is longer than the limit"));
            }
            out.extend_from_slice(&chunk);
        }
        Ok(out)
    }

    /// Stop reading: what the peer still sends is discarded and later reads fail with [`crate::ErrorKind::Stopped`].
    /// The peer is told with `code`: it resets the stream and its writer sees [`crate::ErrorKind::Stopped`] with the code.
    pub fn stop(&mut self, code: u64) {
        self.rx = None;
        self.stopped = code;
        self.cur.clear();
        self.conn
            .remote
            .ctl(Ctl::Stop(self.shared.session, self.shared.id, code));
    }
}

impl Drop for RecvStream {
    fn drop(&mut self) {
        if self.rx.is_some() && !self.done {
            self.rx = None;
            self.conn.remote.nudge(&self.shared);
        }
    }
}

impl AsyncWrite for SendStream {
    fn poll_write(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) -> Poll<io::Result<usize>> {
        self.get_mut().poll_write_inner(cx, buf).map_err(io_err)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        let _ = cx;
        Poll::Ready(self.failed().map_or(Ok(()), |e| Err(io_err(e))))
    }

    fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        self.get_mut().poll_close_inner(cx).map_err(io_err)
    }
}

impl AsyncRead for RecvStream {
    fn poll_read(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<io::Result<usize>> {
        self.get_mut()
            .poll_read_inner(cx, buf)
            .map(|r| r.map(|n| n.unwrap_or(0)).map_err(io_err))
    }
}
