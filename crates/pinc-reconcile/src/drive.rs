//! The drivers: a session run to the end over a [`Channel`].
//!
//! Invariants: after a protocol error the driver resets the channel, so the peer sees a reset and does not wait.
//! A reset or a close from the peer is not an error of the session's logic: the initiator retries the whole session,
//! bounded by the attempt count.

use core::fmt;
use core::mem;

use crate::channel::{Channel, Recv};
use crate::error::Error;
use crate::index::ItemIndex;
use crate::session::{Initiator, Responder, Step};
use crate::wire::first_set_ref;

/// Why a driven session did not complete.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunError<C, I> {
    /// The channel failed.
    Channel(C),
    /// The session failed; the channel was reset.
    Protocol(Error<I>),
    /// The stream was reset by the peer.
    Reset,
    /// The peer finished the stream before the session ended.
    Closed,
    /// The responder has no set of that name; the channel was reset.
    UnknownSet,
    /// Every attempt was reset.
    Exhausted,
}

impl<C: fmt::Debug, I: fmt::Debug> fmt::Display for RunError<C, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Channel(e) => write!(f, "the channel failed: {e:?}"),
            Self::Protocol(e) => write!(f, "{e}"),
            Self::Reset => f.write_str("the stream was reset"),
            Self::Closed => f.write_str("the stream ended before the session did"),
            Self::UnknownSet => f.write_str("the set is not known here"),
            Self::Exhausted => f.write_str("every attempt was reset"),
        }
    }
}

impl<C: fmt::Debug, I: fmt::Debug> core::error::Error for RunError<C, I> {}

type Run<C, I> = Result<(), RunError<<C as Channel>::Error, <I as ItemIndex>::Error>>;

impl Initiator {
    /// Run one session for `set_ref` over `chan`; the difference is in [`report`](Self::report) afterwards.
    ///
    /// # Errors
    /// [`RunError`]; after [`RunError::Reset`] the session may be run again whole.
    pub fn run<C: Channel, I: ItemIndex>(&mut self, chan: &mut C, idx: &I, set_ref: &[u8]) -> Run<C, I> {
        let (mut tx, mut rx) = (mem::take(&mut self.tx), mem::take(&mut self.rx));
        let res = self.drive(chan, idx, set_ref, &mut tx, &mut rx);
        (self.tx, self.rx) = (tx, rx);
        res
    }

    fn drive<C: Channel, I: ItemIndex>(
        &mut self,
        chan: &mut C,
        idx: &I,
        set_ref: &[u8],
        tx: &mut alloc::vec::Vec<u8>,
        rx: &mut alloc::vec::Vec<u8>,
    ) -> Run<C, I> {
        self.start(idx, set_ref, tx).map_err(RunError::Protocol)?;
        chan.send(tx, false).map_err(RunError::Channel)?;
        loop {
            match chan.recv(rx).map_err(RunError::Channel)? {
                Recv::Message => {}
                Recv::Finished => return Err(RunError::Closed),
                Recv::Reset => return Err(RunError::Reset),
            }
            match self.handle(idx, rx, tx) {
                Ok(Step::Send) => chan.send(tx, false).map_err(RunError::Channel)?,
                Ok(Step::Last) => return chan.send(tx, true).map_err(RunError::Channel),
                Ok(Step::Wait) => {}
                Ok(Step::Done) => return Ok(()),
                Ok(Step::Chunk) => return fail(chan, Error::Malformed(crate::error::Reason::State)),
                Err(e) => return fail(chan, e),
            }
        }
    }

    /// Run the session, opening a fresh channel for each attempt and retrying the whole session after a reset, at
    /// most `attempts` times (at least once).
    ///
    /// # Errors
    /// [`RunError::Exhausted`] if every attempt was reset, or any other [`RunError`] at once.
    pub fn run_retry<C: Channel, I: ItemIndex>(
        &mut self,
        mut open: impl FnMut() -> Result<C, C::Error>,
        idx: &I,
        set_ref: &[u8],
        attempts: u32,
    ) -> Run<C, I> {
        for _ in 0..attempts.max(1) {
            let mut chan = open().map_err(RunError::Channel)?;
            match self.run(&mut chan, idx, set_ref) {
                Err(RunError::Reset) => {}
                other => return other,
            }
        }
        Err(RunError::Exhausted)
    }
}

impl Responder {
    /// Serve one session over `chan`. `resolve` maps the set name in the first message to the index to answer from.
    ///
    /// # Errors
    /// [`RunError`]; an unknown set resets the channel and is [`RunError::UnknownSet`].
    pub fn serve<C: Channel, I: ItemIndex>(
        &mut self,
        chan: &mut C,
        resolve: impl FnOnce(&[u8]) -> Option<I>,
    ) -> Run<C, I> {
        let (mut tx, mut rx) = (mem::take(&mut self.tx), mem::take(&mut self.rx));
        self.reset();
        let res = self.drive(chan, resolve, &mut tx, &mut rx);
        (self.tx, self.rx) = (tx, rx);
        res
    }

    fn drive<C: Channel, I: ItemIndex>(
        &mut self,
        chan: &mut C,
        resolve: impl FnOnce(&[u8]) -> Option<I>,
        tx: &mut alloc::vec::Vec<u8>,
        rx: &mut alloc::vec::Vec<u8>,
    ) -> Run<C, I> {
        recv(chan, rx)?;
        let set_ref = match first_set_ref(rx) {
            Ok(r) => r,
            Err(e) => return fail(chan, Error::Malformed(e)),
        };
        let Some(idx) = resolve(set_ref) else {
            chan.reset();
            return Err(RunError::UnknownSet);
        };
        loop {
            let mut step = self.handle(&idx, rx, tx).or_else(|e| fail(chan, e))?;
            while step == Step::Chunk {
                chan.send(tx, false).map_err(RunError::Channel)?;
                step = self.resume(&idx, tx).or_else(|e| fail(chan, e))?;
            }
            match step {
                Step::Send => chan.send(tx, false).map_err(RunError::Channel)?,
                Step::Last => return chan.send(tx, true).map_err(RunError::Channel),
                Step::Done => return chan.send(&[], true).map_err(RunError::Channel),
                Step::Wait | Step::Chunk => {}
            }
            recv(chan, rx)?;
        }
    }
}

fn recv<C: Channel, I>(chan: &mut C, rx: &mut alloc::vec::Vec<u8>) -> Result<(), RunError<C::Error, I>> {
    match chan.recv(rx).map_err(RunError::Channel)? {
        Recv::Message => Ok(()),
        Recv::Finished => Err(RunError::Closed),
        Recv::Reset => Err(RunError::Reset),
    }
}

/// Reset the channel and report the protocol error.
fn fail<C: Channel, T, I>(chan: &mut C, e: Error<I>) -> Result<T, RunError<C::Error, I>> {
    chan.reset();
    Err(RunError::Protocol(e))
}
