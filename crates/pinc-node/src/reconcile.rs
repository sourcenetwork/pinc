//! Reconcile over real sessions: rounds against a peer and the answers to a peer's rounds.
//!
//! A round is one session of the range-fingerprint protocol of `pinc-reconcile` for one named set. The initiator
//! opens a stream on its reconcile session to the peer and writes the first message; the responder, which the peer's
//! stream creates, answers on the same stream, and every message is answered by one message until the exchange ends,
//! however many messages the difference needs. The initiator learns the exact difference, and the node reports it as
//! one event. A reset stream, a closed session or a full table of dials retries the whole round (a full table after one
//! retry period), at most [`ATTEMPTS`] times.
//!
//! The sets are the host's ([`SetsApp`](crate::SetsApp)); a session reads a set by its index and the set must not
//! change while a round over it runs.
//!
//! Invariants: at most [`ROUNDS`] rounds and [`RESPONDERS`] answered streams exist at once; a message is parsed only
//! when whole and never longer than the session's message limit; a round ends with exactly one event.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use pinc_core::{Command, SessionId};
use pinc_membership::NodeId;
use pinc_reconcile::limits::FRAME_MAX;
use pinc_reconcile::{Error, Initiator, Limits, Responder, Step, first_set_ref, frame_len};
use pinc_transport::stream::{RecvStatus, StreamId};
use pinc_values::knobs::OPEN_RETRY;

use crate::apps::{Apps, ServeSource, SetsApp};
use crate::config::{Nanos, Store};
use crate::ep::Ep;
use crate::event::{NodeEvent, ReconcileFailure};
use crate::layer::Layer;
use crate::node::Node;
use crate::trace::{NodeTrace, tag};

/// The most rounds this node runs as initiator at once.
pub const ROUNDS: usize = 8;
/// The most streams this node answers at once.
pub const RESPONDERS: usize = 16;
/// How many times a round is tried before it fails: a reset stream or a closed session retries it whole.
pub const ATTEMPTS: u8 = 4;
/// The reset code of a stream whose first message names a set this node does not hold.
const UNKNOWN_SET: u64 = 2;
/// The reset code of a stream that broke the protocol.
const PROTOCOL: u64 = 1;

/// Why a round could not start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetsError {
    /// The host did not enable the reconcile layer.
    Off,
    /// [`ROUNDS`] rounds are running.
    Busy,
    /// This node holds no set of that name.
    UnknownSet,
}

impl fmt::Display for SetsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Off => "the reconcile layer is not enabled on this node",
            Self::Busy => "too many reconcile rounds are running",
            Self::UnknownSet => "this node holds no set of that name",
        })
    }
}

impl core::error::Error for SetsError {}

/// A round this node started.
struct Round {
    id: u32,
    peer: NodeId,
    set_ref: Vec<u8>,
    init: Box<Initiator>,
    attempt: u8,
    active: Option<(SessionId, StreamId)>,
    /// A stream could not be opened on the session yet: the attempt is tried again at this time.
    open_at: Option<Nanos>,
    inb: Vec<u8>,
}

/// A stream a peer's round arrives on.
struct Resp {
    machine: Box<Responder>,
    set_ref: Option<Vec<u8>>,
    inb: Vec<u8>,
    fresh: bool,
}

/// The state of the reconcile layer.
pub(crate) struct Reconciler {
    rounds: Vec<Round>,
    resps: BTreeMap<(SessionId, StreamId), Resp>,
    next: u32,
    tx: Vec<u8>,
}

impl Reconciler {
    pub(crate) fn new() -> Self {
        Self {
            rounds: Vec::with_capacity(ROUNDS),
            resps: BTreeMap::new(),
            next: 0,
            tx: Vec::new(),
        }
    }

    fn take(&mut self, id: u32) -> Option<Round> {
        let i = self.rounds.iter().position(|r| r.id == id)?;
        Some(self.rounds.remove(i))
    }
}

const fn code_of(r: ReconcileFailure) -> u64 {
    match r {
        ReconcileFailure::Protocol => 1,
        ReconcileFailure::Index => 2,
        ReconcileFailure::ReportTooLarge => 3,
        ReconcileFailure::Mismatch => 4,
        ReconcileFailure::UnknownSet => 5,
        ReconcileFailure::Exhausted => 6,
        ReconcileFailure::Cancelled => 7,
    }
}

fn failure<E>(e: &Error<E>) -> ReconcileFailure {
    match e {
        Error::Index(_) | Error::BadIndex => ReconcileFailure::Index,
        Error::Malformed(_) | Error::MessageTooLarge | Error::ItemTooLarge | Error::TooManyRounds => {
            ReconcileFailure::Protocol
        }
        Error::ReportTooLarge => ReconcileFailure::ReportTooLarge,
        Error::Mismatch => ReconcileFailure::Mismatch,
    }
}

/// The next whole framed message at the front of `inb`, as its length, or an error if it announces more than `cap`.
fn next_message(inb: &[u8], cap: usize) -> Result<Option<usize>, ()> {
    let Some(head) = inb.first_chunk::<3>() else {
        return Ok(None);
    };
    let n = frame_len(*head);
    if n > cap {
        return Err(());
    }
    Ok((inb.len() >= n + 3).then_some(n + 3))
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: pinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    // ---------------------------------------------------------------- the host's commands

    /// Start a round against `peer` over the set named `set_ref`. The exact difference comes out of
    /// [`Node::poll_event`] as [`NodeEvent::ReconcileDone`], or the reason it did not as
    /// [`NodeEvent::ReconcileFailed`]; the session to the peer is dialed if there is none.
    ///
    /// # Errors
    /// [`SetsError`] for a layer that is off, too many rounds, or a set this node does not hold; nothing started.
    pub fn sets_start(&mut self, now: Nanos, peer: &NodeId, set_ref: &[u8]) -> Result<u32, SetsError> {
        self.begin(now);
        let r = self.start_round(now, peer, set_ref);
        self.settle(now);
        r
    }

    fn start_round(&mut self, now: Nanos, peer: &NodeId, set_ref: &[u8]) -> Result<u32, SetsError> {
        let Some(rec) = self.recs.as_deref_mut() else {
            return Err(SetsError::Off);
        };
        if rec.rounds.len() >= ROUNDS {
            return Err(SetsError::Busy);
        }
        let sets = self.apps.sets();
        if sets.index(set_ref).is_none() {
            return Err(SetsError::UnknownSet);
        }
        rec.next = rec.next.wrapping_add(1);
        let id = rec.next;
        rec.rounds.push(Round {
            id,
            peer: *peer,
            set_ref: set_ref.to_vec(),
            init: Box::new(Initiator::new(sets.limits())),
            attempt: 0,
            active: None,
            open_at: None,
            inb: Vec::new(),
        });
        self.round_begin(now, id);
        Ok(id)
    }

    /// Stop a round: nothing more is reported for it. False if no such round runs.
    pub fn sets_cancel(&mut self, now: Nanos, round: u32) -> bool {
        self.begin(now);
        let Some(r) = self.recs.as_deref_mut().and_then(|r| r.take(round)) else {
            return false;
        };
        self.round_abort(&r, PROTOCOL);
        self.settle(now);
        true
    }

    /// How many rounds this node started and has not finished.
    pub fn sets_running(&self) -> usize {
        self.recs.as_deref().map_or(0, |r| r.rounds.len())
    }

    /// The earliest time a round whose stream could not be opened tries again.
    pub(crate) fn sets_deadline(&self) -> Option<Nanos> {
        self.recs.as_deref()?.rounds.iter().filter_map(|r| r.open_at).min()
    }

    /// Try again the rounds whose stream could not be opened, once their time comes.
    pub(crate) fn sets_timeout(&mut self, now: Nanos) {
        let due: Vec<u32> = self.recs.as_deref().map_or_default(|r| {
            r.rounds
                .iter()
                .filter(|x| x.open_at.is_some_and(|t| now >= t))
                .map(|x| x.id)
                .collect()
        });
        for id in due {
            self.round_begin(now, id);
        }
    }

    // ---------------------------------------------------------------- the node's events

    /// A session of the reconcile protocol came up: the rounds waiting for this peer begin.
    pub(crate) fn sets_up(&mut self, now: Nanos, _session: SessionId, peer: &NodeId, _incoming: bool) {
        let waiting: Vec<u32> = self.recs.as_deref().map_or_default(|r| {
            r.rounds
                .iter()
                .filter(|x| x.peer == *peer && x.active.is_none())
                .map(|x| x.id)
                .collect()
        });
        for id in waiting {
            self.round_begin(now, id);
        }
    }

    /// A dial for the reconcile protocol failed: the rounds waiting for the peer count it as an attempt. With `wait`
    /// (a table was full) the next attempt comes after the retry period, not in this call.
    pub(crate) fn sets_failed(&mut self, now: Nanos, peer: &NodeId, wait: bool) {
        let waiting: Vec<u32> = self.recs.as_deref().map_or_default(|r| {
            r.rounds
                .iter()
                .filter(|x| x.peer == *peer && x.active.is_none())
                .map(|x| x.id)
                .collect()
        });
        for id in waiting {
            if let Some(r) = self
                .recs
                .as_deref_mut()
                .and_then(|r| r.rounds.iter_mut().find(|x| x.id == id))
            {
                r.attempt += 1;
            }
            self.round_retry(now, id, wait);
        }
    }

    /// A dial for the reconcile protocol will never be answered (the node leaves or the peer is revoked): the rounds
    /// waiting for the peer end cancelled.
    pub(crate) fn sets_cancelled(&mut self, peer: &NodeId) {
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        let (gone, kept): (Vec<Round>, Vec<Round>) = core::mem::take(&mut rec.rounds)
            .into_iter()
            .partition(|x| x.peer == *peer && x.active.is_none());
        rec.rounds = kept;
        for round in &gone {
            self.round_fail(round, ReconcileFailure::Cancelled);
        }
    }

    /// A session of the reconcile protocol ended: its answered streams go and its active rounds retry.
    pub(crate) fn sets_down(&mut self, now: Nanos, session: SessionId, _peer: &NodeId) {
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        rec.resps.retain(|(s, _), _| *s != session);
        let lost: Vec<u32> = rec
            .rounds
            .iter()
            .filter(|r| r.active.is_some_and(|(s, _)| s == session))
            .map(|r| r.id)
            .collect();
        for id in lost {
            if let Some(r) = self
                .recs
                .as_deref_mut()
                .and_then(|r| r.rounds.iter_mut().find(|x| x.id == id))
            {
                r.active = None;
            }
            let gone = self
                .recs
                .as_deref()
                .and_then(|r| r.rounds.iter().find(|x| x.id == id))
                .is_some_and(|x| self.peer_gone(&x.peer));
            if gone {
                if let Some(round) = self.recs.as_deref_mut().and_then(|r| r.take(id)) {
                    self.round_fail(&round, ReconcileFailure::Cancelled);
                }
                continue;
            }
            self.round_retry(now, id, false);
        }
    }

    /// The peer opened a stream on a reconcile session: a round of its begins.
    pub(crate) fn sets_stream_opened(&mut self, session: SessionId, stream: StreamId) {
        if !self.io.lsess.contains_key(&session) {
            return;
        }
        let limits = self.apps.sets().limits();
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        if rec.resps.contains_key(&(session, stream)) {
            return;
        }
        if rec.resps.len() >= RESPONDERS {
            let _ = self.io.cmd(Command::Reset {
                session,
                stream,
                error: pinc_values_busy(),
            });
            return;
        }
        rec.resps.insert(
            (session, stream),
            Resp {
                machine: Box::new(Responder::new(limits)),
                set_ref: None,
                inb: Vec::new(),
                fresh: true,
            },
        );
        self.io.register_stream(session, stream);
    }

    /// Bytes arrived on a stream of the reconcile protocol.
    pub(crate) fn sets_readable(&mut self, now: Nanos, session: SessionId, stream: StreamId) {
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        if let Some(round) = rec
            .rounds
            .iter()
            .find(|r| r.active == Some((session, stream)))
            .map(|r| r.id)
        {
            self.round_readable(now, round);
        } else {
            if !rec.resps.contains_key(&(session, stream)) {
                self.sets_stream_opened(session, stream);
            }
            self.resp_readable(session, stream);
        }
    }

    /// The peer reset a stream of the reconcile protocol, or asked this side to stop sending on it.
    pub(crate) fn sets_stream_gone(&mut self, now: Nanos, session: SessionId, stream: StreamId, error: u64) {
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        rec.resps.remove(&(session, stream));
        let hit = rec
            .rounds
            .iter()
            .find(|r| r.active == Some((session, stream)))
            .map(|r| r.id);
        let Some(id) = hit else { return };
        if error == UNKNOWN_SET {
            if let Some(mut r) = self.recs.as_deref_mut().and_then(|r| r.take(id)) {
                r.active = None;
                self.round_fail(&r, ReconcileFailure::UnknownSet);
            }
        } else {
            self.round_retry(now, id, false);
        }
    }

    // ---------------------------------------------------------------- initiator

    /// Start (or restart) a round's attempt: on its session to the peer if there is one, else after a dial.
    fn round_begin(&mut self, now: Nanos, id: u32) {
        let Some(mut round) = self.recs.as_deref_mut().and_then(|r| r.take(id)) else {
            return;
        };
        round.open_at = None;
        let Some(session) = self.layer_session(Layer::Sets, &round.peer) else {
            let key = (Layer::Sets, round.peer);
            if !self.io.lconn.contains(&key) && !self.io.ldials.contains(&key) {
                self.io.ldials.push(key);
            }
            self.round_put(round);
            return;
        };
        let Some(stream) = self.io.open_stream_at(session, crate::config::SETS_URGENCY) else {
            // No stream credit now (a session reported before its handshake ends has none until the peer's limits
            // arrive): the attempt waits and is tried again, as a refused open of the values layer is. It is not
            // counted: only a reset stream, a closed session or a full table spends an attempt.
            round.open_at = Some(now.saturating_add(OPEN_RETRY));
            self.round_put(round);
            return;
        };
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        round.attempt += 1;
        rec.tx.clear();
        let started = self.apps.sets().index(&round.set_ref).map(|idx| {
            round
                .init
                .start(&idx, &round.set_ref, &mut rec.tx)
                .map_err(|e| failure(&e))
        });
        match started {
            Some(Ok(())) => {}
            Some(Err(reason)) => {
                self.io.drop_strm(session, stream);
                self.round_fail(&round, reason);
                return;
            }
            None => {
                self.io.drop_strm(session, stream);
                self.round_fail(&round, ReconcileFailure::UnknownSet);
                return;
            }
        }
        round.active = Some((session, stream));
        round.inb.clear();
        if !self.io.write(session, stream, &rec.tx) {
            self.round_abort(&round, PROTOCOL);
            self.round_fail(&round, ReconcileFailure::Protocol);
            return;
        }
        self.io.trace(NodeTrace::SetsStart {
            round: u64::from(round.id),
            peer: tag(&round.peer),
            attempt: u64::from(round.attempt),
        });
        self.round_put(round);
    }

    fn round_put(&mut self, round: Round) {
        if let Some(rec) = self.recs.as_deref_mut() {
            rec.rounds.push(round);
        }
    }

    /// Try the round again (after the retry period when `wait`), or fail it when the attempts are spent.
    fn round_retry(&mut self, now: Nanos, id: u32, wait: bool) {
        let Some(round) = self.recs.as_deref_mut().and_then(|r| r.take(id)) else {
            return;
        };
        if round.attempt >= ATTEMPTS {
            self.round_abort(&round, PROTOCOL);
            self.round_fail(&round, ReconcileFailure::Exhausted);
            return;
        }
        self.round_abort(&round, PROTOCOL);
        let mut round = round;
        round.active = None;
        if wait {
            round.open_at = Some(now.saturating_add(OPEN_RETRY));
            self.round_put(round);
            return;
        }
        self.round_put(round);
        self.round_begin(now, id);
    }

    /// Abandon the round's stream, if it has one.
    fn round_abort(&mut self, round: &Round, code: u64) {
        if let Some((session, stream)) = round.active {
            self.io.abandon_with(session, stream, code);
        }
    }

    fn round_fail(&mut self, round: &Round, reason: ReconcileFailure) {
        self.io.trace(NodeTrace::SetsFailed {
            round: u64::from(round.id),
            reason: code_of(reason),
        });
        self.io.emit(NodeEvent::ReconcileFailed {
            round: round.id,
            peer: round.peer,
            reason,
        });
    }

    fn round_readable(&mut self, now: Nanos, id: u32) {
        let Some(mut round) = self.recs.as_deref_mut().and_then(|r| r.take(id)) else {
            return;
        };
        let Some((session, stream)) = round.active else {
            self.round_put(round);
            return;
        };
        let limits = self.apps.sets().limits();
        let cap = limits.max_message.min(FRAME_MAX) + 3;
        let (status, over) = self
            .io
            .drain_stream(session, stream, &mut round.inb, cap.saturating_mul(2));
        let mut done = false;
        let mut failed = if over { Some(ReconcileFailure::Protocol) } else { None };
        while failed.is_none() && !done {
            let n = match next_message(&round.inb, cap.saturating_sub(3)) {
                Ok(Some(n)) => n,
                Ok(None) => break,
                Err(()) => {
                    failed = Some(ReconcileFailure::Protocol);
                    break;
                }
            };
            let Some(rec) = self.recs.as_deref_mut() else {
                return;
            };
            let Some(idx) = self.apps.sets().index(&round.set_ref) else {
                failed = Some(ReconcileFailure::UnknownSet);
                break;
            };
            rec.tx.clear();
            let step = {
                let msg = round.inb.get(..n).unwrap_or_default();
                round.init.handle(&idx, msg, &mut rec.tx)
            };
            round.inb.drain(..n);
            match step {
                Ok(Step::Send) => {
                    if !self.io.write(session, stream, &rec.tx) {
                        failed = Some(ReconcileFailure::Protocol);
                    }
                }
                Ok(Step::Last) => {
                    if !self.io.write(session, stream, &rec.tx) {
                        failed = Some(ReconcileFailure::Protocol);
                    }
                    self.io.close_stream(session, stream);
                    done = true;
                }
                Ok(Step::Done) => {
                    // The responder ended the exchange; ours ends with an empty finish.
                    self.io.close_stream(session, stream);
                    done = true;
                }
                Ok(Step::Wait) => {}
                Ok(Step::Chunk) => failed = Some(ReconcileFailure::Protocol),
                Err(e) => failed = Some(failure(&e)),
            }
        }
        if let Some(reason) = failed {
            self.round_abort(&round, PROTOCOL);
            self.round_fail(&round, reason);
            return;
        }
        if done {
            self.round_finish(&round);
            return;
        }
        if status == RecvStatus::Finished {
            // The peer ended the stream before the exchange did.
            self.round_abort(&round, PROTOCOL);
            self.round_fail(&round, ReconcileFailure::Protocol);
            return;
        }
        let _ = now;
        self.round_put(round);
    }

    fn round_finish(&mut self, round: &Round) {
        let Some(report) = round.init.report() else {
            self.round_fail(round, ReconcileFailure::Protocol);
            return;
        };
        let here: Vec<Vec<u8>> = report.missing_here().map(<[u8]>::to_vec).collect();
        let there: Vec<Vec<u8>> = report.missing_there().map(<[u8]>::to_vec).collect();
        self.io.trace(NodeTrace::SetsDone {
            round: u64::from(round.id),
            here: here.len() as u64,
            there: there.len() as u64,
        });
        self.io.emit(NodeEvent::ReconcileDone {
            round: round.id,
            peer: round.peer,
            missing_here: here,
            missing_there: there,
        });
    }

    // ---------------------------------------------------------------- responder

    fn resp_readable(&mut self, session: SessionId, stream: StreamId) {
        let Some(rec) = self.recs.as_deref_mut() else {
            return;
        };
        let Some(mut r) = rec.resps.remove(&(session, stream)) else {
            return;
        };
        let limits: Limits = self.apps.sets().limits();
        let cap = limits.max_message.min(FRAME_MAX) + 3;
        let (status, over) = self.io.drain_stream(session, stream, &mut r.inb, cap.saturating_mul(2));
        let mut code = if over { Some(PROTOCOL) } else { None };
        let mut done = false;
        while code.is_none() && !done {
            let n = match next_message(&r.inb, cap.saturating_sub(3)) {
                Ok(Some(n)) => n,
                Ok(None) => break,
                Err(()) => {
                    code = Some(PROTOCOL);
                    break;
                }
            };
            if r.fresh {
                let named = first_set_ref(r.inb.get(..n).unwrap_or_default()).map(<[u8]>::to_vec);
                let Ok(name) = named else {
                    code = Some(PROTOCOL);
                    break;
                };
                r.set_ref = Some(name);
                r.fresh = false;
            }
            let Some(set_ref) = r.set_ref.as_deref() else {
                code = Some(PROTOCOL);
                break;
            };
            let Some(idx) = self.apps.sets().index(set_ref) else {
                code = Some(UNKNOWN_SET);
                break;
            };
            let Some(rec) = self.recs.as_deref_mut() else {
                return;
            };
            rec.tx.clear();
            let mut step = {
                let msg = r.inb.get(..n).unwrap_or_default();
                r.machine.handle(&idx, msg, &mut rec.tx)
            };
            r.inb.drain(..n);
            loop {
                match step {
                    Ok(Step::Chunk) => {
                        if !self.io.write(session, stream, &rec.tx) {
                            code = Some(PROTOCOL);
                            break;
                        }
                        rec.tx.clear();
                        step = r.machine.resume(&idx, &mut rec.tx);
                    }
                    Ok(Step::Send) => {
                        if !self.io.write(session, stream, &rec.tx) {
                            code = Some(PROTOCOL);
                        }
                        break;
                    }
                    Ok(Step::Last) => {
                        if !self.io.write(session, stream, &rec.tx) {
                            code = Some(PROTOCOL);
                        }
                        self.io.close_stream(session, stream);
                        done = true;
                        break;
                    }
                    Ok(Step::Done) => {
                        self.io.close_stream(session, stream);
                        done = true;
                        break;
                    }
                    Ok(Step::Wait) => break,
                    Err(_) => {
                        code = Some(PROTOCOL);
                        break;
                    }
                }
            }
        }
        if let Some(code) = code {
            self.io.abandon_with(session, stream, code);
            return;
        }
        if done {
            return;
        }
        if status == RecvStatus::Finished {
            self.io.drop_strm(session, stream);
            return;
        }
        if let Some(rec) = self.recs.as_deref_mut() {
            rec.resps.insert((session, stream), r);
        }
    }
}

/// The reset code of a refusal for lack of room, the same the values server uses.
const fn pinc_values_busy() -> u64 {
    pinc_values::knobs::code::BUSY
}
