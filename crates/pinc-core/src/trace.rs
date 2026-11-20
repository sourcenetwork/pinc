//! The trace hook: every decision of the endpoint as a record, written as ndjson.
//!
//! With the `trace` feature the endpoint appends a [`TraceRecord`] to a bounded ring each time it decides something a
//! proof or a model checker cares about: which connection a datagram reached, whether the ledger let a datagram
//! out, whether a half-open session was admitted or expired, how the access check resolved, when a sub-session opened
//! or was orphaned, and when the keepalive plan changed. The host drains the ring with
//! [`Endpoint::poll_trace`](crate::Endpoint::poll_trace) and writes each record with
//! [`TraceRecord::write_ndjson`]. Without the feature the log is an empty type and recording compiles to nothing.
//!
//! Invariants: the ring holds at most [`TRACE_CAPACITY`] records and drops the oldest when full, counting the drops;
//! a record is a plain value with named fields, so the line it writes is a function of the record alone.

use core::fmt;

/// The most records the ring holds.
pub const TRACE_CAPACITY: usize = 512;

/// What was decided. Each variant lists its fields in the order the line writes them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceEvent {
    /// A datagram's destination id matched `candidates` sessions and `slot` took it (`slot` is `u64::MAX` for none).
    Demux {
        /// The session slot chosen.
        slot: u64,
        /// How many sessions held the id.
        candidates: u64,
    },
    /// One candidate of a collision opened the packet (`ok` 1) or did not (0).
    Trial {
        /// The session slot tried.
        slot: u64,
        /// Whether it opened the packet.
        ok: u64,
    },
    /// The ledger counted bytes received from an address (`rx` is the new total).
    LedgerRx {
        /// The address, hashed to a number.
        addr: u64,
        /// Bytes received in total.
        rx: u64,
    },
    /// The ledger decided on a datagram to an address.
    LedgerTx {
        /// The address, hashed to a number.
        addr: u64,
        /// 1 if the datagram left, 0 if it was held.
        allowed: u64,
        /// Bytes received from the address.
        rx: u64,
        /// Bytes charged to the address.
        tx: u64,
    },
    /// A decision on a first message: `admitted` 1, refused 0, 2 for one answered with a reject, 3 for one dropped;
    /// `half_open` sessions were open.
    HalfOpen {
        /// 1 if admitted, 0 if refused, 2 if answered with a reject without a session because the prekey or ticket is
        /// not held, 3 if dropped without an answer.
        admitted: u64,
        /// Unauthenticated sessions at the decision.
        half_open: u64,
        /// 1 if a ticket resume (exempt from the cap).
        resume: u64,
        /// The room the host has left to accept sessions, at most `i32::MAX`.
        room: u64,
        /// Server sessions owed to the host.
        owed: u64,
    },
    /// An unauthenticated session lived its life (30 s, 60 s on a thin node, 60 s once it answered) and was dropped.
    HalfOpenExpired {
        /// The session slot.
        slot: u64,
    },
    /// The access check changed state: 0 asked, 1 allowed, 2 denied, 3 asked again.
    Acp {
        /// The session slot.
        slot: u64,
        /// The step.
        step: u64,
    },
    /// The session's application events: 0 held back, 1 released; `held` events concerned.
    Gate {
        /// The session slot.
        slot: u64,
        /// 0 held, 1 released.
        release: u64,
        /// How many events.
        held: u64,
    },
    /// The client's Connected was decided early (1 optimistic) or after READY (2 ready hold).
    Early {
        /// The session slot.
        slot: u64,
        /// The rule.
        rule: u64,
    },
    /// A sub-session: 0 opened here, 1 accepted from the peer, 2 closed as an orphan, 3 a quiet-parent probe
    /// started, 4 a probe rode its parent, 5 a probe lapsed into its own handshake, 6 a probe ended by the
    /// application, 7 a lapsed probe waits on another dial's handshake.
    Sub {
        /// The step.
        step: u64,
        /// The parent session slot.
        parent: u64,
        /// The sub-session slot.
        child: u64,
    },
    /// The keepalive plan of a session changed to these deadlines (`u64::MAX` for none).
    Keepalive {
        /// The session slot.
        slot: u64,
        /// When the next ping is due.
        ping_at: u64,
        /// When the plan is computed again.
        review_at: u64,
    },
    /// The node round trips changed.
    Rtt {
        /// The node average.
        lrtt: u64,
        /// The node peak.
        tgr: u64,
        /// The handshake floor.
        hs_floor: u64,
    },
    /// A session was created (0), established (1) or freed (2).
    Session {
        /// The session slot.
        slot: u64,
        /// The step.
        step: u64,
        /// 1 if this side dialed.
        dialer: u64,
    },
    /// A connection was asked for a datagram with a window of `room` bytes (`len`, `seg` and `dest` are `u64::MAX`
    /// when it gave none).
    #[cfg(feature = "trace")]
    TxConn {
        /// The session slot asked.
        slot: u64,
        /// The window in bytes.
        room: u64,
        /// The datagram's length.
        len: u64,
        /// The datagram's segment size.
        seg: u64,
        /// The remote of the datagram's path, hashed to a number; `u64::MAX - 1` when the path has no address.
        dest: u64,
    },
    /// The first waiting slot was not in use or had no connection, and was taken off its queue.
    #[cfg(feature = "trace")]
    TxGone {
        /// The session slot.
        slot: u64,
    },
    /// The gate asked the ledger for `n` bytes for `segments` datagrams of `len` bytes in total.
    #[cfg(feature = "trace")]
    TxGate {
        /// The destination, hashed to a number.
        dest: u64,
        /// The bytes of the datagrams.
        len: u64,
        /// How many datagrams.
        segments: u64,
        /// The bytes the ledger was asked for.
        n: u64,
        /// 1 if the ledger let them out, 0 if it held them.
        allowed: u64,
    },
    /// A datagram was dropped: `slot` for the loop's path with no address, `u64::MAX` for the kept datagram.
    #[cfg(feature = "trace")]
    TxDrop {
        /// The session slot, or `u64::MAX`.
        slot: u64,
    },
    /// A session was put at the back of a send queue (0 ordinary, 1 broadcast).
    #[cfg(feature = "trace")]
    TxMark {
        /// The session slot.
        slot: u64,
        /// The queue.
        queue: u64,
    },
    /// A reject of the endpoint's own was returned for sending.
    #[cfg(feature = "trace")]
    TxReject {
        /// The destination, hashed to a number.
        dest: u64,
        /// The datagram's length.
        len: u64,
        /// The datagram's segment size.
        seg: u64,
    },
    /// The endpoint made call `call` on the connection of session `slot` for an interface event or a suspension: 1
    /// link down, 2 link back, 3 sleep, 4 wake, 5 closed for a redial, 6 a path rebound to the new address, 7 a path
    /// replaced (added from the new address, the old one lost).
    #[cfg(feature = "trace")]
    Iface {
        /// The session slot.
        slot: u64,
        /// The call.
        call: u64,
    },
    /// A step of a quiet-parent probe (`QUIET_PROBE`): 0 started, 1 the settle gate saw the probed session heard,
    /// 2 a probe rode, 3 a probe lapsed, 4 a ride failed, 5 a command kept while probing, 6 a kept command applied,
    /// 7 a probe ended by the application, 8 a dial read the session it would ride or probe. `gen` is the
    /// generation of the probed slot now, `of_gen` the one the probe names. `bits`: 1 pulse, 2 heard within
    /// `PARENT_RX`, 4 packets in flight, 8 closed by the lapse, 16 and 32 the first address of a lapse (0 none, 1
    /// the caller's, 2 the session's own, 3 a wait on another handshake, in bits 4 and 5), 64 the slot holds the
    /// generation the probe names, 256 to 1024 the command (1 paths, 2 resend, 3 hold, 4 unhold, in bits 8 to 10).
    #[cfg(feature = "trace")]
    Probe {
        /// The step.
        step: u64,
        /// The dial's slot, or `u64::MAX`.
        child: u64,
        /// The generation of the probed slot now.
        r#gen: u64,
        /// The generation the probe names.
        of_gen: u64,
        /// The facts and outcome.
        bits: u64,
    },
}

impl TraceEvent {
    /// The name the line carries.
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Demux { .. } => "demux",
            Self::Trial { .. } => "trial",
            Self::LedgerRx { .. } => "ledger_rx",
            Self::LedgerTx { .. } => "ledger_tx",
            Self::HalfOpen { .. } => "half_open",
            Self::HalfOpenExpired { .. } => "half_open_expired",
            Self::Acp { .. } => "acp",
            Self::Gate { .. } => "gate",
            Self::Early { .. } => "early",
            Self::Sub { .. } => "sub",
            Self::Keepalive { .. } => "keepalive",
            Self::Rtt { .. } => "rtt",
            Self::Session { .. } => "session",
            #[cfg(feature = "trace")]
            Self::TxConn { .. } => "tx_conn",
            #[cfg(feature = "trace")]
            Self::TxGone { .. } => "tx_gone",
            #[cfg(feature = "trace")]
            Self::TxGate { .. } => "tx_gate",
            #[cfg(feature = "trace")]
            Self::TxDrop { .. } => "tx_drop",
            #[cfg(feature = "trace")]
            Self::TxMark { .. } => "tx_mark",
            #[cfg(feature = "trace")]
            Self::TxReject { .. } => "tx_reject",
            #[cfg(feature = "trace")]
            Self::Iface { .. } => "iface",
            #[cfg(feature = "trace")]
            Self::Probe { .. } => "probe",
        }
    }

    /// The named fields, in order, and how many there are.
    pub const fn fields(&self) -> ([(&'static str, u64); 5], usize) {
        const NONE: (&str, u64) = ("", 0);
        match *self {
            Self::Demux { slot, candidates } => ([("slot", slot), ("candidates", candidates), NONE, NONE, NONE], 2),
            Self::Trial { slot, ok } => ([("slot", slot), ("ok", ok), NONE, NONE, NONE], 2),
            Self::LedgerRx { addr, rx } => ([("addr", addr), ("rx", rx), NONE, NONE, NONE], 2),
            Self::LedgerTx { addr, allowed, rx, tx } => {
                ([("addr", addr), ("allowed", allowed), ("rx", rx), ("tx", tx), NONE], 4)
            }
            Self::HalfOpen {
                admitted,
                half_open,
                resume,
                room,
                owed,
            } => (
                [
                    ("admitted", admitted),
                    ("half_open", half_open),
                    ("resume", resume),
                    ("room", room),
                    ("owed", owed),
                ],
                5,
            ),
            Self::HalfOpenExpired { slot } => ([("slot", slot), NONE, NONE, NONE, NONE], 1),
            #[cfg(feature = "trace")]
            Self::TxGone { slot } | Self::TxDrop { slot } => ([("slot", slot), NONE, NONE, NONE, NONE], 1),
            Self::Acp { slot, step } => ([("slot", slot), ("step", step), NONE, NONE, NONE], 2),
            Self::Gate { slot, release, held } => {
                ([("slot", slot), ("release", release), ("held", held), NONE, NONE], 3)
            }
            Self::Early { slot, rule } => ([("slot", slot), ("rule", rule), NONE, NONE, NONE], 2),
            Self::Sub { step, parent, child } => {
                ([("step", step), ("parent", parent), ("child", child), NONE, NONE], 3)
            }
            Self::Keepalive {
                slot,
                ping_at,
                review_at,
            } => (
                [
                    ("slot", slot),
                    ("ping_at", ping_at),
                    ("review_at", review_at),
                    NONE,
                    NONE,
                ],
                3,
            ),
            Self::Rtt { lrtt, tgr, hs_floor } => {
                ([("lrtt", lrtt), ("tgr", tgr), ("hs_floor", hs_floor), NONE, NONE], 3)
            }
            Self::Session { slot, step, dialer } => {
                ([("slot", slot), ("step", step), ("dialer", dialer), NONE, NONE], 3)
            }
            #[cfg(feature = "trace")]
            Self::TxConn {
                slot,
                room,
                len,
                seg,
                dest,
            } => (
                [
                    ("slot", slot),
                    ("room", room),
                    ("len", len),
                    ("seg", seg),
                    ("dest", dest),
                ],
                5,
            ),
            #[cfg(feature = "trace")]
            Self::TxGate {
                dest,
                len,
                segments,
                n,
                allowed,
            } => (
                [
                    ("dest", dest),
                    ("len", len),
                    ("segments", segments),
                    ("n", n),
                    ("allowed", allowed),
                ],
                5,
            ),
            #[cfg(feature = "trace")]
            Self::TxMark { slot, queue } => ([("slot", slot), ("queue", queue), NONE, NONE, NONE], 2),
            #[cfg(feature = "trace")]
            Self::TxReject { dest, len, seg } => ([("dest", dest), ("len", len), ("seg", seg), NONE, NONE], 3),
            #[cfg(feature = "trace")]
            Self::Iface { slot, call } => ([("slot", slot), ("call", call), NONE, NONE, NONE], 2),
            #[cfg(feature = "trace")]
            Self::Probe {
                step,
                child,
                r#gen,
                of_gen,
                bits,
            } => (
                [
                    ("step", step),
                    ("child", child),
                    ("gen", r#gen),
                    ("of_gen", of_gen),
                    ("bits", bits),
                ],
                5,
            ),
        }
    }
}

/// One trace line: when and what.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceRecord {
    /// The time of the call that decided, in nanoseconds of the host clock.
    pub t: u64,
    /// What was decided.
    pub event: TraceEvent,
}

impl TraceRecord {
    /// Write the record as one line of ndjson: `{"t":..,"ev":"..", <fields>}` followed by a newline.
    ///
    /// # Errors
    /// The writer's error.
    pub fn write_ndjson(&self, out: &mut impl fmt::Write) -> fmt::Result {
        write!(out, "{{\"t\":{},\"ev\":\"{}\"", self.t, self.event.name())?;
        let (fields, n) = self.event.fields();
        for (name, value) in fields.iter().take(n) {
            write!(out, ",\"{name}\":{value}")?;
        }
        out.write_str("}\n")
    }
}

/// The bounded ring of records; an empty type without the `trace` feature.
#[cfg(feature = "trace")]
#[derive(Debug)]
pub(crate) struct TraceLog {
    ring: [Option<TraceRecord>; TRACE_CAPACITY],
    head: usize,
    len: usize,
    dropped: u64,
    /// The settle records, kept beside the trace records.
    pub(crate) settles: crate::timers::SettleLog,
}

#[cfg(feature = "trace")]
impl TraceLog {
    pub(crate) const fn new() -> Self {
        Self {
            ring: [None; TRACE_CAPACITY],
            head: 0,
            len: 0,
            dropped: 0,
            settles: crate::timers::SettleLog::new(),
        }
    }

    pub(crate) fn push(&mut self, t: u64, event: TraceEvent) {
        if self.len == TRACE_CAPACITY {
            self.head = (self.head + 1) % TRACE_CAPACITY;
            self.len -= 1;
            self.dropped += 1;
        }
        let at = (self.head + self.len) % TRACE_CAPACITY;
        if let Some(s) = self.ring.get_mut(at) {
            *s = Some(TraceRecord { t, event });
            self.len += 1;
        }
    }

    pub(crate) fn pop(&mut self) -> Option<TraceRecord> {
        if self.len == 0 {
            return None;
        }
        let r = self.ring.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % TRACE_CAPACITY;
        self.len -= 1;
        r
    }

    pub(crate) const fn dropped(&self) -> u64 {
        self.dropped
    }
}

#[cfg(not(feature = "trace"))]
#[derive(Debug)]
pub(crate) struct TraceLog;

#[cfg(not(feature = "trace"))]
impl TraceLog {
    pub(crate) const fn new() -> Self {
        Self
    }

    #[allow(clippy::unused_self)] // the stub keeps the signature of the real log
    pub(crate) fn pop(&mut self) -> Option<TraceRecord> {
        None
    }

    #[allow(clippy::unused_self)] // the stub keeps the signature of the real log
    pub(crate) const fn dropped(&self) -> u64 {
        0
    }
}

/// Record a decision, named by the variant of [`TraceEvent`]; compiles to nothing without the `trace` feature.
macro_rules! trace {
    ($self:expr, $now:expr, $($event:tt)*) => {
        #[cfg(feature = "trace")]
        {
            $self.trace.push($now, $crate::TraceEvent::$($event)*);
        }
        #[cfg(not(feature = "trace"))]
        {
            let _ = &$now;
        }
    };
}
pub(crate) use trace;
