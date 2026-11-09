//! One direction of a path between two sites: delay, jitter, reordering, loss, duplication, bandwidth and MTU.
//!
//! The default behaviour is the reference profile: constant delay, no jitter, no reordering, no duplication, a drop-tail
//! queue measured on the backlog ahead of a datagram, a datagram that is lost still using up line time, and loss
//! decided at the serialisation start. Jitter, reordering, duplication and per-datagram loss are opt-in extras.
//!
//! Invariants: without an explicit reorder draw a link delivers in send order (jitter only lengthens the queue, it
//! never lets a packet overtake); every random choice comes from the link's own stream, so changing another link
//! cannot change this one's draws.

use crate::Time;
use crate::metrics::DropReason;
use crate::rng::Random;

/// A loss model.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Loss {
    /// No loss.
    None,
    /// Each datagram is lost independently with this probability.
    Bernoulli(f64),
    /// Time-based burst loss: a Good/Bad process whose sojourns are exponential with mean `burst` (Bad, everything
    /// lost) and `burst * (1 - loss) / loss` (Good), each at least 1 microsecond. A datagram is lost iff its
    /// serialisation start falls in a Bad sojourn, so the long-run loss rate is `loss`.
    Timed {
        /// The long-run loss rate; 0 or less disables the model.
        loss: f64,
        /// Mean length of a loss burst in nanoseconds.
        burst: Time,
    },
    /// Two-state per-datagram burst model: per datagram the state may flip, then the datagram is lost with the state's rate.
    GilbertElliott {
        /// Probability of moving from the good to the bad state per datagram.
        good_to_bad: f64,
        /// Probability of moving from the bad to the good state per datagram.
        bad_to_good: f64,
        /// Loss probability in the good state.
        loss_good: f64,
        /// Loss probability in the bad state.
        loss_bad: f64,
    },
}

/// The behaviour of one direction of a link. The default is an ideal wire with a 65535-byte MTU.
#[derive(Clone, Debug, PartialEq)]
pub struct LinkConfig {
    /// One-way propagation delay in nanoseconds.
    pub delay: Time,
    /// Extra queueing delay drawn uniformly from `[0, jitter]`; delivery stays in send order.
    pub jitter: Time,
    /// Probability that a datagram is held back and so overtaken (0 means the link never reorders).
    pub reorder_prob: f64,
    /// How many `reorder_slot` periods a reordered datagram is held back.
    pub reorder_depth: u32,
    /// The length of one reorder slot in nanoseconds.
    pub reorder_slot: Time,
    /// The loss model.
    pub loss: Loss,
    /// Probability that a datagram is delivered twice.
    pub dup_prob: f64,
    /// Line rate in bits per second; 0 means unlimited.
    pub bandwidth_bps: u64,
    /// Drop-tail queue size in bytes (waiting plus in service); used only with a bandwidth cap.
    pub queue_bytes: usize,
    /// Largest datagram carried; larger ones are dropped silently.
    pub mtu: usize,
    /// When true every datagram is dropped (UDP blocked, an outage).
    pub blocked: bool,
}

impl Default for LinkConfig {
    fn default() -> Self {
        Self {
            delay: 0,
            jitter: 0,
            reorder_prob: 0.0,
            reorder_depth: 0,
            reorder_slot: 1_000_000,
            loss: Loss::None,
            dup_prob: 0.0,
            bandwidth_bps: 0,
            queue_bytes: 1 << 20,
            mtu: 65_535,
            blocked: false,
        }
    }
}

/// A change applied to a link at a scheduled time.
#[derive(Clone, Debug, PartialEq)]
pub enum LinkChange {
    /// Replace the whole configuration.
    Config(LinkConfig),
    /// Start or end an outage (or a UDP block).
    Blocked(bool),
    /// Set the MTU.
    Mtu(usize),
    /// Set the line rate (a bandwidth step); 0 means unlimited.
    Bandwidth(u64),
    /// Set the propagation delay.
    Delay(Time),
    /// Set the loss model.
    Loss(Loss),
}

/// What a link did with a datagram.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fate {
    Drop(DropReason),
    Sent { at: Time, dup_at: Option<Time> },
}

/// The lazily extended Good/Bad history of a [`Loss::Timed`] link.
#[derive(Default)]
struct Timed {
    ends: Vec<Time>,
    trimmed: u64,
}

impl Timed {
    /// Entries kept before the oldest half is dropped, and how many are dropped (an even number keeps the parity).
    const KEEP: usize = 8192;
    const TRIM: usize = 4096;

    fn lost<R: Random>(&mut self, rng: &mut R, t: Time, loss: f64, burst: Time) -> bool {
        if loss <= 0.0 {
            return false;
        }
        let mean_bad = burst as f64;
        let mean_good = mean_bad * (1.0 - loss) / loss;
        while self.ends.last().is_none_or(|e| *e <= t) {
            let bad = (self.trimmed + self.ends.len() as u64) % 2 == 1;
            let mean = if bad { mean_bad } else { mean_good };
            let dur = (rng.expovariate(1.0 / mean.max(1.0)) as Time).max(1000);
            self.ends.push(self.ends.last().copied().unwrap_or(0) + dur);
        }
        let i = self.ends.partition_point(|e| *e <= t);
        let bad = (self.trimmed + i as u64) % 2 == 1;
        if self.ends.len() > Self::KEEP {
            self.ends.drain(..Self::TRIM);
            self.trimmed += Self::TRIM as u64;
        }
        bad
    }
}

pub(crate) struct Link<R: Random> {
    pub(crate) cfg: LinkConfig,
    rng: R,
    bad: bool,
    timed: Timed,
    next_free: Time,
    last_deliver: Time,
    pub(crate) observer: Option<u32>,
}

impl<R: Random> Link<R> {
    pub(crate) fn new(cfg: LinkConfig, rng: R) -> Self {
        Self {
            cfg,
            rng,
            bad: false,
            timed: Timed::default(),
            next_free: 0,
            last_deliver: 0,
            observer: None,
        }
    }

    pub(crate) fn apply(&mut self, change: LinkChange) {
        match change {
            LinkChange::Config(c) => {
                self.timed = Timed::default();
                self.cfg = c;
            }
            LinkChange::Blocked(b) => self.cfg.blocked = b,
            LinkChange::Mtu(m) => self.cfg.mtu = m,
            LinkChange::Bandwidth(b) => self.cfg.bandwidth_bps = b,
            LinkChange::Delay(d) => self.cfg.delay = d,
            LinkChange::Loss(l) => {
                self.timed = Timed::default();
                self.cfg.loss = l;
            }
        }
    }

    fn lost(&mut self, start: Time) -> bool {
        match self.cfg.loss {
            Loss::None => false,
            Loss::Bernoulli(p) => self.rng.chance(p),
            Loss::Timed { loss, burst } => self.timed.lost(&mut self.rng, start, loss, burst),
            Loss::GilbertElliott {
                good_to_bad,
                bad_to_good,
                loss_good,
                loss_bad,
            } => {
                if self.bad {
                    self.bad = !self.rng.chance(bad_to_good);
                } else {
                    self.bad = self.rng.chance(good_to_bad);
                }
                self.rng.chance(if self.bad { loss_bad } else { loss_good })
            }
        }
    }

    /// Queues one copy: drop-tail on the backlog ahead of it, serialisation, then the loss draw at the start of
    /// serialisation (a lost datagram has still used its line time).
    fn schedule(&mut self, now: Time, len: usize) -> Result<Time, DropReason> {
        let mut start = now;
        let mut ser = 0;
        if self.cfg.bandwidth_bps > 0 {
            let bps = self.cfg.bandwidth_bps as f64;
            start = self.next_free.max(now);
            if (u128::from(start - now) * u128::from(self.cfg.bandwidth_bps)) as f64 / 8e9 > self.cfg.queue_bytes as f64
            {
                return Err(DropReason::QueueFull);
            }
            ser = (len as f64 * 8e9 / bps) as Time;
            self.next_free = start + ser;
        }
        if self.lost(start) {
            return Err(DropReason::Loss);
        }
        let jitter = if self.cfg.jitter > 0 {
            self.rng.below(self.cfg.jitter + 1)
        } else {
            0
        };
        let at = start + ser + self.cfg.delay + jitter;
        if self.cfg.reorder_depth > 0 && self.rng.chance(self.cfg.reorder_prob) {
            return Ok(at + Time::from(self.cfg.reorder_depth) * self.cfg.reorder_slot);
        }
        let at = at.max(self.last_deliver);
        self.last_deliver = at;
        Ok(at)
    }

    pub(crate) fn send(&mut self, now: Time, len: usize) -> Fate {
        if self.cfg.blocked {
            return Fate::Drop(DropReason::Blocked);
        }
        if len > self.cfg.mtu {
            return Fate::Drop(DropReason::Mtu);
        }
        let dup = self.rng.chance(self.cfg.dup_prob);
        match self.schedule(now, len) {
            Err(why) => Fate::Drop(why),
            Ok(at) => Fate::Sent {
                at,
                dup_at: if dup { self.schedule(now, len).ok() } else { None },
            },
        }
    }
}

impl LinkConfig {
    /// The reference profile of a link: constant `delay`, line rate `bandwidth_bps`, a drop-tail queue of
    /// `queue_bytes`, and time-based burst loss with long-run rate `loss` and mean burst `burst` (no loss if `loss`
    /// is 0). No jitter, reordering or duplication.
    pub fn reference(bandwidth_bps: u64, delay: Time, queue_bytes: usize, loss: f64, burst: Time) -> Self {
        let loss = if loss > 0.0 {
            Loss::Timed { loss, burst }
        } else {
            Loss::None
        };
        Self {
            delay,
            loss,
            bandwidth_bps,
            queue_bytes,
            ..Self::default()
        }
    }
}

/// The reference queue size for a home or mobile site: `max(64 KiB, down_bps / 8 / 4)` bytes.
pub fn reference_queue_bytes(down_bps: u64) -> usize {
    (65_536.0_f64).max(down_bps as f64 / 8.0 * 0.25) as usize
}
