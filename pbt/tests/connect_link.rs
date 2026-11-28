//! `pinc-connect` client: the timing machine of one relay carrier ([`Link`]), driven by a host that follows the
//! contract of each `Act`, with every step checked against the invariants of the module doc.
//!
//! Where the expected behaviour comes from (`client::link`, module doc):
//! - "Invariants: `lease_hi` never rises; the retry wait is 1 s or 2 s; `Open` is reached only through
//!   [`Link::opened`]; every deadline returned by [`Link::next_deadline`] is the first instant [`Link::tick`] can
//!   act." The last one is checked both ways: `tick` at any instant from now to just before the deadline does
//!   nothing, `tick` at the deadline does something; and `next_deadline` returns "`None` when nothing is scheduled",
//!   so `tick` long after does nothing either.
//! - "A dial that fails or a stream that closes retries after 1 s, then 2 s, and stays at 2 s until a stream opens
//!   (which resets the wait to 1 s)." (a model of the retry wait).
//! - `tick`: "Returns what the host must do, if anything; call again until it returns `None`", and `Act::Check`:
//!   "write a PING, or let the next ack-eliciting session packet that leaves on it carry the check and call
//!   [`Link::check`] with `ridden`": the host of this test does exactly that, as `Connectivity` does
//!   (`client/carriers.rs`, `act`).

use ephyra::prelude::*;
use pinc_connect::client::link::{Act, Ctx, Link, Shared, State, rule};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000_000_000;
/// The start: a monotonic clock well past 0, as a host's is.
const T0: u64 = 1_000 * SEC;
/// How far past `now` a `None` deadline is checked: longer than every rule of the machine.
const LATER: u64 = 3_600 * SEC;
/// The most acts one tick may chain; the machine needs at most two (a ridden check that falls back to a PING).
const ACTS: usize = 8;

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    /// Time passes.
    Time(#[ephyra(gen = dt())] u64),
    /// What the node tells the link changes.
    Ctx {
        home: bool,
        rides: bool,
        queued: bool,
        #[ephyra(gen = gens::bool_with(0.3))]
        udp_any: bool,
        #[ephyra(gen = gens::pick_from(vec![0, 20 * MS, 400 * MS, SEC, 2 * SEC, 5 * SEC]))]
        rtt: u64,
    },
    /// The host runs the timers now; `ridden` says a session packet leaves in the same step.
    Tick(bool),
    /// The host sleeps until the deadline the link reported, then runs the timers.
    Wake(bool),
    /// The dial in progress opened.
    Opened,
    /// The dial in progress failed.
    DialFailed,
    /// The open stream ended.
    StreamClosed,
    /// Bytes arrived.
    Heard,
    /// The host wrote a frame.
    Wrote,
    /// A frame is about to be written (STALE_SEND first).
    Send,
    /// A quiet hub session asks the carrier to pulse.
    Pulse,
}

fn dt() -> ephyra::BoxGen<u64> {
    gens::frequency(vec![
        (
            5,
            gens::pick_from(vec![
                0,
                1,
                MS,
                599 * MS,
                600 * MS,
                SEC,
                2 * SEC,
                3 * SEC,
                8 * SEC,
                15 * SEC,
                30 * SEC,
                65 * SEC,
                300 * SEC,
                570 * SEC,
                600 * SEC,
            ])
            .boxed(),
        ),
        (3, gens::int(0u64..=700 * SEC).boxed()),
    ])
    .boxed()
}

/// The node's facts at the start: a phone, KEEP_LEARN on, a restart.
fn start() -> impl Gen<Value = (bool, bool, bool)> {
    (gens::bool_with(0.3), gens::bool_with(0.3), gens::bool_with(0.3))
}

#[derive(Clone)]
struct Host {
    link: Link,
    sh: Shared,
    ctx: Ctx,
    now: u64,
}

impl Host {
    /// Do what `act` asks, as the contract of [`Act`] says.
    fn act(&mut self, act: Act, ridden: bool) {
        match act {
            // The link moved to `Dialing` itself; the host opens a stream and reports back later.
            Act::Dial => {}
            // The link is already down; the host closes the stream and reports nothing (a close of a stream the
            // link put down is not a new failure: `Connectivity::stream_closed` ignores it).
            Act::Close => {}
            Act::Ping => self.link.wrote(self.now),
            Act::Check => {
                if ridden {
                    // the session packet that carries the check is a write
                    self.link.wrote(self.now);
                }
                if self.link.check(self.now, &self.ctx, ridden) == Some(Act::Ping) {
                    self.link.wrote(self.now);
                }
            }
        }
    }

    /// Run the timers as a host does: until `tick` returns `None`. Returns how many acts it took.
    fn tick(&mut self, ridden: bool) -> usize {
        for n in 0..ACTS {
            match self.link.tick(self.now, &mut self.sh, &self.ctx) {
                Some(a) => self.act(a, ridden),
                None => return n,
            }
        }
        ACTS
    }
}

/// What a tick on a copy of the state does at `t`, the state itself untouched.
fn acts_at(h: &Host, t: u64) -> Option<Act> {
    let (mut link, mut sh) = (h.link, h.sh);
    link.tick(t, &mut sh, &h.ctx)
}

/// A name for the state a deadline was wrong in, so the distinct causes are reported apart.
fn cause(h: &Host) -> String {
    let lease = h.sh.lease_hi != 0 && !h.ctx.udp_any;
    match h.link.state() {
        State::Down => format!(
            "down, restarted {}, home {}, queued {}",
            h.sh.restarted, h.ctx.home, h.ctx.queued
        ),
        State::Dialing => "dialing".to_owned(),
        State::Open => format!(
            "open, phone {}, keep_fail {}, keep_iv {}, lease {lease}",
            h.sh.phone,
            h.sh.keep_fail.is_some(),
            h.sh.keep_iv != 0
        ),
    }
}

/// One carrier under a host that follows the contract, with every step checked: the deadline is the first instant
/// `tick` acts (nothing before, something at it, nothing ever when there is none), `lease_hi` never rises, the retry
/// wait is 1 s or 2 s and follows the 1 s, 2 s, 2 s rule, and `Open` is reached only through `opened`.
#[ephyra::test(gen = (start(), gens::vec(ephyra::any::<Op>()).len(1..=60)), tests = 3000)]
fn the_link_deadline_is_the_first_instant_tick_acts(input: ((bool, bool, bool), Vec<Op>)) {
    let ((phone, keep_learn, restarted), ops) = input;
    let mut h = Host {
        link: Link::new(),
        sh: Shared {
            phone,
            keep_learn,
            restarted,
            ..Shared::default()
        },
        ctx: Ctx {
            home: true,
            rtt: 0,
            udp_any: false,
            rides: false,
            queued: false,
        },
        now: T0,
    };
    // The model of the retry wait: 1 s after an open (and at the start), doubling to 2 s at each failure.
    let mut retry = rule::RETRY_MIN;
    for (step, op) in ops.iter().enumerate() {
        let before = h.link.state();
        let lease_before = h.sh.lease_hi;
        let mut opened = false;
        match *op {
            Op::Time(d) => h.now = h.now.saturating_add(d),
            Op::Ctx {
                home,
                rides,
                queued,
                udp_any,
                rtt,
            } => {
                // A UDP datagram once heard stays heard.
                let udp_any = udp_any || h.ctx.udp_any;
                h.ctx = Ctx {
                    home,
                    rides,
                    queued,
                    udp_any,
                    rtt,
                };
            }
            Op::Tick(ridden) => {
                h.tick(ridden);
            }
            Op::Wake(ridden) => {
                if let Some(d) = h.link.next_deadline(h.now, &h.sh, &h.ctx) {
                    h.now = h.now.max(d);
                }
                h.tick(ridden);
            }
            Op::Opened => {
                if h.link.state() == State::Dialing {
                    h.link.opened(h.now);
                    opened = true;
                    retry = rule::RETRY_MIN;
                }
            }
            Op::DialFailed | Op::StreamClosed => {
                let want = if matches!(op, Op::DialFailed) {
                    State::Dialing
                } else {
                    State::Open
                };
                if h.link.state() == want {
                    h.link.closed(h.now);
                    assert_eq!(
                        h.link.state(),
                        State::Down,
                        "step {step}: a closed stream puts the link down"
                    );
                    let d = h.link.next_deadline(h.now, &h.sh, &h.ctx);
                    if (h.ctx.home || h.ctx.queued) && !h.sh.restarted {
                        assert_eq!(
                            d,
                            Some(h.now + retry),
                            "step {step}: the dial is retried after {retry} ns"
                        );
                    }
                    retry = (retry * 2).min(rule::RETRY_MAX);
                }
            }
            Op::Heard => {
                if h.link.state() != State::Down {
                    h.link.heard(h.now);
                }
            }
            Op::Wrote => {
                if h.link.state() == State::Open {
                    h.link.wrote(h.now);
                }
            }
            Op::Send => {
                if h.link.before_send(h.now, &h.sh, &h.ctx).is_none() && h.link.state() == State::Open {
                    h.link.wrote(h.now);
                }
            }
            Op::Pulse => {
                if h.link.pulse(h.now, &h.ctx) == pinc_connect::client::link::Pulse::Ping {
                    h.link.wrote(h.now);
                }
            }
        }

        assert!(
            h.link.retry() == rule::RETRY_MIN || h.link.retry() == rule::RETRY_MAX,
            "step {step}: the retry wait is {} ns",
            h.link.retry()
        );
        assert_eq!(
            h.link.retry(),
            retry,
            "step {step}: the retry wait follows 1 s, 2 s, 2 s"
        );
        if lease_before != 0 {
            assert!(
                h.sh.lease_hi <= lease_before,
                "step {step}: lease_hi rose from {lease_before} to {}",
                h.sh.lease_hi
            );
        }
        if h.link.state() == State::Open && before != State::Open {
            assert!(opened, "step {step}: {op:?} made the link open without `opened`");
        }

        let now = h.now;
        match h.link.next_deadline(now, &h.sh, &h.ctx) {
            Some(d) if d > now => {
                let early = acts_at(&h, now);
                assert_eq!(
                    early,
                    None,
                    "step {step}: tick acts at {now}, before the deadline {d} ({})",
                    cause(&h)
                );
                let late = acts_at(&h, d - 1);
                assert_eq!(
                    late,
                    None,
                    "step {step}: tick acts at {}, before the deadline {d} ({})",
                    d - 1,
                    cause(&h)
                );
                if acts_at(&h, d).is_none() {
                    ephyra::signature(format!("nothing done at the deadline: {}", cause(&h)));
                }
                assert!(
                    acts_at(&h, d).is_some(),
                    "step {step}: tick does nothing at the deadline {d} ({})",
                    cause(&h)
                );
            }
            Some(d) => {
                if acts_at(&h, now).is_none() {
                    ephyra::signature(format!("nothing done at a past deadline: {}", cause(&h)));
                }
                assert!(
                    acts_at(&h, now).is_some(),
                    "step {step}: the deadline {d} is not after {now} and tick does nothing ({})",
                    cause(&h)
                );
            }
            None => {
                let at = acts_at(&h, now + LATER);
                assert_eq!(
                    at,
                    None,
                    "step {step}: no deadline, yet tick acts later ({})",
                    cause(&h)
                );
            }
        }
    }
}
