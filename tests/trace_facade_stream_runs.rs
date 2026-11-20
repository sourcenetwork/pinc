//! The fixed and the seeded runs of `trace_facade_stream.rs`, split out below the file limit; included with `#[path]`, not a test target.

use super::*;

// ---- the fixed runs of the code as written ----

pub(super) fn fixed<H: Hosted + 'static>(n: u32, t: &mut T<H>) {
    t.begin();
    match n {
        1 => {
            expect(t.read(), (0, 0, 0), "the chunk the peer wrote first");
            expect(t.read(), (3, 0, 0), "nothing more yet");
            t.psend();
            t.read();
            t.pfin();
            expect(t.read(), (1, 0, 0), "the end after the last chunk");
            expect(t.read(), (1, 0, 0), "the end again");
            t.held();
        }
        2 => {
            t.write();
            t.write();
            expect(t.pread(), (3, 0, 0), "the peer reads what was written and waits");
            assert_eq!(t.p.read.get(), 2);
            expect(t.finish_s(), (0, 0, 0), "finish");
            expect(t.finish_s(), (0, 0, 0), "a second finish is Ok");
            expect(t.write(), (2, KIND_STOPPED, 0), "a write after finish");
            let r = t.pread();
            expect(r, (1, 0, 0), "the peer sees the end");
            assert_eq!(r.v, t.writes_ok, "the peer read what the subject wrote");
        }
        3 => {
            t.write();
            t.pstop();
            expect(t.write(), (2, KIND_STOPPED, PC), "a write after the peer's stop");
            expect(t.finish_s(), (2, KIND_STOPPED, PC), "finish after the peer's stop");
            t.dsend();
            expect(t.pread(), (2, KIND_STOPPED, PC), "the peer's read after its own stop");
        }
        4 => {
            t.psend();
            t.preset();
            let r = t.read();
            assert!(
                r.r == 2 && r.k == KIND_RESET && r.c == PR,
                "the transport hands out the chunks before a reset; the model discards them and needs the fix round"
            );
            expect(t.read(), (2, KIND_RESET, PR), "the reset again, cached");
            t.held();
        }
        5 => {
            t.psend();
            t.stop();
            expect(t.read(), (2, KIND_STOPPED, SC), "a read after stop");
            t.held();
        }
        6 => {
            t.psend();
            t.psend();
            t.drecv();
            t.held();
            t.psend();
            t.held();
            t.pfin();
        }
        7 => {
            expect(t.rdg(true), (3, 0, 0), "no datagram yet");
            t.pdg();
            expect(t.rdg(false), (2, KIND_TOO_LARGE, 0), "a datagram that does not fit");
            let r = t.rdg(true);
            assert_eq!((r.r, r.v), (0, 1), "the datagram that did not fit is still queued");
            for _ in 0..66 {
                t.pdg();
            }
            let first = t.rdg(true);
            assert_eq!((first.r, first.v), (0, 4), "the two oldest datagrams were dropped");
            for want in 5..=67 {
                let r = t.rdg(true);
                assert_eq!((r.r, r.v), (0, want), "datagrams are read in order: {:?}", (r.k, r.c));
            }
            expect(t.rdg(true), (3, 0, 0), "the queue is empty");
            t.sdg(false);
            expect(t.sdg(true), (2, KIND_TOO_LARGE, 0), "a datagram too large to send");
        }
        8 => {
            t.write();
            t.dsend();
            // The drop only queues the end of the stream; the driver sends it when it next wakes, so the peer reads
            // it after some virtual time.
            for _ in 0..300 {
                let Out::Res(r) = t.finish(peer_read(Rc::clone(&t.p))) else {
                    panic!("no result")
                };
                if r.r != 3 {
                    break;
                }
            }
            let r = t.pread();
            expect(r, (1, 0, 0), "the drop finished the stream");
            assert_eq!(r.v, 1, "the peer saw exactly one chunk");
        }
        9 => {
            t.pdg();
            t.pclose();
            expect(
                t.rdg(true),
                (2, KIND_CLOSED_BY_PEER, PCC),
                "a datagram read after the peer's close",
            );
            expect(t.read(), (2, KIND_CLOSED_BY_PEER, PCC), "a read after the peer's close");
            expect(
                t.write(),
                (2, KIND_CLOSED_BY_PEER, PCC),
                "a write after the peer's close",
            );
            expect(
                t.sdg(false),
                (2, KIND_CLOSED_BY_PEER, PCC),
                "a send after the peer's close",
            );
        }
        _ => {
            t.close();
            expect(t.read(), (2, KIND_CLOSED_LOCAL, LC), "a read after close");
            expect(t.finish_s(), (2, KIND_CLOSED_LOCAL, LC), "finish after close");
        }
    }
}

/// What a seeded run may do next.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Step {
    Write,
    Finish,
    Reset,
    Dsend,
    Read,
    Stop,
    Drecv,
    Rdg,
    Sdg,
    Psend,
    Pfin,
    Preset,
    Pstop,
    Pdg,
    Pread,
    Held,
    Close,
    Pclose,
}

/// The steps with the last roll each covers, in the order a guard that fails moves on.
const STEPS: [(u64, Step); 18] = [
    (11, Step::Write),
    (15, Step::Finish),
    (17, Step::Reset),
    (19, Step::Dsend),
    (31, Step::Read),
    (33, Step::Stop),
    (35, Step::Drecv),
    (41, Step::Rdg),
    (45, Step::Sdg),
    (61, Step::Psend),
    (64, Step::Pfin),
    (66, Step::Preset),
    (68, Step::Pstop),
    (80, Step::Pdg),
    (89, Step::Pread),
    (97, Step::Held),
    (98, Step::Close),
    (99, Step::Pclose),
];

/// What the guards of a seeded run read.
#[derive(Default)]
struct Guards {
    writes: u32,
    finished: bool,
    s_held: bool,
    r_held: bool,
    stopped: bool,
    psends: u32,
    pdgs: u32,
    pend: bool,
    pstopped: bool,
}

impl Guards {
    fn ok(&self, step: Step, live: bool) -> bool {
        let peer_may_send = live && !self.pend && !self.stopped && self.psends < 30;
        match step {
            Step::Write => self.s_held && self.writes < 30,
            Step::Finish | Step::Dsend => self.s_held,
            Step::Reset => self.s_held && !self.finished,
            Step::Read | Step::Drecv => self.r_held,
            Step::Stop => self.r_held && !self.stopped,
            Step::Rdg | Step::Sdg | Step::Held => true,
            Step::Psend | Step::Pfin | Step::Preset => peer_may_send,
            Step::Pstop => live && !self.pstopped,
            Step::Pdg => live && self.pdgs < 100,
            Step::Pread | Step::Close | Step::Pclose => live,
        }
    }
}

pub(super) fn seeded<H: Hosted + 'static>(t: &mut T<H>, seed: u64) {
    t.begin();
    let mut rng = SplitMix64::traced(seed);
    let mut g = Guards {
        s_held: true,
        r_held: true,
        ..Guards::default()
    };
    for _ in 0..60 {
        let roll = rng.next_u64() % 100;
        let live = t.live();
        let first = STEPS.iter().position(|(last, _)| roll <= *last).unwrap_or(0);
        let Some(step) = (0..STEPS.len())
            .map(|i| STEPS[(first + i) % STEPS.len()].1)
            .find(|s| g.ok(*s, live))
        else {
            return;
        };
        match step {
            Step::Write => {
                g.writes += 1;
                t.write();
            }
            Step::Finish => {
                g.finished = true;
                t.finish_s();
            }
            Step::Reset => {
                g.finished = true;
                t.reset();
            }
            Step::Dsend => {
                g.s_held = false;
                t.dsend();
            }
            Step::Read => {
                t.read();
            }
            Step::Stop => {
                g.stopped = true;
                t.stop();
            }
            Step::Drecv => {
                g.r_held = false;
                t.drecv();
            }
            Step::Rdg => {
                t.rdg(!rng.next_u64().is_multiple_of(4));
            }
            Step::Sdg => {
                t.sdg(rng.next_u64().is_multiple_of(4));
            }
            Step::Psend => {
                g.psends += 1;
                t.psend();
            }
            Step::Pfin => {
                g.pend = true;
                t.pfin();
            }
            Step::Preset => {
                g.pend = true;
                t.preset();
            }
            Step::Pstop => {
                g.pstopped = true;
                t.pstop();
            }
            Step::Pdg => {
                g.pdgs += 1;
                t.pdg();
            }
            Step::Pread => {
                t.pread();
            }
            Step::Held => {
                t.held();
            }
            Step::Close => t.close(),
            Step::Pclose => t.pclose(),
        }
    }
}
