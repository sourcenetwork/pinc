//! The incarnation and the address tag, recorded for the proofs (`minc.ndjson`).
//!
//! Seeded lives of the real `Incarnation` over a host store of this file: a persistent counter that survives restarts
//! (and fails to read or to seal on demand), and the hybrid clock of a host with no store, across restarts, wall clock
//! jumps back and forward, host floors, record sequences that roll over, observed words below, at and above the
//! node's own, and the epoch space running out. The `AddressTag` is driven through handovers, several at one
//! instant, the settle time, and more than 255 moves. Every event carries the host store as the call found it, so the
//! TLA+ check (`TraceIncarnation.tla`) and the Lean replay (`Vinc.TraceMembershipInc`) apply the model operator to
//! the same inputs and compare the result and the store afterwards.
//!
//! The test also checks the properties of the design itself, against a plain tracker: the words a lineage announces
//! strictly increase for a persistent store whatever the wall clock does, an epoch never exceeds 48 bits, and a
//! failure leaves the value and the word unchanged.

use vinc_membership::Local;
use vinc_membership::incarnation::{AddressTag, Incarnation, IncarnationError, MOVE_SETTLE};
use vinc_membership::session::StoreError;
use vinc_tests::SplitMix64;

use crate::common::{TraceWriter, b, limbs, opt_limbs};

const FILE: &str = "minc.ndjson";
const EPOCH_MAX: u64 = (1 << 48) - 1;

#[derive(Clone, Default)]
struct Host {
    persistent: bool,
    sealed: Option<u64>,
    read_fails: bool,
    seal_fails: bool,
    reflexive: bool,
    ticket: u8,
}

impl Local for Host {
    fn version(&self) -> u16 {
        1
    }
    fn reflexive_known(&self) -> bool {
        self.reflexive
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [self.ticket, moves, 0, 0, 0, 0, 0, 7]
    }
    fn persistent(&self) -> bool {
        self.persistent
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        if self.read_fails {
            Err(StoreError)
        } else {
            Ok(self.sealed)
        }
    }
    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        if self.seal_fails {
            return Err(StoreError);
        }
        self.sealed = Some(epoch);
        Ok(())
    }
}

fn err_name(e: &IncarnationError) -> &'static str {
    match e {
        IncarnationError::Store(_) => "store",
        IncarnationError::Exhausted => "exhausted",
    }
}

/// The result part of an event: ok, error name, word after, store after.
fn outcome(r: &Result<u64, IncarnationError>, h: &Host) -> String {
    match r {
        Ok(w) => format!(
            "\"ok\":true,\"err\":\"\",\"w\":{},\"sl2\":{}",
            limbs(*w),
            opt_limbs(h.sealed)
        ),
        Err(e) => format!(
            "\"ok\":false,\"err\":\"{}\",\"w\":{},\"sl2\":{}",
            err_name(e),
            limbs(0),
            opt_limbs(h.sealed)
        ),
    }
}

fn env(run: usize, op: &str, h: &Host) -> String {
    format!(
        "{{\"t\":\"mi\",\"run\":{run},\"op\":\"{op}\",\"pers\":{},\"sl\":{},\"rf\":{},\"sf\":{}",
        b(h.persistent),
        opt_limbs(h.sealed),
        b(h.read_fails),
        b(h.seal_fails)
    )
}

/// One life being driven: the value, and the words announced so far.
struct Life {
    run: usize,
    host: Host,
    inc: Option<Incarnation>,
    /// The highest word announced in this lineage.
    top: Option<u64>,
    /// The highest epoch this host remembers by other means (what a host passes as the floor).
    heard: u64,
}

impl Life {
    fn new(run: usize, host: Host) -> Self {
        Self {
            run,
            host,
            inc: None,
            top: None,
            heard: 0,
        }
    }

    /// The store was replaced behind the node's back (a lost or rewound store): a new lineage.
    fn rewind(&mut self, sealed: Option<u64>) {
        self.host.sealed = sealed;
        self.top = None;
    }

    fn announce(&mut self, w: u64) {
        if self.host.persistent
            && let Some(t) = self.top
        {
            assert!(w > t, "persistent lineage: word {w} is not above {t}");
        }
        self.top = Some(self.top.map_or(w, |t| t.max(w)));
        self.heard = self.heard.max(w >> 16);
    }

    fn start(&mut self, tw: &mut TraceWriter, wall: u64, floor: u64) {
        let pre = env(self.run, "st", &self.host);
        let before = self.host.sealed;
        let r = Incarnation::start(&mut self.host, wall, floor);
        let (res, word) = match &r {
            Ok(i) => (Ok(i.word()), Some(i.word())),
            Err(e) => (Err(*e), None),
        };
        tw.line(
            FILE,
            &format!(
                "{pre},\"wall\":{},\"fl\":{},{}}}",
                limbs(wall),
                limbs(floor),
                outcome(&res, &self.host)
            ),
        );
        match r {
            Ok(i) => {
                let e = i.epoch();
                assert!(e <= EPOCH_MAX, "epoch within 48 bits");
                assert_eq!(i.word() & 0xffff, 0, "a new life starts at sequence 0");
                if self.host.persistent {
                    assert_eq!(self.host.sealed, Some(e), "sealed before use");
                    assert!(
                        before.is_none_or(|s| e > s) && e > floor,
                        "above the counter and the floor"
                    );
                } else {
                    assert!(
                        e > floor && e > wall.min(EPOCH_MAX),
                        "the clock fallback is above the floor"
                    );
                }
                self.announce(word.unwrap_or(0));
                self.inc = Some(i);
            }
            Err(IncarnationError::Store(_)) => assert_eq!(self.host.sealed, before, "a failed start stores nothing"),
            Err(IncarnationError::Exhausted) => {
                assert_eq!(self.host.sealed, before, "an exhausted start stores nothing");
            }
        }
    }

    fn next(&mut self, tw: &mut TraceWriter) {
        let Some(mut i) = self.inc else { return };
        let pre = env(self.run, "nr", &self.host);
        let (w0, before) = (i.word(), self.host.sealed);
        let r = i.next_record(&mut self.host);
        tw.line(FILE, &format!("{pre},{}}}", outcome(&r, &self.host)));
        match r {
            Ok(w) => {
                assert_eq!(w, i.word());
                assert!(w > w0);
                self.announce(w);
            }
            Err(_) => {
                assert_eq!(i.word(), w0, "a failed record changes nothing");
                assert_eq!(self.host.sealed, before);
            }
        }
        self.inc = Some(i);
    }

    /// `n` records in a row, stopping at the first error; one event.
    fn next_n(&mut self, tw: &mut TraceWriter, n: u32) {
        let Some(mut i) = self.inc else { return };
        let pre = env(self.run, "nrn", &self.host);
        let mut done = 0u32;
        let mut last = Ok(i.word());
        for _ in 0..n {
            let w0 = i.word();
            last = i.next_record(&mut self.host);
            match &last {
                Ok(w) => {
                    assert!(*w > w0);
                    self.announce(*w);
                    done += 1;
                }
                Err(_) => break,
            }
        }
        tw.line(
            FILE,
            &format!("{pre},\"n\":{n},\"done\":{done},{}}}", outcome(&last, &self.host)),
        );
        self.inc = Some(i);
    }

    fn observe(&mut self, tw: &mut TraceWriter, seen: u64) {
        let Some(mut i) = self.inc else { return };
        let pre = env(self.run, "ob", &self.host);
        let (w0, before) = (i.word(), self.host.sealed);
        let r = i.observe(&mut self.host, seen);
        let (res, ch) = match &r {
            Ok(c) => (Ok(i.word()), *c),
            Err(e) => (Err(*e), false),
        };
        tw.line(
            FILE,
            &format!(
                "{pre},\"seen\":{},\"ch\":{},{}}}",
                limbs(seen),
                b(ch),
                outcome(&res, &self.host)
            ),
        );
        match r {
            Ok(true) => {
                assert!(seen < i.word() && w0 < i.word());
                self.announce(i.word());
            }
            Ok(false) => {
                assert!(seen <= w0);
                assert_eq!(i.word(), w0);
            }
            Err(_) => {
                assert_eq!(i.word(), w0, "a failed observe changes nothing");
                assert_eq!(self.host.sealed, before);
            }
        }
        self.inc = Some(i);
    }
}

fn pick(rng: &mut SplitMix64, set: &[u64]) -> u64 {
    set[usize::try_from(rng.next_u64() % set.len() as u64).unwrap_or(0)]
}

/// Walls (milliseconds): 0, small, now-like, clock jumps, the 48-bit edge, the u64 edge.
fn walls(rng: &mut SplitMix64) -> u64 {
    let set = [
        0,
        1,
        1_000_000,
        1_700_000_000_000,
        1_700_000_000_000 + (rng.next_u64() % 1_000_000),
        rng.next_u64() % (1 << 41),
        EPOCH_MAX - 1,
        EPOCH_MAX,
        EPOCH_MAX + 1,
        u64::MAX,
    ];
    pick(rng, &set)
}

fn seens(rng: &mut SplitMix64, own: u64) -> u64 {
    let set = [
        0,
        own.saturating_sub(1),
        own,
        own.saturating_add(1),
        own.saturating_add(65_536),
        own | 0xffff,
        rng.next_u64() % (1 << 50),
        EPOCH_MAX << 16,
        (EPOCH_MAX << 16) | 0xffff,
        u64::MAX,
    ];
    pick(rng, &set)
}

fn lineage(tw: &mut TraceWriter, run: usize, persistent: bool, seed: u64) {
    let mut rng = SplitMix64::traced(seed);
    let mut life = Life::new(
        run,
        Host {
            persistent,
            ..Host::default()
        },
    );
    for _ in 0..14 {
        // Failures come and go with the host.
        life.host.read_fails = rng.next_u64() % 6 == 0;
        life.host.seal_fails = rng.next_u64() % 6 == 0;
        let wall = walls(&mut rng);
        // The host remembers what it has heard: the floor is that, or nothing, or anything.
        let floor = match rng.next_u64() % 4 {
            0 => 0,
            1 => life.heard,
            2 => life.heard.saturating_sub(1),
            _ => rng.next_u64() % (1 << 30),
        };
        life.start(tw, wall, floor);
        life.host.read_fails = false;
        for _ in 0..24 {
            life.host.seal_fails = rng.next_u64() % 9 == 0;
            match rng.next_u64() % 8 {
                0..=2 => life.next(tw),
                3 => life.next_n(tw, 1 + u32::try_from(rng.next_u64() % 70_000).unwrap_or(0)),
                4..=6 => {
                    let own = life.inc.map_or(0, |i| i.word());
                    let seen = seens(&mut rng, own);
                    life.observe(tw, seen);
                }
                _ => {
                    let floor = life.heard;
                    let wall = walls(&mut rng);
                    life.host.read_fails = false;
                    life.start(tw, wall, floor);
                }
            }
        }
    }
}

/// The epoch space running out, and its edges.
fn edges(tw: &mut TraceWriter, run: usize) {
    // A persistent store one below the end: the last epoch is issued, then the sequence rolls into exhaustion.
    let mut life = Life::new(
        run,
        Host {
            persistent: true,
            sealed: Some(EPOCH_MAX - 2),
            ..Host::default()
        },
    );
    life.start(tw, 0, 0);
    life.next_n(tw, 70_000);
    life.observe(tw, u64::MAX);
    life.rewind(Some(EPOCH_MAX));
    life.start(tw, 5, 0);
    life.rewind(Some(EPOCH_MAX - 1));
    life.start(tw, 5, 0);
    life.next_n(tw, 65_536);
    life.next(tw);
    life.observe(tw, EPOCH_MAX << 16);
    life.observe(tw, (EPOCH_MAX << 16) | 0xffff);
    // The floor at the end.
    life.rewind(None);
    life.start(tw, 5, EPOCH_MAX);
    life.start(tw, 5, EPOCH_MAX - 1);
    life.start(tw, 5, u64::MAX);
    // The clock at the end.
    let mut hlc = Life::new(run + 1, Host::default());
    hlc.start(tw, EPOCH_MAX - 1, 0);
    hlc.start(tw, EPOCH_MAX, 0);
    hlc.start(tw, u64::MAX, 0);
    hlc.start(tw, 0, EPOCH_MAX - 1);
    hlc.next_n(tw, 65_536);
    hlc.next(tw);
    hlc.observe(tw, u64::MAX);
    // A store that cannot be read, and one that cannot be written, at start.
    let mut bad = Life::new(
        run + 2,
        Host {
            persistent: true,
            sealed: Some(7),
            read_fails: true,
            ..Host::default()
        },
    );
    bad.start(tw, 1, 0);
    bad.host.read_fails = false;
    bad.host.seal_fails = true;
    bad.start(tw, 1, 0);
    bad.host.seal_fails = false;
    bad.start(tw, 1, 0);
    bad.host.seal_fails = true;
    bad.next_n(tw, 70_000);
    bad.observe(tw, u64::MAX / 2);
    bad.host.seal_fails = false;
    bad.observe(tw, 1 << 40);
}

/// The address tag.
fn tags(tw: &mut TraceWriter, run: usize, seed: u64) {
    let mut rng = SplitMix64::traced(seed);
    let mut host = Host {
        ticket: 9,
        ..Host::default()
    };
    let mut tag = AddressTag::default();
    let mut now = 1_000u64;
    let mut moves = 0u8;
    let mut moved_at: Option<u64> = None;
    let mut cur: Option<[u8; 8]> = None;
    for step in 0..700 {
        now += match rng.next_u64() % 6 {
            0 => 0,
            1 => 1,
            2 => MOVE_SETTLE - 1,
            3 => MOVE_SETTLE,
            4 => MOVE_SETTLE + 1,
            _ => rng.next_u64() % (2 * MOVE_SETTLE),
        };
        host.reflexive = rng.next_u64() % 3 == 0;
        if rng.next_u64() % 17 == 0 {
            host.ticket = u8::try_from(rng.next_u64() % 200).unwrap_or(0);
        }
        if step % 2 == 0 || rng.next_u64() % 3 == 0 {
            tw.line(
                FILE,
                &format!("{{\"t\":\"mi\",\"run\":{run},\"op\":\"mv\",\"now\":{}}}", limbs(now)),
            );
            tag.moved(now);
            if moved_at != Some(now) {
                moves = moves.wrapping_add(1);
            }
            moved_at = Some(now);
            assert_eq!(tag.moves(), moves);
        }
        let t = tag.tag(now, &host);
        tw.line(
            FILE,
            &format!(
                "{{\"t\":\"mi\",\"run\":{run},\"op\":\"tg\",\"now\":{},\"refl\":{},\"tk\":{},\"tag\":{},\"mv\":{}}}",
                limbs(now),
                b(host.reflexive),
                host.ticket,
                super::common::list(&t),
                tag.moves()
            ),
        );
        let settling = moved_at.is_some_and(|m| now.saturating_sub(m) < MOVE_SETTLE && !host.reflexive);
        let expect = match cur {
            Some(prev) if settling => prev,
            _ => host.address_hash(moves),
        };
        assert_eq!(
            t, expect,
            "the tag is the previous one while settling, the hash of the moves after"
        );
        cur = Some(t);
    }
    assert!(moves < 255 || tag.moves() == moves);
}

/// Record and check every incarnation and address tag scenario.
pub fn run(tw: &mut TraceWriter) {
    let mut run = 0;
    for seed in 1..=6 {
        lineage(tw, run, true, seed);
        run += 1;
        lineage(tw, run, false, 100 + seed);
        run += 1;
    }
    edges(tw, run);
    run += 3;
    for seed in 1..=2 {
        tags(tw, run, 500 + seed);
        run += 1;
    }
    assert!(tw.count(FILE) > 1000);
}
