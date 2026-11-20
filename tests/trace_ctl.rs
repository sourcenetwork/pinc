//! Trace generation for the control-frame state of a connection (`pinc-transport`, built with the `trace` feature):
//! a real `Ctl`, stream table and buffer pool driven through `CtlProbe`, recorded as ndjson (`ctl.ndjson`) for the
//! TLA+ trace check (`TraceCtlTable.tla`).
//!
//! Stream frames are tracked past a full table, extension frames are held (bodies at and over the largest, with the
//! pool full), sent and shed, ticket batches are issued and sent, READY is asked for and built, the pool's other
//! users take and give chunks, and every frame reference is reported as acknowledged, lost (to be requeued) or
//! acknowledged late, in scripted and in seeded orders. After every call the record shows the table, the extension
//! slots, the two key counters, the flags, the generation of the ticket batch held and the chunks the pool charges.
//!
//! The test asserts the rules itself (a held frame owns one chunk, keys are distinct and below their counters, a
//! full table refuses, `hold` refuses for the three reasons and only them, a reference is handed to the stream layer
//! exactly when its key was in the table, an answer about an older ticket batch leaves the newer batch as it was), so
//! it is meaningful without the proof tools. Every ticket frame names its batch, and the trace writes the batch an
//! acknowledged or lost frame carried as `g`. The model's packet always has room, so the calls that find no room or no
//! frame reference left are in `a_frame_without_room_stays_owed`, which records nothing. The trace is written to
//! `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::struct_excessive_bools,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::conn::{CtlProbe, CtlView, EXT_BODY_MAX};

/// The places of the stream frame table, and the extension slots.
const TABLE: usize = 24;
const SLOTS: usize = 8;

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    track_refused: bool,
    hold_refused: bool,
    take_failed: bool,
    older_batch_acked: bool,
}

/// A frame reference in flight: kind, id and the generation of a ticket batch.
type Flight = (&'static str, u64, u64);

struct Run<'a> {
    p: CtlProbe,
    pool: usize,
    mine: usize,
    flight: Vec<Flight>,
    /// The key each slot's last `send_ext` returned.
    sent: [Option<u64>; SLOTS],
    generation: u64,
    out: &'a mut String,
    seen: &'a mut Seen,
}

fn show(v: &CtlView) -> String {
    let tab: Vec<String> = v.tab.iter().map(u64::to_string).collect();
    let ext: Vec<String> = v
        .ext
        .iter()
        .map(|e| e.map_or_else(|| "[]".to_owned(), |(k, p)| format!("[{k},{p}]")))
        .collect();
    format!(
        r#"{{"tab":[{}],"ext":[{}],"nk":{},"ne":{},"ready":{},"tk":{},"tp":{},"used":{}}}"#,
        tab.join(","),
        ext.join(","),
        v.nk,
        v.ne,
        v.ready,
        v.tk,
        v.tp,
        v.used
    )
}

impl<'a> Run<'a> {
    fn new(out: &'a mut String, seen: &'a mut Seen, pool: usize) -> Self {
        let mut r = Run {
            p: CtlProbe::new(pool),
            pool,
            mine: 0,
            flight: Vec::new(),
            sent: [None; SLOTS],
            generation: 0,
            out,
            seen,
        };
        r.log(&format!(r#""op":"init","p":{pool}"#));
        r
    }

    /// The rules every state keeps.
    fn check(&self) -> CtlView {
        let v = self.p.view();
        assert_eq!(v.tab.len(), TABLE);
        assert_eq!(v.ext.len(), SLOTS);
        let held = v.ext.iter().flatten().count();
        assert_eq!(v.used, held + self.mine, "a held frame does not own exactly one chunk");
        let keys: Vec<u64> = v.tab.iter().copied().filter(|k| *k != 0).collect();
        let mut once = keys.clone();
        once.sort_unstable();
        once.dedup();
        assert_eq!(once.len(), keys.len(), "a key is in the table twice");
        assert!(keys.iter().all(|k| *k < v.nk), "a key is not below next_key");
        let ekeys: Vec<u64> = v.ext.iter().flatten().map(|e| e.0).collect();
        let mut once = ekeys.clone();
        once.sort_unstable();
        once.dedup();
        assert_eq!(once.len(), ekeys.len(), "an extension key is in two slots");
        assert!(
            ekeys.iter().all(|k| *k < v.ne),
            "an extension key is not below next_ext"
        );
        v
    }

    fn log(&mut self, body: &str) {
        let v = show(&self.check());
        let _ = writeln!(self.out, r#"{{"t":"ctl",{body},"v":{v}}}"#);
    }

    fn track(&mut self) {
        let before = self.check();
        let r = self.p.track();
        match r {
            None => {
                assert!(before.tab.iter().all(|k| *k != 0), "a refusal with a place free");
                self.seen.track_refused = true;
            }
            Some(k) => {
                assert!(before.tab.contains(&0), "a key with no place free");
                assert_eq!(k, before.nk, "the key is not next_key");
                self.flight.push(("sc", k, 0));
            }
        }
        self.log(&format!(
            r#""op":"track","ok":{},"key":{}"#,
            r.is_some(),
            r.unwrap_or(0)
        ));
    }

    fn hold(&mut self, len: usize) {
        let before = self.check();
        let ok = self.p.hold(len);
        let full = before.ext.iter().all(Option::is_some);
        let long = len > EXT_BODY_MAX;
        let no_chunk = before.used >= self.pool;
        assert_eq!(
            ok,
            !(full || long || no_chunk),
            "hold refused or accepted for the wrong reason"
        );
        if ok {
            let first = before.ext.iter().position(Option::is_none).unwrap();
            assert_eq!(
                self.check().ext[first],
                Some((before.ne, true)),
                "the frame is not in the first free slot"
            );
        } else {
            self.seen.hold_refused = true;
        }
        self.log(&format!(r#""op":"hold","long":{long},"ok":{ok}"#));
    }

    fn send_ext(&mut self, slot: usize) {
        if let Some(key) = self.p.send_ext(slot) {
            self.sent[slot] = Some(key);
            self.flight.push(("ext", key, 0));
            self.log(&format!(r#""op":"send_ext","slot":{slot}"#));
        }
    }

    fn shed(&mut self, slot: usize) {
        self.p.shed(slot);
        self.log(&format!(r#""op":"shed","slot":{slot}"#));
    }

    fn take(&mut self) -> bool {
        let ok = self.p.take();
        self.mine += usize::from(ok);
        self.seen.take_failed |= !ok;
        self.log(&format!(r#""op":"take","ok":{ok}"#));
        ok
    }

    fn give(&mut self) -> bool {
        let ok = self.p.give();
        if ok {
            self.mine -= 1;
            self.log(r#""op":"give""#);
        }
        ok
    }

    fn issue(&mut self, g: u64) {
        self.p.issue(g);
        self.log(&format!(r#""op":"issue","g":{g}"#));
    }

    /// The next generation of a ticket batch, from 1.
    fn next_gen(&mut self) -> u64 {
        self.generation += 1;
        self.generation
    }

    fn send_tickets(&mut self) {
        let r = self.p.send_tickets();
        if let Some((id, g)) = r {
            self.flight.push(("tk", id, g));
        }
        self.log(&format!(
            r#""op":"send_tickets","ok":{},"g":{}"#,
            r.is_some(),
            r.map_or(0, |(_, g)| g)
        ));
    }

    /// The id the last frame that carried batch `g` has.
    fn tk(&self, g: u64) -> u64 {
        self.flight
            .iter()
            .rev()
            .find(|f| f.0 == "tk" && f.2 == g)
            .map_or(0, |f| f.1)
    }

    fn send_ready(&mut self) {
        self.p.send_ready();
        self.log(r#""op":"send_ready""#);
    }

    fn build_ready(&mut self) {
        let ok = self.p.build_ready();
        if ok {
            self.flight.push(("rd", 0, 0));
        }
        self.log(&format!(r#""op":"build_ready","ok":{ok}"#));
    }

    /// An acknowledgement (`late` for a late one) of the reference `(k, id)` that carried batch `g`.
    fn ack(&mut self, late: bool, k: &str, id: u64, g: u64) {
        let before = self.check();
        let handed = if late {
            self.p.late_ack(k, id)
        } else {
            self.p.ack(k, id)
        };
        if k == "sc" {
            assert_eq!(
                handed,
                before.tab.contains(&id),
                "the stream layer was handed a frame not in the table"
            );
            assert!(
                !self.check().tab.contains(&id),
                "an acknowledged key is still in the table"
            );
        } else {
            assert!(!handed);
        }
        self.seen.older_batch_acked |= !late && k == "tk" && g < before.tk;
        if k == "tk" && id != before.tg {
            assert_eq!(
                self.check().tk,
                before.tk,
                "the acknowledgement of an older batch changed the batch held"
            );
        }
        let op = if late { "late_ack" } else { "ack" };
        self.log(&format!(r#""op":"{op}","k":"{k}","id":{id},"g":{g},"handed":{handed}"#));
    }

    fn lose(&mut self, k: &str, id: u64) {
        let before = self.check();
        let handed = self.p.lose(k, id);
        let after = self.check();
        match k {
            "sc" => {
                assert_eq!(
                    handed,
                    before.tab.contains(&id),
                    "the stream layer was handed a frame not in the table"
                );
                assert!(!after.tab.contains(&id), "a lost key is still in the table");
            }
            "ext" => {
                if let Some(e) = after.ext.iter().flatten().find(|e| e.0 == id) {
                    assert!(e.1, "a lost extension frame is not pending");
                }
            }
            "rd" => assert!(after.ready, "a lost READY is not asked for again"),
            _ => assert_eq!(
                after.tp,
                if id == before.tg { before.tk != 0 } else { before.tp },
                "lost tickets are pending exactly when they are the newest batch and a batch is held"
            ),
        }
        // The batch the lost frame carried, 0 for a frame of another kind.
        let g = self.flight.iter().find(|f| f.0 == k && f.1 == id).map_or(0, |f| f.2);
        self.log(&format!(r#""op":"lose","k":"{k}","id":{id},"g":{g},"handed":{handed}"#));
    }

    /// Report a reference of the list (the `i`-th), or track when there is none.
    fn report(&mut self, late: Option<bool>, i: usize) {
        let Some(&(k, id, g)) = self.flight.get(i) else {
            return self.track();
        };
        match late {
            Some(late) => self.ack(late, k, id, g),
            None => self.lose(k, id),
        }
    }
}

fn scripted(out: &mut String, seen: &mut Seen) {
    // 1. the table
    let mut r = Run::new(out, seen, 4);
    for _ in 0..26 {
        r.track();
    }
    for k in (1..=23).step_by(2) {
        r.ack(false, "sc", k, 0);
    }
    for k in (2..=24).step_by(2) {
        r.lose("sc", k);
    }
    r.ack(false, "sc", 1, 0);
    r.lose("sc", 2);
    r.ack(true, "sc", 5, 0);
    r.ack(false, "sc", 999, 0);
    for _ in 0..14 {
        r.track();
    }
    for (k, id, g) in r.flight.clone() {
        if k == "sc" {
            r.ack(false, k, id, g);
        }
    }

    // 2. extension slots
    let mut r = Run::new(out, seen, 10);
    for _ in 0..8 {
        r.hold(16);
    }
    r.hold(16);
    r.shed(3);
    r.hold(EXT_BODY_MAX + 1);
    r.hold(EXT_BODY_MAX);
    while r.take() {}
    r.shed(5);
    r.take();
    r.hold(0);
    r.give();
    r.hold(0);
    for s in 0..SLOTS {
        r.send_ext(s);
    }
    r.send_ext(0);
    for s in 0..4 {
        if let Some(key) = r.sent[s] {
            r.lose("ext", key);
        }
    }
    r.send_ext(0);
    r.send_ext(1);
    let (k0, k1) = (r.sent[0].unwrap(), r.sent[1].unwrap());
    r.ack(false, "ext", k0, 0);
    r.ack(true, "ext", k0, 0);
    r.ack(false, "ext", k1, 0);
    r.ack(false, "ext", k1, 0);
    for s in 0..SLOTS {
        r.shed(s);
    }
    while r.give() {}

    // 3. tickets and READY
    let mut r = Run::new(out, seen, 2);
    r.send_tickets();
    r.issue(1);
    r.send_tickets();
    r.send_tickets();
    let a = r.tk(1);
    r.lose("tk", a);
    r.send_tickets();
    r.ack(false, "tk", a, 1);
    r.issue(2);
    r.send_tickets();
    let b = r.tk(2);
    r.issue(3);
    r.ack(false, "tk", b, 2);
    r.lose("tk", b);
    r.send_tickets();
    let c = r.tk(3);
    r.ack(true, "tk", c, 3);
    r.send_ready();
    r.build_ready();
    r.build_ready();
    r.lose("rd", 0);
    r.build_ready();
    r.ack(false, "rd", 0, 0);
    r.lose("rd", 0);
    r.ack(false, "rd", 0, 0);
    r.build_ready();
}

fn seeded(out: &mut String, seen: &mut Seen, rng: &mut SplitMix64) {
    let mut below = |n: usize| (rng.next_u64() % n as u64) as usize;
    let mut r = Run::new(out, seen, [1, 2, 4, 9][below(4)]);
    for _ in 0..150 {
        let op = below(100);
        match op {
            0..=14 => r.track(),
            15..=24 => r.hold([0, 1, EXT_BODY_MAX, EXT_BODY_MAX + 1][below(4)]),
            25..=34 => r.send_ext(below(SLOTS)),
            35..=37 => r.shed(below(SLOTS)),
            38..=41 => {
                r.take();
            }
            42..=45 => {
                r.give();
            }
            46..=49 => {
                let g = r.next_gen();
                r.issue(g);
            }
            50..=55 => r.send_tickets(),
            56..=58 => r.send_ready(),
            59..=63 => r.build_ready(),
            64..=81 => {
                let i = below(r.flight.len().max(1));
                r.report(Some(false), i);
            }
            82..=87 => {
                let i = below(r.flight.len().max(1));
                r.report(Some(true), i);
            }
            _ => {
                let i = below(r.flight.len().max(1));
                r.report(None, i);
            }
        }
    }
}

#[test]
fn the_control_state_matches_the_model() {
    let mut rng = SplitMix64::traced(0x6374_6c74);
    let (mut out, mut seen) = (String::new(), Seen::default());
    scripted(&mut out, &mut seen);
    for _ in 0..100 {
        seeded(&mut out, &mut seen, &mut rng);
    }
    assert!(seen.track_refused, "no track was refused");
    assert!(seen.hold_refused, "no hold was refused");
    assert!(seen.take_failed, "no take failed");
    assert!(
        seen.older_batch_acked,
        "no batch was acknowledged while a newer one was held"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("ctl.ndjson"), &out).unwrap();
    }
}

/// A frame that does not fit the packet, or has no frame reference left to go in, stays owed and changes nothing.
/// Not recorded: the model's packet always has room, so the trace check would refuse these calls.
#[test]
fn a_frame_without_room_stays_owed() {
    let mut p = CtlProbe::new(4);
    p.send_ready();
    p.issue(1);
    assert!(p.hold(16));
    for (room, refs) in [(1500, 8), (0, 0)] {
        p.set_room(room);
        p.set_refs(refs);
        let before = p.view();
        assert!(
            !p.build_ready(),
            "READY went with room {room} and {refs} references held"
        );
        assert_eq!(
            p.send_tickets(),
            None,
            "tickets went with room {room} and {refs} references held"
        );
        assert_eq!(
            p.send_ext(0),
            None,
            "an extension frame went with room {room} and {refs} references held"
        );
        assert_eq!(p.view(), before, "a refused frame changed the state");
    }
    p.set_room(1500);
    p.set_refs(0);
    assert!(p.build_ready() && p.send_tickets().map(|(_, g)| g) == Some(1) && p.send_ext(0).is_some());
    let after = p.view();
    assert!(
        !after.ready && !after.tp && after.ext.iter().flatten().all(|e| !e.1),
        "a sent frame is still owed"
    );
}
