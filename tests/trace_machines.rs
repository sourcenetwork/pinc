//! Trace generation for the pool of handshake machine boxes (`pinc-transport`, built with the `trace` feature): real
//! dialing connections that share one `Machines`, recorded as ndjson (`machines.ndjson`) for the TLA+ trace check
//! (`TraceMachines.tla`).
//!
//! More connections are open at once than the pool has cells (64), and they are dropped in seeded orders, so boxes
//! are taken from the pool, allocated when it is empty, returned, and freed when it is full. After every call the
//! record shows the box in each cell and the box each connection holds, through `Machines::trace_cells` and
//! `Connection::trace_machine`; a box is named by a small id the test gives its address on first sight (0 for an
//! empty cell or no machine, -1 for a place with no connection). No packet is sent or received: opening a client
//! connection takes a box, dropping it returns or frees the box.
//!
//! The test asserts the rules itself (an address is in one place, every open connection holds a box, an open takes
//! the first idle box, a drop returns the box to the first empty cell, and a full pool frees it), so it is
//! meaningful without the proof tools. The trace is written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub,
    clippy::redundant_closure_for_method_calls,
    clippy::single_match_else
)]

use std::collections::HashMap;
use std::fmt::Write as _;

use pinc_crypto::{Drbg, IdentityAlg, Software};
use pinc_security::{Env, PrekeyPolicy, SoftPrekeys};
use pinc_tests::*;
use pinc_transport::conn::{ClientParams, Connection, Machines, PathId, PathInfo};
use pinc_transport::stream::NoSource;

/// The places for connections, and the cells of the pool.
const PLACES: usize = 72;
const CELLS: usize = 64;

type Client = Connection<'static, Caps, NoSource, CN, CC, CF, CNP>;

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    empty_pool_busy: bool,
    full_pool_drop: bool,
}

/// Everything a dialing side needs, built once.
struct Dial {
    w: World,
    prov: Caps,
    drbg: Drbg,
    prekey: pinc_security::PrekeyInfo,
}

struct Run<'a> {
    dial: &'a mut Dial,
    machines: Machines,
    places: Vec<Option<Client>>,
    ids: &'a mut HashMap<usize, u32>,
    out: &'a mut String,
    seen: &'a mut Seen,
}

impl<'a> Run<'a> {
    fn id_of(&mut self, addr: usize) -> i64 {
        if addr == 0 {
            return 0;
        }
        let next = u32::try_from(self.ids.len()).unwrap() + 1;
        i64::from(*self.ids.entry(addr).or_insert(next))
    }

    fn cells(&mut self) -> Vec<i64> {
        let addrs = self.machines.trace_cells();
        assert_eq!(addrs.len(), CELLS);
        addrs.into_iter().map(|a| self.id_of(a)).collect()
    }

    fn conns(&mut self) -> Vec<i64> {
        let addrs: Vec<Option<usize>> = self
            .places
            .iter()
            .map(|c| c.as_ref().map(|c| c.trace_machine()))
            .collect();
        addrs.into_iter().map(|a| a.map_or(-1, |a| self.id_of(a))).collect()
    }

    /// The pool and the connections after a call; checks what always holds.
    fn view(&mut self) -> (Vec<i64>, Vec<i64>) {
        let (cells, conns) = (self.cells(), self.conns());
        assert!(cells.iter().filter(|c| **c != 0).count() <= CELLS);
        assert!(conns.iter().all(|c| *c != 0), "an open connection holds no box");
        let mut ids: Vec<i64> = cells.iter().chain(&conns).copied().filter(|i| *i > 0).collect();
        let n = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), n, "a box is in two places");
        (cells, conns)
    }

    fn log(&mut self, body: &str) {
        let (cells, conns) = self.view();
        let join = |v: &[i64]| v.iter().map(i64::to_string).collect::<Vec<_>>().join(",");
        let _ = writeln!(
            self.out,
            r#"{{"t":"machines",{body},"v":{{"cells":[{}],"conns":[{}]}}}}"#,
            join(&cells),
            join(&conns)
        );
    }

    fn new(dial: &'a mut Dial, ids: &'a mut HashMap<usize, u32>, out: &'a mut String, seen: &'a mut Seen) -> Run<'a> {
        let mut r = Run {
            dial,
            machines: Machines::new(),
            places: (0..PLACES).map(|_| None).collect(),
            ids,
            out,
            seen,
        };
        r.log(r#""op":"init""#);
        r
    }

    fn open_count(&self) -> usize {
        self.places.iter().flatten().count()
    }

    /// Place `n` (from 1), empty, holds a new client connection.
    fn open(&mut self, n: usize) {
        assert!(self.places[n - 1].is_none());
        let before = self.cells();
        let in_use = self.open_count();
        let d = &mut *self.dial;
        let mut env = Env {
            provider: &d.prov,
            now: T0,
            drbg: &mut d.drbg,
        };
        let conn = Client::client(
            d.w.cfg,
            ClientParams {
                peer: d.w.rp.id.node_id(),
                alpn: ALPN,
                identity: &d.w.ip.id,
                prekey: &d.prekey,
                peer_has_prekey: false,
                ticket: None,
                path: PathId(1),
                path_info: PathInfo::default(),
            },
            memory_sharing(true, &self.machines),
            &mut env,
        )
        .unwrap();
        self.places[n - 1] = Some(conn);
        let after = self.cells();
        let held = self.id_of(self.places[n - 1].as_ref().unwrap().trace_machine());
        assert!(held > 0, "an open connection holds no box");
        match before.iter().position(|c| *c != 0) {
            Some(j) => {
                assert_eq!(held, before[j], "an open did not take the first idle box");
                let mut want = before.clone();
                want[j] = 0;
                assert_eq!(after, want, "an open changed more than the cell it took");
            }
            None => {
                assert_eq!(after, before, "an open from an empty pool changed the cells");
                self.seen.empty_pool_busy |= in_use >= CELLS;
            }
        }
        self.log(&format!(r#""op":"open","conn":{n}"#));
    }

    /// The connection of place `n` (from 1) drops.
    fn drop_place(&mut self, n: usize) {
        let before = self.cells();
        let held = self.id_of(self.places[n - 1].as_ref().unwrap().trace_machine());
        self.places[n - 1] = None;
        let after = self.cells();
        match before.iter().position(|c| *c == 0) {
            Some(j) => {
                let mut want = before.clone();
                want[j] = held;
                assert_eq!(after, want, "a drop did not put the box in the first empty cell");
            }
            None => {
                assert_eq!(after, before, "a drop at a full pool changed the cells");
                self.seen.full_pool_drop = true;
            }
        }
        self.log(&format!(r#""op":"drop","conn":{n}"#));
    }

    /// The places holding a connection, or the empty ones.
    fn places(&self, open: bool) -> Vec<usize> {
        (1..=PLACES).filter(|n| self.places[n - 1].is_some() == open).collect()
    }

    fn drop_all(&mut self) {
        for n in self.places(true) {
            self.drop_place(n);
        }
    }
}

#[test]
fn the_machine_pool_matches_the_model() {
    let mut rng = SplitMix64::traced(0x6d61_6368);
    let mut below = |n: usize| (rng.next_u64() % n as u64) as usize;
    let w = World::new(IdentityAlg::Ed25519);
    let prov = Caps(Software, w.hw);
    let mut drbg = Drbg::new(&[0x11; 32]);
    let prekey = {
        let mut env = Env {
            provider: &prov,
            now: T0,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        prekeys.acquire(&mut env).unwrap()
    };
    let mut dial = Dial { w, prov, drbg, prekey };
    let (mut ids, mut out, mut seen) = (HashMap::new(), String::new(), Seen::default());

    // 1. over the pool
    {
        let mut r = Run::new(&mut dial, &mut ids, &mut out, &mut seen);
        for n in 1..=PLACES {
            r.open(n);
        }
        let mut order: Vec<usize> = (1..=PLACES).collect();
        for i in (1..order.len()).rev() {
            order.swap(i, below(i + 1));
        }
        for n in order {
            r.drop_place(n);
        }
        for n in 1..=PLACES {
            r.open(n);
        }
        for n in (1..=PLACES).rev() {
            r.drop_place(n);
        }
    }

    // 2. churn near the bound
    {
        let mut r = Run::new(&mut dial, &mut ids, &mut out, &mut seen);
        for n in 1..=70 {
            r.open(n);
        }
        for _ in 0..400 {
            let open = r.places(true);
            r.drop_place(open[below(open.len())]);
            let empty = r.places(false);
            r.open(empty[below(empty.len())]);
        }
        r.drop_all();
    }

    // 3. seeded runs
    for _ in 0..5 {
        let mut r = Run::new(&mut dial, &mut ids, &mut out, &mut seen);
        for _ in 0..300 {
            if r.open_count() == 0 || (below(2) == 0 && r.open_count() < PLACES) {
                let empty = r.places(false);
                r.open(empty[below(empty.len())]);
            } else {
                let open = r.places(true);
                r.drop_place(open[below(open.len())]);
            }
        }
        r.drop_all();
    }

    assert!(
        seen.empty_pool_busy,
        "no open found the pool empty with 64 boxes or more in use"
    );
    assert!(seen.full_pool_drop, "no drop found the pool full");
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("machines.ndjson"), &out).unwrap();
    }
}
