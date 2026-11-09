//! The runner: builds the simulated network of a [`World`], schedules everything the reference runner schedules, runs
//! the real `vinc-core` endpoints through it, and grades the finished run.
//!
//! [`run`] takes a world, a driver mode and the set of protocol layers the run has. The network is built as the
//! reference builds it ([`net`]); the schedule is pushed in the reference's order and the actions that depend on a
//! node's state wait in an agenda ([`drive`]); [`plan()`] decides which intents the layers at hand can run and tallies
//! the rest honestly; the gates, the terms and the trace hash come from the grading module on the recorder.
//! [`report`] turns results into text tables.
//!
//! # Layers
//!
//! This branch carries the four harness protocols over core UDP only. The layers that do not exist yet are listed in
//! [`LayerSet`] and registered in exactly one place, `make_stack`: setting a flag and handing the `Stack` its layer
//! there is all that adding one takes. A flag that is set without a registration is an error ([`RunError::NotWired`]),
//! never a silent pass. With a flag false the intents that need the layer are not scheduled (they are in
//! [`RunResult::excluded`]), the gates that would need them have no samples, and the status says `Partial`.
//!
//! Invariants: nothing here reads a clock, a socket or a random source of the machine; a run is a pure function of
//! the world, the driver and the layer set; the recorder, the registry and the simulator live on one thread with a
//! large stack, and only plain data leaves it.

// The runner follows the reference's long construction and report routines whole, so they read against their source.
#![allow(
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::struct_excessive_bools,
    clippy::type_complexity,
    clippy::unnecessary_wraps,
    clippy::needless_pass_by_value,
    clippy::assigning_clones,
    clippy::missing_errors_doc
)]

pub mod codec;
pub mod drive;
pub mod net;
pub mod plan;
pub mod reference_table;
pub mod report;

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock, mpsc};

pub use self::plan::{LayerSet, Plan, Status, plan};
use crate::suite::crypto::Registry;
use crate::suite::grade::{
    FairSamples, GateReport, GateStatus, NodeFacts, RunFacts, SecFacts, Terms, compute_fair_terms, compute_terms,
    evaluate_gates,
};
use crate::suite::node::{SetupError, Shared};
use crate::suite::proto::{Durable, MsgIntents, Stack};
use crate::suite::rec::{Rec, Violation};
use crate::suite::world::model::{IntentKind, World};
use crate::{Driver, DropReason, LinkConfig, NodeState, SimConfig};

/// Why a run could not be made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    /// The shared state or a node could not be set up.
    Setup(SetupError),
    /// The world uses something the runner does not build.
    Unsupported(String),
    /// A layer flag is set but the runner has no registration for it.
    NotWired(&'static str),
    /// The run panicked.
    Panicked(String),
}

impl From<SetupError> for RunError {
    fn from(e: SetupError) -> Self {
        Self::Setup(e)
    }
}

impl core::fmt::Display for RunError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Setup(e) => write!(f, "the run could not be set up: {e}"),
            Self::Unsupported(what) => write!(f, "the world uses {what}, which the runner does not build"),
            Self::NotWired(layer) => write!(
                f,
                "the {layer} layer is switched on but the runner has none to register"
            ),
            Self::Panicked(m) => write!(f, "the run panicked: {m}"),
        }
    }
}

impl core::error::Error for RunError {}

/// How many of the must deliveries the application saw in time.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Samples {
    /// Intents recorded (the scheduled ones that were created).
    pub intents: u64,
    /// Intents with a must set.
    pub must_intents: u64,
    /// Must deliveries owed (one per must receiver other than the sender, one per must echo or fetch).
    pub must_owed: u64,
    /// Of those, delivered within the deadline.
    pub must_in_time: u64,
    /// Samples of the small-message latency terms (L1, L2) by the fair rule.
    pub small: u64,
    /// Must echoes.
    pub must_echoes: u64,
}

/// Counters of a run, for reports. None of them is a score term.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Stats {
    /// Bytes on the wire.
    pub wire_bytes: u64,
    /// Bytes the application saw delivered.
    pub app_bytes: u64,
    /// Bytes that carried another node's data.
    pub third_bytes: u64,
    /// Resume records.
    pub resumes: u64,
    /// Protocol crashes.
    pub crashes: u64,
    /// Punched paths.
    pub punched: u64,
    /// Adversary actions by kind.
    pub adversary: BTreeMap<String, u64>,
    /// Datagrams dropped for exceeding the path MTU.
    pub mtu_drops: u64,
    /// Events the simulator ran.
    pub events: u64,
    /// Datagrams the network dropped, by reason.
    pub drops: BTreeMap<String, u64>,
    /// Intents the stacks saw for a layer that is not registered.
    pub stack_waiting: BTreeMap<String, u64>,
}

/// Everything a finished run reports. Plain data: it can leave the run's thread.
#[derive(Clone, Debug)]
pub struct RunResult {
    /// The scenario id.
    pub id: String,
    /// The seed.
    pub seed: u64,
    /// The driver mode.
    pub driver: Driver,
    /// The layers the run had.
    pub layers: LayerSet,
    /// How much of the scenario ran.
    pub status: Status,
    /// The scenario was run (false for a waiting scenario).
    pub ran: bool,
    /// Intents listed as waiting, by reason.
    pub excluded: BTreeMap<String, u64>,
    /// Intents scheduled, by kind.
    pub scheduled: BTreeMap<String, u64>,
    /// Intents in the world.
    pub intents_total: u64,
    /// The gates; `NotEvaluated` entries are kept.
    pub gates: GateReport,
    /// Notes on gates that were decided over part of their input only.
    pub coverage: Vec<String>,
    /// The terms by the current rule.
    pub terms: Terms,
    /// The terms with the fair rule's L1, L2, L4 and T4.
    pub fair: Terms,
    /// Sample counts of the fair rule.
    pub fair_samples: FairSamples,
    /// How much was measured.
    pub samples: Samples,
    /// The trace hash.
    pub trace_hash: String,
    /// The violations kept by the recorder (the first three per gate and message).
    pub violations: Vec<Violation>,
    /// The counters.
    pub stats: Stats,
    /// The first must deliveries that were late or missing, as text, for diagnosis (at most 8).
    pub late: Vec<String>,
}

const STACK_BYTES: usize = 256 << 20;

/// Registers the layers of a node. This is the one place a layer is added: when a layer exists, hand its box to the
/// stack here and let [`check_wiring`] accept its flag.
fn make_stack(idx: usize, world: &Rc<World>, rec: &Rc<RefCell<Rec>>, msgs: &MsgIntents) -> Stack {
    let durable = Rc::new(RefCell::new(Durable::sharing(Rc::clone(msgs))));
    // Broadcast layer: `.with_broadcast(Box::new(..))` goes here once the layer exists.
    // Values layer: `.with_values(Box::new(..), ids)` goes here, with the world's values and providers registered.
    // Reconcile layer: `.with_reconcile(Box::new(..))` goes here.
    // Membership: the layers report member events through `OnTopEvent::Member`; no registration of its own.
    // Connectivity (relay, rendezvous, hole punching, carriers): the node adapter's dial path takes it; nothing here.
    Stack::new(idx, Rc::clone(world), Rc::clone(rec), durable)
}

/// The layers `make_stack` registers. Adding a layer there means setting its flag here.
const fn wired() -> LayerSet {
    LayerSet::NONE
}

/// Fails when a flag claims a layer the runner has no registration for.
fn check_wiring(layers: LayerSet) -> Result<(), RunError> {
    let have = wired();
    for (asked, got, name) in [
        (layers.broadcast, have.broadcast, "broadcast"),
        (layers.values, have.values, "values"),
        (layers.reconcile, have.reconcile, "reconcile"),
        (layers.membership, have.membership, "membership"),
        (layers.connectivity, have.connectivity, "connectivity"),
    ] {
        if asked && !got {
            return Err(RunError::NotWired(name));
        }
    }
    Ok(())
}

fn samples_of(rec: &Rec, small: usize) -> Samples {
    let mut s = Samples {
        intents: rec.intents.len() as u64,
        small: small as u64,
        ..Samples::default()
    };
    for it in rec.intents.values().filter(|i| i.must) {
        s.must_intents += 1;
        let in_time = |t: Option<&u64>| t.is_some_and(|&t| it.deadline.is_none_or(|d| t <= d));
        if matches!(it.kind, IntentKind::Echo | IntentKind::Fetch) {
            s.must_owed += 1;
            s.must_in_time += u64::from(in_time(it.delivered.get(&it.node)));
            s.must_echoes += u64::from(it.kind == IntentKind::Echo);
        } else {
            for r in it.must_set.iter().filter(|&&r| r != it.node) {
                s.must_owed += 1;
                s.must_in_time += u64::from(in_time(it.delivered.get(r)));
            }
        }
    }
    s
}

fn owned(m: &BTreeMap<&'static str, u64>) -> BTreeMap<String, u64> {
    m.iter().map(|(k, v)| ((*k).to_owned(), *v)).collect()
}

fn late_of(rec: &Rec) -> Vec<String> {
    let mut out = Vec::new();
    for it in rec.intents.values().filter(|i| i.must) {
        let owed: Vec<usize> = if matches!(it.kind, IntentKind::Echo | IntentKind::Fetch) {
            vec![it.node]
        } else {
            it.must_set.iter().copied().filter(|&r| r != it.node).collect()
        };
        for r in owed {
            let got = it.delivered.get(&r).copied();
            if got.is_none_or(|t| it.deadline.is_some_and(|d| t > d)) && out.len() < 8 {
                out.push(format!(
                    "{:?} iid {} node {} to {:?} receiver {} t {} deadline {:?} delivered {:?}",
                    it.kind, it.iid, it.node, it.meta.to, r, it.t, it.deadline, got
                ));
            }
        }
    }
    out
}

fn coverage_of(world: &World, layers: LayerSet, excluded: &BTreeMap<&'static str, u64>) -> Vec<String> {
    let mut v = Vec::new();
    let has = |k: &str| excluded.contains_key(k);
    if has(plan::WAIT_VALUES) {
        v.push("G-LIVE, G-INT and G-SIZE: the fetch part is not evaluated (values layer)".to_owned());
    }
    if has(plan::WAIT_BROADCAST) {
        v.push("G-LIVE and G-INT: the publish part is not evaluated (broadcast layer)".to_owned());
    }
    if has(plan::WAIT_RECONCILE) {
        v.push("G-LIVE and G-INT: the reconcile part is not evaluated (reconcile layer)".to_owned());
    }
    if has(plan::WAIT_RELAY) || has(plan::WAIT_CARRIER) {
        v.push("G-LIVE, G-ORDER, G-CONNECT and G-SURFACE: intents toward nodes without a public address are not evaluated (connectivity)".to_owned());
    }
    if !layers.membership {
        v.push("G-AWARE: not evaluated (membership layer)".to_owned());
    }
    if world.id == "S11" && !layers.values {
        v.push("G-SIZE: not evaluated (values layer)".to_owned());
    }
    v
}

fn waiting_result(world: &World, driver: Driver, layers: LayerSet, p: Plan) -> RunResult {
    let facts = RunFacts::new(world);
    let rec = Rec::new(Rc::new(world.clone()));
    let why = match &p.status {
        Status::Waiting(w) => w.join("; "),
        _ => String::new(),
    };
    let mut gates = evaluate_gates(world, &rec, &facts);
    for g in crate::suite::grade::GATES {
        gates.set(g, GateStatus::NotEvaluated(format!("the scenario was not run: {why}")));
    }
    RunResult {
        id: world.id.clone(),
        seed: world.seed,
        driver,
        layers,
        status: p.status,
        ran: false,
        coverage: coverage_of(world, layers, &p.excluded),
        excluded: owned(&p.excluded),
        scheduled: owned(&p.scheduled_kinds),
        intents_total: world.intents.len() as u64,
        gates,
        terms: Terms::new(),
        fair: Terms::new(),
        fair_samples: FairSamples::default(),
        samples: Samples::default(),
        trace_hash: String::new(),
        violations: Vec::new(),
        stats: Stats::default(),
        late: Vec::new(),
    }
}

fn execute(
    world: &World,
    driver: Driver,
    layers: LayerSet,
    p: Plan,
    watch: &[usize],
) -> Result<(RunResult, Vec<String>), RunError> {
    let world_rc = Rc::new(world.clone());
    let rec = Rc::new(RefCell::new(Rec::new(Rc::clone(&world_rc))));
    let reg = Registry::leak(world.seed);
    reg.install();
    let out = (|| {
        let shared = Shared::new(Rc::clone(&world_rc), Rc::clone(&rec), reg)?;
        let msgs: MsgIntents = Rc::default();
        let cfg = SimConfig {
            driver,
            default_link: Some(LinkConfig::default()),
            ..SimConfig::default()
        };
        let net = net::build(world, &shared, cfg, |i| make_stack(i, &world_rc, &rec, &msgs))?;
        let mut exec = drive::Exec::new(world, net, &shared);
        exec.schedule(&p.scheduled);
        exec.run();
        let events = watch
            .iter()
            .filter_map(|&n| exec.net.ids.get(n).map(|&id| (n, id)))
            .flat_map(|(n, id)| {
                exec.net
                    .sim
                    .events(id)
                    .iter()
                    .map(move |(t, e)| format!("n{n} t{t} {e:?}"))
                    .collect::<Vec<_>>()
            })
            .collect();
        Ok((finish(world, driver, layers, p, &exec, &rec, reg), events))
    })();
    Registry::uninstall();
    reg.clear();
    out
}

fn finish(
    world: &World,
    driver: Driver,
    layers: LayerSet,
    p: Plan,
    exec: &drive::Exec<'_>,
    rec: &Rc<RefCell<Rec>>,
    reg: &'static Registry,
) -> RunResult {
    let end = world.duration_ns;
    let sim = &exec.net.sim;
    let mut facts = RunFacts::new(world);
    facts.has_membership = layers.membership;
    let (mut cpu_ns, mut stack_waiting) = (0.0_f64, BTreeMap::new());
    {
        let mut r = rec.borrow_mut();
        for (i, &id) in exec.net.ids.iter().enumerate() {
            let n = sim.node(id);
            let st = sim.state(id);
            cpu_ns += n.cpu_ns() as f64;
            if n.running() {
                r.state_sample(end, i, n.state_bytes());
            }
            if n.timer_violations() > 0 {
                let msg = format!(
                    "{} timeouts were not later than the call that returned them",
                    n.timer_violations()
                );
                r.violation(end, "G-SPEC", i, &msg);
            }
            for (k, v) in &n.layers().waiting {
                *stack_waiting.entry((*k).to_owned()).or_insert(0) += v;
            }
            if let Some(f) = facts.nodes.get_mut(i) {
                *f = NodeFacts {
                    device: f.device.clone(),
                    site: exec.cur_site.get(i).copied().unwrap_or(f.site),
                    state_peak: 0,
                    view: None,
                    alive_at_end: st != NodeState::Crashed,
                    suspended_at_end: st == NodeState::Suspended,
                    export_max: n.max_export() as u64,
                };
            }
        }
        let mtu_drops = sim.metrics().dropped(DropReason::Mtu);
        if mtu_drops > 0 {
            let msg = format!("{mtu_drops} datagrams exceeded the path MTU");
            r.violation(end, "G-MEDIUM", 0, &msg);
        }
        let tap = sim.tap_stats();
        for _ in 0..tap.replayed {
            r.adversary_action("replay");
        }
        for _ in 0..tap.modified {
            r.adversary_action("modify");
        }
        let punched = exec.net.nats.iter().map(|&n| sim.nat_punched(n)).sum();
        r.finish(end, cpu_ns, punched);
    }
    let r = rec.borrow();
    let verdict = reg.sec_verdict(r.amp.values().map(|&[rx, tx]| (rx, tx)));
    facts.sec = SecFacts {
        hndl_known_payload_keys: u64::from(verdict.hndl.is_some()),
        forward_secrecy_broken: u64::from(verdict.forward_secrecy.is_some()),
        nonce_reuse: verdict.nonce_reuse.len() as u64,
        unknown_provenance: u64::from(verdict.unknown_provenance.is_some()),
        plaintext_payload: verdict.plaintext_payload.iter().map(|f| (f.node, f.at_ns)).collect(),
    };
    let (fair, fair_samples) = compute_fair_terms(world, &r, &facts);
    RunResult {
        id: world.id.clone(),
        seed: world.seed,
        driver,
        layers,
        status: p.status,
        ran: true,
        coverage: coverage_of(world, layers, &p.excluded),
        excluded: owned(&p.excluded),
        scheduled: owned(&p.scheduled_kinds),
        intents_total: world.intents.len() as u64,
        gates: evaluate_gates(world, &r, &facts),
        terms: compute_terms(world, &r, &facts),
        fair,
        fair_samples,
        samples: samples_of(&r, fair_samples.small),
        trace_hash: r.trace_hash(),
        violations: r.violations.clone(),
        stats: Stats {
            wire_bytes: r.wire_bytes,
            app_bytes: r.app_bytes,
            third_bytes: r.third_bytes,
            resumes: r.resumes.len() as u64,
            crashes: r.crashes,
            punched: r.punched_paths,
            adversary: r.adv.clone(),
            mtu_drops: sim.metrics().dropped(DropReason::Mtu),
            events: sim.events_processed(),
            drops: DropReason::ALL
                .iter()
                .filter(|r| sim.metrics().dropped(**r) > 0)
                .map(|r| (r.name().to_owned(), sim.metrics().dropped(*r)))
                .collect(),
            stack_waiting,
        },
        late: late_of(&r),
    }
}

/// Runs `world` with `driver` and `layers`. A scenario with nothing runnable is returned as `Waiting` without being
/// run. Every run happens on one long-lived thread with a large stack (the node adapter keeps half a megabyte per endpoint), which also keeps the connection tables of finished runs for the next one.
///
/// # Errors
/// A [`RunError`] when a layer flag has no registration, the world needs something the runner does not build, or the
/// run panicked.
pub fn run(world: &World, driver: Driver, layers: LayerSet) -> Result<RunResult, RunError> {
    run_watching(world, driver, layers, &[]).map(|(r, _)| r)
}

/// [`run`] that also returns the session-level events of the nodes in `watch`, one line each (`n<node> t<ns>
/// <event>`), for diagnosis.
///
/// # Errors
/// As [`run`].
pub fn run_watching(
    world: &World,
    driver: Driver,
    layers: LayerSet,
    watch: &[usize],
) -> Result<(RunResult, Vec<String>), RunError> {
    check_wiring(layers)?;
    let p = plan(world, layers);
    if matches!(p.status, Status::Waiting(_)) {
        return Ok((waiting_result(world, driver, layers, p), Vec::new()));
    }
    let (world, watch) = (world.clone(), watch.to_vec());
    let (done, result) = mpsc::channel();
    let job: Job = Box::new(move || {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| execute(&world, driver, layers, p, &watch)));
        // The caller waits for the answer; if it went away there is nobody to tell.
        let _ = done.send(r);
    });
    worker()?
        .lock()
        .map_err(|_| RunError::Panicked("the run thread failed".to_owned()))?
        .send(job)
        .map_err(|_| RunError::Panicked("the run thread ended".to_owned()))?;
    match result.recv() {
        Ok(Ok(r)) => r,
        Ok(Err(e)) => {
            let m = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default();
            Err(RunError::Panicked(m))
        }
        Err(_) => Err(RunError::Panicked("the run thread ended".to_owned())),
    }
}

/// A run, queued for the run thread.
type Job = Box<dyn FnOnce() + Send>;

/// The thread every run executes on, started on first use and kept for the life of the process: it has the large stack
/// the node adapter needs, and the connection tables of the nodes of a finished run stay with it for the next run
/// instead of being allocated again.
fn worker() -> Result<&'static Mutex<mpsc::Sender<Job>>, RunError> {
    static WORKER: OnceLock<Mutex<mpsc::Sender<Job>>> = OnceLock::new();
    if let Some(w) = WORKER.get() {
        return Ok(w);
    }
    let (tx, rx) = mpsc::channel::<Job>();
    std::thread::Builder::new()
        .name("suite-run".to_owned())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            for job in rx {
                job();
            }
        })
        .map_err(|e| RunError::Panicked(e.to_string()))?;
    Ok(WORKER.get_or_init(|| Mutex::new(tx)))
}
