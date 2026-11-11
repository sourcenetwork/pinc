//! The orchestrator: validate a scenario, plan it, bring the network up, run the workload with its faults for every
//! stack and repetition, write the results, and always tear down, also on a signal or a failed node.
//!
//! Everything it does is also published as [`Event`]s, which the dashboard streams; `run` logs them.

mod faults;
pub mod live;
mod transport;

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use tokio::sync::{broadcast, watch};

use crate::backend::containers::{self, Containers};
use crate::error::{Error, Result};
use crate::plan::{MTU, Plan};
use crate::quiet::{self, Monitor, Snapshot, Thresholds, Usage};
use crate::results::{self, Row};
use crate::scenario::{Scenario, Workload};

pub use faults::FaultRunner;

/// What happened, as the dashboard and the log show it.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Event {
    /// A run started.
    Started {
        /// The run's id.
        run: String,
        /// The scenario's name.
        scenario: String,
        /// Where its results go.
        results: String,
        /// The stacks, in the order they run.
        stacks: Vec<String>,
        /// Repetitions of each measurement.
        reps: u32,
        /// Measurements in all.
        total: u32,
        /// The fault schedule of each repetition.
        faults: Vec<crate::scenario::Fault>,
    },
    /// The network as built.
    Topology(Box<live::Topology>),
    /// What other processes and the hypervisor took in a window: the quiet-host check.
    Quiet(Box<Usage>),
    /// A sample of every node and shaper.
    Sample(Box<live::Sample>),
    /// A step of the run.
    Phase {
        /// What it is doing.
        what: String,
    },
    /// A measurement is starting.
    Progress {
        /// Its number, from 0.
        index: u32,
        /// Measurements in all.
        total: u32,
        /// The test's id.
        test: String,
        /// The stack.
        stack: String,
        /// The repetition, from 0.
        rep: u32,
        /// Repetitions in all.
        reps: u32,
        /// The pair.
        pair: String,
    },
    /// A measurement finished.
    Row(Box<Row>),
    /// A fault was injected.
    Fault {
        /// Seconds into the repetition.
        at_s: f64,
        /// What was done, in words.
        what: String,
        /// The fault as the scenario has it.
        action: crate::scenario::FaultAction,
    },
    /// A line for the log pane.
    Log {
        /// `info`, `warn` or `error`.
        level: String,
        /// The message.
        msg: String,
    },
    /// The run ended and everything was torn down (or what is left is listed).
    Ended {
        /// Whether the run completed.
        ok: bool,
        /// Why it did not.
        error: Option<String>,
        /// Where its results are.
        results: String,
        /// What the teardown check still found.
        left: Vec<String>,
    },
}

/// What a run needs besides the scenario.
#[derive(Debug, Clone)]
pub struct Options {
    /// The node image.
    pub image: String,
    /// Where results directories go.
    pub results: PathBuf,
    /// Repetitions instead of the scenario's (a smoke run); the summary says so.
    pub reps: Option<u32>,
    /// Where events go; with a receiver attached, nodes and shapers are also sampled for the dashboard.
    pub events: Option<broadcast::Sender<Event>>,
    /// Set to true to stop the run (it tears down as on a signal).
    pub cancel: Option<watch::Receiver<bool>>,
    /// When the host counts as quiet enough to measure.
    pub quiet: Thresholds,
}

/// The machine the backend runs on.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HostInfo {
    /// The CPU model.
    pub cpu: String,
    /// CPUs.
    pub cpus: usize,
    /// Memory in GiB.
    pub mem_gib: f64,
    /// The kernel release.
    pub kernel: String,
}

impl HostInfo {
    /// Read this machine.
    pub fn read() -> Self {
        let cpuinfo = std::fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
        let meminfo = std::fs::read_to_string("/proc/meminfo").unwrap_or_default();
        let kb: f64 = meminfo
            .lines()
            .find_map(|l| l.strip_prefix("MemTotal:")?.split_whitespace().next()?.parse().ok())
            .unwrap_or(0.0);
        Self {
            cpu: cpuinfo
                .lines()
                .find_map(|l| Some(l.strip_prefix("model name")?.split_once(':')?.1.trim().to_owned()))
                .unwrap_or_else(|| "unknown".into()),
            cpus: std::thread::available_parallelism().map_or(1, std::num::NonZero::get),
            mem_gib: (kb / 1_048_576.0 * 10.0).round() / 10.0,
            kernel: std::fs::read_to_string("/proc/sys/kernel/osrelease")
                .map_or_else(|_| "unknown".into(), |s| s.trim().to_owned()),
        }
    }
}

/// The versions of the stacks this binary was built with, from its lockfile.
pub fn versions() -> Vec<(String, String)> {
    let lock = include_str!("../../Cargo.lock");
    ["iroh", "noq", "libp2p", "libp2p-quic", "quinn", "tokio", "nuclei"]
        .iter()
        .filter_map(|name| {
            let needle = format!("name = \"{name}\"\nversion = \"");
            let at = lock.find(&needle)? + needle.len();
            let v = lock.get(at..)?.split('"').next()?;
            Some(((*name).to_owned(), v.to_owned()))
        })
        .collect()
}

fn now_s() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs())
}

fn run_id() -> String {
    let n = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_nanos());
    let mix = (n ^ (u128::from(std::process::id()) << 40)) & 0xff_ffff;
    format!("{mix:06x}")
}

/// The orchestrator's own handles, shared by the workload drivers.
pub(crate) struct Ctx {
    pub(crate) plan: Plan,
    pub(crate) sc: Scenario,
    pub(crate) reps: u32,
    events: Option<broadcast::Sender<Event>>,
    raw: std::fs::File,
    quiet_log: std::fs::File,
    pub(crate) monitor: Monitor,
}

impl Ctx {
    pub(crate) fn emit(&self, ev: Event) {
        match &ev {
            Event::Log { level, msg } if level == "error" => tracing::error!("{msg}"),
            Event::Log { level, msg } if level == "warn" => tracing::warn!("{msg}"),
            Event::Log { msg, .. } | Event::Phase { what: msg } => tracing::info!("{msg}"),
            Event::Progress {
                test,
                stack,
                rep,
                reps,
                pair,
                ..
            } => {
                tracing::info!(test, stack, rep = rep + 1, reps, pair, "measuring");
            }
            Event::Row(r) => tracing::info!(
                test = r.test,
                stack = r.stack,
                rep = r.rep + 1,
                status = r.status,
                "measured"
            ),
            Event::Fault { at_s, what, .. } => tracing::info!(at_s, "fault: {what}"),
            Event::Quiet(u) if !u.clean => tracing::warn!(
                other_pct = u.other_pct,
                steal_pct = u.steal_pct,
                top = u.top,
                "the host is busy"
            ),
            Event::Started { .. } | Event::Ended { .. } | Event::Topology(_) | Event::Sample(_) | Event::Quiet(_) => {}
        }
        if let Some(tx) = &self.events {
            let _ = tx.send(ev);
        }
    }

    pub(crate) fn log(&self, level: &str, msg: impl Into<String>) {
        self.emit(Event::Log {
            level: level.into(),
            msg: msg.into(),
        });
    }

    /// Keep one window of the quiet-host check in the results and show it.
    pub(crate) fn quiet(&mut self, what: &str, u: &Usage) {
        note_quiet(&mut self.quiet_log, what, u);
        self.emit(Event::Quiet(Box::new(u.clone())));
    }

    pub(crate) fn record(&mut self, row: Row) -> Result<()> {
        use std::io::Write;
        let line = serde_json::to_string(&row).map_err(|e| Error::Io(std::io::Error::other(e)))?;
        writeln!(self.raw, "{line}")?;
        self.emit(Event::Row(Box::new(row)));
        Ok(())
    }
}

fn note_quiet(log: &mut std::fs::File, what: &str, u: &Usage) {
    use std::io::Write;
    let v = serde_json::json!({ "at": now_s(), "what": what, "usage": u });
    // The samples are provenance; a failed write is reported in the log and the run goes on.
    if let Err(e) = writeln!(log, "{v}") {
        tracing::warn!("the quiet-host samples could not be written: {e}");
    }
}

/// Every few seconds, the quiet-host check over the last window, kept and shown; runs until dropped.
async fn quiet_sampler(monitor: Monitor, mut log: std::fs::File, events: Option<broadcast::Sender<Event>>) {
    let mut a = Snapshot::take();
    loop {
        tokio::time::sleep(std::time::Duration::from_secs(5)).await;
        let b = Snapshot::take();
        let u = monitor.usage(&a, &b);
        note_quiet(&mut log, "during the run", &u);
        if let Some(tx) = &events {
            let _ = tx.send(Event::Quiet(Box::new(u)));
        }
        a = b;
    }
}

/// Resolves when the process gets SIGINT, SIGTERM or SIGHUP; never when the handlers cannot be installed.
pub async fn signalled() {
    use tokio::signal::unix::{SignalKind, signal};
    let (Ok(mut term), Ok(mut hup), Ok(mut int)) = (
        signal(SignalKind::terminate()),
        signal(SignalKind::hangup()),
        signal(SignalKind::interrupt()),
    ) else {
        tracing::warn!("signal handlers could not be installed; stop the run with `vinc-distributed clean`");
        return std::future::pending().await;
    };
    tokio::select! {
        _ = term.recv() => {}
        _ = hup.recv() => {}
        _ = int.recv() => {}
    }
}

/// Resolves when `cancel` turns true; never without one.
async fn cancelled(cancel: Option<watch::Receiver<bool>>) {
    let Some(mut rx) = cancel else {
        return std::future::pending().await;
    };
    if rx.wait_for(|c| *c).await.is_err() {
        std::future::pending::<()>().await;
    }
}

/// What a run produced.
#[derive(Debug)]
pub struct Outcome {
    /// Its results directory.
    pub dir: PathBuf,
    /// Its error, if it did not complete.
    pub error: Option<Error>,
    /// What the teardown check still found.
    pub left: Vec<String>,
}

/// Run a scenario to the end on the container backend and return where its results are.
///
/// # Errors
/// The scenario does not validate, or its results directory cannot be written. Failures after the network is up
/// end the run, are written to the results and returned in [`Outcome::error`].
#[allow(
    clippy::too_many_lines,
    reason = "one run from validation to teardown, read top to bottom"
)]
pub async fn run(sc: Scenario, opts: Options) -> Result<Outcome> {
    let problems = sc.validate();
    if !problems.is_empty() {
        return Err(Error::Scenario(problems));
    }
    let host = HostInfo::read();
    let run = run_id();
    let plan = Plan::new(&sc, &run, host.cpus);
    let dir = results::fresh_dir(&opts.results, &sc.name)?;
    std::fs::write(
        dir.join("scenario.toml"),
        sc.to_toml().map_err(|e| Error::Io(std::io::Error::other(e)))?,
    )?;
    let raw = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(dir.join("raw.jsonl"))?;
    let quiet_log = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(dir.join("quiet.jsonl"))?;
    let reps = opts.reps.unwrap_or(sc.repetitions);
    // The orchestrator, its helper and the Docker command lines it starts run on CPU 0, which no node uses.
    if host.cpus > 1
        && let Err(e) = quiet::pin_self("0")
    {
        tracing::warn!("the orchestrator could not be pinned to CPU 0: {e}");
    }
    let mut ctx = Ctx {
        plan,
        sc,
        reps,
        events: opts.events.clone(),
        raw,
        quiet_log,
        monitor: Monitor {
            containers: Vec::new(),
            limits: opts.quiet,
        },
    };
    let total = match &ctx.sc.workload {
        Workload::Transport(t) => t.pairs.len() * t.tests.len(),
    } * ctx.sc.stacks.len()
        * reps as usize;
    ctx.emit(Event::Started {
        run: run.clone(),
        scenario: ctx.sc.name.clone(),
        results: dir.display().to_string(),
        stacks: ctx.sc.stacks.iter().map(|s| s.name().to_owned()).collect(),
        reps,
        total: u32::try_from(total).unwrap_or(u32::MAX),
        faults: ctx.sc.faults.clone(),
    });
    let started = now_s();
    let mut backend: Option<Containers> = None;
    let result = {
        let work = async {
            ctx.emit(Event::Phase {
                what: format!(
                    "creating {} node and {} router containers and wiring them",
                    ctx.plan.nodes.len(),
                    ctx.plan.sites.len()
                ),
            });
            let b: &Containers = backend.insert(Containers::up(&ctx.plan, &opts.image).await?);
            let pos: Vec<Option<[f64; 2]>> = ctx.sc.sites.iter().map(|s| s.pos).collect();
            let topo = live::Topology::of(&ctx.plan, &pos);
            ctx.emit(Event::Topology(Box::new(topo.clone())));
            ctx.monitor.containers = b.scopes();
            ctx.emit(Event::Phase {
                what: format!(
                    "network up; waiting for the host to be quiet (other processes under {}% of a core, steal under {}%)",
                    ctx.monitor.limits.other_pct, ctx.monitor.limits.steal_pct
                ),
            });
            let mut windows = Vec::new();
            let waited = ctx.monitor.wait_quiet(|u| windows.push(u.clone())).await;
            for u in &windows {
                ctx.quiet("before the run", u);
            }
            if let Err(u) = waited {
                return Err(Error::Host(format!(
                    "the host stayed busy for {} s (other processes {:.1}% of a core, steal {:.2}%, most: {}); nothing was measured",
                    ctx.monitor.limits.wait_s, u.other_pct, u.steal_pct, u.top
                )));
            }
            ctx.emit(Event::Phase {
                what: "the host is quiet; measuring".into(),
            });
            let watch = quiet_sampler(ctx.monitor.clone(), ctx.quiet_log.try_clone()?, opts.events.clone());
            let sampling = async {
                match &opts.events {
                    Some(tx) => live::sampler(b, &topo, tx.clone()).await,
                    None => std::future::pending().await,
                }
            };
            let workload = async {
                match ctx.sc.workload.clone() {
                    Workload::Transport(t) => transport::run(&mut ctx, b, &t).await,
                }
            };
            tokio::select! {
                r = workload => r,
                () = sampling => Ok(()),
                () = watch => Ok(()),
            }
        };
        tokio::select! {
            r = work => r,
            () = signalled() => Err(Error::Interrupted),
            () = cancelled(opts.cancel.clone()) => Err(Error::Interrupted),
        }
    };
    ctx.emit(Event::Phase {
        what: "tearing down".into(),
    });
    let image_id = backend.as_ref().map(|b| b.image_id().to_owned());
    let left = match backend.as_mut() {
        Some(b) => b.down().await,
        None => containers::clean().await.map(|c| c.left),
    }
    .unwrap_or_else(|e| vec![format!("the teardown failed: {e}")]);
    let error = result.err();
    write_run(
        &dir,
        &ctx,
        &host,
        &run,
        image_id.as_deref(),
        started,
        error.as_ref(),
        &left,
        opts.reps,
    )?;
    let rows = results::read_rows(&dir).unwrap_or_default();
    let stacks: Vec<String> = ctx.sc.stacks.iter().map(|s| s.name().to_owned()).collect();
    let tables = results::summarize(&rows, &stacks);
    let md = results::markdown(&ctx.sc.name, &conditions(&ctx, &host, opts.reps), &tables);
    std::fs::write(dir.join("summary.md"), md)?;
    ctx.emit(Event::Ended {
        ok: error.is_none() && left.is_empty(),
        error: error.as_ref().map(ToString::to_string),
        results: dir.display().to_string(),
        left: left.clone(),
    });
    Ok(Outcome { dir, error, left })
}

/// The lines every summary starts with: what was emulated, on what, and with which resources.
fn conditions(ctx: &Ctx, host: &HostInfo, reps_override: Option<u32>) -> Vec<String> {
    let mut c = vec![
        ctx.sc.about.clone(),
        String::new(),
        format!(
            "Backend: containers on one machine ({}, {} CPUs, {} GiB, kernel {}). One kernel and its CPUs emulate the whole network: every node, router and shaper shares them.",
            host.cpu, host.cpus, host.mem_gib, host.kernel
        ),
        format!(
            "Every interface has an MTU of {MTU}. Each node: {} CPU(s) of its own set, {} MiB; CPU sets {}{}.",
            ctx.sc.resources.cpus,
            ctx.sc.resources.memory_mib,
            ctx.plan
                .nodes
                .iter()
                .map(|n| format!("{} {}", n.name, n.container.cpus))
                .collect::<Vec<_>>()
                .join(", "),
            if ctx.plan.shared_cpus {
                " (shared: the machine has fewer CPUs than the scenario asks)"
            } else {
                ""
            }
        ),
        format!(
            "Versions: {}; VINC at commit {}.",
            versions()
                .iter()
                .map(|(k, v)| format!("{k} {v}"))
                .collect::<Vec<_>>()
                .join(", "),
            git_commit()
        ),
        format!(
            "Isolation: one stack at a time on the same cores; repetitions alternate the stacks ({}), all in this one run of one build. The orchestrator runs on CPU 0, which no node uses.",
            ctx.sc.stacks.iter().map(|s| s.name()).collect::<Vec<_>>().join(", ")
        ),
        format!(
            "Quiet host: a measurement counts only when other processes used at most {}% of one core and steal was at most {}% over it; one that was not clean is repeated up to {} times, then reported as not measured. Repetitions: {}.",
            ctx.monitor.limits.other_pct, ctx.monitor.limits.steal_pct, ctx.monitor.limits.retries, ctx.reps
        ),
    ];
    if reps_override.is_some() {
        c.push("**A reduced run (fewer repetitions than the scenario asks): do not quote it.**".into());
    }
    c
}

#[allow(clippy::too_many_arguments)]
fn write_run(
    dir: &Path,
    ctx: &Ctx,
    host: &HostInfo,
    run: &str,
    image: Option<&str>,
    started: u64,
    error: Option<&Error>,
    left: &[String],
    reps_override: Option<u32>,
) -> Result<()> {
    let nodes: Vec<serde_json::Value> = ctx
        .plan
        .nodes
        .iter()
        .map(|n| {
            serde_json::json!({
                "name": n.name, "site": ctx.plan.sites.get(n.site).map(|s| s.name.clone()), "ip": n.ip.to_string(),
                "cpus": n.container.cpus, "memory_mib": n.container.memory_mib,
            })
        })
        .collect();
    let v = serde_json::json!({
        "run": run,
        "scenario": ctx.sc.name,
        "backend": "containers",
        "about_backend": "one machine emulates the network: nodes, routers and shapers share its kernel and CPUs",
        "host": host,
        "image": image,
        "mtu": MTU,
        "versions": versions().into_iter().collect::<std::collections::BTreeMap<_, _>>(),
        "git": git_commit(),
        "stack_code": {
            "vinc": format!("this repository at {}", git_commit()),
            "iroh": versions().into_iter().find(|(k, _)| k == "iroh").map(|(_, v)| format!("crates.io iroh {v}")),
            "libp2p": versions().into_iter().find(|(k, _)| k == "libp2p").map(|(_, v)| format!("crates.io libp2p {v}")),
        },
        "governor": quiet::governor(),
        "orchestrator_cpus": "0",
        "isolation": "one stack at a time on the same cores; repetitions alternate the stacks; one run, one build",
        "quiet": ctx.monitor.limits,
        "quiet_samples": "quiet.jsonl (before and during the run) and each row's host field (over the measurement)",
        "nodes": nodes,
        "shared_cpus": ctx.plan.shared_cpus,
        "repetitions": ctx.reps,
        "reduced": reps_override.is_some(),
        "started": started,
        "ended": now_s(),
        "status": error.map_or_else(|| "ok".to_owned(), ToString::to_string),
        "teardown_left": left,
    });
    std::fs::write(dir.join("run.json"), serde_json::to_vec_pretty(&v).unwrap_or_default())?;
    Ok(())
}

/// The commit the harness and VINC were built from, with `+changes` when the tree had uncommitted changes.
fn git_commit() -> String {
    let git = |args: &[&str]| {
        std::process::Command::new("git")
            .arg("-C")
            .arg(env!("CARGO_MANIFEST_DIR"))
            .args(args)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
    };
    match git(&["rev-parse", "--short", "HEAD"]) {
        Some(c) if git(&["status", "--porcelain", "--untracked-files=no"]).is_some_and(|s| !s.is_empty()) => {
            format!("{c}+changes")
        }
        Some(c) => c,
        None => "unknown".into(),
    }
}
