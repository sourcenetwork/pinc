//! The quiet-host check: no measurement on a busy machine.
//!
//! The kernel counts the CPU time of every process (`/proc/<pid>/stat`) and the time the hypervisor took from this
//! machine (steal, `/proc/stat`). Between two snapshots, the CPU used by every process that is not part of the run is
//! the contamination; load average is not used (it decays for a minute after a job ends). Part of the run are: the
//! processes in the run's containers (by cgroup), the orchestrator and everything it started (by parent), the Docker
//! daemons and `runc` that serve its commands, and the kernel threads that move its packets (`ksoftirqd`, `kworker`, `rcu_`,
//! `migration`) and the SSH daemon that carries its output.
//!
//! Before a run the orchestrator waits (up to a deadline) for a window in which both numbers are under their
//! thresholds; during a run every measurement is judged over its own interval, and one that was not clean is repeated
//! a bounded number of times and otherwise reported as not measured.
//!
//! Invariants: a process that appears or vanishes between snapshots counts with the time it used inside the window
//! as far as the kernel can tell (its whole time when it appeared, nothing when it vanished); a missing `/proc` file is
//! skipped, never counted as zero CPU for the run's processes.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use serde::{Deserialize, Serialize};

/// When a window counts as quiet.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Thresholds {
    /// The most CPU other processes may use, in percent of one core.
    pub other_pct: f64,
    /// The most steal, in percent of the machine's CPU time.
    pub steal_pct: f64,
    /// The length of a quiet window before a run, in seconds.
    pub window_s: f64,
    /// How long to wait for a quiet window before giving up, in seconds.
    pub wait_s: f64,
    /// How many times a measurement that was not clean is repeated.
    pub retries: u32,
}

impl Default for Thresholds {
    fn default() -> Self {
        Self {
            other_pct: 3.0,
            steal_pct: 1.0,
            window_s: 5.0,
            wait_s: 600.0,
            retries: 2,
        }
    }
}

#[derive(Debug, Clone)]
struct Proc {
    ticks: u64,
    ppid: u32,
    name: String,
}

/// The CPU counters of every process and of the machine at one moment.
#[derive(Debug, Clone)]
pub struct Snapshot {
    at: Instant,
    procs: HashMap<u32, Proc>,
    total: u64,
    steal: u64,
}

/// Ticks per second of the kernel's CPU counters (`CLK_TCK`, 100 on Linux).
const HZ: f64 = 100.0;

/// One line of `/proc/<pid>/stat`: the name, the parent and the CPU ticks used (public for the tests).
pub fn parse_stat_line(text: &str) -> Option<(String, u32, u64)> {
    parse_stat(text).map(|p| (p.name, p.ppid, p.ticks))
}

fn parse_stat(text: &str) -> Option<Proc> {
    // `pid (comm) state ppid ... utime stime`: the name may hold spaces and parentheses, so split at the last ')'.
    let open = text.find('(')?;
    let close = text.rfind(')')?;
    let name = text.get(open + 1..close)?.to_owned();
    let rest: Vec<&str> = text.get(close + 2..)?.split_whitespace().collect();
    let ppid = rest.get(1)?.parse().ok()?;
    let ticks = rest.get(11)?.parse::<u64>().ok()? + rest.get(12)?.parse::<u64>().ok()?;
    Some(Proc { ticks, ppid, name })
}

fn machine() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/stat").unwrap_or_default();
    let f: Vec<u64> = s
        .lines()
        .next()
        .unwrap_or("")
        .split_whitespace()
        .skip(1)
        .filter_map(|x| x.parse().ok())
        .collect();
    // user nice system idle iowait irq softirq steal (guest time is already inside user and nice)
    let total = f.iter().take(8).sum();
    (total, f.get(7).copied().unwrap_or(0))
}

impl Snapshot {
    /// A snapshot from given counters (for the tests): each process as (pid, parent, name, ticks), and the machine's
    /// total and steal ticks.
    pub fn from_parts(at: Instant, procs: &[(u32, u32, &str, u64)], total: u64, steal: u64) -> Self {
        Self {
            at,
            procs: procs
                .iter()
                .map(|(pid, ppid, name, ticks)| {
                    (
                        *pid,
                        Proc {
                            ticks: *ticks,
                            ppid: *ppid,
                            name: (*name).to_owned(),
                        },
                    )
                })
                .collect(),
            total,
            steal,
        }
    }

    /// Read every process and the machine now.
    pub fn take() -> Self {
        let mut procs = HashMap::new();
        if let Ok(dir) = std::fs::read_dir("/proc") {
            for e in dir.flatten() {
                let Some(pid) = e.file_name().to_str().and_then(|s| s.parse::<u32>().ok()) else {
                    continue;
                };
                if let Some(p) = std::fs::read_to_string(format!("/proc/{pid}/stat"))
                    .ok()
                    .as_deref()
                    .and_then(parse_stat)
                {
                    procs.insert(pid, p);
                }
            }
        }
        let (total, steal) = machine();
        Self {
            at: Instant::now(),
            procs,
            total,
            steal,
        }
    }
}

/// What other processes and the hypervisor took over a window.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Usage {
    /// CPU used by processes outside the run, in percent of one core.
    pub other_pct: f64,
    /// Steal, in percent of the machine's CPU time.
    pub steal_pct: f64,
    /// The process outside the run that used the most, and its share of one core.
    pub top: String,
    /// The window's length in seconds.
    pub secs: f64,
    /// Whether both were under the thresholds.
    pub clean: bool,
}

/// Tells the run's processes from the others.
#[derive(Debug, Clone, Default)]
pub struct Monitor {
    /// The full ids of the run's containers (their cgroups name them).
    pub containers: Vec<String>,
    /// The thresholds.
    pub limits: Thresholds,
}

// Kernel threads that move the run's packets, the SSH daemon that carries its output, and the container runtime that
// serves its `docker exec` calls (`runc` runs once per call).
const OURS: [&str; 10] = [
    "ksoftirqd",
    "kworker",
    "rcu_",
    "migration",
    "sshd",
    "dockerd",
    "containerd",
    "docker-init",
    "runc",
    "idle_inject",
];

impl Monitor {
    fn is_run(&self, pid: u32, snap: &Snapshot, me: u32, cache: &mut HashMap<u32, bool>) -> bool {
        if let Some(v) = cache.get(&pid) {
            return *v;
        }
        let mut v = false;
        if let Some(p) = snap.procs.get(&pid) {
            if OURS.iter().any(|n| p.name.starts_with(n)) {
                v = true;
            } else if !self.containers.is_empty()
                && std::fs::read_to_string(format!("/proc/{pid}/cgroup"))
                    .is_ok_and(|c| self.containers.iter().any(|id| c.contains(id.as_str())))
            {
                v = true;
            } else {
                // A descendant of the orchestrator (its helper, Docker command lines, tc and ip).
                let mut cur = pid;
                let mut seen = HashSet::new();
                while cur > 1 && seen.insert(cur) {
                    if cur == me {
                        v = true;
                        break;
                    }
                    cur = snap.procs.get(&cur).map_or(0, |p| p.ppid);
                }
            }
        }
        cache.insert(pid, v);
        v
    }

    /// The use of everything outside the run between `a` and `b`.
    pub fn usage(&self, a: &Snapshot, b: &Snapshot) -> Usage {
        let me = std::process::id();
        let secs = b.at.duration_since(a.at).as_secs_f64().max(1e-3);
        let mut cache = HashMap::new();
        let mut other = 0u64;
        let mut top = (0u64, String::new());
        for (pid, p) in &b.procs {
            let before = a.procs.get(pid).map_or(0, |q| q.ticks);
            let d = p.ticks.saturating_sub(before);
            if d == 0 || self.is_run(*pid, b, me, &mut cache) {
                continue;
            }
            other += d;
            if d > top.0 {
                top = (d, p.name.clone());
            }
        }
        // Ticks of one window fit an f64's integer range.
        #[allow(clippy::cast_precision_loss)]
        let (other_pct, top_pct, steal_pct) = {
            let total = b.total.saturating_sub(a.total).max(1) as f64;
            (
                other as f64 / HZ / secs * 100.0,
                top.0 as f64 / HZ / secs * 100.0,
                b.steal.saturating_sub(a.steal) as f64 / total * 100.0,
            )
        };
        Usage {
            other_pct,
            steal_pct,
            top: if top.1.is_empty() {
                String::new()
            } else {
                format!("{} {top_pct:.1}%", top.1)
            },
            secs,
            clean: other_pct <= self.limits.other_pct && steal_pct <= self.limits.steal_pct,
        }
    }

    /// Wait for a quiet window of `window_s`, at most `wait_s`; every window is passed to `seen`.
    ///
    /// # Errors
    /// The deadline passed without a quiet window: the last window's numbers.
    pub async fn wait_quiet(&self, mut seen: impl FnMut(&Usage)) -> Result<Usage, Usage> {
        let deadline = Instant::now() + std::time::Duration::from_secs_f64(self.limits.wait_s);
        loop {
            let a = Snapshot::take();
            tokio::time::sleep(std::time::Duration::from_secs_f64(self.limits.window_s)).await;
            let u = self.usage(&a, &Snapshot::take());
            seen(&u);
            if u.clean {
                return Ok(u);
            }
            if Instant::now() >= deadline {
                return Err(u);
            }
        }
    }
}

/// Pin this process (every thread) to `cpus`, so the orchestrator never runs on a node's cores.
///
/// # Errors
/// `taskset` is missing or refused.
pub fn pin_self(cpus: &str) -> Result<(), String> {
    let out = std::process::Command::new("taskset")
        .args(["-a", "-c", "-p", cpus, &std::process::id().to_string()])
        .output()
        .map_err(|e| format!("taskset did not start ({e}); install util-linux"))?;
    if out.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&out.stderr).trim().to_owned())
    }
}

/// The CPU frequency governor, when the machine exposes one.
pub fn governor() -> String {
    std::fs::read_to_string("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")
        .map_or_else(|_| "not exposed by this machine".into(), |s| s.trim().to_owned())
}
