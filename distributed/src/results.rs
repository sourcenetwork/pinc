//! Results are files: `distributed/results/<date>-<scenario>/` holds `raw.jsonl` (one row per measurement: what the
//! node program reported and what the kernel measured, kept apart), `scenario.toml` (the scenario as run),
//! `run.json` (backend, host, versions, CPU sets, MTU, teardown check) and `summary.md` (the table). The dashboard
//! reads the same files through [`summarize`], so the table and the dashboard cannot disagree.
//!
//! Invariants: a value that was not measured is absent, never zero; every cell is the median with the minimum and
//! maximum over the repetitions and says how many there were; the best value of a row is marked only when two or more
//! stacks have one.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

use crate::metrics::NodeUse;

/// One measurement.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Row {
    /// The run's id.
    pub run: String,
    /// The stack.
    pub stack: String,
    /// The test's id (`setup`, `latency_64b`, ...).
    pub test: String,
    /// The nodes it ran between (`client>server`).
    pub pair: String,
    /// The repetition, from 0.
    pub rep: u32,
    /// `ok`, or why nothing was measured.
    pub status: String,
    /// What the node program reported.
    #[serde(default)]
    pub node: Map<String, Value>,
    /// What the kernel measured, by the node's role (`client`, `server`).
    #[serde(default)]
    pub kernel: BTreeMap<String, NodeUse>,
    /// Packets the shapers on the path dropped during the run (emulated loss and full queues).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub shaper_drops: Option<u64>,
    /// What other processes and the hypervisor took during the measurement, and whether it was clean.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host: Option<crate::quiet::Usage>,
}

/// The status of a measurement repeated because the host was busy.
pub const DISCARDED: &str = "discarded";

/// Whether a smaller or a larger value is better.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Better {
    /// Smaller is better.
    Lower,
    /// Larger is better.
    Higher,
    /// Neither (a count shown for context).
    None,
}

/// Where a metric comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Source {
    /// A field the node program reported.
    Node(&'static str),
    /// CPU seconds the kernel counted for a role.
    Cpu(&'static str),
    /// Peak memory the kernel counted for a role.
    Peak(&'static str),
    /// Bytes the client's interface sent and received, per byte the test moved.
    WirePerByte,
    /// Packets the shapers dropped.
    Drops,
}

/// A metric of a test.
#[derive(Debug, Clone, Copy)]
pub struct Metric {
    /// Where it comes from.
    pub source: Source,
    /// Its label.
    pub label: &'static str,
    /// Its unit.
    pub unit: &'static str,
    /// Which way is better.
    pub better: Better,
}

const fn m(source: Source, label: &'static str, unit: &'static str, better: Better) -> Metric {
    Metric {
        source,
        label,
        unit,
        better,
    }
}

/// The metrics shown for a test id.
pub fn metrics_of(test: &str) -> Vec<Metric> {
    use Better::{Higher, Lower};
    use Source::{Cpu, Drops, Node, Peak, WirePerByte};
    let kernel = [
        m(Cpu("client"), "client CPU (kernel)", "s", Lower),
        m(Cpu("server"), "server CPU (kernel)", "s", Lower),
        m(Peak("client"), "client peak memory (kernel)", "MiB", Lower),
        m(Peak("server"), "server peak memory (kernel)", "MiB", Lower),
        m(Drops, "shaper drops", "packets", Better::None),
    ];
    let mut v = match test {
        "setup" | "resume" => vec![
            m(Node("p50_us"), "time to first byte p50", "us", Lower),
            m(Node("p99_us"), "time to first byte p99", "us", Lower),
            m(Node("failed"), "failed", "", Lower),
        ],
        t if t.starts_with("latency_") => vec![
            m(Node("p50_us"), "round trip p50", "us", Lower),
            m(Node("p99_us"), "round trip p99", "us", Lower),
            m(Node("p999_us"), "round trip p99.9", "us", Lower),
            m(Node("round_trips"), "round trips", "", Better::None),
        ],
        t if t.starts_with("throughput_") => vec![
            m(Node("mib_s"), "goodput", "MiB/s", Higher),
            m(Node("streams_ok"), "streams done", "", Higher),
            m(WirePerByte, "wire bytes per payload byte", "", Lower),
        ],
        "many" => vec![
            m(Node("connected_and_moved"), "connected", "", Higher),
            m(Node("all_done_s"), "all done", "s", Lower),
            m(Node("first_byte_p50_ms"), "first byte p50", "ms", Lower),
            m(Node("first_byte_p99_ms"), "first byte p99", "ms", Lower),
            m(Node("server_kib_per_conn"), "server memory per connection", "KiB", Lower),
        ],
        _ => Vec::new(),
    };
    v.extend(kernel);
    v
}

impl Row {
    /// The value of `src` in this row, if it was measured.
    // Counters of one run fit an f64's integer range.
    #[allow(clippy::cast_precision_loss)]
    pub fn value(&self, src: Source) -> Option<f64> {
        if self.status != "ok" {
            return None;
        }
        match src {
            Source::Node(k) => self.node.get(k).and_then(Value::as_f64),
            Source::Cpu(r) => self.kernel.get(r).and_then(|k| k.cpu_s),
            Source::Peak(r) => self.kernel.get(r).and_then(|k| k.peak_mib),
            Source::WirePerByte => {
                let moved = self.node.get("bytes").and_then(Value::as_f64).filter(|b| *b > 0.0)?;
                let e = self.kernel.get("client")?.eth0?;
                Some((e.tx_bytes + e.rx_bytes) as f64 / moved)
            }
            Source::Drops => self.shaper_drops.map(|d| d as f64),
        }
    }
}

/// The spread of one cell.
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub struct Spread {
    /// The median.
    pub median: f64,
    /// The smallest value.
    pub min: f64,
    /// The largest value.
    pub max: f64,
    /// How many values.
    pub n: usize,
}

/// The spread of `v`, if it has any value.
pub fn spread(mut v: Vec<f64>) -> Option<Spread> {
    v.retain(|x| x.is_finite());
    if v.is_empty() {
        return None;
    }
    v.sort_by(f64::total_cmp);
    let n = v.len();
    let mid = |i: usize| v.get(i).copied().unwrap_or(f64::NAN);
    let median = if n % 2 == 1 { mid(n / 2) } else { f64::midpoint(mid(n / 2 - 1), mid(n / 2)) };
    Some(Spread {
        median,
        min: mid(0),
        max: mid(n - 1),
        n,
    })
}

/// One cell: a spread, or why there is none.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(untagged)]
pub enum Cell {
    /// Measured.
    Value(Spread),
    /// Not measured, and why.
    Missing(String),
}

/// One row of a summary table.
#[derive(Debug, Clone, Serialize)]
pub struct Line {
    /// The metric's label.
    pub label: String,
    /// Its unit.
    pub unit: String,
    /// Which way is better.
    pub better: Better,
    /// One cell per stack, in the table's stack order.
    pub cells: Vec<Cell>,
    /// The index of the best cell, when two or more stacks have a value.
    pub best: Option<usize>,
}

/// The table of one test between one pair.
#[derive(Debug, Clone, Serialize)]
pub struct Table {
    /// The test's id.
    pub test: String,
    /// The pair.
    pub pair: String,
    /// The stacks, in column order.
    pub stacks: Vec<String>,
    /// The rows.
    pub lines: Vec<Line>,
    /// Notes the node programs attached (for example how many resumptions were accepted).
    pub notes: Vec<String>,
}

/// Aggregate rows into tables: one per (test, pair), in the order the rows first appear.
pub fn summarize(rows: &[Row], stacks: &[String]) -> Vec<Table> {
    let mut order: Vec<(String, String)> = Vec::new();
    for r in rows {
        let k = (r.test.clone(), r.pair.clone());
        if !order.contains(&k) {
            order.push(k);
        }
    }
    order
        .into_iter()
        .map(|(test, pair)| {
            let mine: Vec<&Row> = rows.iter().filter(|r| r.test == test && r.pair == pair).collect();
            let lines = metrics_of(&test)
                .into_iter()
                .map(|met| {
                    let cells: Vec<Cell> = stacks
                        .iter()
                        .map(|s| {
                            let of: Vec<&&Row> = mine.iter().filter(|r| &r.stack == s).collect();
                            let vals: Vec<f64> = of.iter().filter_map(|r| r.value(met.source)).collect();
                            match spread(vals) {
                                Some(sp) => Cell::Value(sp),
                                None => Cell::Missing(
                                    of.iter()
                                        .map(|r| r.status.clone())
                                        .find(|st| st != "ok" && !st.starts_with(DISCARDED))
                                        .unwrap_or_else(|| "not measured".into()),
                                ),
                            }
                        })
                        .collect();
                    let best = best_of(&cells, met.better);
                    Line {
                        label: met.label.into(),
                        unit: met.unit.into(),
                        better: met.better,
                        cells,
                        best,
                    }
                })
                .collect();
            let mut notes: Vec<String> = mine
                .iter()
                .filter_map(|r| {
                    let n = r.node.get("note").and_then(Value::as_str).filter(|n| !n.is_empty())?;
                    Some(format!("{}: {n}", r.stack))
                })
                .collect();
            notes.sort();
            notes.dedup();
            let discarded = mine.iter().filter(|r| r.status.starts_with(DISCARDED)).count();
            if discarded > 0 {
                notes.push(format!("{discarded} measurement(s) discarded and repeated: the host was busy"));
            }
            Table {
                test,
                pair,
                stacks: stacks.to_vec(),
                lines,
                notes,
            }
        })
        .collect()
}

fn best_of(cells: &[Cell], better: Better) -> Option<usize> {
    let vals: Vec<(usize, f64)> = cells
        .iter()
        .enumerate()
        .filter_map(|(i, c)| if let Cell::Value(s) = c { Some((i, s.median)) } else { None })
        .collect();
    if vals.len() < 2 {
        return None;
    }
    let pick = match better {
        Better::Lower => vals.iter().min_by(|a, b| a.1.total_cmp(&b.1)),
        Better::Higher => vals.iter().max_by(|a, b| a.1.total_cmp(&b.1)),
        Better::None => None,
    }?;
    // A tie is not a win.
    (vals.iter().filter(|v| v.1 == pick.1).count() == 1).then_some(pick.0)
}

/// A number as tables show it: no needless digits.
#[allow(clippy::float_cmp, reason = "an exact integer prints without decimals")]
pub fn fmt_num(v: f64) -> String {
    let a = v.abs();
    if v == v.trunc() && a < 1e9 {
        return group(&format!("{v:.0}"));
    }
    if a >= 1000.0 {
        group(&format!("{v:.0}"))
    } else if a >= 100.0 {
        format!("{v:.0}")
    } else if a >= 10.0 {
        format!("{v:.1}")
    } else if a >= 0.01 {
        format!("{v:.2}")
    } else {
        format!("{v:.4}")
    }
}

fn group(s: &str) -> String {
    let (sign, digits) = s.strip_prefix('-').map_or(("", s), |d| ("-", d));
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    format!("{sign}{out}")
}

/// A cell as text: `median [min..max]`, or why it is missing.
pub fn fmt_cell(c: &Cell) -> String {
    match c {
        Cell::Value(s) if s.n == 1 => fmt_num(s.median),
        Cell::Value(s) => format!("{} [{}..{}]", fmt_num(s.median), fmt_num(s.min), fmt_num(s.max)),
        Cell::Missing(why) => why.replace('|', "/"),
    }
}

/// The summary as markdown: a heading with the conditions, then one table per test and pair.
pub fn markdown(title: &str, conditions: &[String], tables: &[Table]) -> String {
    let mut md = format!("# {title}\n\n");
    for c in conditions {
        let _ = writeln!(md, "{c}");
    }
    md.push_str("\nEvery cell is the median over the repetitions with [min..max]; the best value of a row is in bold.\n");
    for t in tables {
        let _ = write!(md, "\n## {} ({})\n\n| metric | {} |\n|---|", t.test, t.pair, t.stacks.join(" | "));
        md.push_str(&"---|".repeat(t.stacks.len()));
        md.push('\n');
        for l in &t.lines {
            let unit = if l.unit.is_empty() { String::new() } else { format!(" ({})", l.unit) };
            let cells: Vec<String> = l
                .cells
                .iter()
                .enumerate()
                .map(|(i, c)| if l.best == Some(i) { format!("**{}**", fmt_cell(c)) } else { fmt_cell(c) })
                .collect();
            let _ = writeln!(md, "| {}{} | {} |", l.label, unit, cells.join(" | "));
        }
        for n in &t.notes {
            let _ = writeln!(md, "\n{n}");
        }
    }
    md
}

/// Read every row of a results directory.
///
/// # Errors
/// The file cannot be read.
pub fn read_rows(dir: &Path) -> std::io::Result<Vec<Row>> {
    let text = std::fs::read_to_string(dir.join("raw.jsonl"))?;
    Ok(text.lines().filter_map(|l| serde_json::from_str(l).ok()).collect())
}

/// The days since 1970-01-01 as a civil date `YYYY-MM-DD` (proleptic Gregorian).
pub fn civil_date(days: i64) -> String {
    // Howard Hinnant's days-to-civil algorithm.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}-{m:02}-{d:02}")
}

/// Today's date (UTC).
pub fn today() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    civil_date(i64::try_from(secs / 86_400).unwrap_or(0))
}

/// A fresh directory `<root>/<date>-<scenario>` (with `-2`, `-3`, ... when that is taken).
///
/// # Errors
/// It cannot be created.
pub fn fresh_dir(root: &Path, scenario: &str) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(root)?;
    let base = format!("{}-{scenario}", today());
    for i in 1..1000 {
        let name = if i == 1 { base.clone() } else { format!("{base}-{i}") };
        let p = root.join(name);
        match std::fs::create_dir(&p) {
            Ok(()) => return Ok(p),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e),
        }
    }
    Err(std::io::Error::other("too many results directories for this scenario today"))
}
