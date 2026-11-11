//! The value sync workload and the set reconciliation workload. For every size, repetition and stack: a node program in
//! every node, the group joined, the providers hold the value (outside the timed part), the consumers fetch it all at
//! once while the fault schedule runs, and the time each took, as the consumer's own program measured it, goes in the
//! row with the kernel's readings.

use std::collections::BTreeMap;
use std::time::Duration;

use serde_json::{Map, Value, json};

use crate::backend::Cluster;
use crate::error::{Error, Result};
use crate::node::proto::Cmd;
use crate::orchestrate::apps::AppSet;
use crate::orchestrate::window::Window;
use crate::orchestrate::{Ctx, Event, faults};
use crate::plan::MTU;
use crate::results::Row;
use crate::scenario::Stack;
use crate::workloads::{Reconcile, ValueSync};

/// The seed of the value every stack serves, so all of them move the same bytes.
const VALUE_SEED: u64 = 0x5eed_0001;

fn row(ctx: &Ctx, stack: Stack, test: &str, pair: &str, rep: u32) -> Row {
    Row {
        run: ctx.plan.run.clone(),
        stack: stack.name().into(),
        test: test.into(),
        pair: pair.into(),
        rep,
        status: "ok".into(),
        node: Map::new(),
        kernel: BTreeMap::new(),
        shaper_drops: None,
        host: None,
    }
}

/// Median of the numbers, none when there are none.
fn median(mut v: Vec<f64>) -> Option<f64> {
    v.sort_by(f64::total_cmp);
    let n = v.len();
    let mid = |i: usize| v.get(i).copied();
    if n == 0 {
        None
    } else if n % 2 == 1 {
        mid(n / 2)
    } else {
        mid(n / 2 - 1).zip(mid(n / 2)).map(|(a, b)| f64::midpoint(a, b))
    }
}

pub(crate) async fn run_sync(ctx: &mut Ctx, b: &Cluster, w: &ValueSync) -> Result<()> {
    let label = format!("{}>{}", w.providers.join("+"), w.consumers.join("+"));
    let total = u32::try_from(w.sizes.len() * ctx.sc.stacks.len()).unwrap_or(u32::MAX) * ctx.reps;
    let mut index = 0;
    for &size in &w.sizes {
        for rep in 0..ctx.reps {
            for &stack in &ctx.sc.stacks.clone() {
                ctx.emit(Event::Progress {
                    index,
                    total,
                    test: ValueSync::id(size),
                    stack: stack.name().into(),
                    rep,
                    reps: ctx.reps,
                    pair: label.clone(),
                });
                for attempt in 1.. {
                    let row = sync_one(ctx, b, stack, w, size, rep, &label).await?;
                    if ctx.conclude(row, rep, attempt)? {
                        break;
                    }
                }
                index += 1;
            }
        }
    }
    Ok(())
}

async fn sync_one(ctx: &Ctx, b: &Cluster, stack: Stack, w: &ValueSync, size: u64, rep: u32, pair: &str) -> Result<Row> {
    let mut r = row(ctx, stack, &ValueSync::id(size), pair, rep);
    let set = AppSet::new(b, &ctx.plan, stack, MTU);
    let outcome = sync_body(ctx, b, &set, w, size, &mut r).await;
    if let Some(note) = set.configs().await.into_iter().next() {
        r.node.insert("note".into(), Value::String(note));
    }
    set.stop_all().await;
    if let Err(e) = outcome {
        r.status = format!("not measured: {e}");
    }
    Ok(r)
}

async fn sync_body(ctx: &Ctx, b: &Cluster, set: &AppSet<'_>, w: &ValueSync, size: u64, r: &mut Row) -> Result<()> {
    set.start_all().await?;
    set.join_all("sync", 60_000).await?;
    let providers: Vec<usize> = w.providers.iter().filter_map(|p| ctx.plan.node(p)).collect();
    let consumers: Vec<usize> = w.consumers.iter().filter_map(|p| ctx.plan.node(p)).collect();
    // Every provider holds the same value; the first one's answer says how to ask for it.
    let mut value = Value::Null;
    for i in &providers {
        let v = set
            .call(*i, Cmd::Provide { size, seed: VALUE_SEED }, Duration::from_secs(600))
            .await?;
        if value.is_null() {
            value = v;
        }
    }
    tokio::time::sleep(Duration::from_secs_f64(w.warmup_s)).await;
    let window = Window::open(ctx, b).await?;
    let timeout = Duration::from_secs(w.timeout_s);
    let fetching = futures::future::join_all(consumers.iter().map(|i| {
        set.call(
            *i,
            Cmd::Fetch {
                value: value.clone(),
                providers: w.providers.clone(),
                timeout_ms: w.timeout_s * 1000,
            },
            timeout + Duration::from_secs(10),
        )
    }));
    let results = faults::during(ctx, b, &ctx.sc.faults, &[], Some(set), fetching).await?;
    window.close(ctx, b, r).await?;
    let mut times = Vec::new();
    let mut failures = Vec::new();
    for (i, res) in consumers.iter().zip(results) {
        match res {
            Ok(v) => match v.get("ms").and_then(Value::as_f64) {
                Some(ms) => times.push(ms),
                None => failures.push("a consumer reported no time".to_owned()),
            },
            Err(Error::Node(m) | Error::Timeout(m)) => failures.push(m),
            Err(e) => failures.push(format!(
                "{}: {e}",
                ctx.plan.nodes.get(*i).map_or("?", |n| n.name.as_str())
            )),
        }
    }
    if !failures.is_empty() {
        r.status = format!(
            "failed: {} of {} fetches did not complete ({})",
            failures.len(),
            consumers.len(),
            failures.first().map_or("", String::as_str)
        );
        return Ok(());
    }
    let slowest = times.iter().copied().fold(0.0, f64::max);
    let mid = median(times.clone()).unwrap_or(0.0);
    r.node.insert("fetch_ms".into(), json!(mid));
    r.node.insert("fetch_ms_slowest".into(), json!(slowest));
    #[allow(clippy::cast_precision_loss)]
    if mid > 0.0 {
        r.node
            .insert("mib_s".into(), json!(size as f64 / 1_048_576.0 / (mid / 1000.0)));
    }
    // Payload moved in all: every consumer fetched the whole value.
    #[allow(clippy::cast_precision_loss)]
    r.node
        .insert("bytes".into(), json!(size as f64 * consumers.len() as f64));
    Ok(())
}

pub(crate) async fn run_reconcile(ctx: &mut Ctx, b: &Cluster, w: &Reconcile) -> Result<()> {
    let label = format!("{}>{}", w.b, w.a);
    let cases: Vec<(u32, u32)> = w
        .items
        .iter()
        .flat_map(|n| w.differences.iter().map(move |d| (*n, *d)))
        .collect();
    let total = u32::try_from(cases.len() * ctx.sc.stacks.len()).unwrap_or(u32::MAX) * ctx.reps;
    let mut index = 0;
    for (items, diff) in cases {
        for rep in 0..ctx.reps {
            for &stack in &ctx.sc.stacks.clone() {
                ctx.emit(Event::Progress {
                    index,
                    total,
                    test: Reconcile::id(items, diff),
                    stack: stack.name().into(),
                    rep,
                    reps: ctx.reps,
                    pair: label.clone(),
                });
                for attempt in 1.. {
                    let row = rec_one(ctx, b, stack, w, (items, diff), rep, &label).await?;
                    if ctx.conclude(row, rep, attempt)? {
                        break;
                    }
                }
                index += 1;
            }
        }
    }
    Ok(())
}

async fn rec_one(
    ctx: &Ctx,
    b: &Cluster,
    stack: Stack,
    w: &Reconcile,
    (items, diff): (u32, u32),
    rep: u32,
    pair: &str,
) -> Result<Row> {
    let mut r = row(ctx, stack, &Reconcile::id(items, diff), pair, rep);
    let set = AppSet::new(b, &ctx.plan, stack, MTU);
    let outcome = rec_body(ctx, b, &set, w, (items, diff), &mut r).await;
    if let Some(note) = set.configs().await.into_iter().next() {
        r.node.insert("note".into(), Value::String(note));
    }
    set.stop_all().await;
    if let Err(e) = outcome {
        r.status = format!("not measured: {e}");
    }
    Ok(r)
}

#[allow(
    clippy::many_single_char_names,
    reason = "the two holders are a and b, as in the scenario file"
)]
async fn rec_body(
    ctx: &Ctx,
    b: &Cluster,
    set: &AppSet<'_>,
    w: &Reconcile,
    (items, diff): (u32, u32),
    r: &mut Row,
) -> Result<()> {
    set.start_all().await?;
    set.join_all("sets", 60_000).await?;
    let (Some(a), Some(bi)) = (ctx.plan.node(&w.a), ctx.plan.node(&w.b)) else {
        return Err(Error::Node("a holder is not a node of the plan".into()));
    };
    // Both hold the same items but the last `diff`, which are different on each side.
    for (i, other_seed) in [(a, 0xa001_u64), (bi, 0xb002)] {
        set.call(
            i,
            Cmd::HoldSet {
                set: "s".into(),
                items,
                seed: 0x5e75,
                different: diff,
                other_seed,
            },
            Duration::from_secs(600),
        )
        .await?;
    }
    tokio::time::sleep(Duration::from_secs_f64(w.warmup_s)).await;
    let window = Window::open(ctx, b).await?;
    let round = set.call(
        bi,
        Cmd::Reconcile {
            peer: w.a.clone(),
            set: "s".into(),
            timeout_ms: w.timeout_s * 1000,
        },
        Duration::from_secs(w.timeout_s + 10),
    );
    let res = faults::during(ctx, b, &ctx.sc.faults, &[], Some(set), round).await?;
    window.close(ctx, b, r).await?;
    match res {
        Ok(v) => {
            let n = |k: &str| v.get(k).and_then(Value::as_u64);
            let ms = v.get("ms").and_then(Value::as_f64);
            if n("missing_here") != Some(u64::from(diff)) || n("missing_there") != Some(u64::from(diff)) {
                r.status = format!(
                    "failed: the difference found ({} and {}) is not the {diff} items on each side",
                    n("missing_here").map_or_else(|| "?".to_owned(), |x| x.to_string()),
                    n("missing_there").map_or_else(|| "?".to_owned(), |x| x.to_string())
                );
            } else if let Some(ms) = ms {
                r.node.insert("round_ms".into(), json!(ms));
                r.node.insert("found".into(), json!(u64::from(diff) * 2));
            }
        }
        Err(Error::Node(m) | Error::Timeout(m)) => r.status = format!("failed: {m}"),
        Err(e) => return Err(e),
    }
    Ok(())
}
