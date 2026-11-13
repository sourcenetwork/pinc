//! The publish and subscribe workload. For every repetition and stack (stacks interleaved, so a drift of the machine
//! touches each alike): a node program in every node, everyone joins the topic through the hubs, the group settles, the
//! publishers send at their rate while the fault schedule runs, the counts are read from every node, and the programs
//! are stopped. The programs' counts and the kernel's readings go in the row apart.

use std::collections::BTreeMap;
use std::time::Duration;

use serde_json::{Map, Value};

use crate::backend::Cluster;
use crate::error::Result;
use crate::node::data::wall_ns;
use crate::node::proto::{Cmd, PubSubReport};
use crate::orchestrate::agg::{Subscriber, merge_lives, pubsub_figures};
use crate::orchestrate::apps::AppSet;
use crate::orchestrate::window::Window;
use crate::orchestrate::{Ctx, Event, faults, tracefile};
use crate::plan::MTU;
use crate::results::Row;
use crate::scenario::Stack;
use crate::workloads::Pubsub;

/// The first message leaves this long after the schedule starts, so every publisher is ready for it.
const LEAD_NS: u64 = 1_000_000_000;

pub(crate) async fn run(ctx: &mut Ctx, b: &Cluster, w: &Pubsub) -> Result<()> {
    let nodes = ctx.sc.expand();
    let subs = w.subscribers_of(&nodes);
    let label = format!(
        "{}>{}",
        w.publishers.join("+"),
        if w.subscribers.is_empty() {
            "peers".to_owned()
        } else {
            subs.join("+")
        }
    );
    let total = u32::try_from(ctx.sc.stacks.len()).unwrap_or(u32::MAX) * ctx.reps;
    let mut index = 0;
    for rep in 0..ctx.reps {
        for &stack in &ctx.sc.stacks.clone() {
            ctx.emit(Event::Progress {
                index,
                total,
                test: w.id(),
                stack: stack.name().into(),
                rep,
                reps: ctx.reps,
                pair: label.clone(),
            });
            for attempt in 1.. {
                let row = one(ctx, b, stack, w, rep, &label).await?;
                if ctx.conclude(row, rep, attempt)? {
                    break;
                }
            }
            index += 1;
        }
    }
    Ok(())
}

fn base_row(ctx: &Ctx, stack: Stack, w: &Pubsub, rep: u32, pair: &str) -> Row {
    let mut row = Row {
        run: ctx.plan.run.clone(),
        stack: stack.name().into(),
        test: w.id(),
        pair: pair.into(),
        rep,
        status: "ok".into(),
        node: Map::new(),
        kernel: BTreeMap::new(),
        shaper_drops: None,
        host: None,
    };
    tracefile::mark(ctx, stack, &mut row);
    row
}

async fn one(ctx: &Ctx, b: &Cluster, stack: Stack, w: &Pubsub, rep: u32, pair: &str) -> Result<Row> {
    let mut row = base_row(ctx, stack, w, rep, pair);
    let set = AppSet::new(b, &ctx.plan, stack, MTU)
        .with_iroh_gossip_max(w.iroh_gossip_max)
        .with_trace(tracefile::wanted(ctx, stack));
    let outcome = body(ctx, b, &set, w, stack, &mut row).await;
    if let Some(note) = set.configs().await.into_iter().next() {
        row.node.insert("note".into(), Value::String(note));
    }
    set.stop_all().await;
    if let Err(e) = outcome {
        row.status = format!("not measured: {e}");
    }
    Ok(row)
}

async fn body(ctx: &Ctx, b: &Cluster, set: &AppSet<'_>, w: &Pubsub, stack: Stack, row: &mut Row) -> Result<()> {
    set.start_all().await?;
    set.join_all(&w.topic, w.join_s * 1000).await?;
    tokio::time::sleep(Duration::from_secs_f64(w.warmup_s)).await;
    let window = Window::open(ctx, b).await?;

    let pubs: Vec<usize> = w.publishers.iter().filter_map(|p| ctx.plan.node(p)).collect();
    // Seconds from the first message to the last, at the rate.
    let span = f64::from(w.messages) / w.rate_hz;
    let wait = Duration::from_secs_f64(span + 60.0);
    let interval_us = (1_000_000.0 / w.rate_hz).round().max(1.0);
    // The rate is positive and below a million a second; the interval fits a u64.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let interval_us = interval_us as u64;
    let start_ns = wall_ns() + LEAD_NS;
    let publishing = futures::future::join_all(pubs.iter().map(|i| {
        set.call(
            *i,
            Cmd::Publish {
                topic: w.topic.clone(),
                count: w.messages,
                size: w.size,
                interval_us,
                start_ns,
            },
            wait,
        )
    }));
    let results = faults::during(ctx, b, &ctx.sc.faults, &[], Some(set), publishing).await?;
    let mut notes = Vec::new();
    for (i, r) in pubs.iter().zip(results) {
        if let Err(e) = r {
            // A publisher the schedule killed ends its run early; what it sent before counts, and the note says so.
            let name = ctx.plan.nodes.get(*i).map_or("?", |n| n.name.as_str());
            notes.push(format!("{name} stopped publishing early ({e})"));
        }
    }
    tokio::time::sleep(Duration::from_secs_f64(w.drain_s)).await;

    // Counts from every node: what the publishers sent, and what the subscribers got.
    let published: BTreeMap<u16, u32> = pubs
        .iter()
        .filter_map(|i| u16::try_from(*i).ok().map(|i| (i, w.messages)))
        .collect();
    let specs = ctx.sc.expand();
    let sub_names = w.subscribers_of(&specs);
    let mut subs = Vec::new();
    for name in sub_names {
        let Some(i) = ctx.plan.node(name) else { continue };
        let lives: Vec<PubSubReport> = set
            .reports(i)
            .await
            .iter()
            .filter_map(|v| v.get("pubsub").and_then(|p| serde_json::from_value(p.clone()).ok()))
            .collect();
        subs.push(Subscriber {
            index: u16::try_from(i).unwrap_or(u16::MAX),
            report: (!lives.is_empty()).then(|| merge_lives(&lives, &published)),
        });
    }
    // What each node counted besides deliveries (a stack that counts nothing reports nothing).
    let mut counters = Map::new();
    for (i, n) in ctx.plan.nodes.iter().enumerate() {
        let mut sum: BTreeMap<String, u64> = BTreeMap::new();
        let reports = set.reports(i).await;
        tracefile::write(ctx, stack, row, &n.name, &reports);
        for v in reports {
            for (k, x) in v.get("counters").and_then(Value::as_object).into_iter().flatten() {
                *sum.entry(k.clone()).or_insert(0) += x.as_u64().unwrap_or(0);
            }
        }
        if !sum.is_empty() {
            counters.insert(n.name.clone(), serde_json::json!(sum));
        }
    }
    window.close(ctx, b, row).await?;
    row.node = pubsub_figures(&subs, &published);
    if !counters.is_empty() {
        row.node.insert("counters".into(), Value::Object(counters));
    }
    if !notes.is_empty() {
        row.node.insert("faults_note".into(), Value::String(notes.join("; ")));
    }
    if row.node.is_empty() {
        row.status = "not measured: no message was owed to any subscriber".into();
    }
    Ok(())
}
