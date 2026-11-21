//! The delay-tolerant workload. For every size, repetition and stack: a node program in every node with the layer on
//! for the peers, the group joined, the contact windows set, then the bundles sent at their times while the fault
//! schedule takes nodes away and brings them back. When the repetition's time is up, every node's log is read against
//! the scenario's checks (see [`crate::dtn`]) and the row says which rule failed, if one did.
//!
//! A stack without delay-tolerant delivery runs the baseline when the scenario asks for one: the same sends as one
//! publication each, with no store and forward, and the row says how many reached their destination.

use std::collections::BTreeMap;
use std::time::Duration;

use serde_json::{Map, Value, json};

use crate::backend::Cluster;
use crate::dtn::{self as rules, Dtn, Logs, Sent};
use crate::error::{Error, Result};
use crate::node::data::wall_ns;
use crate::node::pinc::node_id;
use crate::node::proto::{Cmd, Contact, DtnInit, DtnReport, PubSubReport};
use crate::orchestrate::apps::{AppSet, QUICK};
use crate::orchestrate::window::Window;
use crate::orchestrate::{Ctx, Event, faults};
use crate::results::Row;
use crate::scenario::Stack;

/// The seed of the first bundle's payload; each bundle adds its number.
const SEED: u64 = 0xd7_0000;

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

pub(crate) async fn run(ctx: &mut Ctx, b: &Cluster, w: &Dtn) -> Result<()> {
    let mut label: Vec<String> = w.sends.iter().map(|s| format!("{}>{}", s.from, s.to)).collect();
    label.dedup();
    let label = label.join(",");
    let total = u32::try_from(w.sizes.len() * ctx.sc.stacks.len()).unwrap_or(u32::MAX) * ctx.reps;
    let mut index = 0;
    for &size in &w.sizes {
        for rep in 0..ctx.reps {
            for &stack in &ctx.sc.stacks.clone() {
                ctx.emit(Event::Progress {
                    index,
                    total,
                    test: rules::id(size),
                    stack: stack.name().into(),
                    rep,
                    reps: ctx.reps,
                    pair: label.clone(),
                });
                for attempt in 1.. {
                    let row = one(ctx, b, stack, w, size, rep, &label).await?;
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

async fn one(ctx: &Ctx, b: &Cluster, stack: Stack, w: &Dtn, size: u64, rep: u32, pair: &str) -> Result<Row> {
    let mut r = row(ctx, stack, &rules::id(size), pair, rep);
    let nonce = wall_ns();
    let plan = &ctx.plan;
    let sealed = w.sealed_len(size).unwrap_or(size);
    let set = AppSet::new(b, plan, stack)
        .with_identity_salt(ctx.sc.identity_salt())
        .with_dtn(|i| {
            let n = plan.nodes.get(i)?;
            if stack != Stack::Pinc || !rules::runs_layer(n.role) {
                return None;
            }
            let own = w.node(&n.name);
            #[allow(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                clippy::cast_precision_loss
            )]
            let budget = own
                .and_then(|o| o.budget_bundles)
                .map_or(64 << 20, |k| (k * sealed as f64) as u64);
            Some(DtnInit {
                budget,
                retry_ms: 3_000,
                max_sends: 8,
                dir: own
                    .filter(|o| o.persist)
                    .map(|_| format!("/tmp/pinc-dtn/{nonce}/{}", n.name)),
                tamper_slices: own.is_some_and(|o| o.tamper_slices),
                tamper_one_slice: own.is_some_and(|o| o.tamper_one_slice),
                tamper_heads: own.is_some_and(|o| o.tamper_heads),
            })
        });
    let outcome = if stack == Stack::Pinc {
        body(ctx, b, &set, w, size, &mut r).await
    } else {
        baseline(ctx, b, &set, w, size, &mut r).await
    };
    if let Some(note) = set.configs().await.into_iter().next() {
        r.node.insert("note".into(), Value::String(note));
    }
    set.stop_all().await;
    if let Err(e) = outcome {
        r.status = format!("not measured: {e}");
    }
    Ok(r)
}

/// The windows of node `name`, as its program takes them.
fn windows_of(w: &Dtn, name: &str) -> Option<Vec<Contact>> {
    if w.contacts.is_empty() {
        return None;
    }
    let ms = |s: f64| {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let v = (s * 1000.0) as u64;
        v
    };
    Some(
        w.contacts
            .iter()
            .filter_map(|c| {
                let peer = if c.a == name {
                    &c.b
                } else if c.b == name {
                    &c.a
                } else {
                    return None;
                };
                Some(Contact {
                    peer: peer.clone(),
                    from_ms: ms(c.from_s),
                    to_ms: ms(c.to_s),
                })
            })
            .collect(),
    )
}

async fn body(ctx: &Ctx, b: &Cluster, set: &AppSet<'_>, w: &Dtn, size: u64, r: &mut Row) -> Result<()> {
    set.start_all().await?;
    set.join_all("dtn", 60_000).await?;
    tokio::time::sleep(Duration::from_secs_f64(w.warmup_s)).await;
    let layer: Vec<usize> = (0..ctx.plan.nodes.len())
        .filter(|i| ctx.plan.nodes.get(*i).is_some_and(|n| rules::runs_layer(n.role)))
        .collect();
    let t0_ms = wall_ns() / 1_000_000;
    for &i in &layer {
        let name = ctx.plan.nodes.get(i).map_or("", |n| n.name.as_str());
        set.call_kept(
            i,
            Cmd::DtnContacts {
                t0_ms,
                windows: windows_of(w, name),
            },
            QUICK,
        )
        .await?;
    }
    let window = Window::open(ctx, b).await?;
    let start = tokio::time::Instant::now();
    let work = async {
        let mut bundles = Vec::new();
        let mut order: Vec<_> = w.sends.iter().collect();
        order.sort_by(|x, y| x.at_s.total_cmp(&y.at_s));
        let mut seed = SEED;
        for s in order {
            tokio::time::sleep_until(start + Duration::from_secs_f64(s.at_s)).await;
            let from = ctx
                .plan
                .node(&s.from)
                .ok_or_else(|| Error::Node(format!("there is no node {}", s.from)))?;
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let lifetime_ms = (s.lifetime_s * 1000.0) as u64;
            for _ in 0..s.count {
                seed += 1;
                let at_ms = wall_ns() / 1_000_000;
                let v = set
                    .call(
                        from,
                        Cmd::DtnSend {
                            to: s.to.clone(),
                            size,
                            seed,
                            copies: s.copies,
                            lifetime_ms,
                            k: s.k,
                            m: s.m,
                            slice_log: s.slice_log,
                        },
                        QUICK,
                    )
                    .await?;
                let bundle = v
                    .get("bundle")
                    .and_then(Value::as_str)
                    .ok_or_else(|| Error::Node(format!("{} named no bundle", s.from)))?;
                bundles.push(Sent {
                    bundle: bundle.to_owned(),
                    from: s.from.clone(),
                    to: s.to.clone(),
                    copies: s.copies,
                    at_ms,
                    lifetime_ms,
                });
            }
        }
        tokio::time::sleep_until(start + Duration::from_secs_f64(w.duration_s)).await;
        Ok::<_, Error>(bundles)
    };
    let bundles = faults::during(ctx, b, &ctx.sc.faults, &[], Some(set), work).await??;
    window.close(ctx, b, r).await?;
    judge(ctx, set, w, &layer, &bundles, t0_ms, size, r).await;
    Ok(())
}

/// Read every node's log against the checks and write the outcome into the row.
#[allow(
    clippy::too_many_arguments,
    reason = "the parts of one repetition, passed on from its body"
)]
async fn judge(
    ctx: &Ctx,
    set: &AppSet<'_>,
    w: &Dtn,
    layer: &[usize],
    bundles: &[Sent],
    t0_ms: u64,
    size: u64,
    r: &mut Row,
) {
    let mut logs: Logs = BTreeMap::new();
    for &i in layer {
        let Some(n) = ctx.plan.nodes.get(i) else { continue };
        let lives: Vec<DtnReport> = set
            .reports(i)
            .await
            .into_iter()
            .filter_map(|v| serde_json::from_value(v.get("dtn")?.clone()).ok())
            .collect();
        logs.insert(n.name.clone(), lives);
    }
    let salt = ctx.sc.identity_salt();
    let o = rules::evaluate(&w.checks, bundles, &logs, t0_ms, |n| {
        node_id(n, salt).ok().map(|id| id.bytes)
    });
    r.node.extend(o.metrics);
    r.node.insert("checks_passed".into(), json!(o.passed));
    r.node.insert("checks".into(), json!(w.checks.len()));
    #[allow(clippy::cast_precision_loss)]
    r.node.insert("bytes".into(), json!(size as f64 * bundles.len() as f64));
    r.node.insert("logs".into(), json!(logs));
    if let Some(first) = o.failures.first() {
        r.status = format!(
            "failed: {first}{}",
            if o.failures.len() > 1 {
                format!(" (and {} more)", o.failures.len() - 1)
            } else {
                String::new()
            }
        );
        r.node.insert("failures".into(), json!(o.failures));
    }
}

/// The same sends as one publication each, on a stack with no store and forward.
async fn baseline(ctx: &Ctx, b: &Cluster, set: &AppSet<'_>, w: &Dtn, size: u64, r: &mut Row) -> Result<()> {
    set.start_all().await?;
    set.join_all("dtn", 60_000).await?;
    tokio::time::sleep(Duration::from_secs_f64(w.warmup_s)).await;
    let window = Window::open(ctx, b).await?;
    let start = tokio::time::Instant::now();
    let body = u32::try_from(size.clamp(16, 1 << 20)).unwrap_or(1 << 20);
    let work = async {
        let mut order: Vec<_> = w.sends.iter().collect();
        order.sort_by(|x, y| x.at_s.total_cmp(&y.at_s));
        for s in order {
            tokio::time::sleep_until(start + Duration::from_secs_f64(s.at_s)).await;
            let from = ctx
                .plan
                .node(&s.from)
                .ok_or_else(|| Error::Node(format!("there is no node {}", s.from)))?;
            set.call(
                from,
                Cmd::Publish {
                    topic: "dtn".into(),
                    count: s.count,
                    size: body,
                    interval_us: 1_000,
                    start_ns: 0,
                },
                QUICK,
            )
            .await?;
        }
        tokio::time::sleep_until(start + Duration::from_secs_f64(w.duration_s)).await;
        Ok::<_, Error>(())
    };
    faults::during(ctx, b, &ctx.sc.faults, &[], Some(set), work).await??;
    window.close(ctx, b, r).await?;
    let mut published = 0u64;
    let mut got = 0u64;
    for s in &w.sends {
        let (Some(from), Some(to)) = (ctx.plan.node(&s.from), ctx.plan.node(&s.to)) else {
            continue;
        };
        published += u64::from(s.count);
        let origin = u16::try_from(from).unwrap_or(u16::MAX);
        for v in set.reports(to).await {
            if let Some(p) = v
                .get("pubsub")
                .and_then(|p| serde_json::from_value::<PubSubReport>(p.clone()).ok())
            {
                got += p.per_origin.get(&origin).copied().unwrap_or(0);
            }
        }
    }
    #[allow(clippy::cast_precision_loss)]
    r.node.insert(
        "delivered".into(),
        json!(got.min(published) as f64 / published.max(1) as f64),
    );
    #[allow(clippy::cast_precision_loss)]
    r.node.insert("bytes".into(), json!(size as f64 * published as f64));
    r.node.insert(
        "baseline".into(),
        json!("one publication per bundle on the stack's pubsub, no store and forward"),
    );
    Ok(())
}
