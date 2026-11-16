//! The reach workload: for every repetition and stack, a node program in every node, the group joined, a pause for the
//! server's port mapping and its record to settle, then the client dials the server by its node id and reports the
//! session's path when it came up and after a hold. The row says whether the path was direct, the server's mapping and
//! class, and the client's own class.

use std::collections::BTreeMap;
use std::time::Duration;

use serde_json::{Map, Value, json};

use crate::backend::Cluster;
use crate::error::Result;
use crate::node::proto::Cmd;
use crate::orchestrate::apps::AppSet;
use crate::orchestrate::{Ctx, Event, tracefile};
use crate::results::Row;
use crate::scenario::Stack;
use crate::workloads::Reach;

pub(crate) async fn run(ctx: &mut Ctx, b: &Cluster, w: &Reach) -> Result<()> {
    let label = format!("{}>{}", w.client, w.server);
    let total = u32::try_from(ctx.sc.stacks.len()).unwrap_or(u32::MAX) * ctx.reps;
    let mut index = 0;
    for rep in 0..ctx.reps {
        for &stack in &ctx.sc.stacks.clone() {
            ctx.emit(Event::Progress {
                index,
                total,
                test: Reach::ID.into(),
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

async fn one(ctx: &Ctx, b: &Cluster, stack: Stack, w: &Reach, rep: u32, pair: &str) -> Result<Row> {
    let mut r = Row {
        run: ctx.plan.run.clone(),
        stack: stack.name().into(),
        test: Reach::ID.into(),
        pair: pair.into(),
        rep,
        status: "ok".into(),
        node: Map::new(),
        kernel: BTreeMap::new(),
        shaper_drops: None,
        host: None,
    };
    tracefile::mark(ctx, stack, &mut r);
    let set = AppSet::new(b, &ctx.plan, stack).with_trace(tracefile::wanted(ctx, stack));
    let outcome = body(ctx, &set, w, &mut r).await;
    tracefile::save(ctx, &set, stack, &r).await;
    set.stop_all().await;
    if let Err(e) = outcome {
        r.status = format!("not measured: {e}");
    }
    Ok(r)
}

/// A node's port mapping and class, from its report.
fn portmap_of(report: &Value) -> Value {
    report.get("portmap").cloned().unwrap_or(Value::Null)
}

async fn body(ctx: &Ctx, set: &AppSet<'_>, w: &Reach, r: &mut Row) -> Result<()> {
    set.start_all().await?;
    set.join_all("reach", 60_000).await?;
    let (Some(server), Some(client)) = (ctx.plan.node(&w.server), ctx.plan.node(&w.client)) else {
        r.status = "not measured: a node of the pair is not in the plan".into();
        return Ok(());
    };
    tokio::time::sleep(Duration::from_secs_f64(w.settle_s)).await;
    let wait = Duration::from_secs(10);
    let server_pm = portmap_of(&set.call(server, Cmd::Report, wait).await?);
    let client_pm = portmap_of(&set.call(client, Cmd::Report, wait).await?);
    r.node.insert("server_portmap".into(), server_pm.clone());
    r.node.insert("client_portmap".into(), client_pm);
    r.node.insert(
        "server_mapped".into(),
        json!(u8::from(server_pm.get("mapped").is_some_and(|m| !m.is_null()))),
    );
    let cmd = Cmd::Reach {
        peer: w.server.clone(),
        timeout_ms: w.timeout_s * 1000,
        hold_ms: Duration::from_secs_f64(w.hold_s)
            .as_millis()
            .try_into()
            .unwrap_or(u64::MAX),
    };
    let limit = Duration::from_secs(w.timeout_s) + Duration::from_secs_f64(w.hold_s) + Duration::from_secs(10);
    match set.call(client, cmd, limit).await {
        Ok(v) => {
            let relayed = v.pointer("/held/relayed").and_then(Value::as_bool);
            r.node.insert("direct".into(), json!(u8::from(relayed == Some(false))));
            for k in ["ms", "first", "held"] {
                if let Some(x) = v.get(k) {
                    r.node.insert(k.into(), x.clone());
                }
            }
            // The server's state after the session, renewals included.
            let after = portmap_of(&set.call(server, Cmd::Report, wait).await?);
            r.node.insert("server_portmap_after".into(), after);
        }
        Err(e) => r.status = format!("failed: {e}"),
    }
    Ok(())
}
