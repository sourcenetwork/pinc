//! The transport workload: the comparison benches' scenarios between pairs of nodes. For every pair, test,
//! repetition and stack (stacks interleaved, so a drift of the machine touches each alike): a fresh server program in
//! the server's node, a fresh client program in the client's node, the kernel's readings of both nodes and of every
//! shaper before and after, then both programs stopped.

use std::collections::BTreeMap;
use std::time::Duration;

use serde_json::{Map, Value};

use crate::backend::Cluster;
use crate::backend::containers::READY;
use crate::error::Result;
use crate::metrics::NodeUse;
use crate::orchestrate::faults::{self, Launch};
use crate::orchestrate::window::drops;
use crate::orchestrate::{Ctx, Event};
use crate::quiet::Snapshot;
use crate::results::Row;
use crate::scenario::{Stack, Transport, TransportTest, VincEndpoints};

/// The environment of a node program: the address it binds and the interface size VINC states.
pub(crate) fn node_env(ip: std::net::Ipv4Addr, mtu: u32) -> Vec<(String, String)> {
    vec![
        ("VINC_BENCH_BIND".into(), ip.to_string()),
        ("VINC_BENCH_MTU".into(), mtu.to_string()),
    ]
}

/// The node program's arguments, then the options of the test (`--endpoints=per-core`, `--reading=...`).
fn args(stack: Stack, rest: &[String], options: &[String]) -> Vec<String> {
    let mut a = vec!["node".into(), "transport".into(), "--stack".into(), stack.name().into()];
    a.extend_from_slice(rest);
    a.extend_from_slice(options);
    a
}

pub(crate) async fn run(ctx: &mut Ctx, b: &Cluster, t: &Transport) -> Result<()> {
    let total = u32::try_from(t.pairs.len() * t.tests.len() * ctx.sc.stacks.len()).unwrap_or(u32::MAX) * ctx.reps;
    let mut index = 0;
    for pair in &t.pairs {
        let (Some(ci), Some(si)) = (ctx.plan.node(&pair.client), ctx.plan.node(&pair.server)) else {
            continue;
        };
        let label = format!("{}>{}", pair.client, pair.server);
        for test in &t.tests {
            for rep in 0..ctx.reps {
                for &stack in &ctx.sc.stacks.clone() {
                    ctx.emit(Event::Progress {
                        index,
                        total,
                        test: test.id(),
                        stack: stack.name().into(),
                        rep,
                        reps: ctx.reps,
                        pair: label.clone(),
                    });
                    for attempt in 1.. {
                        let row = one(ctx, b, (ci, si), stack, test, rep, t.timeout_s, &label).await?;
                        if ctx.conclude(row, rep, attempt)? {
                            break;
                        }
                    }
                    index += 1;
                }
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
async fn one(
    ctx: &Ctx,
    b: &Cluster,
    (ci, si): (usize, usize),
    stack: Stack,
    test: &TransportTest,
    rep: u32,
    timeout_s: u64,
    pair: &str,
) -> Result<Row> {
    let mut row = Row {
        run: ctx.plan.run.clone(),
        stack: stack.name().into(),
        test: test.id(),
        pair: pair.into(),
        rep,
        status: "ok".into(),
        node: Map::new(),
        kernel: BTreeMap::new(),
        shaper_drops: None,
        host: None,
    };
    if ctx.plan.nodes.get(ci).is_none() || ctx.plan.nodes.get(si).is_none() {
        row.status = "not measured: the pair's nodes are not in the plan".into();
        return Ok(row);
    }
    // Only VINC's many test: every other test and stack runs on one endpoint.
    let per_core = stack == Stack::Vinc
        && ctx.sc.vinc_endpoints == VincEndpoints::PerCore
        && matches!(test, TransportTest::Many { .. });
    let mut options = Vec::new();
    if per_core {
        options.push("--endpoints=per-core".to_owned());
    }
    if let TransportTest::Many { reading, .. } = test {
        options.push(format!("--reading={}", reading.name()));
    }
    let server_args = args(stack, &["server".into()], &options);
    let server_env = node_env(b.address(&ctx.plan, si).0, ctx.plan.mtu);
    let mut srv = b.spawn(si, &server_args, &server_env)?;
    let addr = match srv.expect("ADDR ", READY).await {
        Ok(a) => a,
        Err(e) => {
            row.status = format!("not measured: the server did not start ({e})");
            srv.close().await;
            b.stop(si).await?;
            return Ok(row);
        }
    };
    for i in [ci, si] {
        b.peak_reset(i).await?;
    }
    let (c0, s0, d0) = (
        b.reading(ci).await?,
        b.reading(si).await?,
        drops(b, ctx.plan.sites.len()).await,
    );
    let mut client_args = vec!["client".into(), addr];
    client_args.extend(test.client_args());
    let client_args = args(stack, &client_args, &options);
    let quiet_from = Snapshot::take();
    let mut cli = b.spawn(ci, &client_args, &node_env(b.address(&ctx.plan, ci).0, ctx.plan.mtu))?;
    let launches = [Launch {
        node: si,
        args: server_args,
        env: server_env,
    }];
    let (lines, ended) = faults::during(
        ctx,
        b,
        &ctx.sc.faults,
        &launches,
        None,
        cli.drain(Duration::from_secs(timeout_s)),
    )
    .await?;
    row.host = (!matches!(b, Cluster::Ssh(_))).then(|| ctx.monitor.usage(&quiet_from, &Snapshot::take()));
    let (c1, s1, d1) = (
        b.reading(ci).await?,
        b.reading(si).await?,
        drops(b, ctx.plan.sites.len()).await,
    );
    let (pc, ps) = (b.peak_read(ci).await?, b.peak_read(si).await?);
    if !ended {
        row.status = format!("not measured: timed out after {timeout_s} s");
    }
    let tail = cli.stderr_tail().await;
    cli.close().await;
    srv.close().await;
    b.stop(ci).await?;
    b.stop(si).await?;
    let id = test.scenario();
    let found = lines
        .iter()
        .filter_map(|l| serde_json::from_str::<Map<String, Value>>(l).ok())
        .find(|m| m.get("scenario").and_then(Value::as_str) == Some(id.as_str()));
    match found {
        Some(m) => {
            if let Some(st) = m.get("status").and_then(Value::as_str).filter(|s| *s != "ok")
                && row.status == "ok"
                && !m.contains_key("p50_us")
                && !m.contains_key("mib_s")
                && !m.contains_key("connected_and_moved")
            {
                row.status = st.to_owned();
            }
            row.node = m;
        }
        None if row.status == "ok" => {
            row.status = format!(
                "not measured: the client printed no result ({})",
                tail.lines().last().unwrap_or("no error output")
            );
        }
        None => {}
    }
    row.kernel.insert("client".into(), NodeUse::between(&c0, &c1, pc));
    row.kernel.insert("server".into(), NodeUse::between(&s0, &s1, ps));
    row.shaper_drops = Some(d1.saturating_sub(d0));
    Ok(row)
}

#[cfg(test)]
mod tests {
    use super::node_env;

    #[test]
    fn the_nodes_are_told_the_scenarios_interface_size() {
        let env = node_env("10.1.0.2".parse().unwrap_or(std::net::Ipv4Addr::UNSPECIFIED), 1280);
        assert!(env.contains(&("VINC_BENCH_MTU".to_owned(), "1280".to_owned())));
        assert!(env.contains(&("VINC_BENCH_BIND".to_owned(), "10.1.0.2".to_owned())));
    }
}
