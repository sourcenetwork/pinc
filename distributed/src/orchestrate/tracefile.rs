//! The node traces a scenario's `[debug] trace = true` asks for: after a measurement every PINC node's trace and
//! packet log is written beside the results as `trace-<stack>-<test>-rep<k>-<node>.json`, and the row says its
//! timings are not comparable.

use serde_json::Value;

use crate::orchestrate::Ctx;
use crate::orchestrate::apps::AppSet;
use crate::results::Row;
use crate::scenario::Stack;

/// What a traced row says about its timings.
const NOTE: &str = "node traces were recorded: timings are not comparable";

/// Whether the nodes of `stack` record traces in this run (only PINC's do).
pub(crate) fn wanted(ctx: &Ctx, stack: Stack) -> bool {
    ctx.sc.debug.trace && stack == Stack::Pinc
}

/// Say on `row` that its nodes recorded traces.
pub(crate) fn mark(ctx: &Ctx, stack: Stack, row: &mut Row) {
    if wanted(ctx, stack) {
        row.node.insert("trace_note".into(), Value::String(NOTE.into()));
    }
}

/// Write the traces in `reports`, the reports of node `node` (one per life of the program), when tracing is on. A
/// file that cannot be written is logged, not fatal: the measurement is worth more than its trace.
pub(crate) fn write(ctx: &Ctx, stack: Stack, row: &Row, node: &str, reports: &[Value]) {
    if !wanted(ctx, stack) {
        return;
    }
    let traces = reports.iter().filter_map(|r| r.get("trace"));
    for (life, t) in traces.enumerate() {
        let suffix = if life == 0 {
            String::new()
        } else {
            format!("-life{}", life + 1)
        };
        let file = format!("trace-{}-{}-rep{}-{node}{suffix}.json", row.stack, row.test, row.rep);
        let path = ctx.dir.join(&file);
        let bytes = serde_json::to_vec(t).unwrap_or_default();
        if let Err(e) = std::fs::write(&path, bytes) {
            ctx.log(
                "warn",
                format!("the trace of {node} could not be written to {}: {e}", path.display()),
            );
        }
    }
}

/// Ask every node for its report and write the traces (the workloads that do not collect reports themselves).
pub(crate) async fn save(ctx: &Ctx, set: &AppSet<'_>, stack: Stack, row: &Row) {
    if !wanted(ctx, stack) {
        return;
    }
    for (i, n) in ctx.plan.nodes.iter().enumerate() {
        write(ctx, stack, row, &n.name, &set.reports(i).await);
    }
}
