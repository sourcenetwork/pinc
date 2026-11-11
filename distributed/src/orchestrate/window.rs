//! A measurement window: what the kernel counted for every node and shaper between two moments, and whether the host
//! was quiet over it. Opened before a workload's timed part and closed after it, so the numbers of the programs and of
//! the kernel cover the same span.

use crate::backend::Cluster;
use crate::error::Result;
use crate::metrics::{NodeUse, Reading};
use crate::orchestrate::Ctx;
use crate::quiet::Snapshot;
use crate::results::Row;

/// Packets the emulated links dropped so far, over every site's router.
pub(crate) async fn drops(b: &Cluster, sites: usize) -> u64 {
    let mut total = 0;
    for s in 0..sites {
        if let Ok(q) = b.shapers(s).await {
            total += q.iter().filter(|q| q.kind == "netem").map(|q| q.drops).sum::<u64>();
        }
    }
    total
}

/// The readings at the start of a window.
pub(crate) struct Window {
    before: Vec<Reading>,
    drops: u64,
    from: Snapshot,
}

impl Window {
    /// Start counting: reset the peak memory of every node and read every counter.
    pub(crate) async fn open(ctx: &Ctx, b: &Cluster) -> Result<Self> {
        let n = ctx.plan.nodes.len();
        let mut before = Vec::with_capacity(n);
        for i in 0..n {
            b.peak_reset(i).await?;
            before.push(b.reading(i).await?);
        }
        Ok(Self {
            before,
            drops: drops(b, ctx.plan.sites.len()).await,
            from: Snapshot::take(),
        })
    }

    /// Stop counting and put what the kernel measured, per node by name, in `row`.
    pub(crate) async fn close(self, ctx: &Ctx, b: &Cluster, row: &mut Row) -> Result<()> {
        // Only a run on containers has a machine whose quiet the harness can judge.
        row.host = (!matches!(b, Cluster::Ssh(_))).then(|| ctx.monitor.usage(&self.from, &Snapshot::take()));
        for (i, (node, before)) in ctx.plan.nodes.iter().zip(&self.before).enumerate() {
            let after = b.reading(i).await?;
            let peak = b.peak_read(i).await?;
            row.kernel
                .insert(node.name.clone(), NodeUse::between(before, &after, peak));
        }
        row.shaper_drops = Some(drops(b, ctx.plan.sites.len()).await.saturating_sub(self.drops));
        Ok(())
    }
}
