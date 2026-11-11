//! The fault schedule of a repetition: links reshaped, cut and restored, sites partitioned and healed, nodes paused,
//! killed and restarted, each at its time into the repetition, while the workload runs. Afterwards everything is put
//! back as the scenario has it, so the next repetition starts on the same network.

use std::collections::BTreeSet;
use std::time::Duration;

use crate::backend::Proc;
use crate::backend::containers::Containers;
use crate::error::{Error, Result};
use crate::orchestrate::{Ctx, Event};
use crate::plan::{Plan, ShapePoint, cut};
use crate::scenario::{Fault, FaultAction, Shape};

/// What the faults of one repetition changed, so it can be undone.
#[derive(Debug, Default)]
pub struct FaultRunner {
    changed: Vec<(ShapePoint, Shape)>,
    paused: BTreeSet<usize>,
    /// Programs started again by `restart`, closed when the repetition ends.
    pub restarted: Vec<Proc>,
}

/// How a node's program is started, for `restart`.
#[derive(Debug, Clone)]
pub struct Launch {
    /// The node.
    pub node: usize,
    /// The program's arguments.
    pub args: Vec<String>,
    /// Its environment.
    pub env: Vec<(String, String)>,
}

impl FaultRunner {
    /// Apply one fault now.
    ///
    /// # Errors
    /// The backend failed to apply it.
    pub async fn apply(&mut self, b: &Containers, plan: &Plan, f: &FaultAction, launches: &[Launch]) -> Result<String> {
        let link = |a: &str, c: &str| {
            plan.link_points(a, c)
                .ok_or_else(|| Error::Node(format!("there is no link between {a} and {c}")))
        };
        let node = |n: &str| plan.node(n).ok_or_else(|| Error::Node(format!("there is no node {n}")));
        match f {
            FaultAction::Set { a, b: c, shape } => {
                for (p, s) in link(a, c)? {
                    self.reshape(b, p, s.patched(shape), s).await?;
                }
                Ok(format!("link {a} to {c} reshaped"))
            }
            FaultAction::Cut { a, b: c } => {
                for (p, s) in link(a, c)? {
                    self.reshape(b, p, cut(), s).await?;
                }
                Ok(format!("link {a} to {c} cut"))
            }
            FaultAction::Restore { a, b: c } => {
                for (p, s) in link(a, c)? {
                    b.reshape(&p, &s).await?;
                    self.changed.retain(|(q, _)| q != &p);
                }
                Ok(format!("link {a} to {c} restored"))
            }
            FaultAction::Partition { site } | FaultAction::Heal { site } => {
                let s = plan
                    .site(site)
                    .ok_or_else(|| Error::Node(format!("there is no site {site}")))?;
                let heal = matches!(f, FaultAction::Heal { .. });
                for other in plan.site_links(s) {
                    for (p, shape) in link(site, &other)? {
                        if heal {
                            b.reshape(&p, &shape).await?;
                            self.changed.retain(|(q, _)| q != &p);
                        } else {
                            self.reshape(b, p, cut(), shape).await?;
                        }
                    }
                }
                Ok(format!("site {site} {}", if heal { "healed" } else { "partitioned" }))
            }
            FaultAction::Pause { node: n } => {
                let i = node(n)?;
                b.pause(i, true).await?;
                self.paused.insert(i);
                Ok(format!("node {n} paused"))
            }
            FaultAction::Resume { node: n } => {
                let i = node(n)?;
                b.pause(i, false).await?;
                self.paused.remove(&i);
                Ok(format!("node {n} resumed"))
            }
            FaultAction::Kill { node: n } => {
                b.stop(node(n)?).await?;
                Ok(format!("node {n} killed"))
            }
            FaultAction::Restart { node: n } => {
                let i = node(n)?;
                let l = launches
                    .iter()
                    .find(|l| l.node == i)
                    .ok_or_else(|| Error::Node(format!("node {n} runs no program to restart")))?;
                self.restarted.push(b.spawn(i, &l.args, &l.env)?);
                Ok(format!("node {n} restarted"))
            }
        }
    }

    async fn reshape(&mut self, b: &Containers, p: ShapePoint, to: Shape, original: Shape) -> Result<()> {
        b.reshape(&p, &to).await?;
        if !self.changed.iter().any(|(q, _)| q == &p) {
            self.changed.push((p, original));
        }
        Ok(())
    }

    /// Put back every link and node this runner changed.
    ///
    /// # Errors
    /// The backend failed; the first error is returned after every undo was tried.
    pub async fn reset(&mut self, b: &Containers) -> Result<()> {
        let mut first = None;
        for (p, s) in self.changed.drain(..) {
            if let Err(e) = b.reshape(&p, &s).await {
                first.get_or_insert(e);
            }
        }
        for i in std::mem::take(&mut self.paused) {
            if let Err(e) = b.pause(i, false).await {
                first.get_or_insert(e);
            }
        }
        for p in self.restarted.drain(..) {
            p.close().await;
        }
        first.map_or(Ok(()), Err)
    }
}

/// Run `work` while the faults happen at their times; stop the schedule when `work` ends, then undo the faults.
///
/// # Errors
/// A fault could not be applied or undone (the workload's own result is returned otherwise).
pub(crate) async fn during<T>(
    ctx: &Ctx,
    b: &Containers,
    faults: &[Fault],
    launches: &[Launch],
    work: impl Future<Output = T>,
) -> Result<T> {
    let mut runner = FaultRunner::default();
    let mut order: Vec<&Fault> = faults.iter().collect();
    order.sort_by(|x, y| x.at_s.total_cmp(&y.at_s));
    let start = tokio::time::Instant::now();
    let schedule = async {
        for f in order {
            tokio::time::sleep_until(start + Duration::from_secs_f64(f.at_s.max(0.0))).await;
            match runner.apply(b, &ctx.plan, &f.action, launches).await {
                Ok(what) => ctx.emit(Event::Fault {
                    at_s: f.at_s,
                    what,
                    action: f.action.clone(),
                }),
                Err(e) => return e,
            }
        }
        // Every fault is in; the workload decides when the repetition ends.
        std::future::pending::<Error>().await
    };
    let out = tokio::select! {
        r = work => Ok(r),
        e = schedule => Err(e),
    };
    let undo = runner.reset(b).await;
    let out = out?;
    undo?;
    Ok(out)
}
