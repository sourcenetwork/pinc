//! The node programs of a workload as the orchestrator holds them: one long-lived program per node that takes requests
//! and answers them (see `node::proto`), started in the node's container, and the set of them for one repetition with
//! the lifecycle the fault schedule needs (a node killed and started again, a node asked to sleep before it is paused).
//!
//! Invariants: a request is answered once or fails with the reason; a program that ends takes its pending requests with
//! it as errors; what a killed node counted before it died is kept and added to what its next life counts.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use serde_json::Value;
use tokio::sync::{mpsc, oneshot};

use crate::backend::Cluster;
use crate::backend::containers::READY;
use crate::error::{Error, Result};
use crate::node::proto::{Cmd, DtnInit, Init, PeerSpec, Ready, Reply, Request};
use crate::plan::Plan;
use crate::scenario::{Role, Stack};

type Pending = Arc<Mutex<HashMap<u64, oneshot::Sender<Reply>>>>;

/// One running node program.
#[derive(Debug, Clone)]
pub(crate) struct AppNode {
    name: String,
    lines: mpsc::UnboundedSender<String>,
    pending: Pending,
    next: Arc<AtomicU64>,
    /// What the program announced when it was up.
    pub(crate) ready: Ready,
}

impl AppNode {
    /// Start the program in node `i` with `init` and wait until its stack is up.
    pub(crate) async fn start(b: &Cluster, i: usize, init: &Init) -> Result<Self> {
        let mut proc = b.spawn(i, &["node".to_owned(), "app".to_owned()], &[])?;
        let line = serde_json::to_string(init).map_err(|e| Error::Node(e.to_string()))?;
        proc.send(&line).await?;
        let first = match proc.expect("READY ", READY).await {
            Ok(l) => l,
            Err(e) => {
                let tail = proc.stderr_tail().await;
                proc.close().await;
                return Err(Error::Node(format!(
                    "{}: the {} node did not start: {e} {tail}",
                    init.name, init.stack
                )));
            }
        };
        let ready: Ready = serde_json::from_str(&first).map_err(|e| Error::Node(format!("{}: {e}", init.name)))?;
        let pending: Pending = Arc::default();
        let (lines, mut rx) = mpsc::unbounded_channel::<String>();
        let table = Arc::clone(&pending);
        tokio::spawn(async move {
            loop {
                tokio::select! {
                    out = rx.recv() => match out {
                        Some(l) => if proc.send(&l).await.is_err() { break },
                        None => break,
                    },
                    l = proc.line(Duration::from_secs(3600)) => match l {
                        Ok(Some(l)) => {
                            if let Ok(rep) = serde_json::from_str::<Reply>(&l)
                                && let Ok(mut t) = table.lock()
                                && let Some(tx) = t.remove(&rep.re)
                            {
                                let _ = tx.send(rep);
                            }
                        }
                        Ok(None) => break,
                        // An hour of silence is not an end; keep waiting.
                        Err(_) => {}
                    },
                }
            }
            // Pending requests learn the program ended when their senders drop.
            if let Ok(mut t) = table.lock() {
                t.clear();
            }
            proc.close().await;
        });
        Ok(Self {
            name: init.name.clone(),
            lines,
            pending,
            next: Arc::new(AtomicU64::new(1)),
            ready,
        })
    }

    /// Ask the program to do `cmd` and wait up to `wait` for the answer.
    pub(crate) async fn call(&self, cmd: Cmd, wait: Duration) -> Result<Value> {
        let id = self.next.fetch_add(1, Ordering::Relaxed);
        let (tx, rx) = oneshot::channel();
        self.pending
            .lock()
            .map_err(|_| Error::Node("the request table is unavailable".into()))?
            .insert(id, tx);
        let line = serde_json::to_string(&Request { id, cmd }).map_err(|e| Error::Node(e.to_string()))?;
        self.lines
            .send(line)
            .map_err(|_| Error::Node(format!("{}: the node program ended", self.name)))?;
        match tokio::time::timeout(wait, rx).await {
            Ok(Ok(rep)) if rep.ok => Ok(rep.data),
            Ok(Ok(rep)) => Err(Error::Node(format!(
                "{}: {}",
                self.name,
                rep.error.unwrap_or_else(|| "the request failed".into())
            ))),
            Ok(Err(_)) => Err(Error::Node(format!("{}: the node program ended", self.name))),
            Err(_) => {
                if let Ok(mut t) = self.pending.lock() {
                    t.remove(&id);
                }
                Err(Error::Timeout(format!(
                    "{} did not answer in {} s",
                    self.name,
                    wait.as_secs()
                )))
            }
        }
    }
}

/// The node programs of one repetition.
pub(crate) struct AppSet<'a> {
    b: &'a Cluster,
    plan: &'a Plan,
    inits: Vec<Init>,
    slots: Vec<tokio::sync::Mutex<Option<AppNode>>>,
    /// The topic and the wait for a node that starts again to rejoin.
    rejoin: Mutex<Option<(String, u64)>>,
    /// Reports of lives that ended, by node.
    archived: Mutex<Vec<Vec<Value>>>,
    /// Requests a node that starts again is sent again, by node, in order.
    replay: Mutex<Vec<Vec<Cmd>>>,
}

/// How long a request that is not a long-running one may take.
pub(crate) const QUICK: Duration = Duration::from_secs(60);

impl<'a> AppSet<'a> {
    /// The set-up of every node of the plan for `stack`.
    pub(crate) fn new(b: &'a Cluster, plan: &'a Plan, stack: Stack) -> Self {
        let peers: Vec<PeerSpec> = plan
            .nodes
            .iter()
            .enumerate()
            .map(|(i, n)| {
                let (ip, public_ip, slot) = b.address(plan, i);
                PeerSpec {
                    name: n.name.clone(),
                    index: u16::try_from(i).unwrap_or(u16::MAX),
                    ip,
                    public_ip,
                    slot,
                    role: n.role,
                }
            })
            .collect();
        let sessions = u32::try_from(peers.len() + 8).unwrap_or(u32::MAX);
        let inits = plan
            .nodes
            .iter()
            .map(|n| Init {
                stack,
                name: n.name.clone(),
                peers: peers.clone(),
                mtu: plan.mtu,
                sessions,
                iroh_gossip_max: None,
                dtn: None,
                trace: false,
                portmap: plan.sites.get(n.site).is_some_and(|s| s.portmap.is_some()),
            })
            .collect();
        Self {
            b,
            plan,
            inits,
            slots: plan.nodes.iter().map(|_| tokio::sync::Mutex::new(None)).collect(),
            rejoin: Mutex::new(None),
            archived: Mutex::new(vec![Vec::new(); plan.nodes.len()]),
            replay: Mutex::new(vec![Vec::new(); plan.nodes.len()]),
        }
    }

    /// Set each node's delay-tolerant delivery: `f` is given the node's index and gives its settings.
    pub(crate) fn with_dtn(mut self, f: impl Fn(usize) -> Option<DtnInit>) -> Self {
        for (i, init) in self.inits.iter_mut().enumerate() {
            init.dtn = f(i);
        }
        self
    }

    /// Ask node `i` to do `cmd`, and again whenever it is started again.
    pub(crate) async fn call_kept(&self, i: usize, cmd: Cmd, wait: Duration) -> Result<Value> {
        if let Ok(mut r) = self.replay.lock()
            && let Some(v) = r.get_mut(i)
        {
            v.push(cmd.clone());
        }
        self.call(i, cmd, wait).await
    }

    /// Have every node record its trace and packet log, when `on` (VINC nodes only act on it).
    pub(crate) fn with_trace(mut self, on: bool) -> Self {
        for i in &mut self.inits {
            i.trace = on;
        }
        self
    }

    /// Set the largest iroh gossip message of every node (see `Pubsub::iroh_gossip_max`).
    pub(crate) fn with_iroh_gossip_max(mut self, max: Option<u32>) -> Self {
        for i in &mut self.inits {
            i.iroh_gossip_max = max;
        }
        self
    }

    /// The nodes with a hub or relay role first, then the rest: the others join through them.
    fn start_order(&self) -> (Vec<usize>, Vec<usize>) {
        (0..self.plan.nodes.len()).partition(|i| self.plan.nodes.get(*i).is_some_and(|n| n.role != Role::Peer))
    }

    /// Start every program, the hubs first.
    pub(crate) async fn start_all(&self) -> Result<()> {
        let (hubs, rest) = self.start_order();
        for group in [hubs, rest] {
            let started = futures::future::join_all(group.iter().map(|i| self.start_one(*i))).await;
            for r in started {
                r?;
            }
        }
        Ok(())
    }

    async fn start_one(&self, i: usize) -> Result<()> {
        let init = self
            .inits
            .get(i)
            .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
        let n = AppNode::start(self.b, i, init).await?;
        if let Some(slot) = self.slots.get(i) {
            *slot.lock().await = Some(n);
        }
        Ok(())
    }

    /// Ask node `i` to do `cmd`.
    pub(crate) async fn call(&self, i: usize, cmd: Cmd, wait: Duration) -> Result<Value> {
        // The slot is not held across the wait: a request that takes minutes must not block the fault schedule.
        let node = {
            let slot = self
                .slots
                .get(i)
                .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
            slot.lock().await.clone()
        };
        node.ok_or_else(|| {
            Error::Node(format!(
                "{}: the node program is not running",
                self.plan.nodes.get(i).map_or("?", |n| n.name.as_str())
            ))
        })?
        .call(cmd, wait)
        .await
    }

    /// Ask every node in `nodes` to join the topic, the hubs first.
    pub(crate) async fn join_all(&self, topic: &str, wait_ms: u64) -> Result<()> {
        if let Ok(mut r) = self.rejoin.lock() {
            *r = Some((topic.to_owned(), wait_ms));
        }
        let (hubs, rest) = self.start_order();
        for group in [hubs, rest] {
            let joined = futures::future::join_all(group.iter().map(|i| {
                self.call(
                    *i,
                    Cmd::Join {
                        topic: topic.to_owned(),
                        wait_ms,
                    },
                    Duration::from_millis(wait_ms + 10_000),
                )
            }))
            .await;
            for r in joined {
                r?;
            }
        }
        Ok(())
    }

    /// The report of node `i` now, merged with the reports of its earlier lives.
    pub(crate) async fn reports(&self, i: usize) -> Vec<Value> {
        let mut all = self
            .archived
            .lock()
            .map(|a| a.get(i).cloned().unwrap_or_default())
            .unwrap_or_default();
        if let Ok(v) = self.call(i, Cmd::Report, QUICK).await {
            all.push(v);
        }
        all
    }

    /// Kill node `i`'s processes after keeping what it counted.
    pub(crate) async fn kill(&self, i: usize) -> Result<()> {
        if let Ok(v) = self.call(i, Cmd::Report, Duration::from_secs(5)).await
            && let Ok(mut a) = self.archived.lock()
            && let Some(x) = a.get_mut(i)
        {
            x.push(v);
        }
        self.b.stop(i).await?;
        if let Some(slot) = self.slots.get(i) {
            *slot.lock().await = None;
        }
        Ok(())
    }

    /// Start node `i`'s program again and rejoin the topic.
    pub(crate) async fn restart(&self, i: usize) -> Result<()> {
        self.start_one(i).await?;
        let topic = self.rejoin.lock().ok().and_then(|r| r.clone());
        if let Some((topic, wait_ms)) = topic {
            self.call(i, Cmd::Join { topic, wait_ms }, Duration::from_millis(wait_ms + 10_000))
                .await?;
        }
        let again = self
            .replay
            .lock()
            .ok()
            .and_then(|r| r.get(i).cloned())
            .unwrap_or_default();
        for cmd in again {
            self.call(i, cmd, QUICK).await?;
        }
        Ok(())
    }

    /// Ask node `i` to go to sleep or wake, for stacks that have the notion; others are left as they are.
    pub(crate) async fn sleep(&self, i: usize, asleep: bool) -> Result<()> {
        let cmd = if asleep { Cmd::Suspend } else { Cmd::Resume };
        match self.call(i, cmd, QUICK).await {
            Ok(_) => Ok(()),
            Err(Error::Node(m)) if m.contains("not available") => Ok(()),
            Err(e) => Err(e),
        }
    }

    /// Tell every program to stop and close the connections to them.
    pub(crate) async fn stop_all(&self) {
        let stops = (0..self.slots.len()).map(|i| async move {
            let _ = self.call(i, Cmd::Stop, Duration::from_secs(10)).await;
            if let Some(slot) = self.slots.get(i) {
                *slot.lock().await = None;
            }
        });
        futures::future::join_all(stops).await;
        for i in 0..self.slots.len() {
            // A program that did not stop on request is killed with the rest of the node's processes.
            let _ = self.b.stop(i).await;
        }
    }

    /// What each node announced when it started, for the results.
    pub(crate) async fn configs(&self) -> Vec<String> {
        let mut out = Vec::new();
        for slot in &self.slots {
            if let Some(n) = slot.lock().await.as_ref() {
                out.push(n.ready.config.clone());
            }
        }
        out.sort();
        out.dedup();
        out
    }
}
