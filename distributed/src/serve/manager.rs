//! The run manager: one task that owns the current run, numbers its events, keeps the recent ones for a page that
//! opens mid-run, and fans them out. The HTTP handlers talk to it by message, so nothing is locked.

use std::collections::VecDeque;
use std::path::PathBuf;

use serde::Serialize;
use tokio::sync::{broadcast, mpsc, oneshot, watch};

use crate::orchestrate::{self, Event, Options};
use crate::scenario::Scenario;

/// Events kept for a page that connects mid-run (samples are kept apart, fewer).
const KEEP: usize = 2000;
/// Samples kept: two minutes at two a second.
const KEEP_SAMPLES: usize = 240;

/// An event with its sequence number, as the dashboard receives it.
#[derive(Debug, Clone, Serialize)]
pub struct Numbered {
    /// Increases by one per event over the server's life.
    pub seq: u64,
    /// Milliseconds since the Unix epoch.
    pub at_ms: u64,
    /// The event.
    #[serde(flatten)]
    pub ev: Event,
}

/// What the dashboard sees of the manager.
#[derive(Debug, Clone, Serialize)]
pub struct Status {
    /// Whether a run is going.
    pub running: bool,
    /// The scenario of the current or last run.
    pub scenario: Option<String>,
    /// The recent events, oldest first.
    pub recent: Vec<Numbered>,
}

enum Cmd {
    Start(Box<Scenario>, Option<u32>, oneshot::Sender<Result<(), String>>),
    Stop(oneshot::Sender<bool>),
    Status(oneshot::Sender<Status>),
    Shutdown(oneshot::Sender<()>),
}

/// The handlers' end of the manager.
#[derive(Clone, Debug)]
pub struct Manager {
    tx: mpsc::Sender<Cmd>,
    out: broadcast::Sender<Numbered>,
}

fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

struct State {
    seq: u64,
    recent: VecDeque<Numbered>,
    samples: VecDeque<Numbered>,
    scenario: Option<String>,
    run: Option<(tokio::task::JoinHandle<()>, watch::Sender<bool>)>,
}

impl State {
    fn push(&mut self, ev: Event, out: &broadcast::Sender<Numbered>) {
        self.seq += 1;
        let n = Numbered { seq: self.seq, at_ms: now_ms(), ev };
        let keep = if matches!(n.ev, Event::Sample(_)) { &mut self.samples } else { &mut self.recent };
        let cap = if matches!(n.ev, Event::Sample(_)) { KEEP_SAMPLES } else { KEEP };
        if keep.len() == cap {
            keep.pop_front();
        }
        keep.push_back(n.clone());
        let _ = out.send(n);
    }

    fn status(&self) -> Status {
        let mut recent: Vec<Numbered> = self.recent.iter().chain(self.samples.iter()).cloned().collect();
        recent.sort_by_key(|n| n.seq);
        Status {
            running: self.run.as_ref().is_some_and(|(h, _)| !h.is_finished()),
            scenario: self.scenario.clone(),
            recent,
        }
    }
}

impl Manager {
    /// Start the manager. Runs use `image` and write results under `results`.
    pub fn start(image: String, results: PathBuf) -> Self {
        let (tx, mut rx) = mpsc::channel::<Cmd>(64);
        let (out, _) = broadcast::channel::<Numbered>(4096);
        let (events, mut from_runs) = {
            let (t, r) = broadcast::channel::<Event>(4096);
            (t, r)
        };
        let fan = out.clone();
        tokio::spawn(async move {
            let mut st = State { seq: 0, recent: VecDeque::new(), samples: VecDeque::new(), scenario: None, run: None };
            loop {
                tokio::select! {
                    ev = from_runs.recv() => match ev {
                        Ok(ev) => st.push(ev, &fan),
                        Err(broadcast::error::RecvError::Lagged(n)) => st.push(
                            Event::Log { level: "warn".into(), msg: format!("{n} live samples were skipped: the dashboard fell behind") },
                            &fan,
                        ),
                        Err(broadcast::error::RecvError::Closed) => break,
                    },
                    cmd = rx.recv() => match cmd {
                        None => break,
                        Some(Cmd::Start(sc, reps, reply)) => {
                            if st.run.as_ref().is_some_and(|(h, _)| !h.is_finished()) {
                                let _ = reply.send(Err("a run is going; stop it or wait for it to end".into()));
                                continue;
                            }
                            st.recent.clear();
                            st.samples.clear();
                            st.scenario = Some(sc.name.clone());
                            let (cancel_tx, cancel) = watch::channel(false);
                            let opts = Options {
                                image: image.clone(),
                                results: results.clone(),
                                reps,
                                events: Some(events.clone()),
                                cancel: Some(cancel),
                                quiet: crate::quiet::Thresholds::default(),
                            };
                            let ev = events.clone();
                            let handle = tokio::spawn(async move {
                                if let Err(e) = orchestrate::run(*sc, opts).await {
                                    let _ = ev.send(Event::Ended { ok: false, error: Some(e.to_string()), results: String::new(), left: Vec::new() });
                                }
                            });
                            st.run = Some((handle, cancel_tx));
                            let _ = reply.send(Ok(()));
                        }
                        Some(Cmd::Stop(reply)) => {
                            let going = st.run.as_ref().is_some_and(|(h, _)| !h.is_finished());
                            if let Some((_, c)) = &st.run {
                                let _ = c.send(true);
                            }
                            let _ = reply.send(going);
                        }
                        Some(Cmd::Status(reply)) => {
                            let _ = reply.send(st.status());
                        }
                        Some(Cmd::Shutdown(reply)) => {
                            if let Some((h, c)) = st.run.take() {
                                let _ = c.send(true);
                                // The run tears down before it ends; wait for it so nothing is left behind.
                                let _ = h.await;
                            }
                            let _ = reply.send(());
                            break;
                        }
                    }
                }
            }
        });
        Self { tx, out }
    }

    /// Start a run of `sc`.
    ///
    /// # Errors
    /// A run is already going.
    pub async fn start_run(&self, sc: Scenario, reps: Option<u32>) -> Result<(), String> {
        let (tx, rx) = oneshot::channel();
        self.tx.send(Cmd::Start(Box::new(sc), reps, tx)).await.map_err(|_| "the server is stopping".to_owned())?;
        rx.await.map_err(|_| "the server is stopping".to_owned())?
    }

    /// Ask the current run to stop; whether one was going.
    pub async fn stop_run(&self) -> bool {
        let (tx, rx) = oneshot::channel();
        if self.tx.send(Cmd::Stop(tx)).await.is_err() {
            return false;
        }
        rx.await.unwrap_or(false)
    }

    /// The current status with the recent events.
    pub async fn status(&self) -> Option<Status> {
        let (tx, rx) = oneshot::channel();
        self.tx.send(Cmd::Status(tx)).await.ok()?;
        rx.await.ok()
    }

    /// Stop any run, wait for its teardown, and end the manager.
    pub async fn shutdown(&self) {
        let (tx, rx) = oneshot::channel();
        if self.tx.send(Cmd::Shutdown(tx)).await.is_ok() {
            let _ = rx.await;
        }
    }

    /// The live events.
    pub fn subscribe(&self) -> broadcast::Receiver<Numbered> {
        self.out.subscribe()
    }
}
