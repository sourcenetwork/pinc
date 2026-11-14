//! The dashboard's HTTP routes: the pages, the scenarios (list, read, save, validate), runs (start, stop, live events
//! as server-sent events), results (list, read, export) and the host (what it has, what is left, clean-up).

use std::convert::Infallible;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use bytes::Bytes;
use futures::StreamExt;
use http_body_util::combinators::UnsyncBoxBody;
use http_body_util::{BodyExt, Full, Limited, StreamBody};
use hyper::body::{Frame, Incoming};
use hyper::header::{CACHE_CONTROL, CONTENT_TYPE, COOKIE, HOST, LOCATION, SET_COOKIE};
use hyper::{Method, Request, Response, StatusCode};
use serde_json::{Value, json};
use tokio::sync::broadcast;

use crate::backend::containers;
use crate::docker;
use crate::orchestrate::HostInfo;
use crate::plan::Plan;
use crate::results::{self, Row};
use crate::scenario::Scenario;
use crate::serve::{App, assets};

type Body = UnsyncBoxBody<Bytes, Infallible>;
type Resp = Response<Body>;

/// The largest request body: a scenario file is a few kilobytes.
const MAX_BODY: usize = 1 << 20;

fn full(b: impl Into<Bytes>) -> Body {
    Full::new(b.into()).boxed_unsync()
}

fn reply(status: StatusCode, ctype: &str, body: impl Into<Bytes>) -> Resp {
    let mut r = Response::new(full(body));
    *r.status_mut() = status;
    if let Ok(v) = ctype.parse() {
        r.headers_mut().insert(CONTENT_TYPE, v);
    }
    if let Ok(v) = "no-store".parse() {
        r.headers_mut().insert(CACHE_CONTROL, v);
    }
    r
}

fn json_ok(v: &Value) -> Resp {
    reply(
        StatusCode::OK,
        "application/json",
        serde_json::to_vec(v).unwrap_or_default(),
    )
}

fn fail(status: StatusCode, msg: &str) -> Resp {
    reply(
        status,
        "application/json",
        serde_json::to_vec(&json!({ "error": msg })).unwrap_or_default(),
    )
}

fn cookie_token(req: &Request<Incoming>) -> Option<String> {
    let c = req.headers().get(COOKIE)?.to_str().ok()?;
    c.split(';')
        .find_map(|kv| kv.trim().strip_prefix("vd=").map(str::to_owned))
}

fn query(req: &Request<Incoming>, key: &str) -> Option<String> {
    req.uri()
        .query()?
        .split('&')
        .find_map(|kv| kv.split_once('=').filter(|(k, _)| *k == key).map(|(_, v)| v.to_owned()))
}

/// The checks every request passes: the token (when one is set), the local `Host` (when none is), and the header
/// that marks a request as the dashboard's own for anything that changes state.
#[allow(clippy::result_large_err, reason = "the error is the response to send")]
fn guard(app: &App, req: &Request<Incoming>) -> Result<Option<Resp>, Resp> {
    if let Some(t) = &app.opts.token {
        if req.uri().path() == "/" && query(req, "token").as_deref() == Some(t.as_str()) {
            let mut r = reply(StatusCode::SEE_OTHER, "text/plain", "");
            if let (Ok(c), Ok(l)) = (
                format!("vd={t}; HttpOnly; SameSite=Strict; Path=/").parse(),
                "/".parse(),
            ) {
                r.headers_mut().insert(SET_COOKIE, c);
                r.headers_mut().insert(LOCATION, l);
            }
            return Ok(Some(r));
        }
        if cookie_token(req).as_deref() != Some(t.as_str()) {
            return Err(fail(
                StatusCode::UNAUTHORIZED,
                "open the dashboard with ?token=<the token it was started with>",
            ));
        }
    } else {
        let host = req.headers().get(HOST).and_then(|h| h.to_str().ok()).unwrap_or("");
        let name = host.rsplit_once(':').map_or(host, |(h, _)| h);
        if !matches!(name, "127.0.0.1" | "localhost" | "[::1]") {
            return Err(fail(
                StatusCode::FORBIDDEN,
                "the dashboard answers only to localhost; reach it through an SSH tunnel",
            ));
        }
    }
    if req.method() != Method::GET && !req.headers().contains_key("x-vd") {
        return Err(fail(
            StatusCode::FORBIDDEN,
            "this request did not come from the dashboard",
        ));
    }
    Ok(None)
}

pub(crate) async fn handle(app: Arc<App>, req: Request<Incoming>) -> Result<Resp, Infallible> {
    match guard(&app, &req) {
        Ok(Some(r)) | Err(r) => return Ok(r),
        Ok(None) => {}
    }
    let path = req.uri().path().to_owned();
    let segs: Vec<&str> = path.trim_matches('/').split('/').collect();
    let m = req.method().clone();
    Ok(match (m, segs.as_slice()) {
        (Method::GET, ["api", "scenarios"]) => scenarios(&app),
        (Method::GET, ["api", "scenarios", name]) => scenario(&app, name),
        (Method::PUT, ["api", "scenarios", name]) => save(&app, name, req).await,
        (Method::POST, ["api", "validate"]) => validate(req).await,
        (Method::POST, ["api", "runs"]) => start(&app, req).await,
        (Method::POST, ["api", "runs", "stop"]) => json_ok(&json!({ "stopping": app.runs.stop_run().await })),
        (Method::GET, ["api", "status"]) => match app.runs.status().await {
            Some(s) => json_ok(&json!({ "running": s.running, "scenario": s.scenario })),
            None => fail(StatusCode::SERVICE_UNAVAILABLE, "the server is stopping"),
        },
        (Method::GET, ["api", "events"]) => events(&app).await,
        (Method::GET, ["api", "results"]) => list_results(&app),
        (Method::GET, ["api", "results", dir]) => result(&app, dir),
        (Method::GET, ["api", "results", dir, "raw.jsonl"]) => export(&app, dir, false),
        (Method::GET, ["api", "results", dir, "raw.csv"]) => export(&app, dir, true),
        (Method::GET, ["api", "host"]) => host(&app).await,
        (Method::POST, ["api", "clean"]) => clean(&app).await,
        (Method::GET, _) => match assets::get(&path) {
            Some((ctype, body)) => reply(StatusCode::OK, ctype, Bytes::from_static(body)),
            None => fail(StatusCode::NOT_FOUND, "no such page"),
        },
        _ => fail(StatusCode::METHOD_NOT_ALLOWED, "not supported"),
    })
}

#[allow(clippy::result_large_err, reason = "the error is the response to send")]
async fn body(req: Request<Incoming>) -> Result<Bytes, Resp> {
    Limited::new(req.into_body(), MAX_BODY)
        .collect()
        .await
        .map(http_body_util::Collected::to_bytes)
        .map_err(|_| fail(StatusCode::PAYLOAD_TOO_LARGE, "the request is larger than 1 MiB"))
}

fn safe_name(s: &str) -> bool {
    !s.is_empty() && s.len() <= 80 && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
}

fn scenario_dir(app: &App) -> PathBuf {
    app.opts.root.join("scenarios")
}

fn scenarios(app: &App) -> Resp {
    let mut out = Vec::new();
    let mut files: Vec<PathBuf> = std::fs::read_dir(scenario_dir(app))
        .map(|d| {
            d.filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.extension().is_some_and(|x| x == "toml"))
                .collect()
        })
        .unwrap_or_default();
    files.sort();
    for f in files {
        let file = f
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default();
        let entry = match std::fs::read_to_string(&f)
            .map_err(|e| e.to_string())
            .and_then(|t| Scenario::parse(&t))
        {
            Ok(sc) => {
                let problems = sc.validate();
                let kind = match &sc.workload {
                    crate::scenario::Workload::Transport(_) => "transport",
                    crate::scenario::Workload::Pubsub(_) => "pubsub",
                    crate::scenario::Workload::Sync(_) => "sync",
                    crate::scenario::Workload::Reconcile(_) => "reconcile",
                    crate::scenario::Workload::Dtn(_) => "dtn",
                    crate::scenario::Workload::Reach(_) => "reach",
                };
                json!({
                    "file": file, "name": sc.name, "about": sc.about, "stacks": sc.stacks,
                    "sites": sc.sites.len(), "nodes": sc.expand().len(), "links": sc.links.len(),
                    "faults": sc.faults.len(), "repetitions": sc.repetitions,
                    "workload": kind,
                    "problems": problems,
                })
            }
            Err(e) => json!({ "file": file, "error": e }),
        };
        out.push(entry);
    }
    json_ok(&Value::Array(out))
}

fn scenario(app: &App, name: &str) -> Resp {
    if !safe_name(name) {
        return fail(
            StatusCode::BAD_REQUEST,
            "a scenario name has letters, digits and dashes only",
        );
    }
    let path = scenario_dir(app).join(format!("{name}.toml"));
    let Ok(text) = std::fs::read_to_string(&path) else {
        return fail(StatusCode::NOT_FOUND, "no scenario of that name");
    };
    match Scenario::parse(&text) {
        Ok(sc) => json_ok(&json!({ "scenario": sc, "toml": text, "problems": sc.validate() })),
        Err(e) => json_ok(&json!({ "toml": text, "error": e })),
    }
}

async fn save(app: &App, name: &str, req: Request<Incoming>) -> Resp {
    if !safe_name(name) {
        return fail(
            StatusCode::BAD_REQUEST,
            "a scenario name has letters, digits and dashes only",
        );
    }
    let b = match body(req).await {
        Ok(b) => b,
        Err(r) => return r,
    };
    let sc: Scenario = match serde_json::from_slice(&b) {
        Ok(s) => s,
        Err(e) => return fail(StatusCode::BAD_REQUEST, &format!("not a scenario: {e}")),
    };
    let text = match sc.to_toml() {
        Ok(t) => t,
        Err(e) => return fail(StatusCode::BAD_REQUEST, &e),
    };
    let dir = scenario_dir(app);
    if let Err(e) = std::fs::create_dir_all(&dir).and_then(|()| std::fs::write(dir.join(format!("{name}.toml")), text))
    {
        return fail(
            StatusCode::INTERNAL_SERVER_ERROR,
            &format!("the file could not be written: {e}"),
        );
    }
    json_ok(&json!({ "saved": name, "problems": sc.validate() }))
}

async fn validate(req: Request<Incoming>) -> Resp {
    let b = match body(req).await {
        Ok(b) => b,
        Err(r) => return r,
    };
    let sc: Scenario = match serde_json::from_slice(&b) {
        Ok(s) => s,
        Err(e) => return json_ok(&json!({ "problems": [{ "path": "", "message": format!("not a scenario: {e}") }] })),
    };
    let problems = sc.validate();
    let toml = sc.to_toml().unwrap_or_default();
    if !problems.is_empty() {
        return json_ok(&json!({ "problems": problems, "toml": toml }));
    }
    let cpus = crate::quiet::host_cpus();
    let plan = Plan::new(&sc, "preview", cpus);
    let nodes: Vec<Value> = plan
        .nodes
        .iter()
        .map(|n| json!({ "name": n.name, "ip": n.ip.to_string(), "cpus": n.container.cpus, "memory_mib": n.container.memory_mib }))
        .collect();
    let sites: Vec<Value> = plan
        .sites
        .iter()
        .map(|s| json!({ "name": s.name, "lan": format!("{}/24", s.lan), "gateway": s.gateway.to_string() }))
        .collect();
    json_ok(
        &json!({ "problems": [], "toml": toml, "plan": { "nodes": nodes, "sites": sites, "shared_cpus": plan.shared_cpus } }),
    )
}

async fn start(app: &App, req: Request<Incoming>) -> Resp {
    let b = match body(req).await {
        Ok(b) => b,
        Err(r) => return r,
    };
    let v: Value = serde_json::from_slice(&b).unwrap_or(Value::Null);
    let Some(name) = v.get("scenario").and_then(Value::as_str).filter(|n| safe_name(n)) else {
        return fail(StatusCode::BAD_REQUEST, "name the scenario to run");
    };
    let reps = v
        .get("reps")
        .and_then(Value::as_u64)
        .and_then(|r| u32::try_from(r).ok());
    let path = scenario_dir(app).join(format!("{name}.toml"));
    let sc = match std::fs::read_to_string(&path)
        .map_err(|e| e.to_string())
        .and_then(|t| Scenario::parse(&t))
    {
        Ok(s) => s,
        Err(e) => return fail(StatusCode::BAD_REQUEST, &format!("the scenario cannot be read: {e}")),
    };
    let problems = sc.validate();
    if !problems.is_empty() {
        return reply(
            StatusCode::BAD_REQUEST,
            "application/json",
            serde_json::to_vec(&json!({ "error": "the scenario has problems", "problems": problems }))
                .unwrap_or_default(),
        );
    }
    match app.runs.start_run(sc, reps).await {
        Ok(()) => json_ok(&json!({ "started": name })),
        Err(e) => fail(StatusCode::CONFLICT, &e),
    }
}

struct Sse {
    rx: broadcast::Receiver<crate::serve::manager::Numbered>,
    app: Arc<App>,
    pending: Option<Bytes>,
    last: u64,
}

fn frame(event: Option<&str>, data: &impl serde::Serialize) -> Bytes {
    let mut s = String::new();
    if let Some(e) = event {
        let _ = writeln!(s, "event: {e}");
    }
    let _ = write!(s, "data: {}\n\n", serde_json::to_string(data).unwrap_or_default());
    Bytes::from(s)
}

async fn events(app: &Arc<App>) -> Resp {
    let rx = app.runs.subscribe();
    let Some(status) = app.runs.status().await else {
        return fail(StatusCode::SERVICE_UNAVAILABLE, "the server is stopping");
    };
    let last = status.recent.last().map_or(0, |n| n.seq);
    let st = Sse {
        rx,
        app: app.clone(),
        pending: Some(frame(Some("snapshot"), &status)),
        last,
    };
    let stream = futures::stream::unfold(st, |mut st| async move {
        if let Some(p) = st.pending.take() {
            return Some((Ok::<_, Infallible>(Frame::data(p)), st));
        }
        loop {
            match tokio::time::timeout(Duration::from_secs(15), st.rx.recv()).await {
                Err(_) => return Some((Ok(Frame::data(Bytes::from_static(b": keepalive\n\n"))), st)),
                Ok(Ok(n)) if n.seq <= st.last => {}
                Ok(Ok(n)) => {
                    st.last = n.seq;
                    return Some((Ok(Frame::data(frame(None, &n))), st));
                }
                Ok(Err(broadcast::error::RecvError::Lagged(_))) => {
                    // The page fell behind: send it the whole recent state again.
                    let s = st.app.runs.status().await?;
                    st.last = s.recent.last().map_or(st.last, |n| n.seq);
                    return Some((Ok(Frame::data(frame(Some("snapshot"), &s))), st));
                }
                Ok(Err(broadcast::error::RecvError::Closed)) => return None,
            }
        }
    });
    let mut r = Response::new(StreamBody::new(stream.boxed()).boxed_unsync());
    for (k, v) in [(CONTENT_TYPE, "text/event-stream"), (CACHE_CONTROL, "no-store")] {
        if let Ok(v) = v.parse() {
            r.headers_mut().insert(k, v);
        }
    }
    r
}

fn results_dir(app: &App) -> PathBuf {
    app.opts.root.join("results")
}

fn read_json(p: &Path) -> Value {
    std::fs::read(p)
        .ok()
        .and_then(|b| serde_json::from_slice(&b).ok())
        .unwrap_or(Value::Null)
}

fn list_results(app: &App) -> Resp {
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(results_dir(app))
        .map(|d| {
            d.filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.is_dir())
                .collect()
        })
        .unwrap_or_default();
    dirs.sort();
    dirs.reverse();
    let out: Vec<Value> = dirs
        .iter()
        .map(|d| {
            let run = read_json(&d.join("run.json"));
            let rows = std::fs::read_to_string(d.join("raw.jsonl")).map_or(0, |t| t.lines().count());
            json!({
                "dir": d.file_name().map(|s| s.to_string_lossy().into_owned()),
                "scenario": run.get("scenario"), "status": run.get("status"), "started": run.get("started"),
                "ended": run.get("ended"), "reduced": run.get("reduced"), "backend": run.get("backend"),
                "rows": rows, "finished": !run.is_null(),
            })
        })
        .collect();
    json_ok(&Value::Array(out))
}

fn result_path(app: &App, dir: &str) -> Option<PathBuf> {
    safe_name(dir)
        .then(|| results_dir(app).join(dir))
        .filter(|p| p.is_dir())
}

fn stacks_of(dir: &Path, rows: &[Row]) -> Vec<String> {
    let from_file = std::fs::read_to_string(dir.join("scenario.toml"))
        .ok()
        .and_then(|t| Scenario::parse(&t).ok())
        .map(|s| s.stacks.iter().map(|x| x.name().to_owned()).collect::<Vec<_>>());
    from_file.unwrap_or_else(|| {
        let mut v: Vec<String> = Vec::new();
        for r in rows {
            if !v.contains(&r.stack) {
                v.push(r.stack.clone());
            }
        }
        v
    })
}

fn result(app: &App, dir: &str) -> Resp {
    let Some(p) = result_path(app, dir) else {
        return fail(StatusCode::NOT_FOUND, "no results of that name");
    };
    let rows = results::read_rows(&p).unwrap_or_default();
    let stacks = stacks_of(&p, &rows);
    let tables = results::summarize(&rows, &stacks);
    json_ok(&json!({
        "dir": dir, "run": read_json(&p.join("run.json")),
        "scenario": std::fs::read_to_string(p.join("scenario.toml")).unwrap_or_default(),
        "stacks": stacks, "tables": tables, "rows": rows,
    }))
}

fn csv_cell(v: &str) -> String {
    if v.contains([',', '"', '\n']) {
        format!("\"{}\"", v.replace('"', "\"\""))
    } else {
        v.to_owned()
    }
}

fn export(app: &App, dir: &str, csv: bool) -> Resp {
    let Some(p) = result_path(app, dir) else {
        return fail(StatusCode::NOT_FOUND, "no results of that name");
    };
    if !csv {
        return match std::fs::read(p.join("raw.jsonl")) {
            Ok(b) => reply(StatusCode::OK, "application/x-ndjson", b),
            Err(_) => fail(StatusCode::NOT_FOUND, "this run has no rows"),
        };
    }
    let rows = results::read_rows(&p).unwrap_or_default();
    let mut keys: Vec<String> = rows.iter().flat_map(|r| r.node.keys().cloned()).collect();
    keys.sort();
    keys.dedup();
    let kernel = ["cpu_s", "peak_mib", "tx_bytes", "rx_bytes", "tx_packets", "rx_packets"];
    let mut out = String::from("run,stack,test,pair,rep,status");
    for k in &keys {
        let _ = write!(out, ",node.{k}");
    }
    for role in ["client", "server"] {
        for k in kernel {
            let _ = write!(out, ",kernel.{role}.{k}");
        }
    }
    out.push_str(",shaper_drops\n");
    for r in &rows {
        let mut line = [r.run.as_str(), &r.stack, &r.test, &r.pair]
            .iter()
            .map(|s| csv_cell(s))
            .collect::<Vec<_>>()
            .join(",");
        let _ = write!(line, ",{},{}", r.rep, csv_cell(&r.status));
        for k in &keys {
            let v = r.node.get(k).map_or(String::new(), |v| {
                v.as_str().map_or_else(|| v.to_string(), str::to_owned)
            });
            let _ = write!(line, ",{}", csv_cell(&v));
        }
        for role in ["client", "server"] {
            let u = r.kernel.get(role);
            let e = u.and_then(|u| u.eth0);
            let vals = [
                u.and_then(|u| u.cpu_s).map(|v| v.to_string()),
                u.and_then(|u| u.peak_mib).map(|v| v.to_string()),
                e.map(|e| e.tx_bytes.to_string()),
                e.map(|e| e.rx_bytes.to_string()),
                e.map(|e| e.tx_packets.to_string()),
                e.map(|e| e.rx_packets.to_string()),
            ];
            for v in vals {
                let _ = write!(line, ",{}", v.unwrap_or_default());
            }
        }
        let _ = writeln!(line, ",{}", r.shaper_drops.map(|d| d.to_string()).unwrap_or_default());
        out.push_str(&line);
    }
    reply(StatusCode::OK, "text/csv", out)
}

async fn host(app: &App) -> Resp {
    let info = HostInfo::read();
    let docker_version = docker::docker(&["version", "--format", "{{.Server.Version}}"])
        .await
        .map(|s| s.trim().to_owned());
    let containers = docker::labelled().await.unwrap_or_default();
    let image = docker::docker(&["image", "inspect", "--format", "{{.Id}} {{.Size}}", &app.opts.image])
        .await
        .ok();
    let qdiscs = tokio::process::Command::new("tc")
        .args(["qdisc", "show"])
        .output()
        .await
        .ok();
    let host_netem: Vec<String> = qdiscs
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .filter(|l| l.contains("netem"))
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();
    let status = app.runs.status().await;
    json_ok(&json!({
        "host": info,
        "docker": docker_version.map_err(|e| e.to_string()),
        "image": { "name": app.opts.image, "present": image.as_ref().map(|s| s.trim().to_owned()) },
        "containers": containers.iter().map(|(n, r)| json!({ "name": n, "run": r })).collect::<Vec<_>>(),
        "ifb_loaded": Path::new("/sys/module/ifb").exists(),
        "host_netem": host_netem,
        "running": status.as_ref().is_some_and(|s| s.running),
        "scenario": status.and_then(|s| s.scenario),
    }))
}

async fn clean(app: &App) -> Resp {
    if app.runs.status().await.is_some_and(|s| s.running) {
        return fail(
            StatusCode::CONFLICT,
            "a run is going; stop it first (its teardown removes what it created)",
        );
    }
    match containers::clean().await {
        Ok(c) => json_ok(&serde_json::to_value(&c).unwrap_or(Value::Null)),
        Err(e) => fail(StatusCode::INTERNAL_SERVER_ERROR, &e.to_string()),
    }
}
