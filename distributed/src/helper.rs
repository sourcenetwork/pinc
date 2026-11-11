//! The privileged helper: the one process of a run that holds root (`sudo -n vinc-distributed helper`), so the
//! orchestrator itself runs as the user.
//!
//! It reads one JSON request per line on its standard input and answers one JSON line each, in order. It does only
//! what a run needs and checks every request against that:
//! - run `ip`, `tc`, `iptables` or `sysctl` inside a node's or router's network namespace (`nsenter --net`);
//! - in the host's own namespace, only create a veth pair whose two ends go straight into two other namespaces, and
//!   only read the host's links and queueing disciplines (for the teardown check);
//! - read a node's interface counters (`/proc/<pid>/net/dev`) and its cgroup's files;
//! - reset and read a cgroup's `memory.peak` through a held file descriptor (the kernel resets the peak per
//!   descriptor);
//! - load the `ifb` module with no devices of its own, and unload it.
//!
//! It exits when its input closes, so it never outlives the orchestrator.

use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use serde::{Deserialize, Serialize};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::sync::{mpsc, oneshot};

use crate::error::{Error, Result};

/// A request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Req {
    /// Run a tool, in the namespace of process `ns` or in the host's.
    Run {
        /// The process whose network namespace to enter; the host's own when absent.
        ns: Option<u32>,
        /// `ip`, `tc`, `iptables` or `sysctl`.
        tool: String,
        /// Its arguments.
        args: Vec<String>,
    },
    /// Read a file: `/proc/<pid>/net/dev` or a file under `/sys/fs/cgroup`.
    Read {
        /// The path.
        path: String,
    },
    /// Reset a cgroup's `memory.peak` through a descriptor kept open for [`Req::PeakRead`].
    PeakReset {
        /// The path of the `memory.peak` file.
        path: String,
    },
    /// Read the peak since the last [`Req::PeakReset`] of this path.
    PeakRead {
        /// The path of the `memory.peak` file.
        path: String,
    },
    /// Load (`true`) or unload the `ifb` module. Answers `loaded` when this call loaded it.
    Ifb {
        /// Load or unload.
        load: bool,
    },
}

#[derive(Debug, Serialize, Deserialize)]
struct Envelope {
    id: u64,
    req: Req,
}

/// An answer.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Resp {
    /// The request's id.
    pub id: u64,
    /// Whether it succeeded.
    pub ok: bool,
    /// Its output.
    pub out: String,
    /// Its error output, or why it was refused.
    pub err: String,
}

fn find_tool(name: &str) -> Option<String> {
    ["/usr/sbin", "/sbin", "/usr/bin", "/bin"]
        .iter()
        .map(|d| format!("{d}/{name}"))
        .find(|p| Path::new(p).is_file())
}

/// Whether the helper runs this command in the host's own namespace (public for the tests).
pub fn host_ns_allowed(tool: &str, args: &[String]) -> bool {
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    match (tool, a.as_slice()) {
        // ip link add <name> netns <pid> type veth peer name <name> netns <pid>
        (
            "ip",
            [
                "link",
                "add",
                _,
                "netns",
                p1,
                "type",
                "veth",
                "peer",
                "name",
                _,
                "netns",
                p2,
            ],
        ) => p1.bytes().all(|b| b.is_ascii_digit()) && p2.bytes().all(|b| b.is_ascii_digit()),
        ("ip", ["-o", "link", "show"]) | ("tc", ["qdisc", "show"]) => true,
        _ => false,
    }
}

/// Whether the helper reads this path (public for the tests).
pub fn readable(path: &str) -> bool {
    if path.contains("..") {
        return false;
    }
    if let Some(rest) = path.strip_prefix("/proc/") {
        return rest
            .strip_suffix("/net/dev")
            .is_some_and(|pid| !pid.is_empty() && pid.bytes().all(|b| b.is_ascii_digit()));
    }
    path.starts_with("/sys/fs/cgroup/")
}

fn run_tool(ns: Option<u32>, tool: &str, args: &[String]) -> std::result::Result<String, String> {
    if !matches!(tool, "ip" | "tc" | "iptables" | "sysctl") {
        return Err(format!("the helper does not run {tool}"));
    }
    let Some(path) = find_tool(tool) else {
        return Err(format!("{tool} is not installed"));
    };
    let mut cmd = match ns {
        Some(pid) => {
            let Some(nsenter) = find_tool("nsenter") else {
                return Err("nsenter is not installed".into());
            };
            let mut c = Command::new(nsenter);
            c.arg(format!("--net=/proc/{pid}/ns/net")).arg("--").arg(path);
            c
        }
        None => {
            if !host_ns_allowed(tool, args) {
                return Err("in the host's namespace the helper only creates veth pairs between two other namespaces and reads links and queues".into());
            }
            Command::new(path)
        }
    };
    let out = cmd
        .args(args)
        .stdin(Stdio::null())
        .output()
        .map_err(|e| format!("{tool} did not start: {e}"))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(String::from_utf8_lossy(&out.stderr).trim().to_owned())
    }
}

fn ifb(load: bool) -> std::result::Result<String, String> {
    let loaded = Path::new("/sys/module/ifb").exists();
    let Some(modprobe) = find_tool("modprobe") else {
        return Err("modprobe is not installed".into());
    };
    let args: &[&str] = match (load, loaded) {
        (true, true) | (false, false) => return Ok(String::new()),
        (true, false) => &["ifb", "numifbs=0"],
        (false, true) => &["-r", "ifb"],
    };
    let out = Command::new(modprobe)
        .args(args)
        .output()
        .map_err(|e| format!("modprobe did not start: {e}"))?;
    if out.status.success() {
        Ok(if load { "loaded".into() } else { String::new() })
    } else {
        Err(String::from_utf8_lossy(&out.stderr).trim().to_owned())
    }
}

/// The helper's main loop: answer requests from standard input until it closes.
///
/// # Errors
/// Standard input or output fails.
pub fn serve() -> std::io::Result<()> {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout().lock();
    let mut peaks: HashMap<String, File> = HashMap::new();
    for line in stdin.lock().lines() {
        let line = line?;
        let Ok(env) = serde_json::from_str::<Envelope>(&line) else {
            writeln!(
                stdout,
                "{}",
                serde_json::json!({"id": 0, "ok": false, "out": "", "err": "a request the helper does not understand"})
            )?;
            stdout.flush()?;
            continue;
        };
        let result = match env.req {
            Req::Run { ns, tool, args } => run_tool(ns, &tool, &args),
            Req::Read { path } if readable(&path) => std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}")),
            Req::PeakReset { path } | Req::PeakRead { path }
                if !(readable(&path) && path.ends_with("/memory.peak")) =>
            {
                Err(format!("the helper does not touch {path}"))
            }
            Req::PeakReset { path } => {
                let f = match peaks.remove(&path) {
                    Some(f) => Ok(f),
                    None => OpenOptions::new().read(true).write(true).open(&path),
                };
                f.and_then(|mut f| {
                    f.write_all(b"reset\n")?;
                    peaks.insert(path.clone(), f);
                    Ok(String::new())
                })
                .map_err(|e| format!("{path}: {e}"))
            }
            Req::PeakRead { path } => match peaks.get_mut(&path) {
                Some(f) => {
                    let mut s = String::new();
                    f.seek(SeekFrom::Start(0))
                        .and_then(|_| f.read_to_string(&mut s))
                        .map(|_| s.trim().to_owned())
                        .map_err(|e| format!("{path}: {e}"))
                }
                None => Err(format!("{path} was not reset first")),
            },
            Req::Read { path } => Err(format!("the helper does not read {path}")),
            Req::Ifb { load } => ifb(load),
        };
        let resp = match result {
            Ok(out) => Resp {
                id: env.id,
                ok: true,
                out,
                err: String::new(),
            },
            Err(err) => Resp {
                id: env.id,
                ok: false,
                out: String::new(),
                err,
            },
        };
        writeln!(stdout, "{}", serde_json::to_string(&resp).unwrap_or_default())?;
        stdout.flush()?;
    }
    Ok(())
}

type Call = (Req, oneshot::Sender<Resp>);

/// The orchestrator's end of the helper: requests go to one task that owns the helper process, one at a time.
#[derive(Clone, Debug)]
pub struct Helper {
    tx: mpsc::Sender<Call>,
}

impl Helper {
    /// Start the helper with `sudo -n`.
    ///
    /// # Errors
    /// sudo refuses or the binary cannot start.
    pub async fn start() -> Result<Self> {
        let exe = std::env::current_exe()?;
        let mut child = tokio::process::Command::new("sudo")
            .arg("-n")
            .arg(exe)
            .arg("helper")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .kill_on_drop(true)
            .spawn()
            .map_err(|e| Error::Host(format!("sudo did not start: {e}")))?;
        let (Some(mut input), Some(output)) = (child.stdin.take(), child.stdout.take()) else {
            return Err(Error::Host("the helper's pipes are missing".into()));
        };
        let (tx, mut rx) = mpsc::channel::<Call>(256);
        tokio::spawn(async move {
            let mut lines = BufReader::new(output).lines();
            let mut id = 0u64;
            while let Some((req, reply)) = rx.recv().await {
                id += 1;
                let line = serde_json::to_string(&Envelope { id, req }).unwrap_or_default();
                let fail = |err: &str| Resp {
                    id,
                    ok: false,
                    out: String::new(),
                    err: err.to_owned(),
                };
                if input.write_all(format!("{line}\n").as_bytes()).await.is_err() {
                    let _ = reply.send(fail("the helper stopped (sudo may have refused: check `sudo -n true`)"));
                    continue;
                }
                let resp = match lines.next_line().await {
                    Ok(Some(l)) => {
                        serde_json::from_str(&l).unwrap_or_else(|_| fail("the helper answered something unreadable"))
                    }
                    _ => fail("the helper stopped (sudo may have refused: check `sudo -n true`)"),
                };
                let _ = reply.send(resp);
            }
            drop(input);
            let _ = child.wait().await;
        });
        Ok(Self { tx })
    }

    /// Send one request and wait for its answer.
    ///
    /// # Errors
    /// The helper refused or failed the request.
    pub async fn call(&self, req: Req) -> Result<String> {
        let what = format!("{req:?}");
        let (tx, rx) = oneshot::channel();
        self.tx
            .send((req, tx))
            .await
            .map_err(|_| Error::Host("the helper is gone".into()))?;
        let resp = rx.await.map_err(|_| Error::Host("the helper is gone".into()))?;
        if resp.ok {
            Ok(resp.out)
        } else {
            Err(Error::Command {
                cmd: what,
                stderr: resp.err,
            })
        }
    }

    /// Run a tool in a namespace (or the host's when `ns` is `None`).
    ///
    /// # Errors
    /// The tool failed.
    pub async fn run(&self, ns: Option<u32>, tool: &str, args: Vec<String>) -> Result<String> {
        let line = format!("{tool} {}", args.join(" "));
        self.call(Req::Run {
            ns,
            tool: tool.to_owned(),
            args,
        })
        .await
        .map_err(|e| match e {
            Error::Command { stderr, .. } => Error::Command { cmd: line, stderr },
            other => other,
        })
    }
}
