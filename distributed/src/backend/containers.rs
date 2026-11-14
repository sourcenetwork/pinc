//! Backend (a): one container per node and per router on this machine, with no network of their own, wired by the
//! plan through the root helper. Containers carry the run's label, so teardown and `clean` find them whatever
//! happened; their network namespaces, and every interface, shaper and translation rule inside them, go with them.
//! Nothing is created in the host's own namespace: veth pairs are created straight into the two containers.
//!
//! The one host-wide change is the `ifb` module (loaded with no devices of its own, for the node-to-router shapers);
//! it is unloaded at teardown when this run loaded it.

use std::path::{Path, PathBuf};
use std::time::Duration;

use futures::StreamExt;
use serde::{Deserialize, Serialize};
use tokio::process::Command;

use crate::backend::proc::Proc;
use crate::docker::{self, Info};
use crate::error::{Error, Result};
use crate::helper::{Helper, Req};
use crate::metrics::{self, Qdisc, Reading};
use crate::plan::{Container, LABEL, Ns, Plan, ShapePoint, netem_args};
use crate::scenario::Shape;

/// Where the node binary is mounted in every node container.
pub const BIN: &str = "/opt/vd/vinc-distributed";
/// The base image when the host does not say which distribution it runs: small, with a C library and the GCC runtime.
pub const FALLBACK_IMAGE: &str = "debian:bookworm-slim";

/// The base image when none is given: the build host's own distribution and release, so the C library the bound
/// binary was linked against is in it (an older one refuses to load it).
pub fn default_image() -> String {
    host_image().unwrap_or_else(|| FALLBACK_IMAGE.to_owned())
}

/// The image of the distribution this host says it runs, if it says one that has an image.
fn host_image() -> Option<String> {
    std::fs::read_to_string("/etc/os-release")
        .ok()
        .and_then(|t| image_for(&t))
}

/// The image of the distribution an `/etc/os-release` names. Only distributions whose name and release are an image
/// are taken by name (`ubuntu:24.04`, `debian:12-slim`, `fedora:41`); a derivative is given the image of what it is
/// built on (`ubuntu:<codename>` when it names an Ubuntu codename, `archlinux:latest` for Arch and what is like it,
/// which have no release). Anything else has no image here, and the fallback is used.
pub fn image_for(os_release: &str) -> Option<String> {
    let field = |k: &str| {
        os_release
            .lines()
            .find_map(|l| l.strip_prefix(k)?.strip_prefix('='))
            .map(|v| v.trim().trim_matches('"'))
            .filter(|v| !v.is_empty())
    };
    let like = |d: &str| field("ID_LIKE").is_some_and(|l| l.split_whitespace().any(|x| x == d));
    match field("ID")? {
        "debian" => Some(format!("debian:{}-slim", field("VERSION_ID")?)),
        id @ ("ubuntu" | "fedora") => Some(format!("{id}:{}", field("VERSION_ID")?)),
        "arch" => Some("archlinux:latest".to_owned()),
        _ if like("arch") => Some("archlinux:latest".to_owned()),
        _ if like("ubuntu") => Some(format!("ubuntu:{}", field("UBUNTU_CODENAME")?)),
        _ => None,
    }
}

/// What a refused image is told: both versions, and the image to pass. The host's own image is named only when the
/// host has one and it is not the image that was refused.
pub fn refusal(image: &str, theirs: (u32, u32), host: (u32, u32), own: Option<&str>) -> String {
    let own = own
        .filter(|o| *o != image)
        .map(|o| format!("{o} (this host's distribution) or "))
        .unwrap_or_default();
    format!(
        "the image {image} has glibc {}.{}, older than this host's {}.{}, which the node binary links; \
         pass --image {own}an image with glibc {}.{} or newer",
        theirs.0, theirs.1, host.0, host.1, host.0, host.1
    )
}

/// The glibc version in what `getconf GNU_LIBC_VERSION` prints (`glibc 2.39`), as (major, minor).
pub fn glibc(getconf: &str) -> Option<(u32, u32)> {
    let (major, rest) = getconf.trim().strip_prefix("glibc ")?.split_once('.')?;
    Some((major.parse().ok()?, rest.split('.').next()?.parse().ok()?))
}

/// Refuse an image whose glibc is older than the host's, which the bound binary links. Nothing is refused when
/// either side does not say (a musl image, a host without `getconf`).
async fn check_libc(image: &str) -> Result<()> {
    let host = Command::new("getconf")
        .arg("GNU_LIBC_VERSION")
        .output()
        .await
        .ok()
        .and_then(|o| glibc(&String::from_utf8_lossy(&o.stdout)));
    let args = [
        "run",
        "--rm",
        "--network",
        "none",
        "--entrypoint",
        "getconf",
        image,
        "GNU_LIBC_VERSION",
    ];
    let theirs = docker::docker(&args).await.ok().and_then(|s| glibc(&s));
    if let (Some(h), Some(i)) = (host, theirs)
        && i < h
    {
        return Err(Error::Host(refusal(image, i, h, host_image().as_deref())));
    }
    Ok(())
}

/// Containers started at once.
const PARALLEL: usize = 8;

/// A started container.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Started {
    /// Its name.
    pub name: String,
    /// The pid of its first process on the host: its namespaces.
    pub pid: u32,
    /// Its cgroup directory.
    pub cgroup: PathBuf,
}

/// What a run created, kept in a state file so `clean` can finish what a killed orchestrator left.
#[derive(Debug, Default, Serialize, Deserialize)]
struct State {
    run: String,
    containers: Vec<String>,
    ifb_loaded: bool,
}

fn state_path() -> PathBuf {
    let dir = std::env::var_os("XDG_RUNTIME_DIR").map_or_else(std::env::temp_dir, PathBuf::from);
    dir.join("vinc-distributed-state.json")
}

/// The container backend of one run.
#[derive(Debug)]
pub struct Containers {
    helper: Helper,
    /// The routers, by site.
    pub routers: Vec<Started>,
    /// The nodes, in plan order.
    pub nodes: Vec<Started>,
    image_id: String,
    ifb_loaded: bool,
    names: Vec<String>,
}

async fn cgroup_of(pid: u32) -> Result<PathBuf> {
    let text = tokio::fs::read_to_string(format!("/proc/{pid}/cgroup")).await?;
    let rel = text
        .lines()
        .find_map(|l| l.strip_prefix("0::"))
        .ok_or_else(|| Error::Host("the host does not use cgroup v2, which the kernel metrics read".into()))?;
    Ok(Path::new("/sys/fs/cgroup").join(rel.trim_start_matches('/')))
}

fn run_args(c: &Container, run: &str, image: &str, bin: Option<&Path>) -> Vec<String> {
    let mem = format!("{}m", c.memory_mib);
    let label = format!("{LABEL}={run}");
    let mut a: Vec<String> = [
        "run",
        "-d",
        "--name",
        c.name.as_str(),
        "--label",
        label.as_str(),
        "--network",
        "none",
        "--cpuset-cpus",
        c.cpus.as_str(),
        "--memory",
        mem.as_str(),
        "--memory-swap",
        mem.as_str(),
        "--pids-limit",
        "4096",
        "--ulimit",
        "nofile=65536:65536",
        "--entrypoint",
        "sleep",
    ]
    .iter()
    .map(|s| (*s).to_owned())
    .collect();
    if let Some(b) = bin {
        // Bound read-only, so a rebuild needs no image and every node runs the orchestrator's own build.
        a.extend(["-v".into(), format!("{}:{BIN}:ro", b.display())]);
    }
    if let Some(r) = std::env::var_os("VINC_RELAY_BIN") {
        let at = crate::node::vinc::relay_server::RELAY_BIN;
        a.extend(["-v".into(), format!("{}:{at}:ro", Path::new(&r).display())]);
    }
    a.extend([image.to_owned(), "infinity".into()]);
    a
}

impl Containers {
    /// Refuse to start over leftovers: containers of any run of the harness, or a state file of one.
    ///
    /// # Errors
    /// [`Error::Leftovers`] naming them.
    pub async fn preflight() -> Result<()> {
        let left = docker::labelled().await?;
        if !left.is_empty() {
            return Err(Error::Leftovers(left.into_iter().map(|(n, _)| n).collect()));
        }
        if state_path().exists() {
            return Err(Error::Leftovers(vec![state_path().display().to_string()]));
        }
        Ok(())
    }

    /// Create every container and wire the plan. On any failure, removes what it created and returns the error.
    ///
    /// # Errors
    /// Leftovers, Docker, sudo or a wiring command failed.
    pub async fn up(plan: &Plan, image: &str) -> Result<Self> {
        Self::preflight().await?;
        let image_id = docker::ensure_image(image).await?;
        check_libc(image).await?;
        let helper = Helper::start()?;
        let ifb_loaded = helper.call(Req::Ifb { load: true }).await? == "loaded";
        let mut me = Self {
            helper,
            routers: Vec::new(),
            nodes: Vec::new(),
            image_id,
            ifb_loaded,
            names: Vec::new(),
        };
        me.save_state(&plan.run)?;
        match me.build(plan, image).await {
            Ok(()) => Ok(me),
            Err(e) => {
                let _ = me.down().await;
                Err(e)
            }
        }
    }

    fn save_state(&self, run: &str) -> Result<()> {
        let s = State {
            run: run.to_owned(),
            containers: self.names.clone(),
            ifb_loaded: self.ifb_loaded,
        };
        std::fs::write(state_path(), serde_json::to_vec(&s).unwrap_or_default())?;
        Ok(())
    }

    async fn build(&mut self, plan: &Plan, image: &str) -> Result<()> {
        let exe = std::env::current_exe()?;
        let mut specs: Vec<(Container, Option<&Path>)> = plan.sites.iter().map(|s| (s.router.clone(), None)).collect();
        specs.extend(plan.nodes.iter().map(|n| (n.container.clone(), Some(exe.as_path()))));
        self.names = specs.iter().map(|(c, _)| c.name.clone()).collect();
        self.save_state(&plan.run)?;
        // Owned arguments: a future that borrows through a closure's argument is not `Send` for every lifetime.
        let jobs: Vec<Vec<String>> = specs.iter().map(|(c, b)| run_args(c, &plan.run, image, *b)).collect();
        let results: Vec<Result<String>> = futures::stream::iter(jobs)
            .map(|args: Vec<String>| async move {
                let a: Vec<&str> = args.iter().map(String::as_str).collect();
                docker::docker(&a).await
            })
            .buffered(PARALLEL)
            .collect()
            .await;
        for r in results {
            r?;
        }
        let infos: Vec<Info> = docker::inspect(&self.names).await?;
        let mut started = Vec::with_capacity(infos.len());
        for (name, info) in self.names.iter().zip(infos) {
            started.push(Started {
                name: name.clone(),
                pid: info.pid,
                cgroup: cgroup_of(info.pid).await?,
            });
        }
        let nodes = started.split_off(plan.sites.len());
        self.routers = started;
        self.nodes = nodes;
        for v in &plan.veths {
            let (pa, pb) = (self.pid(v.a.0)?.to_string(), self.pid(v.b.0)?.to_string());
            let args = [
                "link",
                "add",
                v.a.1.as_str(),
                "netns",
                pa.as_str(),
                "type",
                "veth",
                "peer",
                "name",
                v.b.1.as_str(),
                "netns",
                pb.as_str(),
            ];
            self.helper
                .run(None, "ip", args.iter().map(|s| (*s).to_owned()).collect())
                .await?;
        }
        for (ns, cmds) in &plan.setup {
            let pid = self.pid(*ns)?;
            for c in cmds {
                self.helper.run(Some(pid), c.tool.program(), c.args.clone()).await?;
            }
        }
        Ok(())
    }

    fn pid(&self, ns: Ns) -> Result<u32> {
        let s = match ns {
            Ns::Router(i) => self.routers.get(i),
            Ns::Node(i) => self.nodes.get(i),
        };
        s.map(|s| s.pid)
            .ok_or_else(|| Error::Host("a namespace of the plan has no container".into()))
    }

    /// The cgroup names of every container of the run, as `/proc/<pid>/cgroup` shows them.
    pub fn scopes(&self) -> Vec<String> {
        self.routers
            .iter()
            .chain(&self.nodes)
            .filter_map(|s| s.cgroup.file_name().map(|n| n.to_string_lossy().into_owned()))
            .collect()
    }

    /// The image the nodes run on (its id).
    pub fn image_id(&self) -> &str {
        &self.image_id
    }

    /// Start the node binary in node `i` with `args` and the environment `env`.
    ///
    /// # Errors
    /// The node does not exist or Docker failed.
    pub fn spawn(&self, i: usize, args: &[String], env: &[(String, String)]) -> Result<Proc> {
        let n = self
            .nodes
            .get(i)
            .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
        let mut cmd = Command::new("docker");
        cmd.arg("exec").arg("-i");
        for (k, v) in env {
            cmd.arg("-e").arg(format!("{k}={v}"));
        }
        cmd.arg(&n.name).arg(BIN).args(args);
        Proc::spawn(cmd, format!("the node program on {}", n.name))
    }

    /// Kill every program running in node `i` (its first process, which holds the namespaces, stays).
    ///
    /// # Errors
    /// Docker failed.
    pub async fn stop(&self, i: usize) -> Result<()> {
        let n = self
            .nodes
            .get(i)
            .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
        // `kill -1` signals every process but the caller and the namespace's first process.
        docker::docker(&["exec", &n.name, "sh", "-c", "kill -9 -1 2>/dev/null; true"]).await?;
        Ok(())
    }

    /// Freeze or thaw node `i`.
    ///
    /// # Errors
    /// Docker failed.
    pub async fn pause(&self, i: usize, pause: bool) -> Result<()> {
        let n = self
            .nodes
            .get(i)
            .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
        docker::docker(&[if pause { "pause" } else { "unpause" }, &n.name]).await?;
        Ok(())
    }

    /// Read node `i`'s CPU time and interface counters.
    ///
    /// # Errors
    /// The files cannot be read.
    pub async fn reading(&self, i: usize) -> Result<Reading> {
        let n = self
            .nodes
            .get(i)
            .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
        let cpu = tokio::fs::read_to_string(n.cgroup.join("cpu.stat")).await?;
        let dev = self
            .helper
            .call(Req::Read {
                path: format!("/proc/{}/net/dev", n.pid),
            })
            .await?;
        Ok(Reading {
            cpu_usec: metrics::parse_cpu_usec(&cpu),
            eth0: metrics::parse_net_dev(&dev).get("eth0").copied(),
        })
    }

    fn peak_path(&self, i: usize) -> Result<String> {
        let n = self
            .nodes
            .get(i)
            .ok_or_else(|| Error::Node(format!("there is no node {i}")))?;
        Ok(n.cgroup.join("memory.peak").display().to_string())
    }

    /// Start measuring node `i`'s peak memory afresh.
    ///
    /// # Errors
    /// The helper refused.
    pub async fn peak_reset(&self, i: usize) -> Result<()> {
        self.helper
            .call(Req::PeakReset {
                path: self.peak_path(i)?,
            })
            .await
            .map(|_| ())
    }

    /// Node `i`'s peak memory in bytes since [`Self::peak_reset`].
    ///
    /// # Errors
    /// The helper refused.
    pub async fn peak_read(&self, i: usize) -> Result<Option<u64>> {
        Ok(self
            .helper
            .call(Req::PeakRead {
                path: self.peak_path(i)?,
            })
            .await?
            .trim()
            .parse()
            .ok())
    }

    /// The counters of every shaper of site `s`'s router.
    ///
    /// # Errors
    /// The helper refused.
    pub async fn shapers(&self, s: usize) -> Result<Vec<Qdisc>> {
        let pid = self.pid(Ns::Router(s))?;
        let out = self
            .helper
            .run(
                Some(pid),
                "tc",
                vec!["-s".into(), "-j".into(), "qdisc".into(), "show".into()],
            )
            .await?;
        Ok(metrics::parse_tc(&out))
    }

    /// Give one direction of a link a new shape, now.
    ///
    /// # Errors
    /// tc failed.
    pub async fn reshape(&self, at: &ShapePoint, shape: &Shape) -> Result<()> {
        let pid = self.pid(at.ns)?;
        let mut args = vec![
            "qdisc".into(),
            "change".into(),
            "dev".into(),
            at.dev.clone(),
            "root".into(),
        ];
        args.extend(netem_args(shape));
        self.helper.run(Some(pid), "tc", args).await.map(|_| ())
    }

    /// Remove every container of the run and unload `ifb` if this run loaded it; then check that nothing is left.
    /// Returns what is still there (empty when the teardown is clean).
    ///
    /// # Errors
    /// Docker failed.
    pub async fn down(&mut self) -> Result<Vec<String>> {
        docker::remove(&self.names).await?;
        if self.ifb_loaded {
            self.helper.call(Req::Ifb { load: false }).await?;
            self.ifb_loaded = false;
        }
        let left = leftovers(&self.helper).await?;
        if left.is_empty() {
            let _ = std::fs::remove_file(state_path());
        }
        Ok(left)
    }
}

/// What a run of the harness may have left on this machine: its containers, links in the host's namespace with the
/// harness's names, and network emulators in the host's namespace.
async fn leftovers(helper: &Helper) -> Result<Vec<String>> {
    let mut left: Vec<String> = docker::labelled()
        .await?
        .into_iter()
        .map(|(n, r)| format!("container {n} (run {r})"))
        .collect();
    let links = helper
        .run(None, "ip", vec!["-o".into(), "link".into(), "show".into()])
        .await?;
    for l in links.lines() {
        let name = l.split(':').nth(1).map_or("", str::trim);
        let name = name.split('@').next().unwrap_or(name);
        // The run creates no link in the host's namespace; an `ifb` device here means the module was loaded with its
        // default devices.
        if name.starts_with("vd-") || name.starts_with("ifb") {
            left.push(format!("host link {name}"));
        }
    }
    let qdiscs = helper.run(None, "tc", vec!["qdisc".into(), "show".into()]).await?;
    for l in qdiscs.lines().filter(|l| l.contains("netem")) {
        left.push(format!("host shaper: {}", l.trim()));
    }
    Ok(left)
}

/// What `clean` found and did.
#[derive(Debug, Default, Serialize)]
pub struct Cleaned {
    /// The containers removed.
    pub removed: Vec<String>,
    /// Whether the `ifb` module was unloaded.
    pub unloaded_ifb: bool,
    /// What is still there after cleaning.
    pub left: Vec<String>,
}

/// Remove everything a run may have left: its containers (by label), the `ifb` module if a run loaded it, the state
/// file; then check.
///
/// # Errors
/// Docker or sudo failed.
pub async fn clean() -> Result<Cleaned> {
    let mut out = Cleaned::default();
    let found = docker::labelled().await?;
    out.removed = found.iter().map(|(n, _)| n.clone()).collect();
    docker::remove(&out.removed).await?;
    let helper = Helper::start()?;
    let state: Option<State> = std::fs::read(state_path())
        .ok()
        .and_then(|b| serde_json::from_slice(&b).ok());
    if state.as_ref().is_some_and(|s| s.ifb_loaded) {
        helper.call(Req::Ifb { load: false }).await?;
        out.unloaded_ifb = true;
    }
    out.left = leftovers(&helper).await?;
    if out.left.is_empty() {
        let _ = std::fs::remove_file(state_path());
    }
    Ok(out)
}

/// How long the backend waits for a node program to print its first line.
pub const READY: Duration = Duration::from_secs(60);
