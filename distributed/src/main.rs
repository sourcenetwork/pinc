//! `vinc-distributed`: one binary, several modes.
//!
//! ```text
//! vinc-distributed serve [--bind <addr:port>] [--token <token>] [--image <image>]
//! vinc-distributed run <scenario.toml> [--image <image>] [--results <dir>] [--reps <n>]
//!     [--quiet-other <% of a core>] [--quiet-steal <%>] [--quiet-wait <s>]
//! vinc-distributed validate <scenario.toml>
//! vinc-distributed plan <scenario.toml>
//! vinc-distributed clean
//! vinc-distributed node transport --stack <vinc|iroh|libp2p> server|client ...
//! vinc-distributed helper          (started by the orchestrator through sudo; not for direct use)
//! ```

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use vinc_distributed::backend::containers::{self, IMAGE};
use vinc_distributed::orchestrate::{self, Options};
use vinc_distributed::plan::Plan;
use vinc_distributed::quiet::Thresholds;
use vinc_distributed::scenario::Scenario;
use vinc_distributed::serve::{ServeOptions, serve};
use vinc_distributed::{helper, node};

const USAGE: &str = "usage:
  vinc-distributed serve [--bind <addr:port>] [--token <token>] [--image <image>]
  vinc-distributed run <scenario.toml> [--image <image>] [--results <dir>] [--reps <n>]
      [--quiet-other <% of a core>] [--quiet-steal <%>] [--quiet-wait <s>]
  vinc-distributed validate <scenario.toml>
  vinc-distributed plan <scenario.toml>
  vinc-distributed clean
  vinc-distributed node transport --stack <vinc|iroh|libp2p> server|client ...";

fn flag(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn load(path: &str) -> Result<Scenario, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    Scenario::parse(&text).map_err(|e| format!("{path}: {e}"))
}

fn runtime() -> Result<tokio::runtime::Runtime, String> {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .map_err(|e| format!("the runtime did not start: {e}"))
}

fn logs() {
    tracing_subscriber::fmt().with_writer(std::io::stderr).with_target(false).init();
}

fn results_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("results")
}

fn run(args: &[String]) -> Result<(), String> {
    let path = args.first().ok_or(USAGE)?;
    let sc = load(path)?;
    let reps = match flag(args, "--reps") {
        Some(r) => Some(r.parse::<u32>().map_err(|_| "--reps takes a number")?),
        None => None,
    };
    let opts = Options {
        image: flag(args, "--image").unwrap_or_else(|| IMAGE.into()),
        results: flag(args, "--results").map_or_else(results_root, PathBuf::from),
        reps,
        events: None,
        cancel: None,
        quiet: thresholds(args)?,
    };
    logs();
    let out = runtime()?.block_on(orchestrate::run(sc, opts)).map_err(|e| e.to_string())?;
    println!("results: {}", out.dir.display());
    if !out.left.is_empty() {
        return Err(format!(
            "the teardown left {}; run `vinc-distributed clean`",
            out.left.join(", ")
        ));
    }
    match out.error {
        Some(e) => Err(e.to_string()),
        None => Ok(()),
    }
}

fn dashboard(args: &[String]) -> Result<(), String> {
    let bind = flag(args, "--bind").unwrap_or_else(|| "127.0.0.1:7878".into());
    let opts = ServeOptions {
        bind: bind.parse().map_err(|_| format!("--bind takes an address and port, such as 127.0.0.1:7878, not {bind}"))?,
        token: flag(args, "--token"),
        root: PathBuf::from(env!("CARGO_MANIFEST_DIR")),
        image: flag(args, "--image").unwrap_or_else(|| IMAGE.into()),
    };
    logs();
    runtime()?.block_on(serve(opts)).map_err(|e| e.to_string())
}

fn thresholds(args: &[String]) -> Result<Thresholds, String> {
    let mut t = Thresholds::default();
    let num = |name: &str, v: &mut f64| -> Result<(), String> {
        if let Some(s) = flag(args, name) {
            *v = s.parse().map_err(|_| format!("{name} takes a number"))?;
        }
        Ok(())
    };
    num("--quiet-other", &mut t.other_pct)?;
    num("--quiet-steal", &mut t.steal_pct)?;
    num("--quiet-wait", &mut t.wait_s)?;
    Ok(t)
}

fn validate(args: &[String]) -> Result<(), String> {
    let path = args.first().ok_or(USAGE)?;
    let problems = load(path)?.validate();
    if problems.is_empty() {
        println!("{path}: valid");
        Ok(())
    } else {
        Err(problems.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n"))
    }
}

fn plan(args: &[String]) -> Result<(), String> {
    let path = args.first().ok_or(USAGE)?;
    let sc = load(path)?;
    let problems = sc.validate();
    if !problems.is_empty() {
        return Err(problems.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n"));
    }
    let cpus = std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
    let p = Plan::new(&sc, "RUN", cpus);
    for s in &p.sites {
        println!("# router {} ({}), LAN {}/24, cpus {}", s.router.name, s.name, s.lan, s.router.cpus);
    }
    for n in &p.nodes {
        println!("# node {} at {}, cpus {}, {} MiB", n.container.name, n.ip, n.container.cpus, n.container.memory_mib);
    }
    for v in &p.veths {
        println!("ip link add {} netns <{:?}> type veth peer name {} netns <{:?}>", v.a.1, v.a.0, v.b.1, v.b.0);
    }
    for (ns, cmds) in &p.setup {
        for c in cmds {
            println!("[{ns:?}] {}", c.line());
        }
    }
    Ok(())
}

fn clean() -> Result<(), String> {
    logs();
    let c = runtime()?.block_on(containers::clean()).map_err(|e| e.to_string())?;
    if c.removed.is_empty() && !c.unloaded_ifb {
        println!("nothing to clean");
    }
    for n in &c.removed {
        println!("removed container {n}");
    }
    if c.unloaded_ifb {
        println!("unloaded the ifb module a run had loaded");
    }
    if c.left.is_empty() {
        Ok(())
    } else {
        Err(format!("still there: {}", c.left.join(", ")))
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mode, rest) = args.split_first().map_or(("", &[][..]), |(m, r)| (m.as_str(), r));
    let result = match mode {
        "node" => return ExitCode::from(u8::try_from(node::main(rest)).unwrap_or(1)),
        "helper" => helper::serve().map_err(|e| format!("the helper stopped: {e}")),
        "run" => run(rest),
        "serve" => dashboard(rest),
        "validate" => validate(rest),
        "plan" => plan(rest),
        "clean" => clean(),
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
