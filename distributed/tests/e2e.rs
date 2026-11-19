//! End to end on the build host: a two-node scenario on containers of this machine, every stack, one repetition;
//! every measurement must succeed and the teardown must leave nothing. Needs Docker and `sudo -n`, so it is ignored
//! by default and run with `just e2e` (`cargo nextest run --run-ignored only`). Two more runs check hole punching
//! through the home routers: a pair behind port-restricted routers ends on a direct path, a pair behind symmetric ones
//! stays on the relay.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::process::Command;

use pinc_distributed::results::read_rows;

const SCENARIO: &str = r#"
name = "e2e"
about = "Two nodes on one LAN, every stack, small tests."
repetitions = 1

[[sites]]
name = "lan"

[[nodes]]
name = "n1"
site = "lan"

[[nodes]]
name = "n2"
site = "lan"

[workload]
kind = "transport"
timeout_s = 120
pairs = [{ client = "n1", server = "n2" }]

[[workload.tests]]
test = "setup"
count = 5

[[workload.tests]]
test = "latency"
size = 64
round_trips = 200

[[workload.tests]]
test = "throughput"
bytes = 4194304
streams = 2
"#;

#[test]
#[ignore = "needs Docker and sudo: run with `just e2e` on the build host"]
fn a_two_node_scenario_runs_every_stack_and_tears_down() {
    let bin = env!("CARGO_BIN_EXE_pinc-distributed");
    let dir = std::env::temp_dir().join(format!("pinc-distributed-e2e-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("e2e.toml");
    std::fs::write(&file, SCENARIO).unwrap();
    let out = Command::new(bin)
        // The test checks that everything works and tears down, not numbers: any load on the host is accepted.
        .args([
            "run",
            file.to_str().unwrap(),
            "--results",
            dir.join("results").to_str().unwrap(),
        ])
        .args(["--quiet-other", "100000", "--quiet-steal", "100", "--quiet-wait", "60"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "the run failed:\n{stderr}");
    let line = String::from_utf8_lossy(&out.stdout);
    let results = line
        .trim()
        .strip_prefix("results: ")
        .expect("the run names its results directory");
    let rows = read_rows(std::path::Path::new(results)).unwrap();
    assert_eq!(rows.len(), 9, "three tests for three stacks");
    for r in &rows {
        assert_eq!(r.status, "ok", "{} {} was not measured", r.stack, r.test);
        let k = &r.kernel["client"];
        assert!(
            k.cpu_s.is_some() && k.peak_mib.is_some() && k.eth0.is_some(),
            "the kernel's numbers are missing"
        );
    }
    for name in ["summary.md", "run.json", "scenario.toml"] {
        assert!(std::path::Path::new(results).join(name).is_file(), "{name} is missing");
    }
    let left = Command::new("docker")
        .args(["ps", "-aq", "--filter", "label=pinc.distributed"])
        .output()
        .unwrap();
    assert!(left.stdout.is_empty(), "the teardown left containers");
    let _ = std::fs::remove_dir_all(&dir);
}

/// Runs the committed scenario `name` once and returns, for each fetch, the payload size and what the two public nodes
/// received: a relayed session rides the relay or the hub, whichever the dial went through.
fn relay_bytes(name: &str) -> Vec<(f64, u64)> {
    let bin = env!("CARGO_BIN_EXE_pinc-distributed");
    let file = format!("{}/scenarios/{name}.toml", env!("CARGO_MANIFEST_DIR"));
    let dir = std::env::temp_dir().join(format!("pinc-distributed-{name}-{}", std::process::id()));
    let out = Command::new(bin)
        .args(["run", &file, "--reps", "1", "--results", dir.to_str().unwrap()])
        .args(["--quiet-other", "100000", "--quiet-steal", "100", "--quiet-wait", "60"])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "the run failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let line = String::from_utf8_lossy(&out.stdout);
    let results = line
        .trim()
        .strip_prefix("results: ")
        .expect("the run names its results directory");
    let rows = read_rows(std::path::Path::new(results)).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!rows.is_empty(), "nothing was measured");
    rows.iter()
        .map(|r| {
            assert_eq!(r.status, "ok", "{} was not measured", r.test);
            let bytes = r.node["bytes"].as_f64().unwrap();
            let rx = |n: &str| r.kernel[n].eth0.as_ref().unwrap().rx_bytes;
            (bytes, rx("relay") + rx("hub"))
        })
        .collect()
}

#[test]
#[ignore = "needs Docker and sudo: run with `just e2e` on the build host"]
fn a_pair_behind_port_restricted_routers_goes_direct() {
    for (bytes, relay) in relay_bytes("punch-port-restricted") {
        // Direct after the dial: the relay carries the dial and the punch, about 80 KB, never the payload.
        #[allow(clippy::cast_precision_loss)]
        let ok = (relay as f64) < bytes / 8.0;
        assert!(
            ok,
            "the relay and hub received {relay} bytes of a {bytes}-byte fetch: the pair did not punch"
        );
    }
}

#[test]
#[ignore = "needs Docker and sudo: run with `just e2e` on the build host"]
fn a_pair_behind_symmetric_routers_stays_on_the_relay() {
    for (bytes, relay) in relay_bytes("punch-symmetric") {
        #[allow(clippy::cast_precision_loss)]
        let ok = relay as f64 > bytes;
        assert!(
            ok,
            "the relay and hub received {relay} bytes of a {bytes}-byte fetch: a symmetric pair cannot go direct"
        );
    }
}
