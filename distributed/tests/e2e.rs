//! End to end on the build host: a two-node scenario on containers of this machine, every stack, one repetition;
//! every measurement must succeed and the teardown must leave nothing. Needs Docker and `sudo -n`, so it is ignored
//! by default and run with `just e2e` (`cargo nextest run --run-ignored only`).
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::process::Command;

use vinc_distributed::results::read_rows;

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
    let bin = env!("CARGO_BIN_EXE_vinc-distributed");
    let dir = std::env::temp_dir().join(format!("vinc-distributed-e2e-{}", std::process::id()));
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
        .args(["ps", "-aq", "--filter", "label=vinc.distributed"])
        .output()
        .unwrap();
    assert!(left.stdout.is_empty(), "the teardown left containers");
    let _ = std::fs::remove_dir_all(&dir);
}
