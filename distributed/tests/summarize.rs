//! `results::resummarize`: the summary of a results directory rebuilt from its rows.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

use std::path::PathBuf;

use vinc_distributed::results::{Row, markdown, resummarize, summarize};

fn dir(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("vinc-distributed-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn row(stack: &str, p50: f64) -> Row {
    let mut node = serde_json::Map::new();
    node.insert("p50_us".into(), p50.into());
    Row {
        run: "r".into(),
        stack: stack.into(),
        test: "setup".into(),
        pair: "a>b".into(),
        rep: 0,
        status: "ok".into(),
        node,
        kernel: std::collections::BTreeMap::default(),
        shaper_drops: Some(0),
        host: None,
    }
}

#[test]
fn the_summary_is_rebuilt_from_the_rows_and_a_second_call_changes_nothing() {
    let d = dir("summarize");
    let rows = [row("vinc", 900.0), row("iroh", 1200.0)];
    let lines: Vec<String> = rows.iter().map(|r| serde_json::to_string(r).unwrap()).collect();
    std::fs::write(d.join("raw.jsonl"), lines.join("\n")).unwrap();
    let stacks = vec!["vinc".to_owned(), "iroh".to_owned()];
    let conditions = vec!["Backend: a machine.".to_owned()];
    let title = d.file_name().unwrap().to_string_lossy().into_owned();
    let old = markdown(&title, &conditions, &summarize(&rows[..1], &stacks[..1]));
    std::fs::write(d.join("summary.md"), &old).unwrap();

    assert!(resummarize(&d).unwrap());
    let new = std::fs::read_to_string(d.join("summary.md")).unwrap();
    assert_eq!(new, markdown(&title, &conditions, &summarize(&rows, &stacks)));
    assert_eq!(std::fs::read_to_string(d.join("summary.before.md")).unwrap(), old);

    std::fs::remove_file(d.join("summary.before.md")).unwrap();
    assert!(!resummarize(&d).unwrap());
    assert!(
        !d.join("summary.before.md").exists(),
        "an unchanged summary writes nothing"
    );
    assert_eq!(std::fs::read_to_string(d.join("summary.md")).unwrap(), new);
}

#[test]
fn a_directory_without_rows_is_an_error_that_names_it() {
    let d = dir("summarize-none");
    let e = resummarize(&d).unwrap_err();
    assert!(e.contains(&d.display().to_string()) && e.contains("raw.jsonl"), "{e}");
}

fn many_row(stack: &str, test: &str, server_peak: f64, client_peak: f64) -> Row {
    let mut r = row(stack, 0.0);
    r.test = test.into();
    r.node.clear();
    for (k, v) in [
        ("connected_and_moved", 500.0),
        ("all_done_s", 1.0),
        ("server_peak_kib_per_conn", server_peak),
        ("client_peak_kib_per_conn", client_peak),
    ] {
        r.node.insert(k.into(), v.into());
    }
    r
}

#[test]
fn the_peak_rows_and_the_driven_reading_pass_through_a_rebuilt_summary_and_a_stack_without_a_value_never_wins() {
    let mut gone = many_row("libp2p", "many_driven", 1.0, 1.0);
    gone.node.clear();
    gone.status = "not measured: the client printed no result".into();
    let rows = vec![
        many_row("vinc", "many", 120.0, 190.0),
        many_row("iroh", "many", 150.0, 170.0),
        many_row("libp2p", "many", 300.0, 400.0),
        many_row("vinc", "many_driven", 110.0, 180.0),
        many_row("iroh", "many_driven", 140.0, 160.0),
        gone,
    ];
    let stacks: Vec<String> = ["vinc", "iroh", "libp2p"].iter().map(|s| (*s).to_owned()).collect();
    let tables = summarize(&rows, &stacks);
    let tests: Vec<&str> = tables.iter().map(|t| t.test.as_str()).collect();
    assert_eq!(tests, ["many", "many_driven"], "each reading is a table of its own");
    assert!(tables[0].notes[0].contains("500 ms") && tables[0].notes[0].contains("undriven"));
    assert!(tables[1].notes[0].contains("1.5 s") && !tables[1].notes[0].contains("undriven"));
    for t in &tables {
        let line = |label: &str| t.lines.iter().find(|l| l.label == label).unwrap();
        assert_eq!(line("server peak memory per connection").best, Some(0), "{}", t.test);
        assert_eq!(line("client peak memory per connection").best, Some(1), "{}", t.test);
    }
    let last = &tables[1]
        .lines
        .iter()
        .find(|l| l.label.starts_with("server peak"))
        .unwrap();
    assert!(matches!(last.cells[2], vinc_distributed::results::Cell::Missing(_)));

    let d = dir("summarize-many");
    let lines: Vec<String> = rows.iter().map(|r| serde_json::to_string(r).unwrap()).collect();
    std::fs::write(d.join("raw.jsonl"), lines.join("\n")).unwrap();
    let title = d.file_name().unwrap().to_string_lossy().into_owned();
    let conditions = vec!["Backend: a machine.".to_owned()];
    let old = markdown(&title, &conditions, &summarize(&rows[..1], &stacks[..1]));
    std::fs::write(d.join("summary.md"), old).unwrap();
    assert!(resummarize(&d).unwrap());
    let new = std::fs::read_to_string(d.join("summary.md")).unwrap();
    for want in [
        "many_driven",
        "server peak memory per connection",
        "client peak memory per connection",
    ] {
        assert!(new.contains(want), "the rebuilt summary lacks {want}");
    }
    assert_eq!(
        new,
        markdown(&title, &conditions, &tables),
        "the rebuilt rows print what the run printed"
    );
}

#[test]
fn a_many_cell_that_was_null_in_the_line_is_missing_and_never_ranked() {
    let mut unknown = many_row("iroh", "many", 1.0, 1.0);
    unknown
        .node
        .insert("server_peak_kib_per_conn".into(), serde_json::Value::Null);
    let rows = vec![many_row("vinc", "many", 120.0, 190.0), unknown];
    let stacks: Vec<String> = ["vinc", "iroh"].iter().map(|s| (*s).to_owned()).collect();
    let tables = summarize(&rows, &stacks);
    let line = tables[0]
        .lines
        .iter()
        .find(|l| l.label == "server peak memory per connection")
        .unwrap();
    assert!(matches!(line.cells[1], vinc_distributed::results::Cell::Missing(_)));
    assert_ne!(line.best, Some(1), "a value that was not measured is not the best");
}
