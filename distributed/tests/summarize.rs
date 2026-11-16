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
