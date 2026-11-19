//! The node program that runs a workload (`node app`): reads its set-up and then its requests from standard input, runs
//! the stack the set-up names, and answers on standard output (see [`crate::node::proto`]).
//!
//! Invariants: standard output carries only protocol lines; a line that is not a request is answered with an error and
//! the program goes on; the program ends when its input closes.

use std::io::BufRead;

use serde::Serialize;

use crate::node::proto::{Init, Reply, Request};
use crate::scenario::Stack;

/// Print one protocol line.
pub fn emit<T: Serialize>(v: &T) {
    match serde_json::to_string(v) {
        Ok(line) => println!("{line}"),
        Err(e) => eprintln!("a reply could not be written: {e}"),
    }
}

/// The set-up: the first line of standard input.
///
/// # Errors
/// The input ended or the line is not a set-up.
pub fn read_init() -> Result<Init, String> {
    let mut line = String::new();
    std::io::stdin()
        .lock()
        .read_line(&mut line)
        .map_err(|e| format!("the set-up could not be read: {e}"))?;
    serde_json::from_str(&line).map_err(|e| format!("the set-up is not valid: {e}"))
}

/// Call `f` with every request until the input closes or `f` returns false. Blocks; run it on its own thread.
pub fn for_each_request(mut f: impl FnMut(Request) -> bool) {
    for line in std::io::stdin().lock().lines() {
        let Ok(line) = line else { return };
        if line.trim().is_empty() {
            continue;
        }
        match serde_json::from_str::<Request>(&line) {
            Ok(req) => {
                if !f(req) {
                    return;
                }
            }
            Err(e) => emit(&Reply::fail(0, format!("that request is not understood: {e}"))),
        }
    }
}

/// Run the program; returns its exit code.
pub fn main(_args: &[String]) -> i32 {
    let init = match read_init() {
        Ok(i) => i,
        Err(e) => {
            eprintln!("{e}");
            return 2;
        }
    };
    let result = match init.stack {
        Stack::Pinc => super::pinc::run(init),
        Stack::Iroh => super::iroh_app::run(init),
        Stack::Libp2p => super::libp2p_app::run(init),
    };
    match result {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("{e}");
            1
        }
    }
}
