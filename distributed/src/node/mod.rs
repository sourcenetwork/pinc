//! Node mode: what the orchestrator starts in every node, with the stack to run.
//!
//! `node transport --stack <vinc|iroh|libp2p> server|client ...` runs one side of a transport test: the comparison
//! benches' own scenario code, with the same output (`ADDR <address>` from a server, one JSON line per result from a
//! client).

pub mod transport;

use crate::scenario::Stack;

/// Run node mode with the arguments after `node`; returns the process's exit code.
pub fn main(args: &[String]) -> i32 {
    let usage = "usage: vinc-distributed node transport --stack <vinc|iroh|libp2p> server|client ...";
    let Some((kind, rest)) = args.split_first() else {
        eprintln!("{usage}");
        return 2;
    };
    let Some(stack_at) = rest.iter().position(|a| a == "--stack") else {
        eprintln!("{usage}");
        return 2;
    };
    let Some(stack) = rest.get(stack_at + 1).and_then(|s| Stack::parse(s)) else {
        eprintln!("the stack must be vinc, iroh or libp2p");
        return 2;
    };
    let mut rest = rest.to_vec();
    rest.drain(stack_at..stack_at + 2);
    if kind == "transport" {
        transport::run(stack, rest);
        0
    } else {
        eprintln!("{usage}");
        2
    }
}
