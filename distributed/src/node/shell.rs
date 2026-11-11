//! The shell of the node programs that run on tokio (iroh and rust-libp2p): the request loop, shared so the two stacks
//! differ only in what a request does.
//!
//! Every request runs as its own task, so a long one (a publication run, a fetch) does not hold up a report; each is
//! answered exactly once. `Stop` is answered after its handler returns and ends the loop.
//!
//! Invariants: no request is dropped without an answer; the program ends when its input closes or after `Stop`.

use std::sync::Arc;

use serde_json::Value;
use tokio::sync::mpsc;

use crate::node::app::{emit, for_each_request};
use crate::node::proto::{Cmd, Ready, Reply, Request};

/// What a stack does with a request.
pub trait Handler: Send + Sync + 'static {
    /// Do `cmd`; the value is the reply's data, the error its message.
    fn handle(self: Arc<Self>, cmd: Cmd) -> impl Future<Output = Result<Value, String>> + Send;
}

/// Announce the stack is up and serve requests until the input closes or `Stop`.
///
/// # Errors
/// The ready line could not be written or the input thread did not start.
pub async fn serve<H: Handler>(h: Arc<H>, ready: Ready) -> Result<(), String> {
    println!("READY {}", serde_json::to_string(&ready).map_err(|e| e.to_string())?);
    let (tx, mut rx) = mpsc::channel::<Request>(1024);
    std::thread::Builder::new()
        .name("requests".into())
        .spawn(move || for_each_request(|r| tx.blocking_send(r).is_ok()))
        .map_err(|e| format!("the input thread did not start: {e}"))?;
    while let Some(req) = rx.recv().await {
        let id = req.id;
        if matches!(req.cmd, Cmd::Stop) {
            let r = Arc::clone(&h).handle(req.cmd).await;
            emit(&to_reply(id, r));
            return Ok(());
        }
        let h = Arc::clone(&h);
        tokio::spawn(async move {
            let r = h.handle(req.cmd).await;
            emit(&to_reply(id, r));
        });
    }
    Ok(())
}

fn to_reply(id: u64, r: Result<Value, String>) -> Reply {
    match r {
        Ok(v) => Reply::ok(id, v),
        Err(e) => Reply::fail(id, e),
    }
}
