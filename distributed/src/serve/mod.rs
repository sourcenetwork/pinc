//! `serve`: the orchestrator with its dashboard, an HTTP server the binary carries whole (pages, styles and scripts
//! are compiled in; no toolchain, no CDN).
//!
//! It binds 127.0.0.1 by default and is reached through an SSH tunnel. Binding any other address needs `--token`, and
//! then every request must carry it (a cookie the page sets from `?token=` on its first load). Requests that change
//! anything must carry the `x-vd` header, which a page of another origin cannot send without the server's consent,
//! and on a local bind the `Host` header must name the loopback, so another site cannot drive the harness through the
//! operator's browser.

mod api;
mod assets;
pub mod manager;

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper_util::rt::TokioIo;
use tokio::net::TcpListener;

use crate::error::{Error, Result};
use crate::orchestrate::signalled;
use crate::serve::manager::Manager;

/// How the dashboard is served.
#[derive(Debug, Clone)]
pub struct ServeOptions {
    /// The address to listen on.
    pub bind: SocketAddr,
    /// The token every request must carry; required for a non-loopback bind.
    pub token: Option<String>,
    /// The harness directory: `scenarios/` and `results/` are under it.
    pub root: PathBuf,
    /// The node image.
    pub image: String,
    /// The machines to run on over SSH instead of containers.
    pub hosts: Option<crate::backend::fleet::Fleet>,
    /// When the machine counts as quiet enough to measure, for the runs the dashboard starts.
    pub quiet: crate::quiet::Thresholds,
}

/// What every handler shares.
#[derive(Debug)]
pub(crate) struct App {
    pub(crate) opts: ServeOptions,
    pub(crate) runs: Manager,
}

/// Serve the dashboard until a signal; a run that is going is stopped and torn down first.
///
/// # Errors
/// The address cannot be bound, or a non-loopback address was asked for without a token.
pub async fn serve(opts: ServeOptions) -> Result<()> {
    if !opts.bind.ip().is_loopback() && opts.token.as_deref().is_none_or(str::is_empty) {
        return Err(Error::Host(
            "binding an address other than the loopback needs --token; or keep the default and use an SSH tunnel"
                .into(),
        ));
    }
    let listener = TcpListener::bind(opts.bind)
        .await
        .map_err(|e| Error::Host(format!("cannot listen on {}: {e}", opts.bind)))?;
    let runs = Manager::start(
        opts.image.clone(),
        opts.root.join("results"),
        opts.hosts.clone(),
        opts.quiet,
    );
    let app = Arc::new(App { opts, runs });
    tracing::info!("dashboard on http://{}", app.opts.bind);
    loop {
        tokio::select! {
            () = signalled() => break,
            acc = listener.accept() => {
                let Ok((stream, _)) = acc else { continue };
                let app = app.clone();
                tokio::spawn(async move {
                    let svc = service_fn(move |req| api::handle(app.clone(), req));
                    let _ = http1::Builder::new().serve_connection(TokioIo::new(stream), svc).await;
                });
            }
        }
    }
    tracing::info!("stopping: a run that is going is torn down first");
    app.runs.shutdown().await;
    Ok(())
}
