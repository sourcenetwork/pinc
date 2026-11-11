//! A node program started by a backend: its standard input for commands, its standard output as lines, the tail of
//! its error output for the report when it fails.

use std::collections::VecDeque;
use std::process::Stdio;
use std::time::Duration;

use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, Command};
use tokio::sync::{mpsc, oneshot};

use crate::error::{Error, Result};

/// Lines of output a node may have waiting before its reader stops reading (and the node blocks on its output).
const LINES: usize = 4096;
/// Lines of error output kept for the report.
const TAIL: usize = 20;

/// A running node program.
#[derive(Debug)]
pub struct Proc {
    child: Child,
    stdin: Option<ChildStdin>,
    lines: mpsc::Receiver<String>,
    tail: Option<oneshot::Receiver<String>>,
    what: String,
}

impl Proc {
    /// Start `cmd` with its three streams piped.
    ///
    /// # Errors
    /// The program did not start.
    pub fn spawn(mut cmd: Command, what: String) -> Result<Self> {
        let mut child = cmd
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true)
            .spawn()
            .map_err(|e| Error::Node(format!("{what} did not start: {e}")))?;
        let (Some(out), Some(err)) = (child.stdout.take(), child.stderr.take()) else {
            return Err(Error::Node(format!("{what}: its output pipes are missing")));
        };
        let (tx, lines) = mpsc::channel(LINES);
        tokio::spawn(async move {
            let mut r = BufReader::new(out).lines();
            while let Ok(Some(l)) = r.next_line().await {
                if tx.send(l).await.is_err() {
                    break;
                }
            }
        });
        let (ttx, tail) = oneshot::channel();
        tokio::spawn(async move {
            let mut r = BufReader::new(err).lines();
            let mut keep = VecDeque::with_capacity(TAIL);
            while let Ok(Some(l)) = r.next_line().await {
                if keep.len() == TAIL {
                    keep.pop_front();
                }
                keep.push_back(l);
            }
            let _ = ttx.send(keep.into_iter().collect::<Vec<_>>().join("\n"));
        });
        Ok(Self {
            stdin: child.stdin.take(),
            child,
            lines,
            tail: Some(tail),
            what,
        })
    }

    /// The next line of output, `None` once the program closed its output.
    ///
    /// # Errors
    /// No line came within `wait`.
    pub async fn line(&mut self, wait: Duration) -> Result<Option<String>> {
        tokio::time::timeout(wait, self.lines.recv())
            .await
            .map_err(|_| Error::Timeout(format!("{} said nothing for {} s", self.what, wait.as_secs())))
    }

    /// Wait for a line that starts with `prefix` and return the rest of it.
    ///
    /// # Errors
    /// The program ended or said nothing for `wait`.
    pub async fn expect(&mut self, prefix: &str, wait: Duration) -> Result<String> {
        let deadline = tokio::time::Instant::now() + wait;
        loop {
            let left = deadline.saturating_duration_since(tokio::time::Instant::now());
            let Some(l) = self.line(left).await? else {
                let tail = self.stderr_tail().await;
                return Err(Error::Node(format!("{} ended before it was ready: {tail}", self.what)));
            };
            if let Some(rest) = l.strip_prefix(prefix) {
                return Ok(rest.trim().to_owned());
            }
        }
    }

    /// Send one line to the program's input.
    ///
    /// # Errors
    /// The program closed its input.
    pub async fn send(&mut self, line: &str) -> Result<()> {
        let Some(input) = self.stdin.as_mut() else {
            return Err(Error::Node(format!("{} has no input", self.what)));
        };
        input
            .write_all(format!("{line}\n").as_bytes())
            .await
            .map_err(|e| Error::Node(format!("{} stopped reading: {e}", self.what)))
    }

    /// Read every remaining line until the program ends, at most `wait`; whether it ended, with its lines.
    pub async fn drain(&mut self, wait: Duration) -> (Vec<String>, bool) {
        let mut out = Vec::new();
        let deadline = tokio::time::Instant::now() + wait;
        loop {
            let left = deadline.saturating_duration_since(tokio::time::Instant::now());
            match tokio::time::timeout(left, self.lines.recv()).await {
                Ok(Some(l)) => out.push(l),
                Ok(None) => return (out, true),
                Err(_) => return (out, false),
            }
        }
    }

    /// The last lines of the program's error output (once it ended), or a note that there were none.
    pub async fn stderr_tail(&mut self) -> String {
        let Some(t) = self.tail.take() else {
            return String::new();
        };
        match tokio::time::timeout(Duration::from_secs(2), t).await {
            Ok(Ok(s)) if !s.is_empty() => s,
            _ => "no error output".into(),
        }
    }

    /// Stop the local end (the `docker exec` or `ssh` process); the backend stops the program itself.
    pub async fn close(mut self) {
        drop(self.stdin.take());
        let _ = self.child.start_kill();
        let _ = self.child.wait().await;
    }
}
