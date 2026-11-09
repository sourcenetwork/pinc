//! A software TPM (`swtpm`) for the tests that need a TPM: each test starts its own on a free port in a fresh state
//! directory and kills it at the end. Only built with the `hwenc` feature, like the TPM store itself.
#![cfg(feature = "hwenc")]
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::missing_panics_doc,
    missing_docs
)]

use std::net::{Shutdown, TcpListener, TcpStream};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

use vinc_keystore::tpm::SimTransport;
use vinc_keystore::{TpmConfig, TpmStore};

const STARTUP_DEADLINE: Duration = Duration::from_secs(20);

static DIR_SEQ: AtomicU32 = AtomicU32::new(0);

/// A running `swtpm`, killed and cleaned up on drop.
pub struct Swtpm {
    child: Child,
    pub port: u16,
    dir: PathBuf,
}

impl Swtpm {
    pub fn start() -> Self {
        for _ in 0..8 {
            let port = free_port_pair();
            let dir = std::env::temp_dir().join(format!(
                "vinc-swtpm-{}-{}",
                std::process::id(),
                DIR_SEQ.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir_all(&dir).unwrap();
            let spawned = Command::new("swtpm")
                .args(["socket", "--tpm2", "--server"])
                .arg(format!("type=tcp,port={port}"))
                .arg("--ctrl")
                .arg(format!("type=tcp,port={}", port + 1))
                .arg("--tpmstate")
                .arg(format!("dir={}", dir.display()))
                .args(["--flags", "not-need-init,startup-clear"])
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn();
            let child = match spawned {
                Ok(child) => child,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    panic!("swtpm is not installed; install the `swtpm` package (/usr/bin/swtpm) to run the TPM tests")
                }
                Err(e) => panic!("could not start swtpm: {e}"),
            };
            let mut swtpm = Self { child, port, dir };
            if swtpm.wait_ready() {
                return swtpm;
            }
        }
        panic!("swtpm did not become ready on any of 8 ports");
    }

    /// Wait for the command port to accept, with a deadline and bounded backoff; false if swtpm exited (port taken).
    fn wait_ready(&mut self) -> bool {
        let deadline = Instant::now() + STARTUP_DEADLINE;
        let mut backoff = Duration::from_millis(1);
        loop {
            if self.child.try_wait().unwrap().is_some() {
                return false;
            }
            if let Ok(probe) = TcpStream::connect(("127.0.0.1", self.port)) {
                let _ = probe.shutdown(Shutdown::Both);
                // swtpm serves one client at a time and takes the next after this one closes.
                return true;
            }
            assert!(
                Instant::now() < deadline,
                "swtpm did not accept connections within {STARTUP_DEADLINE:?}"
            );
            std::thread::sleep(backoff);
            backoff = (backoff * 2).min(Duration::from_millis(50));
        }
    }

    pub fn open(&self, config: TpmConfig) -> TpmStore<SimTransport> {
        TpmStore::connect_simulator(("127.0.0.1", self.port), None, config).unwrap()
    }
}

impl Drop for Swtpm {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// A port `P` such that `P` and `P + 1` are both free right now.
fn free_port_pair() -> u16 {
    loop {
        let a = TcpListener::bind("127.0.0.1:0").unwrap();
        let port = a.local_addr().unwrap().port();
        if port < u16::MAX && TcpListener::bind(("127.0.0.1", port + 1)).is_ok() {
            return port;
        }
    }
}
