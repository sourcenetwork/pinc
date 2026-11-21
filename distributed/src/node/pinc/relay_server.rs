//! A node with the role `relay-server` runs `pinc_relay`, the deployable relay server, in place of a PINC node: the binary
//! at `PINC_RELAY_BIN`, or at [`RELAY_BIN`] where the container backend mounts it. It listens on the node's UDP port
//! (UDP and TCP carriers on one port) with the identity the other nodes derive from its name, answers a join at once
//! (a relay takes no part in topics), and reports the counters of its `/metrics` endpoint.

use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::process::{Child, Command, Stdio};
use std::time::Duration;

use serde_json::{Map, Value};

use super::agent::UDP_PORT;
use super::core::node_id;
use crate::node::app::{emit, for_each_request};
use crate::node::data::identity_seed;
use crate::node::proto::{Cmd, Init, Ready, Reply};

/// Where the container backend mounts the binary named by `PINC_RELAY_BIN`.
pub const RELAY_BIN: &str = "/opt/vd/pinc-relay";
const METRICS_PORT: u16 = 9100;

struct Server(Child);

impl Drop for Server {
    fn drop(&mut self) {
        let _ = Command::new("kill").args(["-TERM", &self.0.id().to_string()]).status();
        let _ = self.0.wait();
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

/// Run the relay server for `init` until the orchestrator stops it.
///
/// # Errors
/// The binary did not start or did not say it is up.
pub fn run(init: &Init) -> Result<(), String> {
    let me = init
        .me()
        .ok_or_else(|| format!("{} is not a node of the scenario", init.name))?;
    let dir = std::env::temp_dir().join(format!("pinc-relay-{}", init.name));
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let identity = dir.join("identity");
    std::fs::write(&identity, hex(&identity_seed(&init.name, init.identity_salt, 32)))
        .map_err(|e| format!("{}: {e}", identity.display()))?;
    let metrics = SocketAddr::from(([127, 0, 0, 1], me.port(METRICS_PORT)));
    let config = dir.join("relay.toml");
    std::fs::write(
        &config,
        format!(
            "identity = \"identity\"\nlisten = \"0.0.0.0:{}\"\nmetrics = \"{metrics}\"\nstore = \"store\"\n",
            me.port(UDP_PORT),
        ),
    )
    .map_err(|e| format!("{}: {e}", config.display()))?;
    let bin = std::env::var_os("PINC_RELAY_BIN").unwrap_or_else(|| RELAY_BIN.into());
    let mut child = Command::new(&bin)
        .current_dir(&dir)
        .arg(&config)
        .stdout(Stdio::piped())
        .stdin(Stdio::null())
        .spawn()
        .map_err(|e| format!("pinc_relay ({}) did not start: {e}", bin.to_string_lossy()))?;
    let stdout = child.stdout.take().ok_or("pinc_relay has no output")?;
    let server = Server(child);
    let mut line = String::new();
    BufReader::new(stdout)
        .read_line(&mut line)
        .map_err(|e| format!("pinc_relay said nothing: {e}"))?;
    let want = pinc::node_to_string(&node_id(&init.name, init.identity_salt)?);
    // "relay and hub <id> on <address>", or "relay <id> on <address>" with the hub off.
    let words: Vec<&str> = line.split_whitespace().collect();
    let id = words
        .iter()
        .position(|w| *w == "on")
        .and_then(|on| words.get(on.checked_sub(1)?));
    if id != Some(&want.as_str()) {
        return Err(format!("pinc_relay did not come up as {want}: {line}"));
    }
    let ready = Ready {
        stack: "pinc".into(),
        id: hex(&node_id(&init.name, init.identity_salt)?.bytes),
        config: format!("pinc_relay ({}): {}", bin.to_string_lossy(), line.trim()),
    };
    println!("READY {}", serde_json::to_string(&ready).map_err(|e| e.to_string())?);
    for_each_request(|req| {
        match req.cmd {
            Cmd::Join { .. } => emit(&Reply::ok(req.id, Value::Null)),
            Cmd::Report => emit(&match counters(metrics) {
                Ok(v) => Reply::ok(req.id, json_report(&v)),
                Err(e) => Reply::fail(req.id, format!("the relay's metrics could not be read: {e}")),
            }),
            Cmd::Stop => {
                emit(&Reply::ok(req.id, Value::Null));
                return false;
            }
            _ => emit(&Reply::fail(req.id, "a relay server only relays")),
        }
        true
    });
    drop(server);
    Ok(())
}

/// The relay's counters: each sample of its `/metrics`, by name with labels.
fn counters(at: SocketAddr) -> std::io::Result<Map<String, Value>> {
    let mut s = TcpStream::connect_timeout(&at, Duration::from_secs(2))?;
    s.set_read_timeout(Some(Duration::from_secs(2)))?;
    s.write_all(b"GET /metrics HTTP/1.1\r\nHost: relay\r\n\r\n")?;
    let mut text = String::new();
    s.read_to_string(&mut text)?;
    let body = text.split_once("\r\n\r\n").map_or("", |(_, b)| b);
    Ok(body
        .lines()
        .filter(|l| !l.starts_with('#'))
        .filter_map(|l| {
            let (name, v) = l.rsplit_once(' ')?;
            Some((
                name.trim_start_matches("pinc_relay_").to_owned(),
                Value::from(v.parse::<u64>().ok()?),
            ))
        })
        .collect())
}

fn json_report(c: &Map<String, Value>) -> Value {
    serde_json::json!({ "relay_server": c })
}
