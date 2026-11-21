//! The transport workload of a scenario: its tests and the pairs that run them, with the checks of their counts and
//! sizes. Split from `scenario.rs`, which re-exports everything here.

use serde::{Deserialize, Serialize};

use crate::pinc_endpoints::Reading;
use crate::scenario::Pair;
use crate::scenario::Problem;

/// One transport test: the scenarios of the comparison benches.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "test", rename_all = "kebab-case")]
pub enum TransportTest {
    /// Time to the first byte of `count` new connections, each from a fresh endpoint.
    Setup {
        /// Connections.
        count: u32,
    },
    /// The same over the stack's resumption with early data.
    Resume {
        /// Connections.
        count: u32,
    },
    /// Request and response round trips of `size` bytes on one stream.
    Latency {
        /// Bytes each way.
        size: u32,
        /// Round trips measured.
        round_trips: u32,
    },
    /// `requests` requests of `size` bytes each way, `concurrency` in flight on one connection, each on a stream of its
    /// own, as a request-response protocol sends them.
    Requests {
        /// Bytes each way.
        size: u32,
        /// Requests measured.
        requests: u32,
        /// Requests in flight at once.
        concurrency: u32,
    },
    /// Upload `bytes` over `streams` concurrent streams of one connection.
    Throughput {
        /// Bytes in all.
        bytes: u64,
        /// Concurrent streams.
        streams: u32,
        /// Sample the congestion window every `trace_ms` milliseconds into the row's `cwnd_trace` (0, the default: no
        /// trace). PINC and iroh expose the window; libp2p does not, so its samples are `null`.
        #[serde(default)]
        trace_ms: u32,
    },
    /// `connections` clients at once, each moving `bytes_each`.
    Many {
        /// Clients.
        connections: u32,
        /// Bytes each.
        bytes_each: u64,
        /// How memory is read (`undriven`, the reading the row has always had, or `driven`).
        #[serde(default, skip_serializing_if = "Reading::is_default")]
        reading: Reading,
    },
}

impl TransportTest {
    /// The client's arguments for the comparison harness.
    pub fn client_args(&self) -> Vec<String> {
        match *self {
            Self::Setup { count } => vec!["setup".into(), count.to_string()],
            Self::Resume { count } => vec!["resume".into(), count.to_string()],
            Self::Latency { size, round_trips } => vec!["latency".into(), size.to_string(), round_trips.to_string()],
            Self::Requests {
                size,
                requests,
                concurrency,
            } => vec![
                "requests".into(),
                size.to_string(),
                requests.to_string(),
                concurrency.to_string(),
            ],
            Self::Throughput {
                bytes,
                streams,
                trace_ms,
            } => vec![
                "throughput".into(),
                bytes.to_string(),
                streams.to_string(),
                trace_ms.to_string(),
            ],
            Self::Many {
                connections,
                bytes_each,
                ..
            } => vec!["many".into(), connections.to_string(), bytes_each.to_string()],
        }
    }

    /// The name of the result line the client prints, which is also the test's id in results.
    pub fn id(&self) -> String {
        match *self {
            Self::Setup { .. } => "setup".into(),
            Self::Resume { .. } => "resume".into(),
            Self::Latency { size, .. } => format!("latency_{size}b"),
            Self::Requests { size, concurrency, .. } => format!("requests_{size}b_c{concurrency}"),
            Self::Throughput { streams, .. } => format!("throughput_{streams}s"),
            Self::Many {
                reading: Reading::Driven,
                ..
            } => "many_driven".into(),
            Self::Many { .. } => "many".into(),
        }
    }

    /// The name of the result line the client prints: the test's id, except that both readings of `many` print `many`.
    pub fn scenario(&self) -> String {
        match self {
            Self::Many { .. } => "many".into(),
            _ => self.id(),
        }
    }

    pub(crate) fn check(&self, path: &str, out: &mut Vec<Problem>) {
        let ok = match *self {
            Self::Setup { count } | Self::Resume { count } => (1..=100_000).contains(&count),
            Self::Latency { size, round_trips } => {
                (1..=1 << 20).contains(&size) && (1..=10_000_000).contains(&round_trips)
            }
            Self::Requests {
                size,
                requests,
                concurrency,
            } => {
                (1..=1 << 20).contains(&size)
                    && (1..=10_000_000).contains(&requests)
                    && (1..=1024).contains(&concurrency)
            }
            Self::Throughput {
                bytes,
                streams,
                trace_ms,
            } => (1..=1 << 40).contains(&bytes) && (1..=256).contains(&streams) && trace_ms <= 60_000,
            Self::Many {
                connections,
                bytes_each,
                ..
            } => (1..=10_000).contains(&connections) && bytes_each <= 1 << 30,
        };
        if !ok {
            out.push(Problem::new(path, "a count or size of this test is out of range"));
        }
    }
}

/// The transport workload: the comparison benches' scenarios between pairs of nodes.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Transport {
    /// The pairs measured, one after the other.
    pub pairs: Vec<Pair>,
    /// The tests, in order.
    pub tests: Vec<TransportTest>,
    /// The longest one client run may take before it is stopped and reported as timed out.
    #[serde(default = "timeout_default")]
    pub timeout_s: u64,
}

fn timeout_default() -> u64 {
    300
}
