//! The options of the transport workload's `many` test: `vinc_endpoints` (how many endpoints VINC runs, and the check
//! that it is asked for only where it applies) and `reading` (how the test reads memory).

use serde::{Deserialize, Serialize};

use crate::scenario::{Problem, Scenario, Stack, TransportTest, Workload};

/// How the `many` test reads memory (the comparison harness's `--reading`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Reading {
    /// VINC's client endpoints left undriven, 500 ms before the reading: the reading the row has always had.
    #[default]
    Undriven,
    /// Client endpoints driven while the connections are open, 1.5 s before the reading.
    Driven,
}

impl Reading {
    /// The name in files and on the node program's command line.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Driven => "driven",
            Self::Undriven => "undriven",
        }
    }

    #[allow(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's skip_serializing_if passes a reference"
    )]
    pub(crate) fn is_default(&self) -> bool {
        *self == Self::Undriven
    }
}

/// How many endpoints a VINC node runs in the transport workload's `many` test.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum VincEndpoints {
    /// One endpoint on one thread, as in every other test.
    #[default]
    One,
    /// One endpoint on every CPU of the node, all with one identity on one port; the client spreads its connections
    /// over one endpoint per CPU.
    PerCore,
}

impl VincEndpoints {
    /// The name in files and in `run.json`.
    pub const fn name(self) -> &'static str {
        match self {
            Self::One => "one",
            Self::PerCore => "per-core",
        }
    }

    #[allow(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's skip_serializing_if passes a reference"
    )]
    pub(crate) fn is_default(&self) -> bool {
        *self == Self::One
    }
}

impl Scenario {
    /// `per-core` changes nothing unless VINC runs the transport workload's `many` test, and it must not stand over a
    /// test that runs on one endpoint: say so instead of letting a row read as per-core when it was not.
    pub(crate) fn check_vinc_endpoints(&self, out: &mut Vec<Problem>) {
        if self.vinc_endpoints == VincEndpoints::One {
            return;
        }
        let many = matches!(&self.workload, Workload::Transport(t) if t.tests.iter().any(|t| matches!(t, TransportTest::Many { .. })));
        if !self.stacks.contains(&Stack::Vinc) || !many {
            out.push(Problem::new(
                "vinc_endpoints",
                "per-core applies to the many test of the transport workload run by the vinc stack: add both or use one",
            ));
        }
        if let Workload::Transport(t) = &self.workload {
            for other in t.tests.iter().filter(|t| !matches!(t, TransportTest::Many { .. })) {
                out.push(Problem::new(
                    "vinc_endpoints",
                    format!(
                        "per-core applies to the many tests only, so the {} test cannot be in this scenario",
                        other.id()
                    ),
                ));
            }
        }
    }
}
