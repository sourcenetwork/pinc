//! The scenario's `vinc_endpoints` field: how many endpoints VINC runs in the transport workload's `many` test, and
//! the check that it is asked for only where it applies.

use serde::{Deserialize, Serialize};

use crate::scenario::{Problem, Scenario, Stack, TransportTest, Workload};

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
    /// `per-core` changes nothing unless VINC runs the transport workload's `many` test: say so instead of letting a
    /// row read as per-core when it was not.
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
    }
}
