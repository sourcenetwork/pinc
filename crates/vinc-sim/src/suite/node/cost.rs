//! The CPU cost of a suite node: the constants of the adapter and the simulator's cost model.
//!
//! A node reports its work through [`vinc_sim::Node::take_work`](crate::Node::take_work): the crypto time of the
//! instrumented provider on its device class, a fixed charge per handler call, and the transmit I/O of the
//! reference harness (`io_call` per transmit call plus `io_seg` per segment). Only the node knows the segment count of
//! a transmit, so the I/O cost travels in the work report and the cost model only applies the node's speed factor.
//!
//! Invariants: the model is a pure function of its arguments; the speed factor is applied once, here, never by the
//! node.

use crate::config::{Call, CostModel, Cpu};
use crate::{Time, Work};

/// The fixed cost of one handler call (a datagram, a timeout or a command) in nanoseconds. A calibration
/// placeholder for the endpoint's own bookkeeping, which the instrumented crypto does not meter; it has not been
/// measured against a reference build.
pub const HANDLER_CALL_NS: u64 = 2_000;

/// The cost model of the suite: the node's work report scaled by its speed factor.
#[derive(Clone, Copy, Debug, Default)]
pub struct SuiteCost;

impl SuiteCost {
    /// The CPU parameters of a node `factor_milli` thousandths as slow as its device class (1000 is the class
    /// speed). The fixed per-call and per-KiB costs are zero: the node reports everything in its work.
    pub const fn cpu(factor_milli: u32) -> Cpu {
        Cpu {
            factor_milli,
            per_call: 0,
            per_kib: 0,
        }
    }
}

impl CostModel for SuiteCost {
    fn cost(&self, cpu: &Cpu, _call: Call, _bytes: usize, work: Work) -> Time {
        (u128::from(work.ns) * u128::from(cpu.factor_milli) / 1000) as Time
    }
}
