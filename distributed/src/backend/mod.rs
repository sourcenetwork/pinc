//! Where nodes run. Backend (a), [`containers`]: containers and network namespaces on this machine, wired and shaped
//! by the plan. Every backend starts the same binary in node mode in every node and measures it from the kernel.

pub mod containers;
pub mod fleet;
pub mod proc;

pub use proc::Proc;
