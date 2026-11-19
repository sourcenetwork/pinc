//! The comparison binary for PINC: the shared harness in `compare/mod.rs`, the adapter in `compare/pinc.rs`.
#![allow(missing_docs)]

mod compare;

#[global_allocator]
static ALLOC: compare::Counting = compare::Counting;

fn main() {
    compare::main::<compare::pinc::Pinc1>();
}
