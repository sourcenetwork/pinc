//! The comparison binary for VINC: the shared harness in `compare/mod.rs`, the adapter in `compare/vinc.rs`.
#![allow(missing_docs)]

mod compare;

#[global_allocator]
static ALLOC: compare::Counting = compare::Counting;

fn main() {
    compare::main::<compare::vinc::Vinc1>();
}
