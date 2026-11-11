//! The comparison binary for iroh: the shared harness in `compare/mod.rs`, the adapter in `compare/iroh.rs`.
#![allow(missing_docs)]

mod compare;

#[global_allocator]
static ALLOC: compare::Counting = compare::Counting;

fn main() {
    compare::main::<compare::iroh::Iroh>();
}
