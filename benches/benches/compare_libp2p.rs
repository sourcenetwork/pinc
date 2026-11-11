//! The comparison binary for rust-libp2p: the shared harness in `compare/mod.rs`, the adapter in `compare/libp2p.rs`.
#![allow(missing_docs)]

mod compare;

#[global_allocator]
static ALLOC: compare::Counting = compare::Counting;

fn main() {
    compare::main::<compare::libp2p::Libp2p>();
}
