# Proofs

`proofs/tla/` and `proofs/lean/` hold TLA+ specifications, checked with TLC, and Lean 4 proofs of PINC's state machines
and pure functions. Both are kept identical to the Rust code by validating traces recorded from the real code against
each. Proven in full (every non-trivial file has a TLA+ model checked by TLC over stated bounds or a Lean theorem, and a
trace check or model-based test of the code): `pinc-security`, `pinc-wire`, `pinc-dag`, `pinc-table`, `pinc-portmap`,
`pinc-reconcile` and `pinc-dtn`. `pinc-crypto`, `pinc-keystore`, `pinc-membership`, `pinc-connect`, `pinc-transport`,
`pinc-values` and `pinc-broadcast` are proven except for the items under [Being closed](proofs/closing.md). `pinc-core`,
`pinc-node` and the facade `pinc` are proven except for those items and the checks that fail, listed in
[#748](https://github.com/sourcenetwork/pinc/issues/748). The models of the DAG-CBOR codec and of blocks, CAR
files and CIDs run only in the deep profile. A model that is known to state an older rule than the code is listed in
[#601](https://github.com/sourcenetwork/pinc/issues/601) until it is corrected: a green check of such a model says
nothing about the rule that changed.
Run everything with `just proofs` (the quick profile) or `just proofs-deep` (the full bounds).

## Parts

- [How it is checked](proofs/checking.md): the Lean build, TLC, the link between the two languages, the trace
  validation and the model-based tests, and the tools they need.
- [Properties](proofs/properties.md): one row per property, with the Rust item, the TLA+ model and its bounds, the
  Lean theorem, the assumptions and the trace validation.
- [The quick profile](proofs/quick.md): the smaller bounds `just proofs` checks, model by model, and what each
  no longer reaches; `just proofs-deep` checks the full bounds.
- [Assumptions](proofs/assumptions.md): what is taken on trust.
- [Being closed](proofs/closing.md): what is still open.
