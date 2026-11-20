# Proofs

`proofs/tla/` and `proofs/lean/` hold TLA+ specifications, checked with TLC, and Lean 4 proofs of PINC's state machines
and pure functions. Both are kept identical to the Rust code by validating traces recorded from the real code against
each. Proven in full: `pinc-crypto`, `pinc-keystore`, `pinc-values`, `pinc-dtn` (custody, the charged
store, forwarding, erasure coding, layout, codecs, reception, one-shot encryption and the multi-node scenarios) and the
relay side of `pinc-connect` with its codecs, carrier link, client rules and the protected carrier's framing, records and
keys. Of `pinc-wire` the varints are proven, and of `pinc-dag` the verified-range sets, the tree layout, the builder and
the range verifier (value roots and range proofs); the DAG-CBOR codec, the reader and writer, CIDs, blocks and CAR
files are tested, not modelled. `pinc-security` (handshake, key schedule, record keys, key roll, credit
record, amplification budget and padding, ticket stores), `pinc-membership`, `pinc-broadcast` and `pinc-reconcile` are proven except for the
items under [Being closed](proofs/closing.md). A model that is known to state an older rule than the code is listed in
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
