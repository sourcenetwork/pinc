# Proofs: assumptions

The only things taken on trust are the dependencies, not this repository's code:
- The cryptographic primitives behave as specified: BLAKE3 is collision resistant and a PRF (the transcript hash, the
  key derivation and the binder tags), X25519 and ML-KEM-768 give shared secrets only the key holders know, the AEADs
  (ChaCha20-Poly1305, AES-128-GCM) are ideal authenticated encryption, the signature algorithms are unforgeable. These
  appear as the free term algebra and the Dolev-Yao `Known` predicate in the handshake model, as `HashInj` and
  `IdealAead` hypotheses in Lean, and as `Tree.CollisionFree` for the verifier. The two key agreements are not both
  needed for the secrecy of a full handshake: it is also checked and proved with either one broken (`Handshake_xbroken`,
  `Handshake_kbroken`, `HandshakeHybrid.secrecy_xbroken`, `secrecy_kbroken`; with both broken it fails,
  `Handshake_bothbroken`), as it is for the one-shot encryption (`DtnSeal`). Agreement and authentication of a full
  handshake need neither: they rest on the signatures (those of a resumption rest on the ticket's pre-shared key, so
  on one of the two). A broken key agreement is symbolic here (the attacker learns every shared
  secret of that primitive, the other stays perfect); nothing is claimed about a partial computational break or about
  the combiner `extract(ck0, ss_K || ss_X)` as a computational object. A resumed session and the key roll run X25519
  only: with it broken, a resumed session is as secret as its ticket's pre-shared key (`ResumedAsPsk`,
  `HandshakeHybrid.resumed_init_as_psk`) and a roll gives no post-compromise security (`KeyRoll_xbroken`,
  `KeyRoll.xbroken_no_post_compromise`).
- The packet key is an injective function of the traffic secret (a property of the key derivation `expand`; a hypothesis
  of `Record.no_nonce_reuse` and `KeyRoll`), and X25519 gives the same shared value to both sides.
- Rust `core` and `std` semantics, each stated as a hypothesis of the theorems that use it, never as an axiom:
  - the integer operations (`checked_*`, `saturating_*`, shifts, `/`, `%`, `div_ceil`, `is_multiple_of`,
    `try_from`, `is_power_of_two`) mean what their documentation says; `Machine.lean` defines them that way;
  - `u64::leading_zeros(x)` for `x != 0` returns the `z` with `2^(63 - z) <= x < 2^(64 - z)` (`Layout.IsLz`, the
    hypothesis `hlz` of `Layout.depth_eq` and `Machine.depthM_eq`);
  - `u64::ilog2(x)` for `x != 0` returns the `z` with `2^z <= x < 2^(z + 1)`, and `usize::trailing_zeros(2^k)` is `k`
    (`Machine.IsIlog2`, the hypotheses `hil` and `htz` of `Machine.leftGroupsM_eq` and `forGroupBytesM_iff`);
  - slice `get`, `split_at_checked`, `copy_from_slice` and `partition_point`, and the
    `#![forbid(unsafe_code)]` guarantee.
- BLAKE3 as the tree code uses it, beyond collision resistance: hashing a group in several `update` calls gives the
  hash of the concatenation, and `set_input_offset`, `finalize`, `finalize_non_root` and the two `merge_subtrees`
  functions compute the abstract `leaf` and `parent` values of `Tree.Hash`, with the group offset and root flag the
  model passes. The proofs do not check this; the traces do, on real data.
- The libraries below `pinc-crypto` and `pinc-keystore` answer as specified, each an abstract function in the model with
  the code's use of its answer proved: the signature crates (does a key parse, does a signature parse, is `s` low, does
  the equation hold: `Prim`), the `ChaCha20` stream and the AES block (`StreamInj` where a theorem needs the output to
  determine the key), ChaCha20-Poly1305 as an ideal AEAD (`Ideal`, `AeadSpec`), `tpm2-protocol` (its verdict on a body
  and on the public area of a blob), the operating system's random source, and the TPM (a software TPM in the traces).
  The transport of the TPM client pairs each command with its own response; the response carries no command code, so the
  client cannot check it.
- The prekey store (`SoftPrekeys`) numbers its keys by a 64-bit generation that wraps; it is taken that fewer than
  `2^64` rotations happen (one a second takes 5.8e11 years), so the generation of a key never names the current one
  again. `SoftPrekeys_wrap` is a witness of this bound.

