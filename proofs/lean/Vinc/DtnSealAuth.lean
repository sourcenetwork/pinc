import Vinc.DtnSeal

/-!
# Authenticity of a bundle head

The sender signs the encoded head with its identity key (`SignedHead::sign`); the signed message is the
label-separated hash of the body (`Endorsement`), the body is the concatenation of every field of the head, and
`verify` checks the signature under the head's own `source`. Three facts follow:

* `head_authentic`: a head that verifies under a source whose signing key has not leaked is a head that source
  signed, in every field (root, id, destination, times, erasure parameters, payload length and the whole
  encryption envelope). The unforgeability of the signature scheme is the hypothesis `hforge`
  (EUF-CMA, stated for the digest), the collision resistance of the hash is `HashInj`.
* `head_sig_not_ack`: a head signature never verifies as a custody acknowledgement, whatever its body.
* `root_binds_slices`: the root in the signed head commits to the sealed symbols, so two complete bundles that
  carry the same signed head hold the same symbols (the tree's own proofs are in `Vinc.Tree`; this is the
  composition with a collision resistant commitment).
-/

namespace Vinc.DtnSeal
open Vinc.Transcript

/-- A node id as the code compares it: the algorithm tag and the 32 bytes. -/
def HeadB.source (h : HeadB) : Nat × List Nat := (h.stag, h.src)

/-- A head that verifies under a source that did not leak its signing key was signed by that source, in every
field. `Presented n d` says a valid signature of `n` over digest `d` was shown; `hforge` is the unforgeability of
the signature scheme: such a signature exists only if the key leaked or the node signed that digest. -/
theorem head_authentic {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (honest : HeadB → Prop)
    (hwf : ∀ h, honest h → h.WF) (leaked : Nat × List Nat → Prop) (Presented : Nat × List Nat → β → Prop)
    (hforge : ∀ n d, Presented n d → leaked n ∨ ∃ h', honest h' ∧ h'.source = n ∧ headDigest H h' = d)
    (h : HeadB) (hw : h.WF) (hv : Presented h.source (headDigest H h)) (hn : ¬ leaked h.source) : honest h := by
  rcases hforge _ _ hv with hl | ⟨h', hh', hs, hd⟩
  · exact absurd hl hn
  · have := headDigest_inj hH h' h (hwf h' hh') hw hd
    rw [← this]
    exact hh'

/-- A head signature never verifies as a custody acknowledgement signature. -/
theorem head_sig_not_ack {β : Type} {H : List Nat → List Nat → β} (hH : HashInj H) (h : HeadB) (body : List Nat) :
    headDigest H h ≠ ackDigest H body := headDigest_ne_ack hH h body

/-- A collision resistant commitment to the sealed symbols (the tree root) fixes every symbol. -/
theorem root_binds_slices {α ρ : Type} (commit : List α → ρ) (hc : ∀ x y, commit x = commit y → x = y)
    (x y : List α) (h : commit x = commit y) (i : Nat) : x[i]? = y[i]? := by
  rw [hc x y h]

end Vinc.DtnSeal

#audit_axioms Vinc.DtnSeal.head_authentic
#audit_axioms Vinc.DtnSeal.head_sig_not_ack
#audit_axioms Vinc.DtnSeal.root_binds_slices
