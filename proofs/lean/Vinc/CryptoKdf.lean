import Vinc.Labels
import Vinc.Transcript

/-!
# Key derivation of `vinc-crypto` (`kdf.rs`) and the call sites of the BLAKE3 `derive_key` primitive

The primitive is BLAKE3 in `derive_key` mode: a context string (the label) and a key material. The code makes four
kinds of call, and each is a function of its arguments into a `Call`, the pair the primitive receives:

* `expand prk label ctx` feeds the material `prk ++ ctx` under `label` (`kdf.rs`);
* `NodeId::from_public` feeds `[tag] ++ public key` under `NODE_ID`;
* the hybrid signature digest feeds the message under `HYBRID_SIGNATURE`;
* a labelled `Transcript` feeds its length-prefixed fields under its label (`Vinc.Transcript.encode`).

`extract salt ikm` is `keyed_hash` with the salt as the key, a different mode of the primitive (`Mode.keyed`), so it
never meets a `derive_key` call.

What is proved without any assumption: the call each site builds is injective in its arguments, calls of different
labels differ, the 31 labels of the workspace that pass through the primitive are pairwise distinct (so no two sites
share a domain), and the extendable output of `expand` has the length asked for and is a prefix of every longer
output. What needs the collision resistance of the primitive (`PrimInj`, a hypothesis on an abstract function): the output of `expand` is injective in the secret, also along a chain of derivations (the key schedule's
`packet key` from a traffic secret relies on it).
-/

namespace Vinc.CryptoKdf

/-- A byte string. -/
abbrev Bytes := List Nat

/-- The mode of the primitive. -/
inductive Mode where
  | derive
  | keyed
  deriving DecidableEq, Repr

/-- What the primitive receives: the mode, the label (context string) or key, and the material. -/
structure Call where
  mode : Mode
  label : Bytes
  material : Bytes
  deriving DecidableEq, Repr

/-- The bytes of an ASCII label. -/
def bytes (s : String) : Bytes := s.toList.map Char.toNat

/-- `labels::NODE_ID`. -/
def nodeIdLabel : String := "VINC 2026 v1 node id"
/-- `labels::HYBRID_SIGNATURE`. -/
def hybridLabel : String := "VINC 2026 v1 hybrid signature"

/-- `expand(prk, label, ctx)`: `derive_key(label)` over `prk || ctx`. -/
def expandCall (prk : Bytes) (label : Bytes) (ctx : Bytes) : Call := ⟨.derive, label, prk ++ ctx⟩

/-- `extract(salt, ikm)`: `keyed_hash(salt, ikm)`. -/
def extractCall (salt ikm : Bytes) : Call := ⟨.keyed, salt, ikm⟩

/-- The call of `NodeId::from_public` for a non-Ed25519 key. -/
def nodeIdCall (tag : Nat) (pk : Bytes) : Call := ⟨.derive, bytes nodeIdLabel, tag :: pk⟩

/-- The call of `hybrid_digest`. -/
def hybridCall (msg : Bytes) : Call := ⟨.derive, bytes hybridLabel, msg⟩

/-- The call of a labelled transcript over the encoding of its fields. -/
def transcriptCall (label : Bytes) (encoded : Bytes) : Call := ⟨.derive, label, encoded⟩

/-! ## Calls are injective in their arguments -/

/-- `expand` determines the secret, the label and the context (the secret has a fixed length of 32). -/
theorem expandCall_injective {prk prk' l l' c c' : Bytes} (h1 : prk.length = 32) (h2 : prk'.length = 32)
    (h : expandCall prk l c = expandCall prk' l' c') : prk = prk' ∧ l = l' ∧ c = c' := by
  simp only [expandCall, Call.mk.injEq, true_and] at h
  obtain ⟨hl, hm⟩ := h
  have := List.append_inj hm (by omega)
  exact ⟨this.1, hl, this.2⟩

/-- Without the fixed length the material alone would be ambiguous: the length hypothesis is needed. -/
theorem expandCall_needs_length : expandCall [1] [7] [2, 3] = expandCall [1, 2] [7] [3] := by decide

/-- `extract` determines the salt and the input keying material. -/
theorem extractCall_injective {s s' i i' : Bytes} (h : extractCall s i = extractCall s' i') : s = s' ∧ i = i' := by
  simp [extractCall] at h
  exact h

/-- The node id call determines the algorithm tag and the public key. -/
theorem nodeIdCall_injective {t t' : Nat} {pk pk' : Bytes} (h : nodeIdCall t pk = nodeIdCall t' pk') :
    t = t' ∧ pk = pk' := by
  simp [nodeIdCall] at h
  exact h

/-- The hybrid digest call determines the message. -/
theorem hybridCall_injective {m m' : Bytes} (h : hybridCall m = hybridCall m') : m = m' := by
  simp [hybridCall] at h
  exact h

/-- Calls of different labels (or different modes) differ, whatever the material. -/
theorem call_ne_of_label_ne {m m' : Mode} {l l' a a' : Bytes} (h : l ≠ l') : Call.mk m l a ≠ Call.mk m' l' a' := by
  intro e
  exact h (by injection e)

theorem call_ne_of_mode_ne {l l' a a' : Bytes} : Call.mk .derive l a ≠ Call.mk .keyed l' a' := by
  intro e
  injection e with h
  cases h

/-! ## The workspace labels -/

/-- The labels of `vinc-dtn` (`labels.rs`). -/
def dtnLabels : List String :=
  ["VINC 2026 v1 dtn chain", "VINC 2026 v1 dtn transcript", "VINC 2026 v1 dtn slice key",
   "VINC 2026 v1 dtn bundle id", "VINC 2026 v1 dtn head", "VINC 2026 v1 dtn custody ack"]

/-- The labels of `vinc-crypto` (`kdf::labels::ALL`). -/
def cryptoLabels : List String := [nodeIdLabel, hybridLabel]

/-- Every label that reaches the primitive from a public constant: security (23), crypto (2) and dtn (6). -/
def registry : List String := Labels.all ++ cryptoLabels ++ dtnLabels

theorem registry_length : registry.length = 31 := by decide

/-- No two labels of the registry are the same string. -/
theorem registry_nodup : registry.Nodup := by decide

/-- No two labels of the registry are the same byte string, so no two sites share a domain of the primitive. -/
theorem registry_bytes_nodup : (registry.map bytes).Nodup := by decide

theorem registry_prefix : ∀ l ∈ registry, Labels.prefix_.toList <+: l.toList := by decide

theorem registry_ascii : ∀ l ∈ registry, ∀ c ∈ l.toList, c.toNat < 128 := by decide

/-- A label of the registry is longer than the prefix, so the empty context is never used. -/
theorem registry_longer : ∀ l ∈ registry, Labels.prefix_.length < l.length := by decide

/-- The byte string of a label determines the label, within the registry. -/
theorem registry_bytes_inj : ∀ l ∈ registry, ∀ l' ∈ registry, bytes l = bytes l' → l = l' := by decide

/-- Two sites with different labels from the registry never build the same call. -/
theorem sites_separated {l l' : String} (hl : l ∈ registry) (hl' : l' ∈ registry) (hne : l ≠ l') (a a' : Bytes) :
    (⟨.derive, bytes l, a⟩ : Call) ≠ ⟨.derive, bytes l', a'⟩ := by
  apply call_ne_of_label_ne
  intro e
  exact hne (registry_bytes_inj l hl l' hl' e)

/-! ## The extendable output

`xof` is the byte at a position of the extendable output of a call (the BLAKE3 XOF, an abstract function here);
`expand` reads the first `n` bytes of it. -/

/-- The first `n` bytes of the output of a call. -/
def out (xof : Call → Nat → Nat) (c : Call) (n : Nat) : Bytes := (List.range n).map (xof c)

/-- `expand` fills exactly the length asked for. -/
theorem out_length (xof : Call → Nat → Nat) (c : Call) (n : Nat) : (out xof c n).length = n := by
  simp [out]

/-- A shorter output is a prefix of a longer one for the same call: two lengths of one derivation are related. -/
theorem out_prefix (xof : Call → Nat → Nat) (c : Call) {n m : Nat} (h : n ≤ m) : out xof c n <+: out xof c m := by
  have : m = n + (m - n) := by omega
  rw [this]
  simp only [out, List.range_add, List.map_append]
  exact List.prefix_append _ _

theorem out_zero (xof : Call → Nat → Nat) (c : Call) : out xof c 0 = [] := rfl

/-- The 32-byte output of a derivation. -/
def derive32 (xof : Call → Nat → Nat) (prk label ctx : Bytes) : Bytes := out xof (expandCall prk label ctx) 32

/-- The collision resistance of the primitive on its 32-byte output, as a hypothesis on the abstract function. -/
def PrimInj (xof : Call → Nat → Nat) : Prop := ∀ c c', out xof c 32 = out xof c' 32 → c = c'

/-- A derived secret determines the secret, the label and the context it was derived from. -/
theorem derive32_injective {xof : Call → Nat → Nat} (hp : PrimInj xof) {prk prk' l l' c c' : Bytes}
    (h1 : prk.length = 32) (h2 : prk'.length = 32) (h : derive32 xof prk l c = derive32 xof prk' l' c') :
    prk = prk' ∧ l = l' ∧ c = c' :=
  expandCall_injective h1 h2 (hp _ _ h)

theorem derive32_length (xof : Call → Nat → Nat) (prk l c : Bytes) : (derive32 xof prk l c).length = 32 :=
  out_length xof _ 32

/-- A chain of derivations from a secret, each step a label and a context: `packet key` from a traffic secret,
the chain of the handshake. -/
def chain (xof : Call → Nat → Nat) : List (Bytes × Bytes) → Bytes → Bytes
  | [], s => s
  | (l, c) :: rest, s => chain xof rest (derive32 xof s l c)

theorem chain_length (xof : Call → Nat → Nat) : ∀ (steps : List (Bytes × Bytes)) (s : Bytes),
    s.length = 32 → (chain xof steps s).length = 32
  | [], _, h => h
  | (l, c) :: rest, s, _ => chain_length xof rest _ (derive32_length xof s l c)

/-- A chain of derivations, with the same steps, is injective in the secret it starts from. -/
theorem chain_injective {xof : Call → Nat → Nat} (hp : PrimInj xof) :
    ∀ (steps : List (Bytes × Bytes)) {s s' : Bytes}, s.length = 32 → s'.length = 32 →
      chain xof steps s = chain xof steps s' → s = s'
  | [], _, _, _, _, h => h
  | (l, c) :: rest, s, s', h1, h2, h => by
    have := chain_injective hp rest (derive32_length xof s l c) (derive32_length xof s' l c) h
    exact (derive32_injective hp h1 h2 this).1

/-- The key schedule's packet key and IV (and the header key) are derived from a traffic secret with the empty
context under three different labels: the three calls differ, so one secret yields three unrelated outputs. -/
theorem packet_labels_separate (prk : Bytes) :
    expandCall prk (bytes "VINC 2026 v1 packet key") [] ≠ expandCall prk (bytes "VINC 2026 v1 packet iv") [] ∧
    expandCall prk (bytes "VINC 2026 v1 packet key") [] ≠ expandCall prk (bytes "VINC 2026 v1 header key") [] ∧
    expandCall prk (bytes "VINC 2026 v1 packet iv") [] ≠ expandCall prk (bytes "VINC 2026 v1 header key") [] := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro e; simp only [expandCall, Call.mk.injEq] at e; have := e.2.1; revert this; decide)

/-! ## The one label with two roles

`ticket` is the label of the transcript that hashes a ticket's context (the 16-byte ticket id and the 6-byte credit
record) and of the `expand` that derives the ticket key (a 32-byte secret and the 32-byte hash). Every other label has
one role. The two calls have materials of 24 and 64 bytes, so they never meet. -/

theorem ticket_roles_separate (tid cred prk ctx : Bytes) (ht : tid.length = 16) (hc : cred.length = 6)
    (hp : prk.length = 32) (hx : ctx.length = 32) :
    transcriptCall (bytes Labels.ticket) (Transcript.encode (Transcript.ticketCtxFields tid cred)) ≠
      expandCall prk (bytes Labels.ticket) ctx := by
  intro e
  have hm := congrArg (fun c => c.material.length) e
  simp only [transcriptCall, expandCall, Transcript.encode, Transcript.ticketCtxFields, Transcript.absorb,
    List.length_append, List.append_nil, Varint.length_encodeBytes, ht, hc, hp, hx] at hm
  rw [Varint.encodedLen_lt 16 (by omega), Varint.encodedLen_lt 6 (by omega)] at hm
  omega

end Vinc.CryptoKdf

#audit_axioms Vinc.CryptoKdf.expandCall_injective
#audit_axioms Vinc.CryptoKdf.registry_nodup
#audit_axioms Vinc.CryptoKdf.registry_bytes_nodup
#audit_axioms Vinc.CryptoKdf.sites_separated
#audit_axioms Vinc.CryptoKdf.out_prefix
#audit_axioms Vinc.CryptoKdf.chain_injective
#audit_axioms Vinc.CryptoKdf.packet_labels_separate
#audit_axioms Vinc.CryptoKdf.ticket_roles_separate
