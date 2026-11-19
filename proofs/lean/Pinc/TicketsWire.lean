import Pinc.Tickets

/-!
# The exported ticket state

The byte format of `ClientTickets::export` and `ClientTickets::restore` in `pinc-security/src/tickets.rs`, over lists
of bytes (`Nat`s below 256):

    version(1) count(1)   then per ticket
    alg(1) node(32) alpn_len(1) alpn tid(16) psk(32) aead(1) expiry(8, big endian) credit(6)

`encode` is what `export` writes and `decode` is what `restore` checks before it stores anything (`read_export_header`,
`read_export_entry`, then no trailing byte). The version is 1, the algorithm tag is 1 to 4, the ALPN is 1 to 32 bytes,
the AEAD tag is 1 or 2 and the count is a byte. The round trip (`decode_encode`) and the strictness theorems (a
trailing byte, a bad version, a count that is not the number of entries, an unknown algorithm or AEAD and a bad ALPN
length are all rejected) are proved here.
-/

namespace Pinc.Tickets

/-- Every element is a byte. -/
def Bytes (l : List Nat) : Prop := ∀ b ∈ l, b < 256

/-- The big-endian bytes of a `u64`. -/
def be64 (n : Nat) : List Nat :=
  [n / 72057594037927936 % 256, n / 281474976710656 % 256, n / 1099511627776 % 256, n / 4294967296 % 256,
   n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256]

/-- The `u64` of 8 big-endian bytes (`u64::from_be_bytes`). -/
def fromBe64 (l : List Nat) : Nat := l.foldl (fun a b => a * 256 + b) 0

theorem be64_length (n : Nat) : (be64 n).length = 8 := rfl

theorem be64_bytes (n : Nat) : Bytes (be64 n) := by
  intro b hb
  simp only [be64, List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

theorem fromBe64_be64 {n : Nat} (h : n < 2 ^ 64) : fromBe64 (be64 n) = n := by
  simp only [fromBe64, be64, List.foldl]
  have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  omega

theorem be64_fromBe64 {l : List Nat} (hl : l.length = 8) (hb : Bytes l) : be64 (fromBe64 l) = l := by
  match l, hl with
  | [a, b, c, d, e, f, g, h], _ =>
    have ha := hb a (by simp); have hb' := hb b (by simp); have hc := hb c (by simp); have hd := hb d (by simp)
    have he := hb e (by simp); have hf := hb f (by simp); have hg := hb g (by simp); have hh := hb h (by simp)
    simp only [fromBe64, be64, List.foldl, List.cons.injEq, and_true]
    omega

/-- A ticket the export format can carry: the sizes and tags the reader accepts. -/
def Tk.Valid (t : Tk) : Prop :=
  (1 ≤ t.peer.alg ∧ t.peer.alg ≤ 4) ∧ t.peer.node.length = 32 ∧ Bytes t.peer.node ∧
  (1 ≤ t.alpn.length ∧ t.alpn.length ≤ 32) ∧ Bytes t.alpn ∧
  t.tid.length = 16 ∧ Bytes t.tid ∧ t.psk.length = 32 ∧ Bytes t.psk ∧
  (t.aead = 1 ∨ t.aead = 2) ∧ t.expiry < 2 ^ 64 ∧ t.credit.length = 6 ∧ Bytes t.credit

/-- One exported entry. -/
def encodeTk (t : Tk) : List Nat :=
  t.peer.alg :: (t.peer.node ++ (t.alpn.length :: (t.alpn ++ (t.tid ++ (t.psk ++ (t.aead :: (be64 t.expiry ++ t.credit)))))))

/-- The entries of a state, in order. -/
def encodeAll (ts : List Tk) : List Nat := ts.flatMap encodeTk

/-- The state `export` writes for the tickets `ts` (the count is a byte: the code fails above 255). -/
def encode (ts : List Tk) : List Nat := 1 :: ts.length :: encodeAll ts

/-- `n` bytes off the front (`Reader::read_bytes`, `read_array`). -/
def take? (n : Nat) (l : List Nat) : Option (List Nat × List Nat) :=
  if n ≤ l.length then some (l.take n, l.drop n) else none

/-- A byte off the front (`Reader::read_u8`). -/
def u8? : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: r => some (b, r)

/-- `read_export_entry`. -/
def decodeEntry (l : List Nat) : Option (Tk × List Nat) :=
  match u8? l with
  | none => none
  | some (alg, l) =>
    if ¬ (1 ≤ alg ∧ alg ≤ 4) then none else
    match take? 32 l with
    | none => none
    | some (node, l) =>
    match u8? l with
    | none => none
    | some (alen, l) =>
    match take? alen l with
    | none => none
    | some (alpn, l) =>
    if ¬ (1 ≤ alen ∧ alen ≤ 32) then none else
    match take? 16 l with
    | none => none
    | some (tid, l) =>
    match take? 32 l with
    | none => none
    | some (psk, l) =>
    match u8? l with
    | none => none
    | some (aead, l) =>
    if ¬ (aead = 1 ∨ aead = 2) then none else
    match take? 8 l with
    | none => none
    | some (exp, l) =>
    match take? 6 l with
    | none => none
    | some (credit, l) => some (⟨⟨alg, node⟩, alpn, tid, psk, aead, fromBe64 exp, credit⟩, l)

/-- `count` entries. -/
def decodeN : Nat → List Nat → Option (List Tk × List Nat)
  | 0, l => some ([], l)
  | n + 1, l =>
    match decodeEntry l with
    | none => none
    | some (t, l) =>
      match decodeN n l with
      | none => none
      | some (ts, l) => some (t :: ts, l)

/-- `restore`'s check of the whole input: version, count, the entries, no trailing byte. -/
def decode (l : List Nat) : Option (List Tk) :=
  match u8? l with
  | none => none
  | some (v, l) =>
    if v ≠ 1 then none else
    match u8? l with
    | none => none
    | some (c, l) =>
      match decodeN c l with
      | none => none
      | some (ts, l) => if l = [] then some ts else none

theorem take?_append {l₁ : List Nat} (l₂ : List Nat) {n : Nat} (h : l₁.length = n) :
    take? n (l₁ ++ l₂) = some (l₁, l₂) := by
  subst h
  simp [take?]

theorem decodeEntry_encode {t : Tk} (hv : t.Valid) (rest : List Nat) :
    decodeEntry (encodeTk t ++ rest) = some (t, rest) := by
  obtain ⟨⟨ha1, ha2⟩, hn, _, ⟨hl1, hl2⟩, _, htid, _, hpsk, _, hae, hexp, hcr, _⟩ := hv
  obtain ⟨⟨alg, node⟩, alpn, tid, psk, aead, expiry, credit⟩ := t
  simp only at *
  simp only [encodeTk, List.cons_append, List.append_assoc, decodeEntry, u8?]
  have hnot : ¬ ¬ (1 ≤ alg ∧ alg ≤ 4) := by omega
  simp only [hnot, ite_false]
  rw [take?_append _ hn]
  simp only [u8?]
  rw [take?_append _ rfl]
  have hnot2 : ¬ ¬ (1 ≤ alpn.length ∧ alpn.length ≤ 32) := by omega
  simp only [hnot2, ite_false]
  rw [take?_append _ htid]
  dsimp only
  rw [take?_append _ hpsk]
  simp only [u8?]
  have hnot3 : ¬ ¬ (aead = 1 ∨ aead = 2) := by omega
  simp only [hnot3, ite_false]
  rw [take?_append _ (be64_length expiry)]
  dsimp only
  rw [take?_append _ hcr]
  simp [fromBe64_be64 hexp]

theorem decodeN_encode : ∀ (ts : List Tk), (∀ t ∈ ts, t.Valid) → ∀ rest : List Nat,
    decodeN ts.length (encodeAll ts ++ rest) = some (ts, rest) := by
  intro ts
  induction ts with
  | nil => intro _ rest; simp [decodeN, encodeAll]
  | cons t ts ih =>
    intro hv rest
    have h1 : encodeAll (t :: ts) ++ rest = encodeTk t ++ (encodeAll ts ++ rest) := by
      simp [encodeAll]
    simp only [List.length_cons, decodeN, h1]
    rw [decodeEntry_encode (hv t (by simp))]
    simp only
    rw [ih (fun u hu => hv u (by simp [hu]))]

/-- `Tickets.decode_encode`: a state of valid tickets reads back as the same tickets, in the same order. -/
theorem decode_encode {ts : List Tk} (hlen : ts.length < 256) (hv : ∀ t ∈ ts, t.Valid) :
    decode (encode ts) = some ts := by
  have := decodeN_encode ts hv []
  simp only [List.append_nil] at this
  simp [decode, encode, u8?, this]

/-- `Tickets.decode_trailing`: a byte after the last entry is rejected. -/
theorem decode_trailing {ts : List Tk} (hlen : ts.length < 256) (hv : ∀ t ∈ ts, t.Valid) {extra : List Nat}
    (hx : extra ≠ []) : decode (encode ts ++ extra) = none := by
  have := decodeN_encode ts hv extra
  simp [decode, encode, u8?, this, hx]

/-- `Tickets.decode_bad_version`: any version other than 1 is rejected. -/
theorem decode_bad_version {v : Nat} (hv : v ≠ 1) (rest : List Nat) : decode (v :: rest) = none := by
  simp [decode, u8?, hv]

theorem decodeEntry_nil : decodeEntry [] = none := rfl

theorem decodeN_nil_succ (m : Nat) : decodeN (m + 1) [] = none := by
  simp [decodeN, decodeEntry_nil]

theorem decodeN_append : ∀ (ts : List Tk), (∀ t ∈ ts, t.Valid) → ∀ (m : Nat) (rest : List Nat),
    decodeN (ts.length + m) (encodeAll ts ++ rest) = (decodeN m rest).map (fun p => (ts ++ p.1, p.2)) := by
  intro ts
  induction ts with
  | nil => intro _ m rest; cases h : decodeN m rest <;> simp [encodeAll, h]
  | cons t ts ih =>
    intro hv m rest
    have h1 : encodeAll (t :: ts) ++ rest = encodeTk t ++ (encodeAll ts ++ rest) := by simp [encodeAll]
    have h2 : (t :: ts).length + m = (ts.length + m) + 1 := by simp; omega
    rw [h2]
    simp only [decodeN, h1]
    rw [decodeEntry_encode (hv t (by simp))]
    dsimp only
    rw [ih (fun u hu => hv u (by simp [hu]))]
    cases h : decodeN m rest <;> simp

theorem encodeTk_ne_nil (t : Tk) : encodeTk t ≠ [] := by simp [encodeTk]

/-- `Tickets.decode_bad_count`: a count byte that is not the number of entries is rejected: more than there are runs
out of bytes, fewer leaves the remaining entries as trailing bytes. -/
theorem decode_bad_count {ts : List Tk} (hv : ∀ t ∈ ts, t.Valid) {c : Nat} (hc : c ≠ ts.length) :
    decode (1 :: c :: encodeAll ts) = none := by
  rcases Nat.lt_or_gt_of_ne hc with hlt | hgt
  · have hsplit : encodeAll ts = encodeAll (ts.take c) ++ encodeAll (ts.drop c) := by
      simp only [encodeAll, ← List.flatMap_append, List.take_append_drop]
    have hvt : ∀ t ∈ ts.take c, t.Valid := fun t ht => hv t (List.mem_of_mem_take ht)
    have hlen : (ts.take c).length = c := by simp; omega
    have := decodeN_encode (ts.take c) hvt (encodeAll (ts.drop c))
    rw [hlen] at this
    have hne : encodeAll (ts.drop c) ≠ [] := by
      have : ts.drop c ≠ [] := by
        intro h; have := congrArg List.length h; simp at this; omega
      obtain ⟨t, u, hu⟩ : ∃ t u, ts.drop c = t :: u := by
        cases h : ts.drop c with
        | nil => exact absurd h ‹_›
        | cons t u => exact ⟨t, u, rfl⟩
      rw [hu]; simp [encodeAll, encodeTk_ne_nil]
    simp [decode, u8?, hsplit, this, hne]
  · obtain ⟨m, hm⟩ : ∃ m, c = ts.length + (m + 1) := ⟨c - ts.length - 1, by omega⟩
    have := decodeN_append ts hv (m + 1) []
    simp only [List.append_nil, decodeN_nil_succ] at this
    simp [decode, u8?, hm, this]

/-- An algorithm tag outside 1 to 4 is rejected. -/
theorem decodeEntry_unknown_alg {a : Nat} (h : ¬ (1 ≤ a ∧ a ≤ 4)) (rest : List Nat) :
    decodeEntry (a :: rest) = none := by
  simp [decodeEntry, u8?, h]

/-- An ALPN length of 0 or over 32 is rejected. -/
theorem decodeEntry_bad_alpn_len {a : Nat} {node : List Nat} (hn : node.length = 32) {alen : Nat}
    (h : alen = 0 ∨ 32 < alen) (rest : List Nat) : decodeEntry (a :: (node ++ (alen :: rest))) = none := by
  unfold decodeEntry
  simp only [u8?]
  by_cases ha : 1 ≤ a ∧ a ≤ 4
  · have ha' : ¬ ¬ (1 ≤ a ∧ a ≤ 4) := fun x => x ha
    simp only [ha', ite_false]
    rw [take?_append _ hn]
    simp only [u8?]
    cases htk : take? alen rest with
    | none => rfl
    | some r =>
      obtain ⟨alpn, l⟩ := r
      have : ¬ (1 ≤ alen ∧ alen ≤ 32) := by omega
      simp [this]
  · simp [ha]

/-- An AEAD tag other than 1 or 2 is rejected. -/
theorem decodeEntry_unknown_aead {a : Nat} {node alpn tid psk : List Nat} (hn : node.length = 32)
    (hal : 1 ≤ alpn.length ∧ alpn.length ≤ 32) (ht : tid.length = 16) (hp : psk.length = 32) {ae : Nat}
    (h : ¬ (ae = 1 ∨ ae = 2)) (rest : List Nat) :
    decodeEntry (a :: (node ++ (alpn.length :: (alpn ++ (tid ++ (psk ++ (ae :: rest))))))) = none := by
  unfold decodeEntry
  simp only [u8?]
  by_cases ha : 1 ≤ a ∧ a ≤ 4
  · have ha' : ¬ ¬ (1 ≤ a ∧ a ≤ 4) := fun x => x ha
    simp only [ha', ite_false]
    rw [take?_append _ hn]
    simp only [u8?]
    rw [take?_append _ rfl]
    have hal' : ¬ ¬ (1 ≤ alpn.length ∧ alpn.length ≤ 32) := fun x => x hal
    simp only [hal', ite_false]
    rw [take?_append _ ht]
    dsimp only
    rw [take?_append _ hp]
    simp [u8?, h]
  · simp [ha]

end Pinc.Tickets

#audit_axioms Pinc.Tickets.fromBe64_be64
#audit_axioms Pinc.Tickets.be64_fromBe64
#audit_axioms Pinc.Tickets.decodeEntry_encode
#audit_axioms Pinc.Tickets.decode_encode
#audit_axioms Pinc.Tickets.decode_trailing
#audit_axioms Pinc.Tickets.decode_bad_version
#audit_axioms Pinc.Tickets.decode_bad_count
#audit_axioms Pinc.Tickets.decodeEntry_unknown_alg
#audit_axioms Pinc.Tickets.decodeEntry_bad_alpn_len
#audit_axioms Pinc.Tickets.decodeEntry_unknown_aead
