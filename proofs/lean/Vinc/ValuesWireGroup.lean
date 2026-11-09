import Vinc.ValuesWireBase

/-!
# The value wire: the GROUP header

A model of `GroupHeader::parse` and `GroupHeader::encode` (`wire.rs`). `ghBody` is the code after the first 16 bytes
are taken (`first_chunk::<16>`); `ghBody_eq` is its decision procedure in closed form for a 16-byte header, the
type byte first, then the follows flag, then the lengths, as in the code; `ghParse_eq` lifts it to any input.
-/

namespace Vinc.ValuesWire

open Vinc Varint

/-- A parsed GROUP header (`GroupHeader`): offset (`u64`), data length (`u32`), proof length (`u16`), follows. -/
structure GH where
  off : Nat
  len : Nat
  plen : Nat
  follows : Bool
  deriving DecidableEq, Repr

/-- The code after the first 16 bytes `h` are taken: type byte 2, offset, length, proof length, flag. -/
def ghBody (h : List Nat) : Except Err GH :=
  match readBe 1 h with
  | .error e => .error e
  | .ok (t, r1) =>
    if t ≠ 2 then .error (.unexpected "not a group") else
    match readBe 8 r1 with
    | .error e => .error e
    | .ok (off, r2) =>
      match readBe 4 r2 with
      | .error e => .error e
      | .ok (len, r3) =>
        match readBe 2 r3 with
        | .error e => .error e
        | .ok (plen, r4) =>
          match readBe 1 r4 with
          | .error e => .error e
          | .ok (fl, _) =>
            if fl > 1 then .error (.unexpected "bad follows flag") else
            if len = 0 ∨ plen % 64 ≠ 0 then .error (.unexpected "bad group lengths") else
            .ok ⟨off, len, plen, decide (fl = 1)⟩

/-- `GroupHeader::parse`: fewer than 16 bytes is truncated, otherwise the header is the first 16. -/
def ghParse (buf : List Nat) : Except Err GH :=
  if buf.length < 16 then .error (.truncated (16 - buf.length)) else ghBody (buf.take 16)

/-- `GroupHeader::encode`: the 16 header bytes. -/
def ghEncode (g : GH) : List Nat :=
  [2] ++ beBytes 8 g.off ++ beBytes 4 g.len ++ beBytes 2 g.plen ++ [if g.follows then 1 else 0]

theorem length_ghEncode (g : GH) : (ghEncode g).length = 16 := by
  simp [ghEncode, length_beBytes]

theorem ghEncode_valid (g : GH) : ValidBytes (ghEncode g) := by
  intro b hb
  simp only [ghEncode, List.mem_append, List.mem_singleton] at hb
  rcases hb with ((( hb | hb) | hb) | hb) | hb
  · omega
  · exact beBytes_valid 8 _ b hb
  · exact beBytes_valid 4 _ b hb
  · exact beBytes_valid 2 _ b hb
  · split at hb <;> omega

/-- The 16-byte decision procedure in closed form. -/
theorem ghBody_eq (h : List Nat) (hl : h.length = 16) :
    ghBody h =
      if h.getD 0 0 ≠ 2 then .error (.unexpected "not a group")
      else if h.getD 15 0 > 1 then .error (.unexpected "bad follows flag")
      else if beVal ((h.drop 9).take 4) = 0 ∨ beVal ((h.drop 13).take 2) % 64 ≠ 0 then
        .error (.unexpected "bad group lengths")
      else .ok ⟨beVal ((h.drop 1).take 8), beVal ((h.drop 9).take 4), beVal ((h.drop 13).take 2),
        decide (h.getD 15 0 = 1)⟩ := by
  rcases h with _ | ⟨a0, h⟩
  · simp at hl
  rcases h with _ | ⟨a1, h⟩
  · simp at hl
  rcases h with _ | ⟨a2, h⟩
  · simp at hl
  rcases h with _ | ⟨a3, h⟩
  · simp at hl
  rcases h with _ | ⟨a4, h⟩
  · simp at hl
  rcases h with _ | ⟨a5, h⟩
  · simp at hl
  rcases h with _ | ⟨a6, h⟩
  · simp at hl
  rcases h with _ | ⟨a7, h⟩
  · simp at hl
  rcases h with _ | ⟨a8, h⟩
  · simp at hl
  rcases h with _ | ⟨a9, h⟩
  · simp at hl
  rcases h with _ | ⟨a10, h⟩
  · simp at hl
  rcases h with _ | ⟨a11, h⟩
  · simp at hl
  rcases h with _ | ⟨a12, h⟩
  · simp at hl
  rcases h with _ | ⟨a13, h⟩
  · simp at hl
  rcases h with _ | ⟨a14, h⟩
  · simp at hl
  rcases h with _ | ⟨a15, h⟩
  · simp at hl
  have hn : h = [] := List.length_eq_zero_iff.mp (by simpa using hl)
  subst hn
  simp [ghBody, readBe, readBytes, beVal]

theorem take_drop16 (buf : List Nat) {a b : Nat} (hab : a + b ≤ 16) :
    ((buf.take 16).drop a).take b = (buf.drop a).take b := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem split16 (h : List Nat) (hl : h.length = 16) :
    h = [h.getD 0 0] ++ (h.drop 1).take 8 ++ (h.drop 9).take 4 ++ (h.drop 13).take 2 ++ [h.getD 15 0] := by
  rcases h with _ | ⟨a0, h⟩
  · simp at hl
  rcases h with _ | ⟨a1, h⟩
  · simp at hl
  rcases h with _ | ⟨a2, h⟩
  · simp at hl
  rcases h with _ | ⟨a3, h⟩
  · simp at hl
  rcases h with _ | ⟨a4, h⟩
  · simp at hl
  rcases h with _ | ⟨a5, h⟩
  · simp at hl
  rcases h with _ | ⟨a6, h⟩
  · simp at hl
  rcases h with _ | ⟨a7, h⟩
  · simp at hl
  rcases h with _ | ⟨a8, h⟩
  · simp at hl
  rcases h with _ | ⟨a9, h⟩
  · simp at hl
  rcases h with _ | ⟨a10, h⟩
  · simp at hl
  rcases h with _ | ⟨a11, h⟩
  · simp at hl
  rcases h with _ | ⟨a12, h⟩
  · simp at hl
  rcases h with _ | ⟨a13, h⟩
  · simp at hl
  rcases h with _ | ⟨a14, h⟩
  · simp at hl
  rcases h with _ | ⟨a15, h⟩
  · simp at hl
  have hn : h = [] := List.length_eq_zero_iff.mp (by simpa using hl)
  subst hn
  rfl

/-- The parse accepts exactly the headers with type byte 2, a flag of 0 or 1, a length that is not 0 and a proof
length that is a whole number of 64-byte pairs. -/
theorem gh_accept_iff (buf : List Nat) :
    (∃ g, ghParse buf = .ok g) ↔
      16 ≤ buf.length ∧ buf.getD 0 0 = 2 ∧ buf.getD 15 0 ≤ 1 ∧ beVal ((buf.drop 9).take 4) ≠ 0 ∧
        beVal ((buf.drop 13).take 2) % 64 = 0 := by
  by_cases hl : buf.length < 16
  · simp [ghParse, hl]
    omega
  have hl' : 16 ≤ buf.length := by omega
  have hlen : (buf.take 16).length = 16 := by simp; omega
  have g0 : (buf.take 16).getD 0 0 = buf.getD 0 0 := getD_take (by omega)
  have g15 : (buf.take 16).getD 15 0 = buf.getD 15 0 := getD_take (by omega)
  have t9 := take_drop16 buf (a := 9) (b := 4) (by omega)
  have t13 := take_drop16 buf (a := 13) (b := 2) (by omega)
  have t1 := take_drop16 buf (a := 1) (b := 8) (by omega)
  simp only [ghParse, hl, ↓reduceIte, ghBody_eq _ hlen, g0, g15, t9, t13, t1]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨hl', ?_⟩
    revert hg
    repeat' split
    all_goals first | (intro h; exfalso; simp at h; done) | (intro _; omega)
  · rintro ⟨_, a, b, c, d⟩
    refine ⟨⟨beVal ((buf.drop 1).take 8), beVal ((buf.drop 9).take 4), beVal ((buf.drop 13).take 2),
      decide (buf.getD 15 0 = 1)⟩, ?_⟩
    have a' : ¬ buf.getD 0 0 ≠ 2 := by omega
    have b' : ¬ buf.getD 15 0 > 1 := by omega
    have c' : ¬ (beVal ((buf.drop 9).take 4) = 0 ∨ beVal ((buf.drop 13).take 2) % 64 ≠ 0) := by omega
    simp only [a', b', c', ↓reduceIte]

/-- Canonical: an accepted header re-encodes to exactly the 16 bytes it was read from. -/
theorem gh_canonical (buf : List Nat) (hv : ValidBytes buf) (g : GH) (h : ghParse buf = .ok g) :
    ghEncode g = buf.take 16 ∧ g.len ≠ 0 ∧ g.plen % 64 = 0 ∧ g.off < 2 ^ 64 ∧ g.len < 2 ^ 32 ∧ g.plen < 2 ^ 16 := by
  obtain ⟨hl', a, b, c, d⟩ := (gh_accept_iff buf).1 ⟨g, h⟩
  have hl : ¬ buf.length < 16 := by omega
  have hlen : (buf.take 16).length = 16 := by simp; omega
  have hvt : ValidBytes (buf.take 16) := fun x hx => hv x (List.mem_of_mem_take hx)
  have g0 : (buf.take 16).getD 0 0 = buf.getD 0 0 := getD_take (by omega)
  have g15 : (buf.take 16).getD 15 0 = buf.getD 15 0 := getD_take (by omega)
  have t9 := take_drop16 buf (a := 9) (b := 4) (by omega)
  have t13 := take_drop16 buf (a := 13) (b := 2) (by omega)
  have t1 := take_drop16 buf (a := 1) (b := 8) (by omega)
  simp only [ghParse, hl, ↓reduceIte, ghBody_eq _ hlen, g0, g15, t9, t13, t1] at h
  have a' : ¬ buf.getD 0 0 ≠ 2 := by omega
  have b' : ¬ buf.getD 15 0 > 1 := by omega
  have c' : ¬ (beVal ((buf.drop 9).take 4) = 0 ∨ beVal ((buf.drop 13).take 2) % 64 ≠ 0) := by omega
  simp only [a', b', c', ↓reduceIte, Except.ok.injEq] at h
  subst h
  have vb : ∀ x y, ValidBytes ((buf.drop x).take y) :=
    fun x y z hz => hv z (List.mem_of_mem_drop (List.mem_of_mem_take hz))
  have lb : ∀ x y, x + y ≤ buf.length → ((buf.drop x).take y).length = y := by
    intro x y hxy; simp; omega
  refine ⟨?_, c, d, ?_, ?_, ?_⟩
  · have hs := split16 (buf.take 16) hlen
    rw [g0, g15, t9, t13, t1] at hs
    rw [hs]
    simp only [ghEncode]
    rw [beBytes_beVal_of_length 8 _ (vb 1 8) (lb 1 8 (by omega)),
      beBytes_beVal_of_length 4 _ (vb 9 4) (lb 9 4 (by omega)),
      beBytes_beVal_of_length 2 _ (vb 13 2) (lb 13 2 (by omega))]
    have hf : (if decide (buf.getD 15 0 = 1) = true then 1 else 0) = buf.getD 15 0 := by
      by_cases e : buf.getD 15 0 = 1
      · rw [e]; rfl
      · have e0 : buf.getD 15 0 = 0 := by omega
        rw [e0]; rfl
    rw [hf, a]
  · have := beVal_lt _ (vb 1 8); rw [lb 1 8 (by omega)] at this; omega
  · have := beVal_lt _ (vb 9 4); rw [lb 9 4 (by omega)] at this; omega
  · have := beVal_lt _ (vb 13 2); rw [lb 13 2 (by omega)] at this; omega

/-- The parse in closed form on the whole input. -/
theorem ghParse_eq (buf : List Nat) (hl : 16 ≤ buf.length) :
    ghParse buf =
      if buf.getD 0 0 ≠ 2 then .error (.unexpected "not a group")
      else if buf.getD 15 0 > 1 then .error (.unexpected "bad follows flag")
      else if beVal ((buf.drop 9).take 4) = 0 ∨ beVal ((buf.drop 13).take 2) % 64 ≠ 0 then
        .error (.unexpected "bad group lengths")
      else .ok ⟨beVal ((buf.drop 1).take 8), beVal ((buf.drop 9).take 4), beVal ((buf.drop 13).take 2),
        decide (buf.getD 15 0 = 1)⟩ := by
  have hlen : (buf.take 16).length = 16 := by simp; omega
  have g0 : (buf.take 16).getD 0 0 = buf.getD 0 0 := getD_take (by omega)
  have g15 : (buf.take 16).getD 15 0 = buf.getD 15 0 := getD_take (by omega)
  have t9 := take_drop16 buf (a := 9) (b := 4) (by omega)
  have t13 := take_drop16 buf (a := 13) (b := 2) (by omega)
  have t1 := take_drop16 buf (a := 1) (b := 8) (by omega)
  have hl' : ¬ buf.length < 16 := by omega
  simp only [ghParse, hl', ↓reduceIte, ghBody_eq _ hlen, g0, g15, t9, t13, t1]

/-- Round trip: parsing an encoded header, with anything after it, returns the header (every field in range). -/
theorem gh_roundtrip (g : GH) (rest : List Nat) (h1 : g.off < 2 ^ 64) (h2 : g.len ≠ 0) (h3 : g.len < 2 ^ 32)
    (h4 : g.plen < 2 ^ 16) (h5 : g.plen % 64 = 0) : ghParse (ghEncode g ++ rest) = .ok g := by
  have hl : ¬ (ghEncode g ++ rest).length < 16 := by simp [length_ghEncode]
  have e : (ghEncode g ++ rest).take 16 = ghEncode g := List.take_left' (length_ghEncode g)
  have hf : ghEncode g = [2] ++ (beBytes 8 g.off ++ (beBytes 4 g.len ++ (beBytes 2 g.plen ++ [if g.follows then 1 else 0]))) := by
    simp [ghEncode]
  unfold ghParse
  simp only [hl, ↓reduceIte, e]
  rw [hf]
  unfold ghBody
  simp only [readBe_append (n := 1) [2] _ rfl, beVal_single, ne_eq, not_true_eq_false, ↓reduceIte,
    readBe_append (n := 8) (beBytes 8 g.off) _ (length_beBytes 8 _),
    readBe_append (n := 4) (beBytes 4 g.len) _ (length_beBytes 4 _),
    readBe_append (n := 2) (beBytes 2 g.plen) _ (length_beBytes 2 _), readBe_single, beVal_beBytes]
  have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := rfl
  have e4 : (256 : Nat) ^ 4 = 2 ^ 32 := rfl
  have e2 : (256 : Nat) ^ 2 = 2 ^ 16 := rfl
  rw [e8, e4, e2, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  rcases g with ⟨off, len, plen, f⟩
  cases f <;> simp_all

/-- Injective: two inputs that parse to the same header agree on their first 16 bytes. -/
theorem gh_injective (a b : List Nat) (ha : ValidBytes a) (hb : ValidBytes b) (g : GH)
    (h1 : ghParse a = .ok g) (h2 : ghParse b = .ok g) : a.take 16 = b.take 16 := by
  rw [← (gh_canonical a ha g h1).1, ← (gh_canonical b hb g h2).1]

theorem gh_reject_short (buf : List Nat) (h : buf.length < 16) :
    ghParse buf = .error (.truncated (16 - buf.length)) := by
  simp [ghParse, h]

/-- Truncation at every length: a prefix shorter than 16 bytes is truncated, with the exact shortfall. -/
theorem gh_prefix_truncated (buf : List Nat) (m : Nat) (hm : m < 16) (hb : m ≤ buf.length) :
    ghParse (buf.take m) = .error (.truncated (16 - m)) := by
  have := gh_reject_short (buf.take m) (by simp; omega)
  simpa [Nat.min_eq_left hb] using this

theorem gh_reject_type (buf : List Nat) (hl : 16 ≤ buf.length) (ht : buf.getD 0 0 ≠ 2) :
    ghParse buf = .error (.unexpected "not a group") := by
  rw [ghParse_eq buf hl]; simp only [ne_eq, ht, not_false_eq_true, ↓reduceIte]

theorem gh_reject_follows (buf : List Nat) (hl : 16 ≤ buf.length) (h0 : buf.getD 0 0 = 2) (hf : 1 < buf.getD 15 0) :
    ghParse buf = .error (.unexpected "bad follows flag") := by
  rw [ghParse_eq buf hl]
  have : ¬ buf.getD 0 0 ≠ 2 := by omega
  simp only [this, ↓reduceIte, gt_iff_lt, hf]

theorem gh_reject_empty (buf : List Nat) (hl : 16 ≤ buf.length) (h0 : buf.getD 0 0 = 2) (hf : buf.getD 15 0 ≤ 1)
    (hz : beVal ((buf.drop 9).take 4) = 0) : ghParse buf = .error (.unexpected "bad group lengths") := by
  rw [ghParse_eq buf hl]
  have a : ¬ buf.getD 0 0 ≠ 2 := by omega
  have b : ¬ buf.getD 15 0 > 1 := by omega
  simp only [a, b, hz, true_or, ↓reduceIte]

theorem gh_reject_pairs (buf : List Nat) (hl : 16 ≤ buf.length) (h0 : buf.getD 0 0 = 2) (hf : buf.getD 15 0 ≤ 1)
    (hp : beVal ((buf.drop 13).take 2) % 64 ≠ 0) : ghParse buf = .error (.unexpected "bad group lengths") := by
  rw [ghParse_eq buf hl]
  have a : ¬ buf.getD 0 0 ≠ 2 := by omega
  have b : ¬ buf.getD 15 0 > 1 := by omega
  have c : beVal ((buf.drop 9).take 4) = 0 ∨ beVal ((buf.drop 13).take 2) % 64 ≠ 0 := Or.inr hp
  simp only [a, b, c, ↓reduceIte]

end Vinc.ValuesWire

#audit_axioms Vinc.ValuesWire.ghBody_eq
#audit_axioms Vinc.ValuesWire.gh_accept_iff
#audit_axioms Vinc.ValuesWire.gh_canonical
#audit_axioms Vinc.ValuesWire.gh_roundtrip
#audit_axioms Vinc.ValuesWire.gh_injective
#audit_axioms Vinc.ValuesWire.gh_prefix_truncated
#audit_axioms Vinc.ValuesWire.gh_reject_type
#audit_axioms Vinc.ValuesWire.gh_reject_follows
#audit_axioms Vinc.ValuesWire.gh_reject_empty
#audit_axioms Vinc.ValuesWire.gh_reject_pairs
