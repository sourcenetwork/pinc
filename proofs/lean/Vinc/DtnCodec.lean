import Vinc.Axioms

/-!
# Codec combinators

A `Codec α` is a parser and an emitter on byte lists with the two laws every wire format of the delay-tolerant layer
needs: parsing what was emitted gives the value back and leaves the rest (`rt`), and whatever the parser accepts is
exactly the emission of a well-formed value followed by the rest (`inv`). Both laws hold for all values and all
byte strings, with unbounded lengths. From them `decodeAll` (parse and require that no byte remains, as
`SignedHead::decode` and `CustodyAck::decode` do) is a bijection between the well-formed values and the byte strings it
accepts: encoding is canonical and injective, garbage is rejected, trailing bytes and every proper prefix are
rejected.

The combinators mirror `vinc-wire::Reader` (`read_array`, `read_u16`, `read_u32`, `read_u64`: fixed width big-endian,
nothing consumed on a short input) and the field checks of the decoders (a guard is a check after the fields are
read). Bytes are `Fin 256`, so the input is bytes by type.
-/

namespace Vinc.DtnCodec

abbrev Byte := Fin 256
abbrev Bytes := List Byte

/-- Big-endian value of a byte list. -/
def ofBE (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.val) 0

/-- The `w` big-endian bytes of `v` (the low bytes if `v` is too large). -/
def toBE : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, v => toBE w (v / 256) ++ [⟨v % 256, Nat.mod_lt _ (by decide)⟩]

theorem snoc_induction {α : Type} {P : List α → Prop} (nil : P []) (snoc : ∀ xs x, P xs → P (xs ++ [x])) :
    ∀ l, P l := by
  have : ∀ l : List α, P l.reverse := fun l => by
    induction l with
    | nil => exact nil
    | cons x xs ih => simpa using snoc _ x ih
  intro l; simpa using this l.reverse

theorem toBE_length (w v : Nat) : (toBE w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [toBE, ih]

theorem ofBE_append_one (xs : Bytes) (b : Byte) : ofBE (xs ++ [b]) = ofBE xs * 256 + b.val := by
  simp [ofBE, List.foldl_append]

theorem ofBE_toBE (w v : Nat) (h : v < 256 ^ w) : ofBE (toBE w v) = v := by
  induction w generalizing v with
  | zero => simp [toBE, ofBE] at *; omega
  | succ w ih =>
    simp only [toBE, ofBE_append_one]
    rw [ih (v / 256) (by rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by omega))]
    omega

theorem toBE_ofBE (bs : Bytes) : toBE bs.length (ofBE bs) = bs := by
  induction bs using snoc_induction with
  | nil => rfl
  | snoc xs b ih =>
    simp only [List.length_append, List.length_singleton, toBE, ofBE_append_one]
    have h1 : (ofBE xs * 256 + b.val) / 256 = ofBE xs := by omega
    have h2 : (ofBE xs * 256 + b.val) % 256 = b.val := by omega
    simp only [h1, h2]
    rw [ih]

theorem ofBE_lt (bs : Bytes) : ofBE bs < 256 ^ bs.length := by
  induction bs using snoc_induction with
  | nil => simp [ofBE]
  | snoc xs b ih =>
    simp only [List.length_append, List.length_singleton, ofBE_append_one, Nat.pow_succ]
    have := b.isLt
    omega

structure Codec (α : Type) where
  wf : α → Prop
  emit : α → Bytes
  parse : Bytes → Option (α × Bytes)
  rt : ∀ a rest, wf a → parse (emit a ++ rest) = some (a, rest)
  inv : ∀ bs a r, parse bs = some (a, r) → bs = emit a ++ r ∧ wf a

/-- `w` raw bytes (`read_array`, `read_bytes`). -/
def bytesC (w : Nat) : Codec Bytes where
  wf xs := xs.length = w
  emit xs := xs
  parse bs := if w ≤ bs.length then some (bs.take w, bs.drop w) else none
  rt a rest h := by
    have : w ≤ a.length + rest.length := by omega
    simp [this, List.take_left' h, List.drop_left' h]
  inv bs a r h := by
    by_cases hw : w ≤ bs.length
    · simp [hw] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨(List.take_append_drop w bs).symm, by simp; omega⟩
    · simp [hw] at h

/-- A big-endian unsigned integer of `w` bytes (`read_u8`, `read_u16`, `read_u32`, `read_u64`). -/
def uC (w : Nat) : Codec Nat where
  wf v := v < 256 ^ w
  emit v := toBE w v
  parse bs := ((bytesC w).parse bs).map fun p => (ofBE p.1, p.2)
  rt a rest h := by
    have e : (bytesC w).parse (toBE w a ++ rest) = some (toBE w a, rest) := (bytesC w).rt (toBE w a) rest (toBE_length w a)
    show Option.map _ ((bytesC w).parse (toBE w a ++ rest)) = _
    rw [e]
    simp [ofBE_toBE w a h]
  inv bs a r h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨x, y⟩, hp, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := (bytesC w).inv bs x y hp
    have hl : x.length = w := this.2
    refine ⟨?_, ?_⟩
    · have e : toBE w (ofBE x) = x := by rw [← hl]; exact toBE_ofBE x
      simp only [e]; exact this.1
    · have := ofBE_lt x; rw [hl] at this; exact this

/-- Two fields in a row, the second chosen by the first (an endorsement's length depends on the algorithm). -/
def pairD {α β : Type} (c1 : Codec α) (c2 : α → Codec β) : Codec (α × β) where
  wf p := c1.wf p.1 ∧ (c2 p.1).wf p.2
  emit p := c1.emit p.1 ++ (c2 p.1).emit p.2
  parse bs := (c1.parse bs).bind fun x => ((c2 x.1).parse x.2).map fun y => ((x.1, y.1), y.2)
  rt p rest h := by
    obtain ⟨a, b⟩ := p
    simp only [List.append_assoc]
    simp [c1.rt a _ h.1, (c2 a).rt b rest h.2]
  inv bs p r h := by
    obtain ⟨a, b⟩ := p
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    have h1 := c1.inv bs x.1 x.2 hx
    have h2 := (c2 x.1).inv x.2 y.1 y.2 hy
    refine ⟨?_, h1.2, h2.2⟩
    show bs = c1.emit x.1 ++ (c2 x.1).emit y.1 ++ y.2
    rw [List.append_assoc, ← h2.1]; exact h1.1

/-- Two independent fields. -/
def pair {α β : Type} (c1 : Codec α) (c2 : Codec β) : Codec (α × β) := pairD c1 fun _ => c2

/-- A check after the fields are read (the decoders' `ok_or(Params)`). -/
def guardC {α : Type} (c : Codec α) (p : α → Prop) [DecidablePred p] : Codec α where
  wf a := c.wf a ∧ p a
  emit := c.emit
  parse bs := match c.parse bs with
    | some (a, r) => if p a then some (a, r) else none
    | none => none
  rt a rest h := by simp [c.rt a rest h.1, h.2]
  inv bs a r h := by
    cases hp : c.parse bs with
    | none => simp [hp] at h
    | some x =>
      obtain ⟨a', r'⟩ := x
      simp only [hp] at h
      by_cases hq : p a'
      · simp [hq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨(c.inv bs a' r' hp).1, (c.inv bs a' r' hp).2, hq⟩
      · simp [hq] at h

/-- The same wire format for an isomorphic type. -/
def mapC {α β : Type} (c : Codec α) (f : α → β) (g : β → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) :
    Codec β where
  wf b := c.wf (g b)
  emit b := c.emit (g b)
  parse bs := (c.parse bs).map fun p => (f p.1, p.2)
  rt b rest h := by simp [c.rt (g b) rest h, hfg]
  inv bs b r h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨x, y⟩, hp, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := c.inv bs x y hp
    simpa [hgf] using this

/-- Parse and require that no byte remains (`if !r.is_empty() { return Err(Params) }`). -/
def decodeAll {α : Type} (c : Codec α) (bs : Bytes) : Option α :=
  match c.parse bs with
  | some (a, []) => some a
  | _ => none

theorem decodeAll_emit {α : Type} (c : Codec α) (a : α) (h : c.wf a) : decodeAll c (c.emit a) = some a := by
  have := c.rt a [] h
  simp only [List.append_nil] at this
  simp [decodeAll, this]

/-- Garbage is rejected: whatever decodes is the encoding of a well-formed value. -/
theorem decodeAll_some {α : Type} (c : Codec α) (bs : Bytes) (a : α) (h : decodeAll c bs = some a) :
    bs = c.emit a ∧ c.wf a := by
  unfold decodeAll at h
  split at h
  · rename_i a' r hp
    simp at h; subst h
    have := c.inv bs _ _ hp
    simpa using this
  · simp at h

/-- Encoding is injective on well-formed values: one byte string per value. -/
theorem emit_inj {α : Type} (c : Codec α) (a b : α) (ha : c.wf a) (hb : c.wf b) (h : c.emit a = c.emit b) : a = b := by
  have := decodeAll_emit c a ha
  rw [h, decodeAll_emit c b hb] at this
  exact (Option.some.inj this).symm

/-- Trailing bytes are rejected. -/
theorem decodeAll_trailing {α : Type} (c : Codec α) (a : α) (ha : c.wf a) (extra : Bytes) (hx : extra ≠ []) :
    decodeAll c (c.emit a ++ extra) = none := by
  unfold decodeAll
  rw [c.rt a extra ha]
  cases extra with
  | nil => exact absurd rfl hx
  | cons x xs => rfl

/-- Every proper prefix of an encoding is rejected (the reader runs out before the value is complete). -/
theorem decodeAll_prefix {α : Type} (c : Codec α) (a : α) (ha : c.wf a) (p q : Bytes) (hq : q ≠ [])
    (hpq : p ++ q = c.emit a) : decodeAll c p = none := by
  cases hd : decodeAll c p with
  | none => rfl
  | some b =>
    exfalso
    obtain ⟨hb, hwb⟩ := decodeAll_some c p b hd
    have e : c.emit a = c.emit b ++ q := by rw [← hpq, hb]
    have := c.rt b q hwb
    rw [← e] at this
    have h2 := c.rt a [] ha
    simp only [List.append_nil] at h2
    rw [h2] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact hq this.2.symm

end Vinc.DtnCodec
