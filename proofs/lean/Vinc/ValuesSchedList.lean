import Vinc.Axioms
/-!
# The span lists of the value fetch scheduler

A model of `crates/vinc-values/src/span.rs`: `Span`, the bounded `RangeList<N>` (`push`, `push_front`, `pop_front`,
`push_new`, `extend`, `total`), `holes` (the part of a span the store has not verified), `align` (round out to whole
groups) and the constants `GROUP` and `u64::MAX`.

Offsets and lengths are `Nat`. The code is `u64` with `saturating_add` in `Span::end` and `RangeList::total`; the
scheduler only holds spans inside a value of at most `u64::MAX` bytes, so `off + len ≤ M` (`Bounded`) and the
saturating operations never saturate: `endSat_eq` and `totalSat_eq` say so, and `push_bounded` shows the bound is kept
by every list operation. The live slice `items[..len]` of the Rust array is the `List`; capacity `N` is the argument
`n` (the code needs `0 < n`).

What a list is for: it is the fetch queue, a provider's assigned work and a request's ranges. Its one promise is
*coverage never shrinks*: `push` and `push_front` onto a full list widen the last (first) span over the gap instead of
failing, which can only make a byte be asked for twice, never skip it (`push_cov`, `pushFront_cov`); below capacity, or
when the new span touches the last one, the covered set is exactly the union (`push_cov_iff_room`,
`push_cov_iff_touch`); and a widened byte always lies in the hull of the last span and the new one
(`push_cov_hull`). `holes` returns exactly the unverified part of a span, ordered and strictly separated
(`holesOf_cov`, `holesOf_mult`, `holesOf_sorted`, in `ValuesSchedHoles`). `align` rounds a non-empty span out to whole groups clamped to the value
(`align_spec`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

/-- `u64::MAX`. -/
def M : Nat := 2 ^ 64 - 1

/-- `knobs::GROUP`: 16 chunks of 1024 bytes. -/
def G : Nat := 16384

theorem G_pos : 0 < G := by decide

/-- A byte span `(off, len)`. -/
structure Span where
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

namespace Span

/-- `Span::end` on unbounded naturals; see `endSat_eq`. -/
def fin (s : Span) : Nat := s.off + s.len

/-- `Span::end` as the code writes it. -/
def endSat (s : Span) : Nat := min (s.off + s.len) M

/-- The byte `x` lies in the span. -/
def Mem (s : Span) (x : Nat) : Prop := s.off ≤ x ∧ x < s.off + s.len

instance (s : Span) (x : Nat) : Decidable (s.Mem x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The smallest span holding both: what a push onto a full list (or onto a touching last span) writes. -/
def hull (a b : Span) : Span :=
  ⟨min a.off b.off, max (a.off + a.len) (b.off + b.len) - min a.off b.off⟩

theorem endSat_eq {s : Span} (h : s.off + s.len ≤ M) : s.endSat = s.fin := by
  simp only [endSat, fin]; omega

theorem hull_mem (a b : Span) (x : Nat) :
    (hull a b).Mem x ↔ min a.off b.off ≤ x ∧ x < max (a.off + a.len) (b.off + b.len) := by
  simp only [hull, Mem]; omega

/-- A touching span (starts inside or right after `a`, not before it) merges into `a` with nothing extra. -/
theorem hull_mem_touch {a b : Span} (h1 : a.off ≤ b.off) (h2 : b.off ≤ a.off + a.len) (x : Nat) :
    (hull a b).Mem x ↔ a.Mem x ∨ b.Mem x := by
  simp only [hull, Mem]; omega

end Span

/-- The bytes a list covers. -/
def cov (l : List Span) (x : Nat) : Prop := ∃ s ∈ l, s.Mem x

/-- How many spans of the list hold the byte (1 for each byte of a list without overlap). -/
def mult : List Span → Nat → Nat
  | [], _ => 0
  | s :: t, x => (if s.Mem x then 1 else 0) + mult t x

/-- The sum of the lengths. -/
def total : List Span → Nat
  | [] => 0
  | s :: t => s.len + total t

/-- `RangeList::total`: the fold with `saturating_add`. -/
def totalSat (l : List Span) : Nat := l.foldl (fun a s => min (a + s.len) M) 0

/-- Every span fits below `u64::MAX`. -/
def Bounded (l : List Span) : Prop := ∀ s ∈ l, s.off + s.len ≤ M

theorem cov_nil (x : Nat) : ¬ cov [] x := by simp [cov]

theorem cov_cons (s : Span) (l : List Span) (x : Nat) : cov (s :: l) x ↔ s.Mem x ∨ cov l x := by
  simp [cov]

theorem cov_append (a b : List Span) (x : Nat) : cov (a ++ b) x ↔ cov a x ∨ cov b x := by
  simp only [cov, List.mem_append]
  constructor
  · rintro ⟨s, h | h, hm⟩
    · exact Or.inl ⟨s, h, hm⟩
    · exact Or.inr ⟨s, h, hm⟩
  · rintro (⟨s, h, hm⟩ | ⟨s, h, hm⟩)
    · exact ⟨s, Or.inl h, hm⟩
    · exact ⟨s, Or.inr h, hm⟩

theorem cov_single (s : Span) (x : Nat) : cov [s] x ↔ s.Mem x := by simp [cov]

theorem mult_append (a b : List Span) (x : Nat) : mult (a ++ b) x = mult a x + mult b x := by
  induction a with
  | nil => simp [mult]
  | cons s t ih => simp [mult, ih]; omega

theorem mult_single (s : Span) (x : Nat) : mult [s] x = if s.Mem x then 1 else 0 := by simp [mult]

theorem cov_iff_mult (l : List Span) (x : Nat) : cov l x ↔ 0 < mult l x := by
  induction l with
  | nil => simp [cov, mult]
  | cons s t ih =>
    rw [cov_cons, ih]
    simp only [mult]
    by_cases h : s.Mem x <;> simp [h] <;> omega

theorem total_append (a b : List Span) : total (a ++ b) = total a + total b := by
  induction a with
  | nil => simp [total]
  | cons s t ih => simp [total, ih]; omega

theorem totalSat_eq_aux (l : List Span) (acc : Nat) (h : acc + total l ≤ M) :
    l.foldl (fun a s => min (a + s.len) M) acc = acc + total l := by
  induction l generalizing acc with
  | nil => simp [total]
  | cons s t ih =>
    simp only [List.foldl_cons, total] at *
    have : min (acc + s.len) M = acc + s.len := by omega
    rw [this, ih (acc + s.len) (by omega)]
    omega

/-- `RangeList::total` never saturates for the lists the scheduler holds (sum of lengths below `u64::MAX`). -/
theorem totalSat_eq (l : List Span) (h : total l ≤ M) : totalSat l = total l := by
  have := totalSat_eq_aux l 0 (by omega)
  simpa [totalSat] using this

/-! ## `push`, `push_front`, `pop_front` -/

/-- `RangeList::push` with capacity `n`. -/
def push (n : Nat) (l : List Span) (s : Span) : List Span :=
  if s.len = 0 then l else
  match l.getLast? with
  | none => if 0 < n then [s] else l
  | some last =>
    if (last.off ≤ s.off ∧ s.off ≤ last.off + last.len) ∨ l.length = n then
      l.dropLast ++ [Span.hull last s]
    else if l.length < n then l ++ [s] else l

/-- `RangeList::push_front` with capacity `n`. -/
def pushFront (n : Nat) (l : List Span) (s : Span) : List Span :=
  if s.len = 0 then l else
  if l.length = n then
    match l with
    | [] => []
    | f :: t => Span.hull f s :: t
  else s :: l

/-- `RangeList::pop_front`: the first span and the rest. -/
def popFront : List Span → Option Span × List Span
  | [] => (none, [])
  | f :: t => (some f, t)

/-- The touch test of `push`: `s` starts inside or right after `last`, not before it. -/
abbrev Touch (last s : Span) : Prop := last.off ≤ s.off ∧ s.off ≤ last.off + last.len

theorem list_snoc (l : List Span) : l = [] ∨ ∃ ys last, l = ys ++ [last] := by
  rcases List.eq_nil_or_concat l with h | ⟨ys, last, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨ys, last, by simpa using h⟩

theorem push_nil (n : Nat) (s : Span) : push n [] s = if s.len = 0 then [] else if 0 < n then [s] else [] := by
  by_cases h : s.len = 0 <;> by_cases hn : 0 < n <;> simp [push, h, hn]

theorem push_snoc (n : Nat) (ys : List Span) (last s : Span) :
    push n (ys ++ [last]) s =
      if s.len = 0 then ys ++ [last]
      else if Touch last s ∨ ys.length + 1 = n then ys ++ [Span.hull last s]
      else if ys.length + 1 < n then ys ++ [last, s] else ys ++ [last] := by
  by_cases h : s.len = 0
  · simp [push, h]
  · simp [push, h, Touch, List.getLast?_concat, List.dropLast_concat]

/-- The list stays within its capacity. -/
theorem push_length_le {n : Nat} (hn : 0 < n) {l : List Span} (h : l.length ≤ n) (s : Span) :
    (push n l s).length ≤ n := by
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rw [push_nil]; repeat' split
    all_goals simp
    all_goals omega
  · rw [push_snoc]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_singleton] at h ⊢
    repeat' split
    all_goals simp
    all_goals omega

theorem cov_snoc (ys : List Span) (t : Span) (x : Nat) : cov (ys ++ [t]) x ↔ cov ys x ∨ t.Mem x := by
  rw [cov_append, cov_single]

theorem cov_snoc2 (ys : List Span) (a b : Span) (x : Nat) :
    cov (ys ++ [a, b]) x ↔ cov ys x ∨ a.Mem x ∨ b.Mem x := by
  rw [cov_append, cov_cons, cov_single]

/-- Coverage never shrinks, and the new span is covered: a push onto a full list widens, it never drops. -/
theorem push_cov {n : Nat} (hn : 0 < n) {l : List Span} (hl : l.length ≤ n) (s : Span) (x : Nat) :
    cov l x ∨ s.Mem x → cov (push n l s) x := by
  intro h
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rcases h with h | h
    · exact absurd h (cov_nil x)
    · have : s.len ≠ 0 := by simp [Span.Mem] at h; omega
      rw [push_nil]; simp [this, hn, cov_single, h]
  · simp only [List.length_append, List.length_singleton] at hl
    rw [cov_snoc] at h
    rw [push_snoc]
    by_cases h0 : s.len = 0
    · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
      rw [if_pos h0, cov_snoc]
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hs
    · rw [if_neg h0]
      by_cases h1 : Touch last s ∨ ys.length + 1 = n
      · rw [if_pos h1, cov_snoc, Span.hull_mem]
        rcases h with (h | h) | h
        · exact Or.inl h
        · right; simp only [Span.Mem] at h ⊢; omega
        · right; simp only [Span.Mem] at h ⊢; omega
      · rw [if_neg h1]
        have h2 : ys.length + 1 < n := by omega
        rw [if_pos h2, cov_snoc2]
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-- Below capacity the covered set after a push is exactly the old one plus the new span. -/
theorem push_cov_iff_room {n : Nat} {l : List Span} (hl : l.length < n) (s : Span) (x : Nat) :
    cov (push n l s) x ↔ cov l x ∨ s.Mem x := by
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rw [push_nil]
    by_cases h0 : s.len = 0
    · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
      simp [h0, hs, cov_nil]
    · have : 0 < n := by simpa using hl
      simp [h0, this, cov_single, cov_nil]
  · simp only [List.length_append, List.length_singleton] at hl
    rw [cov_snoc, push_snoc]
    by_cases h0 : s.len = 0
    · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
      rw [if_pos h0, cov_snoc]; simp [hs]
    · rw [if_neg h0]
      by_cases h1 : Touch last s ∨ ys.length + 1 = n
      · rw [if_pos h1, cov_snoc]
        have ht : Touch last s := by
          rcases h1 with h1 | h1
          · exact h1
          · omega
        rw [Span.hull_mem_touch ht.1 ht.2]
        constructor
        · rintro (h | h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · rw [if_neg h1, if_pos (by omega), cov_snoc2]
        constructor
        · rintro (h | h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)

/-- A span that touches the last one merges with it exactly, full list or not. -/
theorem push_cov_iff_touch {n : Nat} (ys : List Span) (last s : Span) (ht : Touch last s) (x : Nat) :
    cov (push n (ys ++ [last]) s) x ↔ cov (ys ++ [last]) x ∨ s.Mem x := by
  rw [cov_snoc, push_snoc]
  by_cases h0 : s.len = 0
  · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
    rw [if_pos h0, cov_snoc]; simp [hs]
  · rw [if_neg h0, if_pos (Or.inl ht), cov_snoc, Span.hull_mem_touch ht.1 ht.2]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- A byte the push added beyond the old list and the new span is in the hull of the last span and the new one:
the widening of a full list covers a gap, nothing farther. -/
theorem push_cov_hull {n : Nat} (ys : List Span) (last s : Span) (x : Nat)
    (h : cov (push n (ys ++ [last]) s) x) :
    cov (ys ++ [last]) x ∨ s.Mem x ∨
      (min last.off s.off ≤ x ∧ x < max (last.off + last.len) (s.off + s.len)) := by
  rw [push_snoc] at h
  by_cases h0 : s.len = 0
  · rw [if_pos h0] at h; exact Or.inl h
  · rw [if_neg h0] at h
    by_cases h1 : Touch last s ∨ ys.length + 1 = n
    · rw [if_pos h1, cov_snoc, Span.hull_mem] at h
      rcases h with h | h
      · exact Or.inl ((cov_snoc ys last x).2 (Or.inl h))
      · exact Or.inr (Or.inr h)
    · rw [if_neg h1] at h
      by_cases h2 : ys.length + 1 < n
      · rw [if_pos h2, cov_snoc2] at h
        rcases h with h | h | h
        · exact Or.inl ((cov_snoc ys last x).2 (Or.inl h))
        · exact Or.inl ((cov_snoc ys last x).2 (Or.inr h))
        · exact Or.inr (Or.inl h)
      · rw [if_neg h2] at h; exact Or.inl h

/-- Every span of the list stays below `u64::MAX`, so `Span::end` and `total` never saturate. -/
theorem push_bounded {n : Nat} {l : List Span} (hb : Bounded l) (s : Span) (hs : s.off + s.len ≤ M) :
    Bounded (push n l s) := by
  intro t ht
  unfold push at ht
  split at ht
  · exact hb t ht
  · split at ht
    · split at ht
      · simp at ht; subst ht; exact hs
      · exact hb t ht
    · rename_i last hlast
      have hlm : last ∈ l := List.mem_of_getLast? hlast
      have hb' : ∀ u ∈ l.dropLast, u.off + u.len ≤ M := fun u hu => hb u (List.dropLast_subset l hu)
      have hl1 := hb last hlm
      split at ht
      · rcases List.mem_append.1 ht with h | h
        · exact hb' t h
        · simp at h; subst h; simp only [Span.hull]; omega
      · split at ht
        · rcases List.mem_append.1 ht with h | h
          · exact hb t h
          · simp at h; subst h; exact hs
        · exact hb t ht

/-- `push_front` stays within capacity. -/
theorem pushFront_length_le {n : Nat} (hn : 0 < n) {l : List Span} (hl : l.length ≤ n) (s : Span) :
    (pushFront n l s).length ≤ n := by
  unfold pushFront
  by_cases h0 : s.len = 0
  · rw [if_pos h0]; exact hl
  · rw [if_neg h0]
    by_cases h1 : l.length = n
    · rw [if_pos h1]
      cases l with
      | nil => simp at h1; omega
      | cons f t => simpa using hl
    · rw [if_neg h1]; simp; omega

/-- A byte of the list or of the new span is covered after `push_front`, also on a full list (it widens the first
span). -/
theorem pushFront_cov {n : Nat} (hn : 0 < n) {l : List Span} (s : Span) (x : Nat) (hl : l.length ≤ n) :
    cov l x ∨ s.Mem x → cov (pushFront n l s) x := by
  intro h
  unfold pushFront
  by_cases h0 : s.len = 0
  · rw [if_pos h0]
    rcases h with h | h
    · exact h
    · exact absurd h (by simp only [Span.Mem]; omega)
  · rw [if_neg h0]
    by_cases h1 : l.length = n
    · rw [if_pos h1]
      cases l with
      | nil => simp at h1; omega
      | cons f t =>
        simp only [cov_cons, Span.hull_mem] at h ⊢
        rcases h with (h | h) | h
        · left; simp only [Span.Mem] at h ⊢; omega
        · right; exact h
        · left; simp only [Span.Mem] at h ⊢; omega
    · rw [if_neg h1, cov_cons]
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- Below capacity `push_front` covers exactly the union, and adds the span as a separate element. -/
theorem pushFront_eq_of_room {n : Nat} {l : List Span} (hl : l.length < n) (s : Span) (h0 : s.len ≠ 0) :
    pushFront n l s = s :: l := by
  unfold pushFront
  rw [if_neg h0, if_neg (by omega)]

theorem pushFront_mult_of_room {n : Nat} {l : List Span} (hl : l.length < n) (s : Span) (x : Nat) :
    mult (pushFront n l s) x = mult l x + (if s.Mem x then 1 else 0) := by
  by_cases h0 : s.len = 0
  · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
    unfold pushFront; rw [if_pos h0]; simp [hs]
  · rw [pushFront_eq_of_room hl s h0]; simp only [mult]; omega

theorem pushFront_bounded {n : Nat} {l : List Span} (hb : Bounded l) (s : Span) (hs : s.off + s.len ≤ M) :
    Bounded (pushFront n l s) := by
  intro t ht
  unfold pushFront at ht
  by_cases h0 : s.len = 0
  · rw [if_pos h0] at ht; exact hb t ht
  · rw [if_neg h0] at ht
    by_cases h1 : l.length = n
    · rw [if_pos h1] at ht
      cases l with
      | nil => simp at ht
      | cons f t' =>
        have hf := hb f (by simp)
        rcases List.mem_cons.1 ht with h | h
        · subst h; simp only [Span.hull]; omega
        · exact hb t (by simp [h])
    · rw [if_neg h1] at ht
      rcases List.mem_cons.1 ht with h | h
      · subst h; exact hs
      · exact hb t h

theorem popFront_cons {l f : Span} {t : List Span} (h : popFront (l :: t) = (some f, t)) : True := trivial

/-- `pop_front` removes exactly the first span. -/
theorem popFront_spec (l : List Span) :
    (popFront l).1 = l.head? ∧ (popFront l).2 = l.tail := by
  cases l <;> simp [popFront]

theorem mult_cons (f : Span) (t : List Span) (x : Nat) :
    mult (f :: t) x = (if f.Mem x then 1 else 0) + mult t x := rfl

/-! ## Order -/

/-- The spans are in increasing order and do not overlap (touching is allowed). -/
def Sorted (l : List Span) : Prop := l.Pairwise (fun a b => a.off + a.len ≤ b.off)

theorem sorted_snoc {ys : List Span} {t : Span} :
    Sorted (ys ++ [t]) ↔ Sorted ys ∧ ∀ y ∈ ys, y.off + y.len ≤ t.off := by
  simp [Sorted, List.pairwise_append]

theorem sorted_tail {f : Span} {t : List Span} (h : Sorted (f :: t)) : Sorted t :=
  (List.pairwise_cons.1 h).2

/-- `pop_front` keeps a sorted list sorted. -/
theorem popFront_sorted {l : List Span} (h : Sorted l) : Sorted (popFront l).2 := by
  cases l with
  | nil => simp [popFront, Sorted]
  | cons f t => exact sorted_tail h

/-- A push at or after the last span's offset keeps the list sorted, whether it merges, appends or widens. -/
theorem push_sorted {n : Nat} (ys : List Span) (last s : Span) (hs : Sorted (ys ++ [last])) (h : last.off ≤ s.off) :
    Sorted (push n (ys ++ [last]) s) := by
  rw [push_snoc]
  by_cases h0 : s.len = 0
  · rw [if_pos h0]; exact hs
  · rw [if_neg h0]
    obtain ⟨hy, hyl⟩ := sorted_snoc.1 hs
    by_cases h1 : Touch last s ∨ ys.length + 1 = n
    · rw [if_pos h1]
      refine sorted_snoc.2 ⟨hy, fun y hy' => ?_⟩
      have := hyl y hy'
      simp only [Span.hull]; omega
    · rw [if_neg h1]
      have hn : ¬ (last.off ≤ s.off ∧ s.off ≤ last.off + last.len) := fun hh => h1 (Or.inl hh)
      by_cases h2 : ys.length + 1 < n
      · rw [if_pos h2]
        have : Sorted ((ys ++ [last]) ++ [s]) := sorted_snoc.2 ⟨hs, fun y hy' => by
          rcases List.mem_append.1 hy' with hh | hh
          · have := hyl y hh; omega
          · simp at hh; subst hh; omega⟩
        simpa using this
      · rw [if_neg h2]; exact hs

/-- `push_front` of a span that ends before the first one keeps the list sorted. -/
theorem pushFront_sorted {n : Nat} (f : Span) (t : List Span) (s : Span) (hs : Sorted (f :: t))
    (h : s.off + s.len ≤ f.off) : Sorted (pushFront n (f :: t) s) := by
  unfold pushFront
  by_cases h0 : s.len = 0
  · rw [if_pos h0]; exact hs
  · rw [if_neg h0]
    obtain ⟨hf, ht⟩ := List.pairwise_cons.1 hs
    by_cases h1 : (f :: t).length = n
    · rw [if_pos h1]
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, ht⟩
      have := hf y hy
      simp only [Span.hull]; omega
    · rw [if_neg h1]
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, hs⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · have := hf y hy; omega

/-! ## Exact multiplicity below capacity -/

theorem push_length_succ {n : Nat} (l : List Span) (s : Span) : (push n l s).length ≤ l.length + 1 := by
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rw [push_nil]; repeat' split
    all_goals simp
  · rw [push_snoc]
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
    repeat' split
    all_goals simp

/-- A push *widened*: the list was full, the span non-empty and it did not touch the last span, so `push` replaced
the last span by the hull and the bytes in the gap are covered twice over. This is the one documented lossy case. -/
def Wid (n : Nat) (l : List Span) (s : Span) : Prop :=
  s.len ≠ 0 ∧ ∃ ys last, l = ys ++ [last] ∧ ¬ Touch last s ∧ ys.length + 1 = n

theorem not_wid_of_room {n : Nat} {l : List Span} (hl : l.length < n) (s : Span) : ¬ Wid n l s := by
  rintro ⟨_, ys, last, rfl, _, h⟩
  simp at hl; omega

/-- Without widening (and within capacity) a push of a span disjoint from the list adds the span's bytes once and no
others: the case the scheduler is in whenever no list overflowed. -/
theorem push_mult_nw {n : Nat} (hn : 0 < n) {l : List Span} (hl : l.length ≤ n) (s : Span) (hnw : ¬ Wid n l s)
    (hd : ∀ x, s.Mem x → mult l x = 0) (x : Nat) :
    mult (push n l s) x = mult l x + (if s.Mem x then 1 else 0) := by
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rw [push_nil]
    by_cases h0 : s.len = 0
    · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
      simp [h0, hs, mult]
    · simp [h0, hn, mult]
  · simp only [List.length_append, List.length_singleton] at hl
    rw [push_snoc]
    by_cases h0 : s.len = 0
    · have hs : ¬ s.Mem x := by simp only [Span.Mem]; omega
      rw [if_pos h0]; simp [hs]
    · rw [if_neg h0]
      by_cases h1 : Touch last s ∨ ys.length + 1 = n
      · have ht : Touch last s := by
          rcases h1 with h1 | h1
          · exact h1
          · by_cases ht : Touch last s
            · exact ht
            · exact absurd ⟨h0, ys, last, rfl, ht, h1⟩ hnw
        rw [if_pos h1]
        have hs0 := hd s.off ⟨Nat.le_refl _, by omega⟩
        rw [mult_append, mult_single] at hs0
        have hlast : ¬ last.Mem s.off := by
          intro hm; simp [hm] at hs0
        have hfin : s.off = last.off + last.len := by
          simp only [Span.Mem] at hlast; have := ht.1; have := ht.2; omega
        rw [mult_append, mult_append, mult_single, mult_single]
        by_cases hx1 : last.Mem x
        · have hx2 : ¬ s.Mem x := by simp only [Span.Mem] at hx1 ⊢; omega
          have hh : (Span.hull last s).Mem x := (Span.hull_mem_touch ht.1 ht.2 x).2 (Or.inl hx1)
          simp [hx1, hx2, hh, mult]
        · by_cases hx2 : s.Mem x
          · have hh : (Span.hull last s).Mem x := (Span.hull_mem_touch ht.1 ht.2 x).2 (Or.inr hx2)
            simp [hx1, hx2, hh, mult]
          · have hh : ¬ (Span.hull last s).Mem x := fun hh =>
              (Span.hull_mem_touch ht.1 ht.2 x).1 hh |>.elim hx1 hx2
            simp [hx1, hx2, hh, mult]
      · rw [if_neg h1, if_pos (by omega)]
        simp [mult_append, mult]
        omega

/-- Below capacity, a push of a span disjoint from the list adds the span's bytes once. -/
theorem push_mult {n : Nat} {l : List Span} (hl : l.length < n) (s : Span)
    (hd : ∀ x, s.Mem x → mult l x = 0) (x : Nat) :
    mult (push n l s) x = mult l x + (if s.Mem x then 1 else 0) :=
  push_mult_nw (by omega) (by omega) s (not_wid_of_room hl s) hd x

/-- The summed lengths with no widening: a disjoint push adds exactly the span's length. -/
theorem push_total_nw {n : Nat} (hn : 0 < n) {l : List Span} (hl : l.length ≤ n) (s : Span) (hnw : ¬ Wid n l s)
    (hd : ∀ x, s.Mem x → mult l x = 0) :
    total (push n l s) = total l + s.len := by
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rw [push_nil]
    by_cases h0 : s.len = 0
    · simp [h0, total]
    · simp [h0, hn, total]
  · simp only [List.length_append, List.length_singleton] at hl
    rw [push_snoc]
    by_cases h0 : s.len = 0
    · rw [if_pos h0]; simp [h0]
    · rw [if_neg h0]
      by_cases h1 : Touch last s ∨ ys.length + 1 = n
      · have ht : Touch last s := by
          rcases h1 with h1 | h1
          · exact h1
          · by_cases ht : Touch last s
            · exact ht
            · exact absurd ⟨h0, ys, last, rfl, ht, h1⟩ hnw
        rw [if_pos h1]
        have hs0 := hd s.off ⟨Nat.le_refl _, by omega⟩
        rw [mult_append, mult_single] at hs0
        have hlast : ¬ last.Mem s.off := by
          intro hm; simp [hm] at hs0
        have hfin : s.off = last.off + last.len := by
          simp only [Span.Mem] at hlast; have := ht.1; have := ht.2; omega
        rw [total_append, total_append]
        simp only [total, Span.hull]
        omega
      · rw [if_neg h1, if_pos (by omega)]
        simp [total_append, total]
        omega

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.push_length_le
#audit_axioms Vinc.ValuesSched.push_cov
#audit_axioms Vinc.ValuesSched.push_cov_iff_room
#audit_axioms Vinc.ValuesSched.push_cov_iff_touch
#audit_axioms Vinc.ValuesSched.push_cov_hull
#audit_axioms Vinc.ValuesSched.push_bounded
#audit_axioms Vinc.ValuesSched.pushFront_length_le
#audit_axioms Vinc.ValuesSched.pushFront_cov
#audit_axioms Vinc.ValuesSched.pushFront_bounded
#audit_axioms Vinc.ValuesSched.pushFront_mult_of_room
#audit_axioms Vinc.ValuesSched.push_mult_nw
#audit_axioms Vinc.ValuesSched.push_total_nw
#audit_axioms Vinc.ValuesSched.push_length_succ
#audit_axioms Vinc.ValuesSched.popFront_spec
#audit_axioms Vinc.ValuesSched.popFront_sorted
#audit_axioms Vinc.ValuesSched.push_sorted
#audit_axioms Vinc.ValuesSched.pushFront_sorted
#audit_axioms Vinc.ValuesSched.totalSat_eq
#audit_axioms Vinc.ValuesSched.Span.endSat_eq
#audit_axioms Vinc.ValuesSched.not_wid_of_room
