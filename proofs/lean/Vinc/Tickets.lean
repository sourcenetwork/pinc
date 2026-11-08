import Vinc.Axioms

/-!
# The ticket stores

A model of the slot arithmetic of `vinc-security/src/tickets.rs`. A store is a list of `N` slots (`Option Slot`):
`ServerTickets` and `ClientTickets` are arrays of `N` optional slots, `victim` picks where an issued ticket goes
(the first empty slot, else the first expired one, else the one with the lowest `(stamp, index)`), `remove` empties a
slot, and `ClientTickets::take` drops the expired tickets and removes the matching ticket with the greatest stamp (the
last one on a tie, as `Iterator::max_by_key`). Times and stamps are `Nat`s; the code's `u64` comparisons are the same
comparisons, and the stamp is a wrapping counter that does not wrap in practice (2^64 tickets).

The server store does not check that two tickets have different ids: the single-use theorem for `find` assumes the
ids of the stored tickets are pairwise distinct (`Distinct`), which the 128 random bits of an id provide, and
proves the rest from that.
-/

namespace Vinc.Tickets

/-- A stored ticket: its id, who it resumes with (peer and ALPN, for the client store), expiry and stamp. -/
structure Slot where
  tid : List Nat
  peer : Nat
  alpn : Nat
  expiry : Nat
  stamp : Nat

abbrev Slots := List (Option Slot)

/-- Slots that hold a ticket. -/
def occ (l : Slots) : Nat := (l.filter Option.isSome).length

/-! ## Searching with an offset -/

/-- The index (offset by `i`) of the first element satisfying `p`. -/
def firstIdx {α : Type} (p : α → Bool) : List α → Nat → Option Nat
  | [], _ => none
  | x :: l, i => if p x then some i else firstIdx p l (i + 1)

theorem firstIdx_none_iff {α : Type} (p : α → Bool) : ∀ (l : List α) (i : Nat),
    firstIdx p l i = none ↔ ∀ (j : Nat) (x : α), l[j]? = some x → p x = false := by
  intro l
  induction l with
  | nil => intro i; simp [firstIdx]
  | cons x l ih =>
    intro i
    simp only [firstIdx]
    by_cases hx : p x = true
    · simp only [hx, ite_true]
      constructor
      · intro h; cases h
      · intro h; have := h 0 x (by simp); simp_all
    · simp only [hx, Bool.false_eq_true, ite_false]
      rw [ih]
      constructor
      · intro h j y hy
        cases j with
        | zero => simp at hy; subst hy; simpa using hx
        | succ j => exact h j y (by simpa using hy)
      · intro h j y hy; exact h (j + 1) y (by simpa using hy)

theorem firstIdx_some {α : Type} (p : α → Bool) : ∀ (l : List α) (i k : Nat), firstIdx p l i = some k →
    i ≤ k ∧ ∃ x, l[k - i]? = some x ∧ p x = true := by
  intro l
  induction l with
  | nil => intro i k h; simp [firstIdx] at h
  | cons x l ih =>
    intro i k h
    simp only [firstIdx] at h
    by_cases hx : p x = true
    · simp only [hx, ite_true] at h
      cases h
      exact ⟨Nat.le_refl _, x, by simp, hx⟩
    · simp only [hx, Bool.false_eq_true, ite_false] at h
      obtain ⟨hik, y, hy, hp⟩ := ih (i + 1) k h
      refine ⟨by omega, y, ?_, hp⟩
      have : k - i = (k - (i + 1)) + 1 := by omega
      rw [this]; simpa using hy

/-- It is the first: nothing before it satisfies `p`. -/
theorem firstIdx_first {α : Type} (p : α → Bool) : ∀ (l : List α) (i k : Nat), firstIdx p l i = some k →
    ∀ (j : Nat) (x : α), j < k - i → l[j]? = some x → p x = false := by
  intro l
  induction l with
  | nil => intro i k h; simp [firstIdx] at h
  | cons x l ih =>
    intro i k h j y hj hy
    simp only [firstIdx] at h
    by_cases hx : p x = true
    · simp only [hx, ite_true] at h; cases h; omega
    · simp only [hx, Bool.false_eq_true, ite_false] at h
      cases j with
      | zero => simp at hy; subst hy; simpa using hx
      | succ j => exact ih (i + 1) k h j y (by omega) (by simpa using hy)

/-! ## Where an issued ticket goes -/

def isEmpty (s : Option Slot) : Bool := s.isNone
def isExpired (now : Nat) (s : Option Slot) : Bool := s.any fun x => decide (x.expiry < now)

/-- `(lowest stamp, index)` over the occupied slots, from index `i`: `.min()` on the pairs. -/
def minAux : Slots → Nat → Option (Nat × Nat)
  | [], _ => none
  | none :: l, i => minAux l (i + 1)
  | some s :: l, i =>
    match minAux l (i + 1) with
    | none => some (s.stamp, i)
    | some (st, j) => if s.stamp ≤ st then some (s.stamp, i) else some (st, j)

/-- `victim`: the first empty slot, else the first expired one, else the least recently stamped. -/
def victim (l : Slots) (now : Nat) : Option Nat :=
  match firstIdx isEmpty l 0 with
  | some i => some i
  | none =>
    match firstIdx (isExpired now) l 0 with
    | some i => some i
    | none => (minAux l 0).map (·.2)

theorem minAux_none_iff : ∀ (l : Slots) (i : Nat),
    minAux l i = none ↔ ∀ (k : Nat) (t : Slot), l[k]? = some (some t) → False := by
  intro l
  induction l with
  | nil => intro i; simp [minAux]
  | cons x l ih =>
    intro i
    cases x with
    | none =>
      simp only [minAux]
      rw [ih]
      constructor
      · intro h k t hk
        cases k with
        | zero => simp at hk
        | succ k => exact h k t (by simpa using hk)
      · intro h k t hk; exact h (k + 1) t (by simpa using hk)
    | some s =>
      simp only [minAux]
      constructor
      · intro h
        cases hm : minAux l (i + 1) with
        | none => rw [hm] at h; simp at h
        | some r => obtain ⟨a, b⟩ := r; rw [hm] at h; by_cases hle : s.stamp ≤ a <;> simp [hle] at h
      · intro h; exact absurd (h 0 s (by simp)) id

theorem minAux_some : ∀ (l : Slots) (i st j : Nat), minAux l i = some (st, j) →
    i ≤ j ∧ (∃ s, l[j - i]? = some (some s) ∧ s.stamp = st) ∧
      ∀ (k : Nat) (t : Slot), l[k]? = some (some t) → st ≤ t.stamp := by
  intro l
  induction l with
  | nil => intro i st j h; simp [minAux] at h
  | cons x l ih =>
    intro i st j h
    cases x with
    | none =>
      simp only [minAux] at h
      obtain ⟨h1, ⟨s, hs, hst⟩, h3⟩ := ih (i + 1) st j h
      refine ⟨by omega, ⟨s, ?_, hst⟩, ?_⟩
      · have : j - i = (j - (i + 1)) + 1 := by omega
        rw [this]; simpa using hs
      · intro k t hk
        cases k with
        | zero => simp at hk
        | succ k => exact h3 k t (by simpa using hk)
    | some s =>
      simp only [minAux] at h
      cases hm : minAux l (i + 1) with
      | none =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Nat.le_refl _, ⟨s, by simp, rfl⟩, ?_⟩
        intro k t hk
        cases k with
        | zero => simp at hk; subst hk; exact Nat.le_refl _
        | succ k =>
          -- no occupied slot in the tail
          exfalso
          exact (minAux_none_iff l (i + 1)).1 hm k t (by simpa using hk)
      | some r =>
        obtain ⟨st', j'⟩ := r
        rw [hm] at h
        obtain ⟨h1, ⟨s', hs', hst'⟩, h3⟩ := ih (i + 1) st' j' hm
        by_cases hle : s.stamp ≤ st'
        · simp only [hle, ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Nat.le_refl _, ⟨s, by simp, rfl⟩, ?_⟩
          intro k t hk
          cases k with
          | zero => simp at hk; subst hk; exact Nat.le_refl _
          | succ k => have := h3 k t (by simpa using hk); omega
        · simp only [hle, ite_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by omega, ⟨s', ?_, hst'⟩, ?_⟩
          · have : j' - i = (j' - (i + 1)) + 1 := by omega
            rw [this]; simpa using hs'
          · intro k t hk
            cases k with
            | zero => simp at hk; subst hk; omega
            | succ k => exact h3 k t (by simpa using hk)


theorem victim_lt {l : Slots} {now j : Nat} (h : victim l now = some j) : j < l.length := by
  unfold victim at h
  cases e1 : firstIdx isEmpty l 0 with
  | some i =>
    rw [e1] at h; cases h
    obtain ⟨_, x, hx, _⟩ := firstIdx_some _ _ _ _ e1
    exact (List.getElem?_eq_some_iff.mp hx).1
  | none =>
    rw [e1] at h
    cases e2 : firstIdx (isExpired now) l 0 with
    | some i =>
      rw [e2] at h; cases h
      obtain ⟨_, x, hx, _⟩ := firstIdx_some _ _ _ _ e2
      exact (List.getElem?_eq_some_iff.mp hx).1
    | none =>
      rw [e2] at h
      cases e3 : minAux l 0 with
      | none => rw [e3] at h; simp at h
      | some r =>
        obtain ⟨st, j'⟩ := r
        rw [e3] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨_, ⟨s, hs, _⟩, _⟩ := minAux_some _ _ _ _ e3
        exact (List.getElem?_eq_some_iff.mp hs).1

/-- A store with no slots never offers a victim, and one with a slot always does. -/
theorem victim_none_iff (l : Slots) (now : Nat) : victim l now = none ↔ l = [] := by
  constructor
  · intro h
    unfold victim at h
    cases e1 : firstIdx isEmpty l 0 with
    | some i => rw [e1] at h; cases h
    | none =>
      rw [e1] at h
      cases e2 : firstIdx (isExpired now) l 0 with
      | some i => rw [e2] at h; cases h
      | none =>
        rw [e2] at h
        cases e3 : minAux l 0 with
        | some r => rw [e3] at h; simp at h
        | none =>
          cases l with
          | nil => rfl
          | cons x l =>
            exfalso
            cases x with
            | none => exact absurd ((firstIdx_none_iff _ _ _).1 e1 0 none (by simp)) (by simp [isEmpty])
            | some t => exact (minAux_none_iff _ _).1 e3 0 t (by simp)
  · rintro rfl; simp [victim, firstIdx, minAux]

/-- When there is an empty slot, the victim is empty (nothing is evicted). -/
theorem victim_empty {l : Slots} {now j : Nat} (h : victim l now = some j) (hex : ∃ k : Nat, l[k]? = some none) :
    l[j]? = some none := by
  unfold victim at h
  cases e1 : firstIdx isEmpty l 0 with
  | some i =>
    rw [e1] at h; cases h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e1
    cases x with
    | none => simpa using hx
    | some _ => simp [isEmpty] at hp
  | none =>
    obtain ⟨k, hk⟩ := hex
    exact absurd ((firstIdx_none_iff _ _ _).1 e1 k none hk) (by simp [isEmpty])

/-- With no empty slot but an expired one, the victim is expired. -/
theorem victim_expired {l : Slots} {now j : Nat} (h : victim l now = some j) (hne : ∀ k : Nat, l[k]? ≠ some none)
    (hex : ∃ (k : Nat) (s : Slot), l[k]? = some (some s) ∧ s.expiry < now) : ∃ s, l[j]? = some (some s) ∧ s.expiry < now := by
  unfold victim at h
  cases e1 : firstIdx isEmpty l 0 with
  | some i =>
    rw [e1] at h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e1
    cases x with
    | none => exact absurd (by simpa using hx) (hne i)
    | some _ => simp [isEmpty] at hp
  | none =>
    rw [e1] at h
    cases e2 : firstIdx (isExpired now) l 0 with
    | some i =>
      rw [e2] at h; cases h
      obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e2
      cases x with
      | none => simp [isExpired] at hp
      | some t =>
        simp only [isExpired, Option.any_some, decide_eq_true_eq] at hp
        exact ⟨t, by simpa using hx, hp⟩
    | none =>
      obtain ⟨k, s, hk, hs⟩ := hex
      have := (firstIdx_none_iff _ _ _).1 e2 k (some s) hk
      simp [isExpired, hs] at this

/-- With no empty and no expired slot, the victim is the slot with the lowest stamp. -/
theorem victim_min {l : Slots} {now j : Nat} (h : victim l now = some j) (hne : ∀ k : Nat, l[k]? ≠ some none)
    (hfresh : ∀ (k : Nat) (s : Slot), l[k]? = some (some s) → ¬ s.expiry < now) :
    ∃ s, l[j]? = some (some s) ∧ ∀ (k : Nat) (t : Slot), l[k]? = some (some t) → s.stamp ≤ t.stamp := by
  unfold victim at h
  cases e1 : firstIdx isEmpty l 0 with
  | some i =>
    rw [e1] at h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e1
    cases x with
    | none => exact absurd (by simpa using hx) (hne i)
    | some _ => simp [isEmpty] at hp
  | none =>
    rw [e1] at h
    cases e2 : firstIdx (isExpired now) l 0 with
    | some i =>
      rw [e2] at h
      obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e2
      cases x with
      | none => simp [isExpired] at hp
      | some t =>
        simp only [isExpired, Option.any_some, decide_eq_true_eq] at hp
        exact absurd hp (hfresh i t (by simpa using hx))
    | none =>
      rw [e2] at h
      cases e3 : minAux l 0 with
      | none => rw [e3] at h; simp at h
      | some r =>
        obtain ⟨st, j'⟩ := r
        rw [e3] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨_, ⟨s, hs, hst⟩, h3⟩ := minAux_some _ _ _ _ e3
        exact ⟨s, by simpa using hs, fun k t hk => by have := h3 k t hk; omega⟩

/-! ## Issuing -/

/-- `issue_batch` for one ticket: place it in the victim slot, if there is one. -/
def issueAt (l : Slots) (now : Nat) (s : Slot) : Slots × Bool :=
  match victim l now with
  | some j => (l.set j (some s), true)
  | none => (l, false)

theorem issueAt_length (l : Slots) (now : Nat) (s : Slot) : (issueAt l now s).1.length = l.length := by
  unfold issueAt; cases victim l now <;> simp

theorem occ_le (l : Slots) : occ l ≤ l.length := List.length_filter_le _ _

/-- With no slot (`N = 0`) nothing is stored and nothing is issued. -/
theorem issueAt_nil (now : Nat) (s : Slot) : issueAt [] now s = ([], false) := by
  have := (victim_none_iff [] now).2 rfl
  simp [issueAt, this]

/-- The ticket lands in the victim slot when there is one. -/
theorem issueAt_places {l : Slots} {now : Nat} {s : Slot} (h : (issueAt l now s).2 = true) :
    ∃ j, victim l now = some j ∧ (issueAt l now s).1[j]? = some (some s) := by
  unfold issueAt at h ⊢
  cases hv : victim l now with
  | none => rw [hv] at h; simp at h
  | some j =>
    refine ⟨j, rfl, ?_⟩
    simp only
    have := victim_lt hv
    simp [List.getElem?_set_self this]

/-- An occupied slot is evicted only when no slot is empty, and an unexpired one only when none is expired. -/
theorem issueAt_evicts {l : Slots} {now j : Nat} {old : Slot} (hv : victim l now = some j)
    (hold : l[j]? = some (some old)) :
    (∀ k : Nat, l[k]? ≠ some none) ∧
      (¬ old.expiry < now → ∀ (k : Nat) (s : Slot), l[k]? = some (some s) → ¬ s.expiry < now) := by
  have hne : ∀ k : Nat, l[k]? ≠ some none := by
    intro k hk
    have := victim_empty hv ⟨k, hk⟩
    rw [hold] at this; cases this
  refine ⟨hne, fun hfresh k s hk hexp => ?_⟩
  obtain ⟨s', hs', hexp'⟩ := victim_expired hv hne ⟨k, s, hk, hexp⟩
  rw [hold] at hs'
  simp only [Option.some.injEq] at hs'
  subst hs'
  exact hfresh hexp'

/-- The stores reachable from empty by issuing and removing. -/
inductive Reach (N : Nat) : Slots → Prop where
  | init : Reach N (List.replicate N none)
  | issue {l} (now : Nat) (s : Slot) : Reach N l → Reach N (issueAt l now s).1
  | remove {l} (i : Nat) : Reach N l → Reach N (l.set i none)

/-- A store always has exactly `N` slots, so it holds at most `N` tickets. -/
theorem reach_length {N : Nat} {l : Slots} (h : Reach N l) : l.length = N := by
  induction h with
  | init => simp
  | issue now s _ ih => rw [issueAt_length, ih]
  | remove i _ ih => simp [ih]

theorem reach_occ_le {N : Nat} {l : Slots} (h : Reach N l) : occ l ≤ N := by
  have := occ_le l
  rw [reach_length h] at this
  exact this

/-- `N = 0` stores nothing. -/
theorem reach_zero {l : Slots} (h : Reach 0 l) : occ l = 0 := by
  have := reach_occ_le h
  omega


/-! ## Single use -/

/-- `find`: the first slot holding a ticket with this id. -/
def find (l : Slots) (tid : List Nat) : Option Nat :=
  firstIdx (fun x => x.any fun s => decide (s.tid = tid)) l 0

/-- `remove`: empty a slot. -/
def remove (l : Slots) (i : Nat) : Slots := l.set i none

/-- The ticket in slot `i`, if any. -/
def get (l : Slots) (i : Nat) : Option Slot := (l[i]?).getD none

/-- The tickets in the store have pairwise different ids. The store does not check this; 128 random bits make a
collision negligible. -/
def Distinct (l : Slots) : Prop :=
  ∀ (i j : Nat) (s t : Slot), l[i]? = some (some s) → l[j]? = some (some t) → s.tid = t.tid → i = j

theorem find_get {l : Slots} {tid : List Nat} {i : Nat} (h : find l tid = some i) :
    ∃ s, l[i]? = some (some s) ∧ s.tid = tid := by
  obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ h
  cases x with
  | none => simp at hp
  | some s => exact ⟨s, by simpa using hx, by simpa using hp⟩

/-- A removed ticket is gone from its slot. -/
theorem remove_get {l : Slots} {i : Nat} (h : i < l.length) : get (remove l i) i = none := by
  simp [get, remove, List.getElem?_set_self h]

/-- After the found ticket is removed, `find` never answers that slot again. -/
theorem find_remove_ne {l : Slots} {tid : List Nat} {i j : Nat} (hf : find l tid = some i)
    (h : find (remove l i) tid = some j) : j ≠ i := by
  obtain ⟨s, hs, _⟩ := find_get hf
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨t, ht, _⟩ := find_get h
  rintro rfl
  simp [remove, List.getElem?_set_self hi] at ht

/-- Single use: if the stored ids are distinct, a ticket that was found and removed is never found again. -/
theorem find_remove_none {l : Slots} {tid : List Nat} {i : Nat} (hd : Distinct l) (hf : find l tid = some i) :
    find (remove l i) tid = none := by
  obtain ⟨s, hs, hst⟩ := find_get hf
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp hs).1
  unfold find
  rw [firstIdx_none_iff]
  intro j x hx
  cases x with
  | none => rfl
  | some t =>
    refine Classical.byContradiction fun hp => ?_
    have hpt : t.tid = tid := by simpa using hp
    by_cases hji : j = i
    · subst hji; simp [remove, List.getElem?_set_self hi] at hx
    · have hx' : l[j]? = some (some t) := by
        simpa [remove, List.getElem?_set_ne (Ne.symm hji)] using hx
      exact hji (hd j i t s hx' hs (by rw [hpt, hst]))

/-! ## The client store -/

/-- Expired tickets are dropped. -/
def dropExpired (now : Nat) (l : Slots) : Slots :=
  l.map fun s => s.bind fun x => if x.expiry < now then none else some x

def matchesKey (peer alpn : Nat) (s : Slot) : Bool := decide (s.peer = peer ∧ s.alpn = alpn)

/-- `(stamp, index)` of the matching ticket with the greatest stamp, the last one on a tie
(`Iterator::max_by_key`), from index `i`. -/
def bestAux (peer alpn : Nat) : Slots → Nat → Option (Nat × Nat)
  | [], _ => none
  | x :: l, i =>
    match x with
    | none => bestAux peer alpn l (i + 1)
    | some s =>
      if matchesKey peer alpn s then
        match bestAux peer alpn l (i + 1) with
        | none => some (s.stamp, i)
        | some (st, j) => if s.stamp ≤ st then some (st, j) else some (s.stamp, i)
      else bestAux peer alpn l (i + 1)

/-- `ClientTickets::take`: the new store and the ticket taken. -/
def take (l : Slots) (now peer alpn : Nat) : Slots × Option Slot :=
  let d := dropExpired now l
  match bestAux peer alpn d 0 with
  | none => (d, none)
  | some (_, i) => (d.set i none, (d[i]?).getD none)

theorem bestAux_none_iff (peer alpn : Nat) : ∀ (l : Slots) (i : Nat), bestAux peer alpn l i = none ↔
    ∀ (k : Nat) (t : Slot), l[k]? = some (some t) → matchesKey peer alpn t = false := by
  intro l
  induction l with
  | nil => intro i; simp [bestAux]
  | cons x l ih =>
    intro i
    cases x with
    | none =>
      simp only [bestAux]
      rw [ih]
      constructor
      · intro h k t hk
        cases k with
        | zero => simp at hk
        | succ k => exact h k t (by simpa using hk)
      · intro h k t hk; exact h (k + 1) t (by simpa using hk)
    | some s =>
      simp only [bestAux]
      by_cases hm : matchesKey peer alpn s = true
      · simp only [hm, ite_true]
        constructor
        · intro h
          exfalso
          cases e : bestAux peer alpn l (i + 1) with
          | none => rw [e] at h; simp at h
          | some r => obtain ⟨a, b⟩ := r; rw [e] at h; by_cases hle : s.stamp ≤ a <;> simp [hle] at h
        · intro h; have := h 0 s (by simp); simp_all
      · simp only [hm, Bool.false_eq_true, ite_false]
        rw [ih]
        constructor
        · intro h k t hk
          cases k with
          | zero => simp at hk; subst hk; simpa using hm
          | succ k => exact h k t (by simpa using hk)
        · intro h k t hk; exact h (k + 1) t (by simpa using hk)

theorem bestAux_some (peer alpn : Nat) : ∀ (l : Slots) (i st j : Nat), bestAux peer alpn l i = some (st, j) →
    i ≤ j ∧ (∃ s, l[j - i]? = some (some s) ∧ matchesKey peer alpn s = true ∧ s.stamp = st) ∧
      ∀ (k : Nat) (t : Slot), l[k]? = some (some t) → matchesKey peer alpn t = true → t.stamp ≤ st := by
  intro l
  induction l with
  | nil => intro i st j h; simp [bestAux] at h
  | cons x l ih =>
    intro i st j h
    -- the result of the tail, used in every case
    have tail : bestAux peer alpn l (i + 1) = some (st, j) →
        i ≤ j ∧ (∃ s, (x :: l)[j - i]? = some (some s) ∧ matchesKey peer alpn s = true ∧ s.stamp = st) := by
      intro h'
      obtain ⟨h1, ⟨s, hs, hm, hst⟩, _⟩ := ih (i + 1) st j h'
      refine ⟨by omega, s, ?_, hm, hst⟩
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this]; simpa using hs
    cases x with
    | none =>
      simp only [bestAux] at h
      obtain ⟨_, _, h3⟩ := ih (i + 1) st j h
      refine ⟨(tail h).1, (tail h).2, ?_⟩
      intro k t hk hm
      cases k with
      | zero => simp at hk
      | succ k => exact h3 k t (by simpa using hk) hm
    | some s =>
      simp only [bestAux] at h
      by_cases hm : matchesKey peer alpn s = true
      · simp only [hm, ite_true] at h
        cases e : bestAux peer alpn l (i + 1) with
        | none =>
          rw [e] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Nat.le_refl _, ⟨s, by simp, hm, rfl⟩, ?_⟩
          intro k t hk hmt
          cases k with
          | zero => simp at hk; subst hk; exact Nat.le_refl _
          | succ k => exact absurd ((bestAux_none_iff peer alpn l (i + 1)).1 e k t (by simpa using hk)) (by simp [hmt])
        | some r =>
          obtain ⟨st', j'⟩ := r
          rw [e] at h
          obtain ⟨h1, ⟨s', hs', hm', hst'⟩, h3⟩ := ih (i + 1) st' j' e
          by_cases hle : s.stamp ≤ st'
          · simp only [hle, ite_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨(tail e).1, (tail e).2, ?_⟩
            intro k t hk hmt
            cases k with
            | zero => simp at hk; subst hk; exact hle
            | succ k => exact h3 k t (by simpa using hk) hmt
          · simp only [hle, ite_false, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨Nat.le_refl _, ⟨s, by simp, hm, rfl⟩, ?_⟩
            intro k t hk hmt
            cases k with
            | zero => simp at hk; subst hk; exact Nat.le_refl _
            | succ k => have := h3 k t (by simpa using hk) hmt; omega
      · simp only [hm, Bool.false_eq_true, ite_false] at h
        obtain ⟨_, _, h3⟩ := ih (i + 1) st j h
        refine ⟨(tail h).1, (tail h).2, ?_⟩
        intro k t hk hmt
        cases k with
        | zero => simp at hk; subst hk; exact absurd hmt hm
        | succ k => exact h3 k t (by simpa using hk) hmt

theorem dropExpired_get {now : Nat} {l : Slots} {j : Nat} {x : Slot}
    (h : (dropExpired now l)[j]? = some (some x)) : l[j]? = some (some x) ∧ ¬ x.expiry < now := by
  simp only [dropExpired, List.getElem?_map] at h
  cases hl : l[j]? with
  | none => rw [hl] at h; simp at h
  | some y =>
    rw [hl] at h
    cases y with
    | none => simp at h
    | some z =>
      simp only [Option.map_some, Option.some.injEq, Option.bind_some] at h
      by_cases hz : z.expiry < now
      · simp [hz] at h
      · simp only [hz, ite_false, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hz⟩

theorem occ_cons (x : Option Slot) (l : Slots) : occ (x :: l) = (if x.isSome then 1 else 0) + occ l := by
  cases x <;> simp [occ] <;> omega

theorem occ_set_none : ∀ (l : Slots) (i : Nat) (s : Slot), l[i]? = some (some s) → occ (l.set i none) + 1 = occ l := by
  intro l
  induction l with
  | nil => intro i s h; simp at h
  | cons x l ih =>
    intro i s h
    cases i with
    | zero => simp at h; subst h; simp [occ_cons]; omega
    | succ i =>
      have := ih i s (by simpa using h)
      rw [List.set_cons_succ, occ_cons, occ_cons]
      omega

/-- A `take` that returns a ticket removes exactly that ticket (from the store with its expired tickets dropped),
the ticket matches the peer and ALPN, it has the greatest stamp among the matches, and it was not expired. -/
theorem take_some {l l' : Slots} {now peer alpn : Nat} {s : Slot} (h : take l now peer alpn = (l', some s)) :
    ∃ i, (dropExpired now l)[i]? = some (some s) ∧ l' = (dropExpired now l).set i none ∧
      occ l' + 1 = occ (dropExpired now l) ∧ matchesKey peer alpn s = true ∧ ¬ s.expiry < now ∧
      ∀ (k : Nat) (t : Slot), (dropExpired now l)[k]? = some (some t) → matchesKey peer alpn t = true →
        t.stamp ≤ s.stamp := by
  unfold take at h
  simp only at h
  cases e : bestAux peer alpn (dropExpired now l) 0 with
  | none => rw [e] at h; simp at h
  | some r =>
    obtain ⟨st, i⟩ := r
    rw [e] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hs⟩ := h
    obtain ⟨_, ⟨s', hs', hm, hst⟩, h3⟩ := bestAux_some _ _ _ _ _ _ e
    simp only [Nat.sub_zero] at hs'
    rw [hs'] at hs
    simp only [Option.getD_some, Option.some.injEq] at hs
    subst hs
    exact ⟨i, hs', rfl, occ_set_none _ _ _ hs', hm, (dropExpired_get hs').2, by
      intro k t hk hmt; have := h3 k t hk hmt; omega⟩

/-- When `take` finds nothing, no unexpired ticket matches the peer and ALPN, and only the expired ones were
dropped. -/
theorem take_none {l l' : Slots} {now peer alpn : Nat} (h : take l now peer alpn = (l', none)) :
    l' = dropExpired now l ∧ ∀ (k : Nat) (t : Slot), (dropExpired now l)[k]? = some (some t) →
      matchesKey peer alpn t = false := by
  unfold take at h
  simp only at h
  cases e : bestAux peer alpn (dropExpired now l) 0 with
  | none =>
    rw [e] at h
    simp only [Prod.mk.injEq, and_true] at h
    exact ⟨h.symm, (bestAux_none_iff _ _ _ _).1 e⟩
  | some r =>
    obtain ⟨st, i⟩ := r
    rw [e] at h
    obtain ⟨_, ⟨s', hs', _, _⟩, _⟩ := bestAux_some _ _ _ _ _ _ e
    simp only [Nat.sub_zero] at hs'
    simp [hs'] at h

/-- A ticket taken is not taken twice: two successive takes return tickets from two different slots. -/
theorem take_twice {l l₁ l₂ : Slots} {now peer alpn : Nat} {s s₂ : Slot} (h₁ : take l now peer alpn = (l₁, some s))
    (h₂ : take l₁ now peer alpn = (l₂, some s₂)) :
    ∃ i j : Nat, i ≠ j ∧ (dropExpired now l)[i]? = some (some s) ∧ (dropExpired now l)[j]? = some (some s₂) := by
  obtain ⟨i, hi, hl₁, _⟩ := take_some h₁
  obtain ⟨j, hj, _⟩ := take_some h₂
  have hj' := (dropExpired_get hj).1
  have hilt : i < (dropExpired now l).length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨i, j, ?_, hi, ?_⟩
  · rintro rfl
    rw [hl₁] at hj'
    simp [List.getElem?_set_self hilt] at hj'
  · rw [hl₁] at hj'
    by_cases hij : i = j
    · subst hij; simp [List.getElem?_set_self hilt] at hj'
    · simpa [List.getElem?_set_ne hij] using hj'

end Vinc.Tickets

#audit_axioms Vinc.Tickets.victim_lt
#audit_axioms Vinc.Tickets.victim_none_iff
#audit_axioms Vinc.Tickets.victim_empty
#audit_axioms Vinc.Tickets.victim_expired
#audit_axioms Vinc.Tickets.victim_min
#audit_axioms Vinc.Tickets.issueAt_length
#audit_axioms Vinc.Tickets.issueAt_nil
#audit_axioms Vinc.Tickets.issueAt_places
#audit_axioms Vinc.Tickets.issueAt_evicts
#audit_axioms Vinc.Tickets.reach_length
#audit_axioms Vinc.Tickets.reach_occ_le
#audit_axioms Vinc.Tickets.reach_zero
#audit_axioms Vinc.Tickets.remove_get
#audit_axioms Vinc.Tickets.find_remove_ne
#audit_axioms Vinc.Tickets.find_remove_none
#audit_axioms Vinc.Tickets.take_some
#audit_axioms Vinc.Tickets.take_none
#audit_axioms Vinc.Tickets.take_twice
