import Pinc.Axioms

/-!
# The ticket stores

A model of `pinc-security/src/tickets.rs`. A store is a list of `N` slots (`Option Slot`): `ServerTickets` and
`ClientTickets` are arrays of `N` optional slots with a clock that stamps every insertion. `victim` picks where an
inserted ticket goes (the first empty slot, else the first expired one, else the one with the lowest `(stamp, index)`),
`remove` empties a slot. Times and stamps are `Nat`s; the code's `u64` comparisons are the same comparisons, and the
stamp is a `wrapping_add` counter that does not wrap before 2^64 insertions (a documented ceiling; the model counts in
`Nat`).

This module holds the slot arithmetic and the server store. The server store draws ticket ids with `fresh_id`: at most
`ID_ATTEMPTS = 8` draws, each of which must differ from every stored id, else `Failure::TicketId`. The random
generator is the environment, so the model takes the sequence of draws as an arbitrary function (`draw p`, `none` when
the generator refuses) and proves, for every such sequence, that the stored ids stay pairwise distinct: the old
assumption "the ids of one store are distinct" is a theorem (`server_ids_distinct`). The client store is in
`Pinc.TicketsClient`, the export format in `Pinc.TicketsWire`.
-/

namespace Pinc.Tickets

/-- A node: the identity algorithm tag and the 32 node bytes (`NodeId`; equality is equality of both). -/
structure Peer where
  alg : Nat
  node : List Nat
  deriving DecidableEq

/-- A ticket as the stores keep and export it: peer, ALPN bytes, id, pre-shared key, AEAD tag, expiry and the
issuer's credit record bytes. -/
structure Tk where
  peer : Peer
  alpn : List Nat
  tid : List Nat
  psk : List Nat
  aead : Nat
  expiry : Nat
  credit : List Nat
  deriving DecidableEq

/-- A stored ticket and its stamp. -/
structure Slot where
  tk : Tk
  stamp : Nat

abbrev Slot.tid (s : Slot) : List Nat := s.tk.tid
abbrev Slot.peer (s : Slot) : Peer := s.tk.peer
abbrev Slot.alpn (s : Slot) : List Nat := s.tk.alpn
abbrev Slot.expiry (s : Slot) : Nat := s.tk.expiry

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

/-- The tickets in the store have pairwise different ids. The server store keeps this (`server_ids_distinct`). -/
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


/-! ## The server store -/

/-- The most draws `fresh_id` makes (`ID_ATTEMPTS`). -/
def idAttempts : Nat := 8
/-- The most tickets of one `issue_batch` (`MAX_BATCH`). -/
def maxBatch : Nat := 4
/-- Nanoseconds in a second. -/
def nsPerS : Nat := 1000000000
/-- `u64::MAX`. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- `expiry`: `now.saturating_add(lifetime_s.saturating_mul(NS_PER_S))`; the product of a `u32` and 10^9 fits a `u64`. -/
def expiryOf (now life : Nat) : Nat := min (now + life * nsPerS) u64Max

theorem expiryOf_ge (now life : Nat) (h : now ≤ u64Max) : now ≤ expiryOf now life := by
  unfold expiryOf; omega

theorem expiryOf_exact (now life : Nat) (h : now + life * nsPerS ≤ u64Max) : expiryOf now life = now + life * nsPerS := by
  unfold expiryOf; omega

/-- A store: the `N` slots and the clock that stamps insertions. -/
structure Store where
  slots : Slots
  clock : Nat

/-- A fresh store of `n` slots. -/
def Store.empty (n : Nat) : Store := ⟨List.replicate n none, 0⟩

/-- Why `issue_batch` fails: the generator refused, or no unused id turned up (`Failure::Randomness`, `Failure::TicketId`). -/
inductive Fail where
  | randomness
  | ticketId

/-- `fresh_id`: at most `k` draws from position `p` of the generator's output; the first draw that no stored ticket
has. `draw q` is the `q`-th draw (`none` if the generator refuses). Returns the result and the next position. -/
def freshId (l : Slots) (draw : Nat → Option (List Nat)) : Nat → Nat → Except Fail (List Nat) × Nat
  | 0, p => (.error .ticketId, p)
  | k + 1, p =>
    match draw p with
    | none => (.error .randomness, p)
    | some tid => if (find l tid).isNone then (.ok tid, p + 1) else freshId l draw k (p + 1)

/-- `issue_batch`: for each of `k` tickets draw a fresh id, stamp it with the next clock value and place it in the
victim slot. `mine` holds the slots this batch has filled: when `victim` finds no slot, or one of `mine`, the batch
ends there (after the draw and the clock step, as the code does) with the tickets already placed, so a ticket of the
batch never evicts another of the same batch. The code's `victim` skips the protected slots instead; the two agree on
every reachable store, because a slot of `mine` is neither empty nor expired (its expiry is at least `now`) and holds
a stamp above every other, so `victim` reaches one only when every other slot is protected or missing. The trace
replay of `issue_batch` checks the agreement on the code's runs. On a failure the tickets already placed stay stored
and the call returns the error, as the code does. `mk tid` is the ticket of the session with id `tid`. -/
def issueLoop (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) :
    Nat → Store → Nat → List Nat → Store × Except Fail (List (List Nat))
  | 0, st, _, _ => (st, .ok [])
  | k + 1, st, p, mine =>
    match (freshId st.slots draw idAttempts p).1 with
    | .error e => (st, .error e)
    | .ok tid =>
      match victim st.slots now with
      | none => (⟨st.slots, st.clock + 1⟩, .ok [])
      | some j =>
        if j ∈ mine then (⟨st.slots, st.clock + 1⟩, .ok [])
        else
          let rest := issueLoop mk now draw k ⟨(issueAt st.slots now ⟨mk tid, st.clock + 1⟩).1, st.clock + 1⟩
            (freshId st.slots draw idAttempts p).2 (j :: mine)
          (rest.1, rest.2.map (tid :: ·))

/-- `ServerTickets::issue_batch` with `count` asked: `min count MAX_BATCH` tickets. -/
def issueBatch (st : Store) (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) (count : Nat) :
    Store × Except Fail (List (List Nat)) :=
  issueLoop mk now draw (min count maxBatch) st 0 []

/-- Setting a slot: what an index holds afterwards. -/
theorem set_get_cases {α : Type} {l : List α} {j k : Nat} {x y : α} (h : (l.set j x)[k]? = some y) :
    (k = j ∧ y = x ∧ j < l.length) ∨ (k ≠ j ∧ l[k]? = some y) := by
  rw [List.getElem?_set] at h
  by_cases hjk : j = k
  · subst hjk
    by_cases hl : j < l.length
    · simp [hl] at h; exact Or.inl ⟨rfl, h.symm, hl⟩
    · simp [hl] at h
  · simp [hjk] at h; exact Or.inr ⟨fun e => hjk e.symm, h⟩

theorem freshId_fresh (l : Slots) (draw : Nat → Option (List Nat)) : ∀ (k p : Nat) (tid : List Nat),
    (freshId l draw k p).1 = .ok tid → find l tid = none := by
  intro k
  induction k with
  | zero => intro p tid h; simp [freshId] at h
  | succ k ih =>
    intro p tid h
    simp only [freshId] at h
    cases hd : draw p with
    | none => rw [hd] at h; simp at h
    | some t =>
      rw [hd] at h
      by_cases hf : (find l t).isNone = true
      · simp only [hf, ite_true] at h
        have : t = tid := by simpa using h
        subst this
        simpa using hf
      · simp only [hf, Bool.false_eq_true, ite_false] at h
        exact ih (p + 1) tid h

/-- `Tickets.issue_ids_distinct`: a drawn id that `fresh_id` accepts differs from the id of every stored ticket. -/
theorem issue_ids_distinct {l : Slots} {draw : Nat → Option (List Nat)} {k p : Nat} {tid : List Nat}
    (h : (freshId l draw k p).1 = .ok tid) : ∀ (i : Nat) (s : Slot), l[i]? = some (some s) → s.tid ≠ tid := by
  intro i s hs heq
  have hn := freshId_fresh l draw k p tid h
  unfold find at hn
  have := (firstIdx_none_iff _ _ _).1 hn i (some s) hs
  simp [heq] at this

/-- If every draw of the `k` attempts is an id that is already stored, `fresh_id` fails with `TicketId`. -/
theorem freshId_collide (l : Slots) (draw : Nat → Option (List Nat)) : ∀ (k p : Nat),
    (∀ i, i < k → ∃ tid, draw (p + i) = some tid ∧ find l tid ≠ none) → (freshId l draw k p).1 = .error .ticketId := by
  intro k
  induction k with
  | zero => intro p _; simp [freshId]
  | succ k ih =>
    intro p h
    obtain ⟨tid, hd, hf⟩ := h 0 (by omega)
    simp only [freshId, Nat.add_zero] at hd ⊢
    rw [hd]
    have : (find l tid).isNone = false := by
      cases e : find l tid with
      | none => exact absurd e hf
      | some _ => rfl
    simp only [this, Bool.false_eq_true, ite_false]
    apply ih
    intro i hi
    obtain ⟨t, ht, hft⟩ := h (i + 1) (by omega)
    exact ⟨t, by rw [show p + 1 + i = p + (i + 1) by omega]; exact ht, hft⟩

theorem freshId_refuse (l : Slots) (draw : Nat → Option (List Nat)) (k p : Nat) (h : draw p = none) :
    (freshId l draw (k + 1) p).1 = .error .randomness := by
  simp [freshId, h]

/-! ### Invariants of the server store -/

/-- Every stamp is at most the clock and no two stored tickets share a stamp: the stamps are the order of issue. -/
def StampInv (st : Store) : Prop :=
  (∀ (i : Nat) (s : Slot), st.slots[i]? = some (some s) → s.stamp ≤ st.clock) ∧
  ∀ (i j : Nat) (s t : Slot), st.slots[i]? = some (some s) → st.slots[j]? = some (some t) → s.stamp = t.stamp → i = j

theorem replicate_none_get {α : Type} {n i : Nat} {s : α} (h : (List.replicate n (none : Option α))[i]? = some (some s)) :
    False := by
  rw [List.getElem?_replicate] at h
  split at h <;> simp at h

theorem StampInv.empty (n : Nat) : StampInv (Store.empty n) := by
  constructor
  · intro i s h; exact (replicate_none_get h).elim
  · intro i j s t hs; exact (replicate_none_get hs).elim

theorem issueAt_distinct {l : Slots} {now : Nat} {s : Slot} (hd : Distinct l)
    (hf : ∀ (i : Nat) (t : Slot), l[i]? = some (some t) → t.tid ≠ s.tid) : Distinct (issueAt l now s).1 := by
  unfold issueAt
  cases hv : victim l now with
  | none => simpa using hd
  | some j =>
    simp only
    intro a b x y hx hy hxy
    rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
      rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
    · rfl
    · cases hxs
      exact absurd hxy.symm (hf b y hy')
    · cases hys
      exact absurd hxy (hf a x hx')
    · exact hd a b x y hx' hy' hxy

theorem issueAt_stamps {st : Store} (hs : StampInv st) (now : Nat) (s : Slot) (hst : s.stamp = st.clock + 1) :
    StampInv ⟨(issueAt st.slots now s).1, st.clock + 1⟩ := by
  unfold issueAt
  cases hv : victim st.slots now with
  | none =>
    simp only
    constructor
    · intro i t h; have := hs.1 i t h; simp only; omega
    · exact hs.2
  | some j =>
    simp only
    constructor
    · intro i t h
      simp only
      rcases set_get_cases h with ⟨rfl, hts, _⟩ | ⟨hne, h'⟩
      · cases hts; omega
      · have := hs.1 i t h'; omega
    · intro a b x y hx hy hxy
      simp only at hx hy
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
        rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
      · rfl
      · cases hxs
        have := hs.1 b y hy'; omega
      · cases hys
        have := hs.1 a x hx'; omega
      · exact hs.2 a b x y hx' hy' hxy

/-- The clock step alone keeps the stamp invariant. -/
theorem StampInv.tick {st : Store} (hs : StampInv st) : StampInv ⟨st.slots, st.clock + 1⟩ :=
  ⟨fun i t h => by have := hs.1 i t h; simp only; omega, hs.2⟩

theorem issueLoop_length (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat),
      (issueLoop mk now draw k st p mine).1.slots.length = st.slots.length := by
  intro k
  induction k with
  | zero => intro st p mine; simp [issueLoop]
  | succ k ih =>
    intro st p mine
    simp only [issueLoop]
    cases (freshId st.slots draw idAttempts p).1 with
    | error e => rfl
    | ok tid =>
      simp only
      cases victim st.slots now with
      | none => rfl
      | some j =>
        simp only
        split
        · rfl
        · rw [ih]; exact issueAt_length _ _ _

theorem issueLoop_distinct (mk : List Nat → Tk) (hmk : ∀ t, (mk t).tid = t) (now : Nat)
    (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat), Distinct st.slots →
      Distinct (issueLoop mk now draw k st p mine).1.slots := by
  intro k
  induction k with
  | zero => intro st p mine h; simpa [issueLoop] using h
  | succ k ih =>
    intro st p mine hd
    simp only [issueLoop]
    cases hf : (freshId st.slots draw idAttempts p).1 with
    | error e => exact hd
    | ok tid =>
      simp only
      cases victim st.slots now with
      | none => exact hd
      | some j =>
        simp only
        split
        · exact hd
        · apply ih
          apply issueAt_distinct hd
          intro i t ht
          show t.tid ≠ (mk tid).tid
          rw [hmk]
          exact issue_ids_distinct hf i t ht

theorem issueLoop_stamps (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat), StampInv st →
      StampInv (issueLoop mk now draw k st p mine).1 := by
  intro k
  induction k with
  | zero => intro st p mine h; simpa [issueLoop] using h
  | succ k ih =>
    intro st p mine hs
    simp only [issueLoop]
    cases (freshId st.slots draw idAttempts p).1 with
    | error e => exact hs
    | ok tid =>
      simp only
      cases victim st.slots now with
      | none => exact hs.tick
      | some j =>
        simp only
        split
        · exact hs.tick
        · exact ih _ _ _ (issueAt_stamps hs now _ rfl)

theorem issueLoop_reach {N : Nat} (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat), Reach N st.slots →
      Reach N (issueLoop mk now draw k st p mine).1.slots := by
  intro k
  induction k with
  | zero => intro st p mine h; simpa [issueLoop] using h
  | succ k ih =>
    intro st p mine hr
    simp only [issueLoop]
    cases (freshId st.slots draw idAttempts p).1 with
    | error e => exact hr
    | ok tid =>
      simp only
      cases victim st.slots now with
      | none => exact hr
      | some j =>
        simp only
        split
        · exact hr
        · exact ih _ _ _ (Reach.issue now _ hr)

/-- A slot the batch has already filled (one of `mine`) holds afterwards what it held before the rest of the batch. -/
theorem issueLoop_keep (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat) (i : Nat), i ∈ mine →
      (issueLoop mk now draw k st p mine).1.slots[i]? = st.slots[i]? := by
  intro k
  induction k with
  | zero => intro st p mine i _; simp [issueLoop]
  | succ k ih =>
    intro st p mine i hi
    simp only [issueLoop]
    cases (freshId st.slots draw idAttempts p).1 with
    | error e => rfl
    | ok tid =>
      simp only
      cases hv : victim st.slots now with
      | none => rfl
      | some j =>
        simp only
        split
        · rfl
        · rename_i hj
          rw [ih _ _ _ i (List.mem_cons_of_mem j hi)]
          simp only [issueAt, hv]
          exact List.getElem?_set_ne (fun e => by subst e; exact hj hi)

/-- Every id the loop returns is in the store it returns. -/
theorem issueLoop_stored (mk : List Nat → Tk) (hmk : ∀ t, (mk t).tid = t) (now : Nat)
    (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat) (ids : List (List Nat)),
      (issueLoop mk now draw k st p mine).2 = .ok ids → ∀ tid ∈ ids,
        ∃ (i : Nat) (s : Slot), (issueLoop mk now draw k st p mine).1.slots[i]? = some (some s) ∧ s.tid = tid := by
  intro k
  induction k with
  | zero =>
    intro st p mine ids h t ht
    simp only [issueLoop, Except.ok.injEq] at h
    subst h; simp at ht
  | succ k ih =>
    intro st p mine ids
    simp only [issueLoop]
    cases (freshId st.slots draw idAttempts p).1 with
    | error e => intro h; simp at h
    | ok tid =>
      simp only
      cases hv : victim st.slots now with
      | none =>
        intro h t ht
        simp only [Except.ok.injEq] at h
        subst h; simp at ht
      | some j =>
        simp only
        by_cases hj : j ∈ mine
        · simp only [hj, ↓reduceIte]
          intro h t ht
          simp only [Except.ok.injEq] at h
          subst h; simp at ht
        · simp only [hj, ↓reduceIte]
          intro h t ht
          cases hr : (issueLoop mk now draw k ⟨(issueAt st.slots now ⟨mk tid, st.clock + 1⟩).1, st.clock + 1⟩
              (freshId st.slots draw idAttempts p).2 (j :: mine)).2 with
          | error e => rw [hr] at h; simp [Except.map] at h
          | ok r =>
            rw [hr] at h
            simp only [Except.map, Except.ok.injEq] at h
            subst h
            rcases List.mem_cons.mp ht with rfl | hr'
            · refine ⟨j, ⟨mk t, st.clock + 1⟩, ?_, hmk t⟩
              rw [issueLoop_keep mk now draw k _ _ _ j (List.mem_cons_self ..)]
              simp only [issueAt, hv]
              simp [List.getElem?_set_self (victim_lt hv)]
            · exact ih _ _ _ r hr t hr'

/-- `Tickets.issue_batch_stored`: every ticket `issue_batch` returns is in the store when the call returns, whatever
the generator drew: a ticket of the batch never evicts another of the same batch. -/
theorem issue_batch_stored (st : Store) (mk : List Nat → Tk) (hmk : ∀ t, (mk t).tid = t) (now : Nat)
    (draw : Nat → Option (List Nat)) (count : Nat) {ids : List (List Nat)}
    (h : (issueBatch st mk now draw count).2 = .ok ids) :
    ∀ tid ∈ ids, ∃ (i : Nat) (s : Slot), (issueBatch st mk now draw count).1.slots[i]? = some (some s) ∧ s.tid = tid :=
  issueLoop_stored mk hmk now draw _ st 0 [] ids h

/-- The server stores reachable from empty by `issue_batch` (with any generator output) and `remove`. -/
inductive SReach (N : Nat) : Store → Prop where
  | init : SReach N (Store.empty N)
  | issue {st : Store} (mk : List Nat → Tk) (hmk : ∀ t, (mk t).tid = t) (now : Nat) (draw : Nat → Option (List Nat))
      (count : Nat) : SReach N st → SReach N (issueBatch st mk now draw count).1
  | remove {st : Store} (i : Nat) : SReach N st → SReach N ⟨st.slots.set i none, st.clock⟩

theorem sreach_reach {N : Nat} {st : Store} (h : SReach N st) : Reach N st.slots := by
  induction h with
  | init => exact Reach.init
  | issue mk hmk now draw count _ ih => exact issueLoop_reach mk now draw _ _ _ _ ih
  | remove i _ ih => exact Reach.remove i ih

/-- `Tickets.server_len`: a server store has `N` slots, so it holds at most `N` tickets; `N = 0` stores nothing. -/
theorem server_len {N : Nat} {st : Store} (h : SReach N st) : st.slots.length = N ∧ occ st.slots ≤ N :=
  ⟨reach_length (sreach_reach h), reach_occ_le (sreach_reach h)⟩

theorem server_zero {st : Store} (h : SReach 0 st) : occ st.slots = 0 := reach_zero (sreach_reach h)

/-- `Tickets.server_ids_distinct`: over every reachable server store, the stored ticket ids are pairwise
distinct, whatever the generator returned. -/
theorem server_ids_distinct {N : Nat} {st : Store} (h : SReach N st) : Distinct st.slots := by
  induction h with
  | init => intro i j s t hs; exact (replicate_none_get hs).elim
  | issue mk hmk now draw count _ ih => exact issueLoop_distinct mk hmk now draw _ _ _ _ ih
  | remove i _ ih =>
    intro a b x y hx hy hxy
    simp only at hx hy
    rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩
    · cases hxs
    · rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
      · cases hys
      · exact ih a b x y hx' hy' hxy

/-- Stamps of a reachable server store are distinct and bounded by the clock. -/
theorem server_stamps {N : Nat} {st : Store} (h : SReach N st) : StampInv st := by
  induction h with
  | init => exact StampInv.empty N
  | issue mk hmk now draw count _ ih => exact issueLoop_stamps mk now draw _ _ _ _ ih
  | remove i _ ih =>
    constructor
    · intro a x hx
      simp only at hx ⊢
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩
      · cases hxs
      · exact ih.1 a x hx'
    · intro a b x y hx hy hxy
      simp only at hx hy
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩
      · cases hxs
      · rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
        · cases hys
        · exact ih.2 a b x y hx' hy' hxy

/-- `Tickets.server_evicts_oldest`: when an issue overwrites an occupied, unexpired slot, the overwritten ticket is
the one issued earliest of all stored tickets. -/
theorem server_evicts_oldest {N : Nat} {st : Store} (h : SReach N st) {now j : Nat} {old : Slot}
    (hv : victim st.slots now = some j) (hold : st.slots[j]? = some (some old)) (hfresh : ¬ old.expiry < now) :
    ∀ (k : Nat) (t : Slot), st.slots[k]? = some (some t) → k ≠ j → old.stamp < t.stamp := by
  intro k t hk hkj
  obtain ⟨hne, hall⟩ := issueAt_evicts hv hold
  obtain ⟨s', hs', hmin⟩ := victim_min hv hne (hall hfresh)
  rw [hold] at hs'
  cases hs'
  have hle := hmin k t hk
  refine Nat.lt_of_le_of_ne hle fun heq => hkj ?_
  exact (server_stamps h).2 k j t old hk hold heq.symm

/-- `Tickets.issue_zero_empty`: a store without slots issues no ticket (the batch is empty), whatever it draws. -/
theorem issue_zero_empty (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat)) :
    ∀ (k : Nat) (st : Store) (p : Nat) (mine : List Nat) (ids : List (List Nat)), st.slots = [] →
      (issueLoop mk now draw k st p mine).2 = .ok ids → ids = [] := by
  intro k st p mine ids hs
  cases k with
  | zero => intro h; simp only [issueLoop, Except.ok.injEq] at h; exact h.symm
  | succ k =>
    simp only [issueLoop]
    cases (freshId st.slots draw idAttempts p).1 with
    | error e => intro h; simp at h
    | ok tid =>
      have hv : victim st.slots now = none := (victim_none_iff st.slots now).2 hs
      simp only [hv]
      intro h
      simp only [Except.ok.injEq] at h
      exact h.symm

/-- `Tickets.issue_all_collide`: when every one of the 8 draws is an id that is already stored, the call asked for
at least one ticket fails with `TicketId` and stores nothing. -/
theorem issue_all_collide (st : Store) (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat))
    (count : Nat) (hc : 1 ≤ count)
    (h : ∀ i, i < 8 → ∃ tid, draw i = some tid ∧ find st.slots tid ≠ none) :
    (issueBatch st mk now draw count).1 = st ∧ (issueBatch st mk now draw count).2 = .error .ticketId := by
  unfold issueBatch maxBatch
  obtain ⟨m, hm⟩ : ∃ m, min count 4 = m + 1 := ⟨min count 4 - 1, by omega⟩
  rw [hm]
  have hf := freshId_collide st.slots draw idAttempts 0 (by simpa [idAttempts] using h)
  simp only [issueLoop]
  rw [hf]
  simp

/-- A generator that refuses fails the call with `Randomness` and stores nothing for that ticket. -/
theorem issue_refuse (st : Store) (mk : List Nat → Tk) (now : Nat) (draw : Nat → Option (List Nat))
    (count : Nat) (hc : 1 ≤ count) (h : draw 0 = none) :
    (issueBatch st mk now draw count).1 = st ∧ (issueBatch st mk now draw count).2 = .error .randomness := by
  unfold issueBatch maxBatch
  obtain ⟨m, hm⟩ : ∃ m, min count 4 = m + 1 := ⟨min count 4 - 1, by omega⟩
  rw [hm]
  have hf := freshId_refuse st.slots draw (idAttempts - 1) 0 h
  simp only [issueLoop]
  have : idAttempts = (idAttempts - 1) + 1 := by simp [idAttempts]
  rw [this, hf]
  simp

end Pinc.Tickets

#audit_axioms Pinc.Tickets.victim_lt
#audit_axioms Pinc.Tickets.victim_none_iff
#audit_axioms Pinc.Tickets.victim_empty
#audit_axioms Pinc.Tickets.victim_expired
#audit_axioms Pinc.Tickets.victim_min
#audit_axioms Pinc.Tickets.issueAt_length
#audit_axioms Pinc.Tickets.issueAt_nil
#audit_axioms Pinc.Tickets.issueAt_places
#audit_axioms Pinc.Tickets.issueAt_evicts
#audit_axioms Pinc.Tickets.reach_length
#audit_axioms Pinc.Tickets.reach_occ_le
#audit_axioms Pinc.Tickets.reach_zero
#audit_axioms Pinc.Tickets.remove_get
#audit_axioms Pinc.Tickets.find_remove_ne
#audit_axioms Pinc.Tickets.find_remove_none
#audit_axioms Pinc.Tickets.issue_ids_distinct
#audit_axioms Pinc.Tickets.freshId_collide
#audit_axioms Pinc.Tickets.server_len
#audit_axioms Pinc.Tickets.server_zero
#audit_axioms Pinc.Tickets.server_ids_distinct
#audit_axioms Pinc.Tickets.server_stamps
#audit_axioms Pinc.Tickets.server_evicts_oldest
#audit_axioms Pinc.Tickets.issueLoop_keep
#audit_axioms Pinc.Tickets.issueLoop_stored
#audit_axioms Pinc.Tickets.issue_batch_stored
#audit_axioms Pinc.Tickets.issue_zero_empty
#audit_axioms Pinc.Tickets.issue_all_collide
#audit_axioms Pinc.Tickets.issue_refuse
