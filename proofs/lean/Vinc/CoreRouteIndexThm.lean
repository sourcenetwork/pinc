import Vinc.Axioms
import Vinc.CoreRouteIndex

/-!
# The table of sessions by address: it names exactly the live sessions, and it is bounded

What the model of `Vinc.CoreRouteIndex` proves, for any capacity `k` (the endpoint's `K`, its number of slots), any
run of settles and frees, and any paths:

- the table is well formed after every call (`Inv`: an entry `(a, i)` is held exactly when slot `i`'s `route` is `a`,
  no entry is held twice, a slot past the table holds none): `empty_inv`, `sync_inv`, `free_inv`;
- it is bounded: it never holds more than `k` entries (`len_le`), and a settle never finds it full, so the entry a
  session needs is never refused (`drop_room`, `sync_route`);
- a settle of slot `i` leaves the slot's entry saying exactly what its path says, and touches no other slot's
  (`sync_route`, `sync_other`);
- the lookup answers as the walk does: while every session whose path is from an address holds its entry
  (`Complete`), the slots `session_from` chooses among are exactly the slots the walk of every session finds, each
  once (`candidates_iff`, `walk_iff`, `candidates_eq_walk`, `candidates_nodup`), so their least session id is the
  same; and `Complete` is kept by everything that happens between lookups: a settle (`settle_complete`), a free of a
  slot whose session ended (`free_complete`), and a path taken away without a settle, as when the table of address
  pairs evicts a pair (`lose_complete`). An entry left behind that way is not an answer, because the lookup checks
  each holder's path (`candidates_iff`).
-/

namespace Vinc.CoreRouteIndex

-- The table is well formed.
structure Inv (k : Nat) (s : S) : Prop where
  -- An entry `(a, i)` is held exactly when slot `i` says it holds one under `a`.
  mem_iff : ∀ a i, (a, i) ∈ s.idx ↔ s.route i = some a
  -- No entry is held twice.
  nodup : s.idx.Nodup
  -- A slot past the table holds no entry.
  bound : ∀ i, k ≤ i → s.route i = none

-- Every session whose path is from an address holds its entry under that address: what a lookup needs.
def Complete (s : S) (cur : Nat → Option Nat) : Prop := ∀ j a, cur j = some a → s.route j = some a

-- Slot `i` set to `v` reads `v`.
theorem upd_self (f : Nat → Option Nat) (i : Nat) (v : Option Nat) : upd f i v i = v := by simp [upd]

-- Any other slot reads what it read.
theorem upd_other (f : Nat → Option Nat) {i j : Nat} (v : Option Nat) (h : j ≠ i) : upd f i v j = f j := by
  simp [upd, h]

-- Two entries of one slot are one entry: a slot holds at most one.
theorem one_per_slot {k : Nat} {s : S} (hs : Inv k s) {a b i : Nat} (ha : (a, i) ∈ s.idx) (hb : (b, i) ∈ s.idx) :
    a = b := by
  have h1 := (hs.mem_iff a i).1 ha
  have h2 := (hs.mem_iff b i).1 hb
  rw [h1] at h2
  exact Option.some.inj h2

-- Without slot `i`'s entry, the table holds exactly the entries of the other slots.
theorem mem_drop {k : Nat} {s : S} (hs : Inv k s) (i a j : Nat) : (a, j) ∈ drop s i ↔ (a, j) ∈ s.idx ∧ j ≠ i := by
  unfold drop
  cases h : s.route i with
  | none =>
    constructor
    · intro hm
      refine ⟨hm, ?_⟩
      intro hji
      subst hji
      have := (hs.mem_iff a j).1 hm
      rw [h] at this
      cases this
    · intro hm
      exact hm.1
  | some b =>
    rw [List.Nodup.mem_erase_iff hs.nodup]
    constructor
    · intro ⟨hne, hm⟩
      refine ⟨hm, ?_⟩
      intro hji
      subst hji
      have hb : (b, j) ∈ s.idx := (hs.mem_iff b j).2 h
      have := one_per_slot hs hm hb
      subst this
      exact hne rfl
    · intro ⟨hm, hne⟩
      refine ⟨?_, hm⟩
      intro heq
      exact hne (Prod.mk.inj heq).2

-- Taking slot `i`'s entry out leaves no entry twice.
theorem drop_nodup {k : Nat} {s : S} (hs : Inv k s) (i : Nat) : (drop s i).Nodup := by
  unfold drop
  cases s.route i with
  | none => exact hs.nodup
  | some b => exact List.Nodup.erase (b, i) hs.nodup

-- The slots of the entries, once each.
theorem slots_nodup {k : Nat} {s : S} (hs : Inv k s) {l : List (Nat × Nat)} (hl : l.Nodup)
    (hsub : ∀ e ∈ l, e ∈ s.idx) : (l.map (·.2)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ hl
  intro x y hx hy hne hxy
  -- Two entries with one slot: the slot holds one entry, so they are the same.
  apply hne
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  simp only at hxy
  subst hxy
  have := one_per_slot hs (hsub _ hx) (hsub _ hy)
  subst this
  rfl

-- Keeping some entries of a list without repeats leaves none repeated.
theorem nodup_filter {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup :=
  List.Sublist.nodup List.filter_sublist h

-- A list of distinct slots, all below `n`, has at most `n` of them.
theorem nodup_lt_len {l : List Nat} {n : Nat} (hl : l.Nodup) (h : ∀ x ∈ l, x < n) : l.length ≤ n := by
  have hsub : l ⊆ List.range n := fun x hx => List.mem_range.2 (h x hx)
  have := List.Nodup.length_le_of_subset hl hsub
  simpa using this

-- A slot that holds an entry is a slot of the table.
theorem slot_lt {k : Nat} {s : S} (hs : Inv k s) {a i : Nat} (h : (a, i) ∈ s.idx) : i < k := by
  apply Nat.lt_of_not_le
  intro hle
  have := (hs.mem_iff a i).1 h
  rw [hs.bound i hle] at this
  cases this

/-- The table never holds more than `k` entries. -/
theorem len_le {k : Nat} {s : S} (hs : Inv k s) : s.idx.length ≤ k := by
  have hn := slots_nodup hs hs.nodup (fun e he => he)
  have := nodup_lt_len hn (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact slot_lt hs he)
  simpa using this

/-- With slot `i`'s entry out, the table has room for it: a settle is never refused. -/
theorem drop_room {k : Nat} {s : S} (hs : Inv k s) {i : Nat} (hi : i < k) : (drop s i).length < k := by
  -- The slots of the other entries are distinct, below `k` and not `i`: at most `k - 1` of them.
  have hn := slots_nodup hs (drop_nodup hs i) (fun e he => ((mem_drop hs i e.1 e.2).1 he).1)
  have hsub : (drop s i).map (·.2) ⊆ (List.range k).erase i := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have ⟨hm, hne⟩ := (mem_drop hs i e.1 e.2).1 he
    exact (List.Nodup.mem_erase_iff List.nodup_range).2 ⟨hne, List.mem_range.2 (slot_lt hs hm)⟩
  have hle := List.Nodup.length_le_of_subset hn hsub
  rw [List.length_map, List.length_erase_of_mem (List.mem_range.2 hi), List.length_range] at hle
  omega

/-- A new endpoint's table is well formed. -/
theorem empty_inv (k : Nat) : Inv k S.empty where
  mem_iff := by intro a i; simp [S.empty]
  nodup := List.nodup_nil
  bound := by intro i _; rfl

-- Slot `i` loses its entry and holds none.
theorem clear_inv {k : Nat} {s : S} (hs : Inv k s) (i : Nat) : Inv k ⟨upd s.route i none, drop s i⟩ where
  mem_iff := by
    intro a j
    show (a, j) ∈ drop s i ↔ upd s.route i none j = some a
    rw [mem_drop hs]
    by_cases hj : j = i
    · subst hj
      rw [upd_self]
      simp
    · rw [upd_other _ _ hj, hs.mem_iff]
      simp [hj]
  nodup := drop_nodup hs i
  bound := by
    intro j hj
    show upd s.route i none j = none
    by_cases hji : j = i
    · subst hji; rw [upd_self]
    · rw [upd_other _ _ hji]; exact hs.bound j hj

-- Slot `i` holds its entry under `a` in place of the one it held.
theorem add_inv {k : Nat} {s : S} (hs : Inv k s) {i : Nat} (hi : i < k) (a : Nat) :
    Inv k ⟨upd s.route i (some a), (a, i) :: drop s i⟩ where
  mem_iff := by
    intro b j
    show (b, j) ∈ (a, i) :: drop s i ↔ upd s.route i (some a) j = some b
    rw [List.mem_cons, mem_drop hs]
    by_cases hj : j = i
    · subst hj
      rw [upd_self]
      constructor
      · intro h
        rcases h with h | h
        · rw [(Prod.mk.inj h).1]
        · exact absurd rfl h.2
      · intro h
        left
        rw [Option.some.inj h]
    · rw [upd_other _ _ hj, hs.mem_iff]
      constructor
      · intro h
        rcases h with h | h
        · exact absurd (Prod.mk.inj h).2 hj
        · exact h.1
      · intro h
        right
        exact ⟨h, hj⟩
  nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, drop_nodup hs i⟩
    intro h
    exact ((mem_drop hs i a i).1 h).2 rfl
  bound := by
    intro j hj
    show upd s.route i (some a) j = none
    have hji : j ≠ i := by omega
    rw [upd_other _ _ hji]
    exact hs.bound j hj

/-- A settle keeps the table well formed. -/
theorem sync_inv {k : Nat} {s : S} (hs : Inv k s) {i : Nat} (hi : i < k) (want : Option Nat) :
    Inv k (sync k s i want) := by
  by_cases h : s.route i = want
  · unfold sync; rw [if_pos h]
    exact hs
  · unfold sync; rw [if_neg h]
    cases want with
    | none => exact clear_inv hs i
    | some a =>
      show Inv k (if (drop s i).length < k then _ else _)
      by_cases hr : (drop s i).length < k
      · rw [if_pos hr]
        exact add_inv hs hi a
      · rw [if_neg hr]
        exact clear_inv hs i

/-- A free keeps the table well formed. -/
theorem free_inv {k : Nat} {s : S} (hs : Inv k s) (i : Nat) : Inv k (free s i) := clear_inv hs i

/-- After a settle, slot `i`'s entry says exactly what its path says. -/
theorem sync_route {k : Nat} {s : S} (hs : Inv k s) {i : Nat} (hi : i < k) (want : Option Nat) :
    (sync k s i want).route i = want := by
  by_cases h : s.route i = want
  · unfold sync; rw [if_pos h]
    exact h
  · unfold sync; rw [if_neg h]
    cases want with
    | none => exact upd_self _ _ _
    | some a =>
      show (if (drop s i).length < k then (⟨_, _⟩ : S) else ⟨_, _⟩).route i = some a
      rw [if_pos (drop_room hs hi)]
      exact upd_self _ _ _

/-- A settle of slot `i` changes no other slot's entry. -/
theorem sync_other (k : Nat) (s : S) {i j : Nat} (want : Option Nat) (h : j ≠ i) :
    (sync k s i want).route j = s.route j := by
  by_cases hw : s.route i = want
  · unfold sync; rw [if_pos hw]
  · unfold sync; rw [if_neg hw]
    cases want with
    | none => exact upd_other _ _ h
    | some a =>
      show (if (drop s i).length < k then (⟨_, _⟩ : S) else ⟨_, _⟩).route j = s.route j
      by_cases hr : (drop s i).length < k
      · rw [if_pos hr]
        exact upd_other _ _ h
      · rw [if_neg hr]
        exact upd_other _ _ h

/-- The slots `session_from` chooses among are exactly the sessions whose path is from `a` now and that `keep`
accepts, while the table is complete. -/
theorem candidates_iff {k : Nat} {s : S} (hs : Inv k s) {cur : Nat → Option Nat} (hc : Complete s cur)
    (keep : Nat → Bool) (a j : Nat) : j ∈ candidates s cur keep a ↔ cur j = some a ∧ keep j = true := by
  unfold candidates holders
  simp only [List.mem_filter, List.mem_map, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro ⟨_, hcur, hkeep⟩
    exact ⟨hcur, hkeep⟩
  · intro ⟨hcur, hkeep⟩
    refine ⟨⟨(a, j), ⟨(hs.mem_iff a j).2 (hc j a hcur), rfl⟩, rfl⟩, hcur, hkeep⟩

/-- The walk finds every slot below `k` whose path is from `a` now and that `keep` accepts. -/
theorem walk_iff (k : Nat) (cur : Nat → Option Nat) (keep : Nat → Bool) (a j : Nat) :
    j ∈ walk k cur keep a ↔ j < k ∧ cur j = some a ∧ keep j = true := by
  unfold walk
  simp [List.mem_filter, List.mem_range]

/-- The lookup and the walk find the same sessions, while the table is complete and no slot past the table has a
path. -/
theorem candidates_eq_walk {k : Nat} {s : S} (hs : Inv k s) {cur : Nat → Option Nat} (hc : Complete s cur)
    (hk : ∀ j, k ≤ j → cur j = none) (keep : Nat → Bool) (a j : Nat) :
    j ∈ candidates s cur keep a ↔ j ∈ walk k cur keep a := by
  rw [candidates_iff hs hc, walk_iff]
  constructor
  · intro ⟨hcur, hkeep⟩
    refine ⟨Nat.lt_of_not_le fun hle => ?_, hcur, hkeep⟩
    rw [hk j hle] at hcur
    cases hcur
  · intro ⟨_, hcur, hkeep⟩
    exact ⟨hcur, hkeep⟩

/-- The lookup finds each session once. -/
theorem candidates_nodup {k : Nat} {s : S} (hs : Inv k s) (cur : Nat → Option Nat) (keep : Nat → Bool) (a : Nat) :
    (candidates s cur keep a).Nodup := by
  unfold candidates holders
  apply nodup_filter
  apply slots_nodup hs (nodup_filter _ hs.nodup)
  intro e he
  exact (List.mem_filter.1 he).1

/-- A settle of slot `i` to what its path says keeps the table complete. -/
theorem settle_complete {k : Nat} {s : S} (hs : Inv k s) {cur : Nat → Option Nat} (hc : Complete s cur) {i : Nat}
    (hi : i < k) : Complete (sync k s i (cur i)) cur := by
  intro j a hj
  by_cases hji : j = i
  · subst hji
    rw [sync_route hs hi]
    exact hj
  · rw [sync_other k s _ hji]
    exact hc j a hj

/-- Freeing a slot whose session has no path keeps the table complete. -/
theorem free_complete {s : S} {cur : Nat → Option Nat} (hc : Complete s cur) {i : Nat} (hi : cur i = none) :
    Complete (free s i) cur := by
  intro j a hj
  show upd s.route i none j = some a
  by_cases hji : j = i
  · subst hji
    rw [hi] at hj
    cases hj
  · rw [upd_other _ _ hji]
    exact hc j a hj

/-- A path taken away without a settle (an evicted pair of addresses) keeps the table complete: the entry it leaves
behind is no answer, since the lookup checks the path. -/
theorem lose_complete {s : S} {cur cur' : Nat → Option Nat} (hc : Complete s cur)
    (h : ∀ j, cur' j = cur j ∨ cur' j = none) : Complete s cur' := by
  intro j a hj
  rcases h j with h | h
  · rw [h] at hj
    exact hc j a hj
  · rw [h] at hj
    cases hj

#audit_axioms len_le
#audit_axioms drop_room
#audit_axioms sync_inv
#audit_axioms free_inv
#audit_axioms sync_route
#audit_axioms candidates_eq_walk
#audit_axioms candidates_nodup
#audit_axioms settle_complete
#audit_axioms free_complete
#audit_axioms lose_complete

end Vinc.CoreRouteIndex
