import Pinc.Tickets

/-!
# The prekey cache

`PrekeyCache` of `pinc-security/src/cache.rs`: a bounded LRU of initiator prekeys keyed by the prekey hash. It has `N`
slots and a clock; every `get` and `insert` first advances the clock (a `u64` `wrapping_add`) and stamps with the new
value. `get` refreshes the stamp of the entry it finds. `insert` of a hash that is already cached only refreshes its
stamp (the cached key is kept); a new hash goes to the first empty slot, else replaces the entry with the lowest
`(stamp, index)`, the least recently used. `N = 0` caches nothing, so every `get` misses.

The clock wraps after 2^64 operations. The model keeps the wrapping (`tick`) and the theorems about reachable caches
carry the hypothesis `n < 2^64` on the number of operations performed (`PReach N n`): a documented ceiling, not an
assumption. The theorems about a single operation need only `st.clock + 1 < 2^64`.

`get_most_recent` and `insert_most_recent` show that the entry touched carries the newest stamp and every other entry is older.
The refinement of the stamps by a plain recency list (most recent first: `get` moves the hash to the front, `insert` puts it
at the front and drops the last when the list is over `N`) is `Pinc.PrekeyRecency.cache_refines_list`.
-/

namespace Pinc.PrekeyCache
open Pinc.Tickets (firstIdx firstIdx_none_iff firstIdx_some firstIdx_first set_get_cases replicate_none_get)

/-- A cached prekey: the hash, the key (opaque here), and the stamp of its last use. -/
structure Entry where
  hash : List Nat
  val : Nat
  stamp : Nat

abbrev Ents := List (Option Entry)

/-- The `N` slots and the clock. -/
structure Cache where
  slots : Ents
  clock : Nat

/-- A fresh cache of `n` slots. -/
def Cache.empty (n : Nat) : Cache := ⟨List.replicate n none, 0⟩

/-- `u64::wrapping_add(1)`. -/
def tick (c : Nat) : Nat := (c + 1) % 2 ^ 64

theorem tick_eq {c : Nat} (h : c + 1 < 2 ^ 64) : tick c = c + 1 := by
  unfold tick; exact Nat.mod_eq_of_lt h

/-- A slot holding hash `h`. -/
def hashIs (h : List Nat) (x : Option Entry) : Bool := x.any fun e => decide (e.hash = h)

def isEmptyE (x : Option Entry) : Bool := x.isNone

/-- `(lowest stamp, index)` over the occupied slots from index `i`: `.min()` on the pairs. -/
def minE : Ents → Nat → Option (Nat × Nat)
  | [], _ => none
  | none :: l, i => minE l (i + 1)
  | some s :: l, i =>
    match minE l (i + 1) with
    | none => some (s.stamp, i)
    | some (st, j) => if s.stamp ≤ st then some (s.stamp, i) else some (st, j)

/-- The slot a new entry takes: the first empty slot, else the least recently used. -/
def evict (l : Ents) : Option Nat := (firstIdx isEmptyE l 0).or ((minE l 0).map (·.2))

theorem minE_none_iff : ∀ (l : Ents) (i : Nat),
    minE l i = none ↔ ∀ (k : Nat) (t : Entry), l[k]? = some (some t) → False := by
  intro l
  induction l with
  | nil => intro i; simp [minE]
  | cons x l ih =>
    intro i
    cases x with
    | none =>
      simp only [minE]
      rw [ih]
      constructor
      · intro h k t hk
        cases k with
        | zero => simp at hk
        | succ k => exact h k t (by simpa using hk)
      · intro h k t hk; exact h (k + 1) t (by simpa using hk)
    | some s =>
      simp only [minE]
      constructor
      · intro h
        cases hm : minE l (i + 1) with
        | none => rw [hm] at h; simp at h
        | some r => obtain ⟨a, b⟩ := r; rw [hm] at h; by_cases hle : s.stamp ≤ a <;> simp [hle] at h
      · intro h; exact absurd (h 0 s (by simp)) id

theorem minE_some : ∀ (l : Ents) (i st j : Nat), minE l i = some (st, j) →
    i ≤ j ∧ (∃ s, l[j - i]? = some (some s) ∧ s.stamp = st) ∧
      ∀ (k : Nat) (t : Entry), l[k]? = some (some t) → st ≤ t.stamp := by
  intro l
  induction l with
  | nil => intro i st j h; simp [minE] at h
  | cons x l ih =>
    intro i st j h
    cases x with
    | none =>
      simp only [minE] at h
      obtain ⟨h1, ⟨s, hs, hst⟩, h3⟩ := ih (i + 1) st j h
      refine ⟨by omega, ⟨s, ?_, hst⟩, ?_⟩
      · have : j - i = (j - (i + 1)) + 1 := by omega
        rw [this]; simpa using hs
      · intro k t hk
        cases k with
        | zero => simp at hk
        | succ k => exact h3 k t (by simpa using hk)
    | some s =>
      simp only [minE] at h
      cases hm : minE l (i + 1) with
      | none =>
        rw [hm] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Nat.le_refl _, ⟨s, by simp, rfl⟩, ?_⟩
        intro k t hk
        cases k with
        | zero => simp at hk; subst hk; exact Nat.le_refl _
        | succ k => exact absurd hk (by simpa using (minE_none_iff l (i + 1)).1 hm k t)
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

theorem evict_lt {l : Ents} {j : Nat} (h : evict l = some j) : j < l.length := by
  unfold evict at h
  cases e1 : firstIdx isEmptyE l 0 with
  | some i =>
    rw [e1] at h; cases h
    obtain ⟨_, x, hx, _⟩ := firstIdx_some _ _ _ _ e1
    exact (List.getElem?_eq_some_iff.mp hx).1
  | none =>
    rw [e1] at h
    cases e3 : minE l 0 with
    | none => rw [e3] at h; simp at h
    | some r =>
      obtain ⟨st, j'⟩ := r
      rw [e3] at h
      simp only [Option.none_or, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨_, ⟨s, hs, _⟩, _⟩ := minE_some _ _ _ _ e3
      exact (List.getElem?_eq_some_iff.mp hs).1

theorem evict_none_iff (l : Ents) : evict l = none ↔ l = [] := by
  constructor
  · intro h
    unfold evict at h
    cases e1 : firstIdx isEmptyE l 0 with
    | some i => rw [e1] at h; cases h
    | none =>
      rw [e1] at h
      cases e3 : minE l 0 with
      | some r => rw [e3] at h; simp at h
      | none =>
        cases l with
        | nil => rfl
        | cons x l =>
          exfalso
          cases x with
          | none => exact absurd ((firstIdx_none_iff _ _ _).1 e1 0 none (by simp)) (by simp [isEmptyE])
          | some t => exact (minE_none_iff _ _).1 e3 0 t (by simp)
  · rintro rfl; simp [evict, firstIdx, minE]

/-- A new entry goes into an empty slot whenever there is one. -/
theorem evict_empty {l : Ents} {j : Nat} (h : evict l = some j) (hex : ∃ k : Nat, l[k]? = some none) :
    l[j]? = some none := by
  unfold evict at h
  cases e1 : firstIdx isEmptyE l 0 with
  | some i =>
    rw [e1] at h; cases h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e1
    cases x with
    | none => simpa using hx
    | some _ => simp [isEmptyE] at hp
  | none =>
    obtain ⟨k, hk⟩ := hex
    exact absurd ((firstIdx_none_iff _ _ _).1 e1 k none hk) (by simp [isEmptyE])

/-- With no empty slot, the entry replaced has the lowest stamp. -/
theorem evict_min {l : Ents} {j : Nat} (h : evict l = some j) (hne : ∀ k : Nat, l[k]? ≠ some none) :
    ∃ s, l[j]? = some (some s) ∧ ∀ (k : Nat) (t : Entry), l[k]? = some (some t) → s.stamp ≤ t.stamp := by
  unfold evict at h
  cases e1 : firstIdx isEmptyE l 0 with
  | some i =>
    rw [e1] at h
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ e1
    cases x with
    | none => exact absurd (by simpa using hx) (hne i)
    | some _ => simp [isEmptyE] at hp
  | none =>
    rw [e1] at h
    cases e3 : minE l 0 with
    | none => rw [e3] at h; simp at h
    | some r =>
      obtain ⟨st, j'⟩ := r
      rw [e3] at h
      simp only [Option.none_or, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨_, ⟨s, hs, hst⟩, h3⟩ := minE_some _ _ _ _ e3
      exact ⟨s, by simpa using hs, fun k t hk => by have := h3 k t hk; omega⟩

/-! ## The operations -/

/-- `PrekeyCache::get`: the clock advances and stamps; a hit refreshes the entry's stamp and returns its key. -/
def get (st : Cache) (h : List Nat) : Cache × Option Nat :=
  match firstIdx (hashIs h) st.slots 0 with
  | none => (⟨st.slots, tick st.clock⟩, none)
  | some i =>
    match (st.slots[i]?).getD none with
    | none => (⟨st.slots, tick st.clock⟩, none)
    | some e => (⟨st.slots.set i (some { e with stamp := tick st.clock }), tick st.clock⟩, some e.val)

/-- `PrekeyCache::insert`: the clock advances and stamps; a cached hash only has its stamp refreshed (its key is
kept); a new hash goes to the first empty slot, else replaces the least recently used entry. -/
def insert (st : Cache) (h : List Nat) (v : Nat) : Cache :=
  match firstIdx (hashIs h) st.slots 0 with
  | some i =>
    match (st.slots[i]?).getD none with
    | none => ⟨st.slots, tick st.clock⟩
    | some e => ⟨st.slots.set i (some { e with stamp := tick st.clock }), tick st.clock⟩
  | none =>
    match evict st.slots with
    | some j => ⟨st.slots.set j (some ⟨h, v, tick st.clock⟩), tick st.clock⟩
    | none => ⟨st.slots, tick st.clock⟩

theorem get_cases (st : Cache) (h : List Nat) :
    ((∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h) ∧
      get st h = (⟨st.slots, tick st.clock⟩, none)) ∨
    (∃ (i : Nat) (e : Entry), st.slots[i]? = some (some e) ∧ e.hash = h ∧
      get st h = (⟨st.slots.set i (some { e with stamp := tick st.clock }), tick st.clock⟩, some e.val)) := by
  unfold get
  cases hf : firstIdx (hashIs h) st.slots 0 with
  | none =>
    refine Or.inl ⟨fun k e hk he => ?_, rfl⟩
    have := (firstIdx_none_iff _ _ _).1 hf k (some e) hk
    simp [hashIs, he] at this
  | some i =>
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ hf
    simp only [Nat.sub_zero] at hx
    cases x with
    | none => simp [hashIs] at hp
    | some e =>
      simp only [hashIs, Option.any_some, decide_eq_true_eq] at hp
      refine Or.inr ⟨i, e, hx, hp, ?_⟩
      simp [hx]

theorem insert_cases (st : Cache) (h : List Nat) (v : Nat) :
    (∃ (i : Nat) (e : Entry), st.slots[i]? = some (some e) ∧ e.hash = h ∧
      insert st h v = ⟨st.slots.set i (some { e with stamp := tick st.clock }), tick st.clock⟩) ∨
    ((∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h) ∧
      ((∃ j, evict st.slots = some j ∧ insert st h v = ⟨st.slots.set j (some ⟨h, v, tick st.clock⟩), tick st.clock⟩) ∨
       (evict st.slots = none ∧ insert st h v = ⟨st.slots, tick st.clock⟩))) := by
  unfold insert
  cases hf : firstIdx (hashIs h) st.slots 0 with
  | none =>
    refine Or.inr ⟨fun k e hk he => ?_, ?_⟩
    · have := (firstIdx_none_iff _ _ _).1 hf k (some e) hk
      simp [hashIs, he] at this
    · cases hv : evict st.slots with
      | some j => exact Or.inl ⟨j, rfl, by simp⟩
      | none => exact Or.inr ⟨rfl, by simp⟩
  | some i =>
    obtain ⟨_, x, hx, hp⟩ := firstIdx_some _ _ _ _ hf
    simp only [Nat.sub_zero] at hx
    cases x with
    | none => simp [hashIs] at hp
    | some e =>
      simp only [hashIs, Option.any_some, decide_eq_true_eq] at hp
      refine Or.inl ⟨i, e, hx, hp, ?_⟩
      simp [hx]

/-! ## Invariants -/

/-- No two cached entries share a hash. -/
def HashesDistinct (st : Cache) : Prop :=
  ∀ (i j : Nat) (e f : Entry), st.slots[i]? = some (some e) → st.slots[j]? = some (some f) → e.hash = f.hash → i = j

/-- Stamps are at most the clock and pairwise distinct: the stamps are the order of use. -/
def StampsOk (st : Cache) : Prop :=
  (∀ (i : Nat) (e : Entry), st.slots[i]? = some (some e) → e.stamp ≤ st.clock) ∧
  ∀ (i j : Nat) (e f : Entry), st.slots[i]? = some (some e) → st.slots[j]? = some (some f) → e.stamp = f.stamp → i = j

/-- The caches reachable from empty by `n` operations. -/
inductive PReach (N : Nat) : Nat → Cache → Prop where
  | init : PReach N 0 (Cache.empty N)
  | get {n : Nat} {st : Cache} (h : List Nat) : PReach N n st → PReach N (n + 1) (get st h).1
  | insert {n : Nat} {st : Cache} (h : List Nat) (v : Nat) : PReach N n st → PReach N (n + 1) (insert st h v)

/-- Entries in the slots. -/
def occE (l : Ents) : Nat := (l.filter Option.isSome).length

theorem refresh_inv {st : Cache} (hH : HashesDistinct st) (hS : StampsOk st) {i : Nat} {e : Entry}
    (he : st.slots[i]? = some (some e)) (c : Nat) (hc : c = st.clock + 1) :
    HashesDistinct ⟨st.slots.set i (some { e with stamp := c }), c⟩ ∧
      StampsOk ⟨st.slots.set i (some { e with stamp := c }), c⟩ := by
  subst hc
  constructor
  · intro a b x y hx hy hxy
    simp only at hx hy
    rcases set_get_cases hx with ⟨hai, hxs, _⟩ | ⟨hne, hx'⟩ <;>
      rcases set_get_cases hy with ⟨hbi, hys, _⟩ | ⟨hne', hy'⟩
    · exact hai.trans hbi.symm
    · cases hxs
      exact absurd (hH i b e y he hy' hxy).symm hne'
    · cases hys
      exact absurd (hH a i x e hx' he hxy) hne
    · exact hH a b x y hx' hy' hxy
  · constructor
    · intro a x hx
      simp only at hx ⊢
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩
      · cases hxs; exact Nat.le_refl _
      · have := hS.1 a x hx'; omega
    · intro a b x y hx hy hxy
      simp only at hx hy
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
        rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
      · rfl
      · cases hxs
        have := hS.1 b y hy'; simp only at hxy; omega
      · cases hys
        have := hS.1 a x hx'; simp only at hxy; omega
      · exact hS.2 a b x y hx' hy' hxy

theorem add_inv {st : Cache} (hH : HashesDistinct st) (hS : StampsOk st) (j : Nat) (h : List Nat) (v c : Nat)
    (hc : c = st.clock + 1) (habs : ∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h) :
    HashesDistinct ⟨st.slots.set j (some ⟨h, v, c⟩), c⟩ ∧ StampsOk ⟨st.slots.set j (some ⟨h, v, c⟩), c⟩ := by
  subst hc
  constructor
  · intro a b x y hx hy hxy
    simp only at hx hy
    rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
      rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
    · rfl
    · cases hxs
      exact absurd (hxy.symm) (habs b y hy')
    · cases hys
      exact absurd hxy (habs a x hx')
    · exact hH a b x y hx' hy' hxy
  · constructor
    · intro a x hx
      simp only at hx ⊢
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩
      · cases hxs; exact Nat.le_refl _
      · have := hS.1 a x hx'; omega
    · intro a b x y hx hy hxy
      simp only at hx hy
      rcases set_get_cases hx with ⟨rfl, hxs, _⟩ | ⟨hne, hx'⟩ <;>
        rcases set_get_cases hy with ⟨rfl, hys, _⟩ | ⟨hne', hy'⟩
      · rfl
      · cases hxs
        have := hS.1 b y hy'; simp only at hxy; omega
      · cases hys
        have := hS.1 a x hx'; simp only at hxy; omega
      · exact hS.2 a b x y hx' hy' hxy

theorem noop_inv {st : Cache} (hH : HashesDistinct st) (hS : StampsOk st) (c : Nat) (hc : c = st.clock + 1) :
    HashesDistinct ⟨st.slots, c⟩ ∧ StampsOk ⟨st.slots, c⟩ := by
  subst hc
  exact ⟨hH, fun i e h => by have := hS.1 i e h; simp only; omega, hS.2⟩

theorem get_inv {st : Cache} (hH : HashesDistinct st) (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64) (h : List Nat) :
    HashesDistinct (get st h).1 ∧ StampsOk (get st h).1 := by
  rcases get_cases st h with ⟨_, he⟩ | ⟨i, e, hi, _, he⟩ <;> rw [he] <;> simp only
  · exact noop_inv hH hS _ (tick_eq hc)
  · exact refresh_inv hH hS hi _ (tick_eq hc)

theorem insert_inv {st : Cache} (hH : HashesDistinct st) (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64) (h : List Nat)
    (v : Nat) : HashesDistinct (insert st h v) ∧ StampsOk (insert st h v) := by
  rcases insert_cases st h v with ⟨i, e, hi, _, he⟩ | ⟨habs, ⟨j, _, he⟩ | ⟨_, he⟩⟩ <;> rw [he]
  · exact refresh_inv hH hS hi _ (tick_eq hc)
  · exact add_inv hH hS j h v _ (tick_eq hc) habs
  · exact noop_inv hH hS _ (tick_eq hc)

theorem get_length (st : Cache) (h : List Nat) : (get st h).1.slots.length = st.slots.length := by
  rcases get_cases st h with ⟨_, he⟩ | ⟨i, e, _, _, he⟩ <;> rw [he] <;> simp

theorem insert_length (st : Cache) (h : List Nat) (v : Nat) : (insert st h v).slots.length = st.slots.length := by
  rcases insert_cases st h v with ⟨i, e, _, _, he⟩ | ⟨_, ⟨j, _, he⟩ | ⟨_, he⟩⟩ <;> rw [he] <;> simp

theorem preach_length {N n : Nat} {st : Cache} (h : PReach N n st) : st.slots.length = N := by
  induction h with
  | init => simp [Cache.empty]
  | get h _ ih => rw [get_length]; exact ih
  | insert h v _ ih => rw [insert_length]; exact ih

theorem get_clock (st : Cache) (h : List Nat) : (get st h).1.clock = tick st.clock := by
  rcases get_cases st h with ⟨_, he⟩ | ⟨i, e, _, _, he⟩ <;> rw [he]

theorem insert_clock (st : Cache) (h : List Nat) (v : Nat) : (insert st h v).clock = tick st.clock := by
  rcases insert_cases st h v with ⟨i, e, _, _, he⟩ | ⟨_, ⟨j, _, he⟩ | ⟨_, he⟩⟩ <;> rw [he]

/-- `PrekeyCache.cache_inv`: while fewer than 2^64 operations were performed, the clock counts them, the hashes in the
cache are pairwise distinct, and the stamps are distinct and bounded by the clock. -/
theorem cache_inv {N n : Nat} {st : Cache} (h : PReach N n st) (hn : n < 2 ^ 64) :
    st.clock = n ∧ HashesDistinct st ∧ StampsOk st := by
  induction h with
  | init =>
    refine ⟨rfl, fun i j e f hs => (replicate_none_get hs).elim, ?_, fun i j e f hs => (replicate_none_get hs).elim⟩
    intro i e hs; exact (replicate_none_get hs).elim
  | @get n st0 h _ ih =>
    obtain ⟨hc, hH, hS⟩ := ih (by omega)
    have hlt : st0.clock + 1 < 2 ^ 64 := by omega
    obtain ⟨h1, h2⟩ := get_inv hH hS hlt h
    exact ⟨by rw [get_clock, tick_eq hlt, hc], h1, h2⟩
  | @insert n st0 h v _ ih =>
    obtain ⟨hc, hH, hS⟩ := ih (by omega)
    have hlt : st0.clock + 1 < 2 ^ 64 := by omega
    obtain ⟨h1, h2⟩ := insert_inv hH hS hlt h v
    exact ⟨by rw [insert_clock, tick_eq hlt, hc], h1, h2⟩

/-- `PrekeyCache.cache_len`: a cache never holds more than `N` entries. -/
theorem cache_len {N n : Nat} {st : Cache} (h : PReach N n st) : st.slots.length = N ∧ occE st.slots ≤ N := by
  have := preach_length h
  exact ⟨this, by unfold occE; have := List.length_filter_le Option.isSome st.slots; omega⟩

/-- `PrekeyCache.cache_zero`: with `N = 0` nothing is cached and every `get` misses. -/
theorem cache_zero {n : Nat} {st : Cache} (h : PReach 0 n st) (hash : List Nat) :
    st.slots = [] ∧ occE st.slots = 0 ∧ (get st hash).2 = none := by
  have hl := preach_length h
  have hs : st.slots = [] := List.length_eq_zero_iff.mp hl
  refine ⟨hs, by simp [hs, occE], ?_⟩
  rcases get_cases st hash with ⟨_, he⟩ | ⟨i, e, hi, _, _⟩
  · rw [he]
  · rw [hs] at hi; simp at hi

/-- `PrekeyCache.get_refreshes`: a hit stamps exactly the entry it found with the new clock value and changes
nothing else; it returns the cached key. -/
theorem get_refreshes {st : Cache} {h : List Nat} {i : Nat} {e : Entry} (hi : st.slots[i]? = some (some e))
    (he : e.hash = h) (hH : HashesDistinct st) (hc : st.clock + 1 < 2 ^ 64) :
    (get st h).2 = some e.val ∧
      (get st h).1.slots = st.slots.set i (some { e with stamp := st.clock + 1 }) ∧
      (∀ k : Nat, k ≠ i → (get st h).1.slots[k]? = st.slots[k]?) := by
  rcases get_cases st h with ⟨habs, _⟩ | ⟨i', e', hi', he', hg⟩
  · exact absurd he (habs i e hi)
  · have : i' = i := hH i' i e' e hi' hi (by rw [he', he])
    subst this
    have hee : e' = e := by rw [hi] at hi'; simpa using hi'.symm
    subst hee
    rw [hg, tick_eq hc]
    refine ⟨rfl, rfl, fun k hk => ?_⟩
    simp [List.getElem?_set_ne (Ne.symm hk)]

/-- `PrekeyCache.get_miss`: a miss changes no entry (it advances the clock only). -/
theorem get_miss {st : Cache} {h : List Nat} (habs : ∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h) :
    (get st h).2 = none ∧ (get st h).1.slots = st.slots := by
  rcases get_cases st h with ⟨_, he⟩ | ⟨i, e, hi, he, _⟩
  · rw [he]; exact ⟨rfl, rfl⟩
  · exact absurd he (habs i e hi)

/-- `PrekeyCache.insert_known`: inserting a hash that is cached only refreshes that entry's stamp: one copy, the key
is the one already cached. -/
theorem insert_known {st : Cache} {h : List Nat} {v : Nat} {i : Nat} {e : Entry} (hi : st.slots[i]? = some (some e))
    (he : e.hash = h) (hH : HashesDistinct st) (hc : st.clock + 1 < 2 ^ 64) :
    (insert st h v).slots = st.slots.set i (some { e with stamp := st.clock + 1 }) := by
  rcases insert_cases st h v with ⟨i', e', hi', he', hg⟩ | ⟨habs, _⟩
  · have : i' = i := hH i' i e' e hi' hi (by rw [he', he])
    subst this
    have hee : e' = e := by rw [hi] at hi'; simpa using hi'.symm
    subst hee
    rw [hg, tick_eq hc]
  · exact absurd he (habs i e hi)

/-- `PrekeyCache.insert_fills_empty`: a new hash goes to an empty slot whenever there is one; nothing is evicted. -/
theorem insert_fills_empty {st : Cache} {h : List Nat} {v : Nat}
    (habs : ∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h) (hex : ∃ k : Nat, st.slots[k]? = some none)
    (hc : st.clock + 1 < 2 ^ 64) :
    ∃ j : Nat, st.slots[j]? = some none ∧ (insert st h v).slots = st.slots.set j (some ⟨h, v, st.clock + 1⟩) := by
  rcases insert_cases st h v with ⟨i, e, hi, he, _⟩ | ⟨_, ⟨j, hj, he⟩ | ⟨hn, _⟩⟩
  · exact absurd he (habs i e hi)
  · exact ⟨j, evict_empty hj hex, by rw [he, tick_eq hc]⟩
  · obtain ⟨k, hk⟩ := hex
    have := (evict_none_iff _).1 hn
    rw [this] at hk; simp at hk

/-- `PrekeyCache.insert_evicts_lru`: inserting a new hash into a full cache replaces exactly the entry with the least
stamp (the least recently used) and keeps every other entry. -/
theorem insert_evicts_lru {st : Cache} {h : List Nat} {v : Nat} (hS : StampsOk st)
    (habs : ∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h)
    (hfull : ∀ k : Nat, st.slots[k]? ≠ some none) (hne : st.slots ≠ []) (hc : st.clock + 1 < 2 ^ 64) :
    ∃ (j : Nat) (old : Entry), st.slots[j]? = some (some old) ∧
      (∀ (k : Nat) (t : Entry), st.slots[k]? = some (some t) → k ≠ j → old.stamp < t.stamp) ∧
      (insert st h v).slots = st.slots.set j (some ⟨h, v, st.clock + 1⟩) := by
  rcases insert_cases st h v with ⟨i, e, hi, he, _⟩ | ⟨_, ⟨j, hj, he⟩ | ⟨hn, _⟩⟩
  · exact absurd he (habs i e hi)
  · obtain ⟨old, hold, hmin⟩ := evict_min hj hfull
    refine ⟨j, old, hold, fun k t hk hkj => ?_, by rw [he, tick_eq hc]⟩
    refine Nat.lt_of_le_of_ne (hmin k t hk) fun heq => hkj ?_
    exact hS.2 k j t old hk hold heq.symm
  · exact absurd ((evict_none_iff _).1 hn) hne

/-- `PrekeyCache.get_after_insert`: with a slot (`N > 0`), a `get` right after the `insert` of a new hash hits and
returns the key just inserted. -/
theorem get_after_insert {st : Cache} {h : List Nat} {v : Nat}
    (habs : ∀ (k : Nat) (e : Entry), st.slots[k]? = some (some e) → e.hash ≠ h) (hne : st.slots ≠ []) :
    (get (insert st h v) h).2 = some v := by
  rcases insert_cases st h v with ⟨i, e, hi, he, _⟩ | ⟨_, ⟨j, hj, he⟩ | ⟨hn, _⟩⟩
  · exact absurd he (habs i e hi)
  · have hjl := evict_lt hj
    have hnew : (insert st h v).slots[j]? = some (some ⟨h, v, tick st.clock⟩) := by
      rw [he]; simp [List.getElem?_set_self hjl]
    rcases get_cases (insert st h v) h with ⟨hab2, _⟩ | ⟨i2, e2, hi2, he2, hg⟩
    · exact absurd rfl (hab2 j _ hnew)
    · rw [hg]
      simp only
      rcases set_get_cases (l := st.slots) (j := j) (k := i2) (x := some ⟨h, v, tick st.clock⟩) (y := some e2) (by rw [he] at hi2; exact hi2) with
        ⟨rfl, hy, _⟩ | ⟨_, hy⟩
      · cases hy; rfl
      · exact absurd he2 (habs i2 e2 hy)
  · exact absurd ((evict_none_iff _).1 hn) hne

/-- The touched entry (stamp = clock) is the most recent: every other entry has a smaller stamp. This is the order
that eviction reads (`insert_evicts_lru` replaces the smallest stamp), so stamp order is recency order. -/
theorem touch_most_recent {st : Cache} (hS : StampsOk st) {i : Nat} {e : Entry} (he : st.slots[i]? = some (some e))
    (hst : e.stamp = st.clock) : ∀ (k : Nat) (t : Entry), st.slots[k]? = some (some t) → k ≠ i → t.stamp < st.clock := by
  intro k t hk hki
  have h1 := hS.1 k t hk
  refine Nat.lt_of_le_of_ne h1 fun heq => hki ?_
  exact hS.2 k i t e hk he (by rw [heq, hst])

/-- `PrekeyCache.get_most_recent`: after a hit, the entry found carries the clock value and every other entry is older. -/
theorem get_most_recent {st : Cache} {h : List Nat} {i : Nat} {e : Entry} (hi : st.slots[i]? = some (some e))
    (he : e.hash = h) (hH : HashesDistinct st) (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64) :
    ∃ (j : Nat) (f : Entry), (get st h).1.slots[j]? = some (some f) ∧ f.hash = h ∧ f.stamp = (get st h).1.clock ∧
      ∀ (k : Nat) (t : Entry), (get st h).1.slots[k]? = some (some t) → k ≠ j → t.stamp < (get st h).1.clock := by
  obtain ⟨_, hsl, _⟩ := get_refreshes hi he hH hc
  have hS' := (get_inv hH hS hc h).2
  have hclk := get_clock st h
  have hf : (get st h).1.slots[i]? = some (some { e with stamp := st.clock + 1 }) := by
    rw [hsl]; simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
  refine ⟨i, _, hf, he, by rw [hclk, tick_eq hc], touch_most_recent hS' hf (by rw [hclk, tick_eq hc])⟩

/-- `PrekeyCache.insert_most_recent`: with a slot (`N > 0`) the entry of the inserted hash carries the clock value
afterwards and every other entry is older. -/
theorem insert_most_recent {st : Cache} {h : List Nat} {v : Nat} (hH : HashesDistinct st) (hS : StampsOk st)
    (hne : st.slots ≠ []) (hc : st.clock + 1 < 2 ^ 64) :
    ∃ (j : Nat) (f : Entry), (insert st h v).slots[j]? = some (some f) ∧ f.hash = h ∧ f.stamp = (insert st h v).clock ∧
      ∀ (k : Nat) (t : Entry), (insert st h v).slots[k]? = some (some t) → k ≠ j → t.stamp < (insert st h v).clock := by
  have hS' := (insert_inv hH hS hc h v).2
  have hclk := insert_clock st h v
  rcases insert_cases st h v with ⟨i, e, hi, he, hg⟩ | ⟨_, ⟨j, hj, hg⟩ | ⟨hn, _⟩⟩
  · have hf : (insert st h v).slots[i]? = some (some { e with stamp := st.clock + 1 }) := by
      rw [insert_known hi he hH hc]; simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
    exact ⟨i, _, hf, he, by rw [hclk, tick_eq hc], touch_most_recent hS' hf (by rw [hclk, tick_eq hc])⟩
  · have hf : (insert st h v).slots[j]? = some (some ⟨h, v, st.clock + 1⟩) := by
      rw [hg, tick_eq hc]; simp [List.getElem?_set_self (evict_lt hj)]
    exact ⟨j, _, hf, rfl, by rw [hclk, tick_eq hc], touch_most_recent hS' hf (by rw [hclk, tick_eq hc])⟩
  · exact absurd ((evict_none_iff _).1 hn) hne

end Pinc.PrekeyCache

#audit_axioms Pinc.PrekeyCache.evict_lt
#audit_axioms Pinc.PrekeyCache.evict_none_iff
#audit_axioms Pinc.PrekeyCache.evict_empty
#audit_axioms Pinc.PrekeyCache.evict_min
#audit_axioms Pinc.PrekeyCache.cache_inv
#audit_axioms Pinc.PrekeyCache.cache_len
#audit_axioms Pinc.PrekeyCache.cache_zero
#audit_axioms Pinc.PrekeyCache.get_refreshes
#audit_axioms Pinc.PrekeyCache.get_miss
#audit_axioms Pinc.PrekeyCache.insert_known
#audit_axioms Pinc.PrekeyCache.insert_fills_empty
#audit_axioms Pinc.PrekeyCache.insert_evicts_lru
#audit_axioms Pinc.PrekeyCache.get_after_insert
#audit_axioms Pinc.PrekeyCache.touch_most_recent
#audit_axioms Pinc.PrekeyCache.get_most_recent
#audit_axioms Pinc.PrekeyCache.insert_most_recent
