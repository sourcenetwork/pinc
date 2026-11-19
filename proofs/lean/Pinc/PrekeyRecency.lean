import Pinc.PrekeyCache

/-!
# The prekey cache is a recency list

`PrekeyCache.tla` checks, for small `N`, that the stamp implementation refines an independent recency list. This file
proves it in Lean for every capacity `N` and every sequence of operations from empty.

The reference (`refGet`, `refInsert`) has no stamps. It is a list of `(hash, key)` pairs, most recent first. A `get`
that finds the hash moves it to the front and returns the key; a miss changes nothing. An `insert` of a known hash
moves it to the front (the cached key is kept); a new hash goes to the front and the list is cut to its first `N`
entries, so the last (the least recently used) is dropped when the list is over `N`. The hashes of a list are pairwise
distinct, so removing "the entry with this hash" is removing the one entry.

`Sorted st es` says that `es` is the entries of the slots ordered by decreasing stamp: strictly decreasing stamps, and
the members are exactly the occupied slots. `Sim st L` says that `L` is those entries without their stamps. With
distinct stamps (`StampsOk`) the sorted list is unique (`sorted_unique`), so `Sim` is a function of the cache: ordering
the entries by stamp, descending, gives exactly the list.

`run_sim` is the refinement: from empty, over any list of operations (fewer than `2^64`, the ceiling of
`PrekeyCache`), the cache stays related to the list and every `get` answers as the list does.
-/

namespace Pinc.PrekeyRecency
open Pinc.PrekeyCache
open Pinc.Tickets (set_get_cases replicate_none_get)

/-- A list entry: hash and key. -/
abbrev Pr := List Nat × Nat

def pr (e : Entry) : Pr := (e.hash, e.val)

/-! ## The reference -/

/-- `get` on the reference: a hit moves the entry to the front and returns its key. -/
def refGet (L : List Pr) (h : List Nat) : List Pr × Option Nat :=
  match L.find? (fun p => decide (p.1 = h)) with
  | some p => (p :: L.filter (fun q => decide (q.1 ≠ h)), some p.2)
  | none => (L, none)

/-- `insert` on the reference: a known hash moves to the front with its key; a new one goes to the front and the list
is cut to `N` entries. -/
def refInsert (N : Nat) (L : List Pr) (h : List Nat) (v : Nat) : List Pr :=
  match L.find? (fun p => decide (p.1 = h)) with
  | some p => p :: L.filter (fun q => decide (q.1 ≠ h))
  | none => ((h, v) :: L).take N

/-! ## The relation -/

/-- `es` is the occupied slots ordered by decreasing stamp. -/
def Sorted (st : Cache) (es : List Entry) : Prop :=
  es.Pairwise (fun a b => b.stamp < a.stamp) ∧ ∀ f : Entry, f ∈ es ↔ ∃ i : Nat, st.slots[i]? = some (some f)

/-- `L` is the entries of the cache, most recent (highest stamp) first, without their stamps. -/
def Sim (st : Cache) (L : List Pr) : Prop := ∃ es, Sorted st es ∧ L = es.map pr

theorem nodup_of_sorted {st : Cache} {es : List Entry} (hs : Sorted st es) : es.Nodup :=
  hs.1.imp (fun {a b} h hab => by subst hab; exact absurd h (Nat.lt_irrefl _))

/-- The entries in the slots, in slot order. -/
def ents (l : Ents) : List Entry := l.filterMap id

theorem ents_mem {l : Ents} {e : Entry} : e ∈ ents l ↔ ∃ i : Nat, l[i]? = some (some e) := by
  unfold ents
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    exact ⟨i, by rw [hi]; simpa using h⟩
  · rintro ⟨i, hi⟩
    exact ⟨some e, List.mem_iff_getElem?.mpr ⟨i, hi⟩, rfl⟩

theorem ents_length (l : Ents) : (ents l).length = occE l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases x <;> simp [ents, occE] at ih ⊢ <;> omega

theorem ents_nodup : ∀ (l : Ents),
    (∀ (i j : Nat) (e f : Entry), l[i]? = some (some e) → l[j]? = some (some f) → e.stamp = f.stamp → i = j) →
    (ents l).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons x l ih =>
    intro hS
    have hS' : ∀ (i j : Nat) (e f : Entry), l[i]? = some (some e) → l[j]? = some (some f) → e.stamp = f.stamp → i = j :=
      fun i j e f he hf hst => by
        have := hS (i + 1) (j + 1) e f (by simpa using he) (by simpa using hf) hst
        omega
    cases x with
    | none => simpa [ents] using ih hS'
    | some x =>
      have h1 : ents (some x :: l) = x :: ents l := by simp [ents]
      rw [h1, List.nodup_cons]
      refine ⟨fun hm => ?_, ih hS'⟩
      obtain ⟨k, hk⟩ := ents_mem.mp hm
      have := hS 0 (k + 1) x x (by simp) (by simpa using hk) rfl
      omega

/-- The sorted list has one entry per occupied slot. -/
theorem sorted_length {st : Cache} {es : List Entry} (hs : Sorted st es) (hS : StampsOk st) :
    es.length = occE st.slots := by
  rw [← ents_length]
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (nodup_of_sorted hs) (ents_nodup _ hS.2)).2 fun a => ?_)
  rw [hs.2 a, ents_mem]

/-- The sorted list is unique: the entries ordered by decreasing stamp. -/
theorem sorted_unique {st : Cache} {es fs : List Entry} (hs : Sorted st es) (ht : Sorted st fs) : es = fs := by
  have hp : es.Perm fs :=
    (List.perm_ext_iff_of_nodup (nodup_of_sorted hs) (nodup_of_sorted ht)).2 fun a => by rw [hs.2 a, ht.2 a]
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl _)) hs.1 ht.1 hp

theorem stamp_le {st : Cache} {es : List Entry} (hs : Sorted st es) (hS : StampsOk st) {a : Entry} (ha : a ∈ es) :
    a.stamp ≤ st.clock := by
  obtain ⟨i, hi⟩ := (hs.2 a).1 ha
  exact hS.1 i a hi

theorem hash_unique {st : Cache} {es : List Entry} (hs : Sorted st es) (hH : HashesDistinct st) {e x : Entry}
    (he : e ∈ es) (hx : x ∈ es) (hh : x.hash = e.hash) : x = e := by
  obtain ⟨i, hi⟩ := (hs.2 e).1 he
  obtain ⟨j, hj⟩ := (hs.2 x).1 hx
  have := hH j i x e hj hi hh
  subst this
  rw [hi] at hj
  exact (Option.some.inj (Option.some.inj hj)).symm

/-! ## Lookups on the reference agree with lookups on the entries -/

theorem find_miss {es : List Entry} {h : List Nat} (hm : ∀ x ∈ es, x.hash ≠ h) :
    (es.map pr).find? (fun p => decide (p.1 = h)) = none := by
  rw [List.find?_eq_none]
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  simp [pr, hm x hx]

theorem find_hit {st : Cache} {es : List Entry} (hs : Sorted st es) (hH : HashesDistinct st) {e : Entry}
    (he : e ∈ es) : (es.map pr).find? (fun p => decide (p.1 = e.hash)) = some (pr e) := by
  cases hf : (es.map pr).find? (fun p => decide (p.1 = e.hash)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [pr]) (hf (pr e) (List.mem_map.2 ⟨e, he, rfl⟩))
  | some p =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    have := hash_unique hs hH he hx (of_decide_eq_true hp)
    rw [this]

theorem filter_pr (es : List Entry) (h : List Nat) :
    (es.map pr).filter (fun q => decide (q.1 ≠ h)) = (es.filter (fun f => decide (f.hash ≠ h))).map pr := by
  rw [List.filter_map]
  rfl

/-! ## The slot updates keep the order -/

/-- A hit (a `get` or an `insert` of a known hash) puts the refreshed entry in front of the others. -/
theorem sorted_hit {st : Cache} {es : List Entry} (hs : Sorted st es) (hH : HashesDistinct st) (hS : StampsOk st)
    {i : Nat} {e : Entry} (hi : st.slots[i]? = some (some e)) (c : Nat) (hc : c = st.clock + 1) :
    Sorted ⟨st.slots.set i (some { e with stamp := c }), c⟩
      ({ e with stamp := c } :: es.filter (fun f => decide (f.hash ≠ e.hash))) := by
  have hei : e ∈ es := (hs.2 e).2 ⟨i, hi⟩
  have hil : i < st.slots.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨?_, fun f => ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨fun a ha => ?_, hs.1.sublist (List.filter_sublist)⟩
    have := stamp_le hs hS (List.mem_filter.mp ha).1
    simp only; omega
  · simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨hf, hne⟩)
      · exact ⟨i, by simp [List.getElem?_set_self hil]⟩
      · obtain ⟨k, hk⟩ := (hs.2 f).1 hf
        have hki : k ≠ i := by
          rintro rfl
          rw [hi] at hk
          exact hne (by cases hk; rfl)
        exact ⟨k, by simp [List.getElem?_set_ne (Ne.symm hki), hk]⟩
    · rintro ⟨k, hk⟩
      rcases set_get_cases hk with ⟨_, hy, _⟩ | ⟨hki, hk'⟩
      · exact Or.inl (Option.some.inj hy)
      · refine Or.inr ⟨(hs.2 f).2 ⟨k, hk'⟩, fun hh => hki ?_⟩
        exact hH k i f e hk' hi hh

/-- A new entry in an empty slot goes in front. -/
theorem sorted_add_empty {st : Cache} {es : List Entry} (hs : Sorted st es) (hS : StampsOk st) {j : Nat}
    (hj : st.slots[j]? = some none) (h : List Nat) (v c : Nat) (hc : c = st.clock + 1) :
    Sorted ⟨st.slots.set j (some ⟨h, v, c⟩), c⟩ (⟨h, v, c⟩ :: es) := by
  have hjl : j < st.slots.length := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨?_, fun f => ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨fun a ha => ?_, hs.1⟩
    have := stamp_le hs hS ha
    simp only; omega
  · simp only [List.mem_cons]
    constructor
    · rintro (rfl | hf)
      · exact ⟨j, by simp [List.getElem?_set_self hjl]⟩
      · obtain ⟨k, hk⟩ := (hs.2 f).1 hf
        have hkj : k ≠ j := by rintro rfl; rw [hj] at hk; simp at hk
        exact ⟨k, by simp [List.getElem?_set_ne (Ne.symm hkj), hk]⟩
    · rintro ⟨k, hk⟩
      rcases set_get_cases hk with ⟨_, hy, _⟩ | ⟨hkj, hk'⟩
      · exact Or.inl (Option.some.inj hy)
      · exact Or.inr ((hs.2 f).2 ⟨k, hk'⟩)

/-- In a full cache the entry with the lowest stamp is the last of the list; the new entry replaces it in front. -/
theorem sorted_evict {st : Cache} {es : List Entry} (hs : Sorted st es) (hS : StampsOk st) {j : Nat} {old : Entry}
    (hj : st.slots[j]? = some (some old))
    (hmin : ∀ (k : Nat) (t : Entry), st.slots[k]? = some (some t) → old.stamp ≤ t.stamp)
    (h : List Nat) (v c : Nat) (hc : c = st.clock + 1) :
    es = es.dropLast ++ [old] ∧
      Sorted ⟨st.slots.set j (some ⟨h, v, c⟩), c⟩ (⟨h, v, c⟩ :: es.dropLast) := by
  have hjl : j < st.slots.length := (List.getElem?_eq_some_iff.mp hj).1
  have hold : old ∈ es := (hs.2 old).2 ⟨j, hj⟩
  have hne : es ≠ [] := List.ne_nil_of_mem hold
  have hsplit : es = es.dropLast ++ [es.getLast hne] := (List.dropLast_concat_getLast hne).symm
  have hpw : (es.dropLast ++ [es.getLast hne]).Pairwise (fun a b => b.stamp < a.stamp) := by
    rw [← hsplit]; exact hs.1
  rw [List.pairwise_append] at hpw
  have hlast : es.getLast hne ∈ es := List.getLast_mem hne
  -- the last entry is `old`
  have hOL : es.getLast hne = old := by
    have hm : old ∈ es.dropLast ++ [es.getLast hne] := by rw [← hsplit]; exact hold
    rcases List.mem_append.mp hm with hd | hd
    · exfalso
      have h1 := hpw.2.2 old hd (es.getLast hne) (by simp)
      obtain ⟨k, hk⟩ := (hs.2 _).1 hlast
      have := hmin k _ hk
      omega
    · exact (List.mem_singleton.mp hd).symm
  rw [hOL] at hsplit
  have hdm : ∀ x, x ∈ es.dropLast ↔ x ∈ es ∧ x ≠ old := by
    intro x
    constructor
    · intro hx
      refine ⟨List.dropLast_subset _ hx, fun hxo => ?_⟩
      subst hxo
      have := hpw.2.2 x hx x (by simp [hOL])
      omega
    · rintro ⟨hx, hne'⟩
      have hm : x ∈ es.dropLast ++ [old] := by rw [← hsplit]; exact hx
      rcases List.mem_append.mp hm with hd | hd
      · exact hd
      · exact absurd (by simpa using hd) hne'
  refine ⟨hsplit, ?_, fun f => ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨fun a ha => ?_, hs.1.sublist (List.dropLast_sublist _)⟩
    have := stamp_le hs hS (List.dropLast_subset _ ha)
    simp only; omega
  · simp only [List.mem_cons, hdm]
    constructor
    · rintro (rfl | ⟨hf, hfo⟩)
      · exact ⟨j, by simp [List.getElem?_set_self hjl]⟩
      · obtain ⟨k, hk⟩ := (hs.2 f).1 hf
        have hkj : k ≠ j := by
          rintro rfl
          rw [hj] at hk
          exact hfo (by cases hk; rfl)
        exact ⟨k, by simp [List.getElem?_set_ne (Ne.symm hkj), hk]⟩
    · rintro ⟨k, hk⟩
      rcases set_get_cases hk with ⟨_, hy, _⟩ | ⟨hkj, hk'⟩
      · exact Or.inl (Option.some.inj hy)
      · refine Or.inr ⟨(hs.2 f).2 ⟨k, hk'⟩, fun hfo => hkj ?_⟩
        subst hfo
        have := hS.2 k j f f hk' hj rfl
        exact this

/-! ## The operations refine the list -/

theorem sim_get {st : Cache} {L : List Pr} (hH : HashesDistinct st) (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64)
    (h : List Nat) (hsim : Sim st L) :
    Sim (get st h).1 (refGet L h).1 ∧ (get st h).2 = (refGet L h).2 := by
  obtain ⟨es, hs, rfl⟩ := hsim
  rcases get_cases st h with ⟨habs, he⟩ | ⟨i, e, hi, hh, he⟩
  · have hm : ∀ x ∈ es, x.hash ≠ h := fun x hx hxh =>
      habs _ x (((hs.2 x).1 hx).choose_spec) hxh |> fun _ => by
        obtain ⟨k, hk⟩ := (hs.2 x).1 hx
        exact habs k x hk hxh
    rw [he]
    simp only [refGet, find_miss hm]
    exact ⟨⟨es, hs, rfl⟩, trivial⟩
  · have hei : e ∈ es := (hs.2 e).2 ⟨i, hi⟩
    rw [he, tick_eq hc]
    have hfind := find_hit hs hH hei
    subst hh
    simp only [refGet, hfind]
    refine ⟨⟨{ e with stamp := st.clock + 1 } :: es.filter (fun f => decide (f.hash ≠ e.hash)), ?_, ?_⟩, rfl⟩
    · exact sorted_hit hs hH hS hi (st.clock + 1) rfl
    · simp only [List.map_cons, filter_pr]
      rfl

theorem sim_insert {st : Cache} {L : List Pr} {N : Nat} (hlen : st.slots.length = N) (hH : HashesDistinct st)
    (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64) (h : List Nat) (v : Nat) (hsim : Sim st L) :
    Sim (insert st h v) (refInsert N L h v) := by
  obtain ⟨es, hs, rfl⟩ := hsim
  have hcl : st.clock + 1 = tick st.clock := (tick_eq hc).symm
  rcases insert_cases st h v with ⟨i, e, hi, hh, he⟩ | ⟨habs, ⟨j, hj, he⟩ | ⟨hn, he⟩⟩
  · -- known hash
    have hei : e ∈ es := (hs.2 e).2 ⟨i, hi⟩
    rw [he]
    have hfind := find_hit hs hH hei
    subst hh
    simp only [refInsert, hfind]
    refine ⟨{ e with stamp := tick st.clock } :: es.filter (fun f => decide (f.hash ≠ e.hash)), ?_, ?_⟩
    · exact sorted_hit hs hH hS hi (tick st.clock) hcl.symm
    · simp only [List.map_cons, filter_pr]
      rfl
  · -- a new hash, a slot to take
    have hm : ∀ x ∈ es, x.hash ≠ h := fun x hx hxh => by
      obtain ⟨k, hk⟩ := (hs.2 x).1 hx
      exact habs k x hk hxh
    rw [he]
    simp only [refInsert, find_miss hm]
    by_cases hex : ∃ k : Nat, st.slots[k]? = some none
    · have hjn := evict_empty hj hex
      refine ⟨_, sorted_add_empty hs hS hjn h v _ hcl.symm, ?_⟩
      have hlt : es.length < N := by
        rw [sorted_length hs hS, ← hlen]
        unfold occE
        refine (List.length_filter_lt_length_iff_exists).2 ?_
        obtain ⟨k, hk⟩ := hex
        exact ⟨none, List.mem_iff_getElem?.mpr ⟨k, hk⟩, by simp⟩
      rw [List.take_of_length_le (by simp; omega)]
      rfl
    · have hfull : ∀ k : Nat, st.slots[k]? ≠ some none := fun k hk => hex ⟨k, hk⟩
      obtain ⟨old, hold, hmin⟩ := evict_min hj hfull
      obtain ⟨hsplit, hsorted⟩ := sorted_evict hs hS hold (fun k t hk => hmin k t hk) h v _ hcl.symm
      have hne : es ≠ [] := by intro h0; rw [h0] at hsplit; simp at hsplit
      refine ⟨_, hsorted, ?_⟩
      have hesN : es.length = N := by
        rw [sorted_length hs hS, ← hlen]
        unfold occE
        refine List.length_filter_eq_length_iff.2 fun x hx => ?_
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
        cases x with
        | none => exact absurd hk (hfull k)
        | some _ => rfl
      obtain ⟨m, hm'⟩ : ∃ m, N = m + 1 := ⟨N - 1, by
        have : 0 < es.length := Nat.pos_of_ne_zero (fun h0 => hne (List.length_eq_zero_iff.mp h0))
        omega⟩
      have : (⟨h, v, tick st.clock⟩ :: es).length = N + 1 := by simp [hesN]
      simp only [List.map_cons, List.take_succ_cons, hm']
      rw [List.dropLast_eq_take]
      have : es.length - 1 = m := by omega
      rw [this, List.map_take]
      rfl
  · -- no slot at all
    have hs0 : st.slots = [] := (evict_none_iff _).1 hn
    have hN : N = 0 := by rw [← hlen, hs0]; rfl
    have hes : es = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
      obtain ⟨k, hk⟩ := (hs.2 x).1 hx
      rw [hs0] at hk
      simp at hk
    subst hes
    rw [he]
    simp only [refInsert, List.map_nil, List.find?_nil, hN, List.take_zero]
    exact ⟨[], ⟨List.Pairwise.nil, fun f => by simp [hs0]⟩, rfl⟩

/-! ## Any sequence of operations -/

inductive Op where
  | get (h : List Nat)
  | insert (h : List Nat) (v : Nat)

def stepC (st : Cache) : Op → Cache × Option Nat
  | .get h => get st h
  | .insert h v => (insert st h v, none)

def stepR (N : Nat) (L : List Pr) : Op → List Pr × Option Nat
  | .get h => refGet L h
  | .insert h v => (refInsert N L h v, none)

/-- Run a list of operations, collecting the answer of each (`none` for an insert). -/
def run {α : Type} (step : α → Op → α × Option Nat) : α → List Op → α × List (Option Nat)
  | s, [] => (s, [])
  | s, o :: os =>
    let r := step s o
    let t := run step r.1 os
    (t.1, r.2 :: t.2)

theorem stepC_inv {st : Cache} (hH : HashesDistinct st) (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64) (o : Op) :
    HashesDistinct (stepC st o).1 ∧ StampsOk (stepC st o).1 := by
  cases o with
  | get h => exact get_inv hH hS hc h
  | insert h v => exact insert_inv hH hS hc h v

theorem stepC_clock (st : Cache) (o : Op) : (stepC st o).1.clock = tick st.clock := by
  cases o with
  | get h => exact get_clock st h
  | insert h v => exact insert_clock st h v

theorem stepC_length (st : Cache) (o : Op) : (stepC st o).1.slots.length = st.slots.length := by
  cases o with
  | get h => exact get_length st h
  | insert h v => exact insert_length st h v

theorem step_sim {N : Nat} {st : Cache} {L : List Pr} (hlen : st.slots.length = N) (hH : HashesDistinct st)
    (hS : StampsOk st) (hc : st.clock + 1 < 2 ^ 64) (hsim : Sim st L) (o : Op) :
    Sim (stepC st o).1 (stepR N L o).1 ∧ (stepC st o).2 = (stepR N L o).2 := by
  cases o with
  | get h => exact sim_get hH hS hc h hsim
  | insert h v => exact ⟨sim_insert hlen hH hS hc h v hsim, rfl⟩

theorem run_sim {N : Nat} : ∀ (ops : List Op) (st : Cache) (L : List Pr) (k : Nat),
    st.slots.length = N → st.clock = k → k + ops.length < 2 ^ 64 → HashesDistinct st → StampsOk st → Sim st L →
    Sim (run stepC st ops).1 (run (stepR N) L ops).1 ∧ (run stepC st ops).2 = (run (stepR N) L ops).2 := by
  intro ops
  induction ops with
  | nil => intro st L k _ _ _ _ _ hsim; exact ⟨hsim, rfl⟩
  | cons o os ih =>
    intro st L k hlen hck hk hH hS hsim
    simp only [List.length_cons] at hk
    have hc : st.clock + 1 < 2 ^ 64 := by omega
    obtain ⟨hsim1, hans⟩ := step_sim hlen hH hS hc hsim o
    obtain ⟨hH1, hS1⟩ := stepC_inv hH hS hc o
    have hcl : (stepC st o).1.clock = k + 1 := by
      rw [stepC_clock, tick_eq hc, hck]
    obtain ⟨r1, r2⟩ := ih (stepC st o).1 (stepR N L o).1 (k + 1) (by rw [stepC_length]; exact hlen) hcl
      (by omega) hH1 hS1 hsim1
    simp only [run]
    exact ⟨r1, by rw [r2, hans]⟩

/-- `PrekeyRecency.cache_refines_list`: from an empty cache of any capacity `N`, over any sequence of fewer than
`2^64` operations, the entries of the cache ordered by decreasing stamp are exactly the recency list (`get` moves the
hash to the front, `insert` puts it at the front and drops the last when the list is over `N`), and every `get` answers
as the list does (same hit, same key). -/
theorem cache_refines_list (N : Nat) (ops : List Op) (hn : ops.length < 2 ^ 64) :
    Sim (run stepC (Cache.empty N) ops).1 (run (stepR N) [] ops).1 ∧
      (run stepC (Cache.empty N) ops).2 = (run (stepR N) [] ops).2 := by
  refine run_sim ops (Cache.empty N) [] 0 (by simp [Cache.empty]) rfl (by omega)
    (fun i j e f hs => (replicate_none_get hs).elim) ⟨?_, fun i j e f hs => (replicate_none_get hs).elim⟩ ?_
  · intro i e hs; exact (replicate_none_get hs).elim
  · exact ⟨[], ⟨List.Pairwise.nil, fun f => ⟨fun h => by simp at h, fun ⟨i, hi⟩ => (replicate_none_get hi).elim⟩⟩, rfl⟩

end Pinc.PrekeyRecency

#audit_axioms Pinc.PrekeyRecency.sorted_unique
#audit_axioms Pinc.PrekeyRecency.sorted_length
#audit_axioms Pinc.PrekeyRecency.sim_get
#audit_axioms Pinc.PrekeyRecency.sim_insert
#audit_axioms Pinc.PrekeyRecency.run_sim
#audit_axioms Pinc.PrekeyRecency.cache_refines_list
