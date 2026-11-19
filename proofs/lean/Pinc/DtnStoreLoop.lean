import Pinc.DtnStoreAdmit

/-!
# The charged store: the fit test and the eviction loop

`fits` is the test of `admitItem` before it evicts anything (the sums are the code's saturating `u64` sums), `evictLoop` is
its `while` loop: while the free bytes are fewer than the item needs or every slot is taken, take the oldest transit
item. The loop is written as the recursion that returns the evictions the loop makes (the code accumulates them in the
callback), with the number of slots as fuel: every round removes one item.

`fits_iff` states the test independently of the code's arithmetic: it passes exactly when the items that cannot be
evicted (custody) leave room in bytes and in slots. `evictLoop_spec` proves, for every ledger that passes, that the loop
succeeds, evicts transit items only, oldest admission first, and stops as soon as there is room.
-/

namespace Pinc.DtnStore

/-- A transit item. -/
def isTransit (e : Entry) : Bool := decide (e.cls = .transit)

/-- The saturating sum of the sizes of the transit items (`transit_bytes`). -/
def transitBytes (L : Ledger) : Nat := (L.entries.filter isTransit).foldl (fun b e => satAdd b e.bytes) 0

/-- The test of `admitItem`: the free bytes plus the transit bytes cover the item, and a slot is free or a transit item
holds one. -/
def fits (L : Ledger) (bytes : Nat) : Bool :=
  decide (bytes ≤ satAdd (L.budget - L.used) (transitBytes L) ∧
    (0 < L.slots.length - L.entries.length ∨ 0 < (L.entries.filter isTransit).length))

/-- The test stated by what cannot be evicted: the custody items plus the new item fit the budget, and leave a slot. -/
def FitsSpec (L : Ledger) (bytes : Nat) : Prop :=
  sumB (L.entries.filter fun e => !isTransit e) + bytes ≤ L.budget ∧
    (L.entries.filter fun e => !isTransit e).length < L.slots.length

/-- The loop condition: fewer free bytes than needed, or no free slot. -/
def room (L : Ledger) (bytes : Nat) : Bool := decide (L.budget - L.used < bytes ∨ L.entries.length = L.slots.length)

/-- The eviction loop with `fuel` rounds; `none` is the unreachable `ok_or(refused)` exit (proved so below). -/
def evictLoop (bytes : Nat) : Nat → Ledger → Option (Ledger × List Entry)
  | 0, L => if room L bytes then none else some (L, [])
  | f + 1, L =>
    if room L bytes then
      match oldestIdx L with
      | none => none
      | some i =>
        match takeAt L i with
        | none => none
        | some (L', e) => (evictLoop bytes f L').map fun r => (r.1, e :: r.2)
    else some (L, [])

theorem len_split (es : List Entry) (p : Entry → Bool) :
    es.length = (es.filter p).length + (es.filter fun e => !p e).length := by
  have := (List.filter_append_perm p es).length_eq
  simp at this; omega

theorem fits_iff {L : Ledger} (hI : Inv L) (b : Nat) : fits L b = true ↔ FitsSpec L b := by
  have hs := sumB_filter isTransit L.entries
  have hl := len_split L.entries isTransit
  have hlen : L.entries.length ≤ L.slots.length := List.length_filterMap_le _ _
  have hle : sumB L.entries ≤ L.budget := by have := hI.used_eq; have := hI.used_le; omega
  have hT : transitBytes L = sumB (L.entries.filter isTransit) := by
    unfold transitBytes
    rw [satAdd_foldl 0 (by simp [MAX]), Nat.zero_add]
    have : sumB (L.entries.filter isTransit) ≤ MAX := by have := hI.budget_le; omega
    omega
  have hsat : satAdd (L.budget - L.used) (transitBytes L) = L.budget - L.used + sumB (L.entries.filter isTransit) := by
    rw [hT]; unfold satAdd; have := hI.budget_le; have := hI.used_eq; omega
  unfold fits FitsSpec
  rw [decide_eq_true_iff, hsat]
  have := hI.used_eq
  have := hI.used_le
  constructor
  · rintro ⟨h1, h2⟩; omega
  · rintro ⟨h1, h2⟩; omega

theorem takeAt_facts {L L' : Ledger} {i : Nat} {e : Entry} (h : takeAt L i = some (L', e)) :
    L'.budget = L.budget ∧ L'.nextSeq = L.nextSeq ∧ L'.slots.length = L.slots.length ∧ L'.used = L.used - e.bytes := by
  unfold takeAt at h; split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  · simp at h

theorem evictLoop_spec (b : Nat) : ∀ (fuel : Nat) (L : Ledger), Inv L → FitsSpec L b → L.entries.length ≤ fuel →
    ∃ L2 ev, evictLoop b fuel L = some (L2, ev) ∧ Inv L2 ∧ L2.budget = L.budget ∧ L2.nextSeq = L.nextSeq ∧
      L2.slots.length = L.slots.length ∧ L.entries.Perm (ev ++ L2.entries) ∧ L2.used = L.used - sumB ev ∧
      (∀ e ∈ ev, e.cls = .transit) ∧ room L2 b = false ∧ ev.Pairwise (fun x y => x.seq < y.seq) ∧
      (∀ e ∈ ev, ∀ r ∈ L2.entries, r.cls = .transit → e.seq < r.seq) ∧
      (∀ l, ev.getLast? = some l → L.budget - (L2.used + l.bytes) < b ∨ L2.entries.length + 1 = L2.slots.length) := by
  intro fuel
  induction fuel with
  | zero =>
    intro L hI hF hlen
    have hnil : L.entries = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hroom : room L b = false := by
      unfold room
      have h1 := hF.1; have h2 := hF.2
      have hu := hI.used_eq
      rw [hnil] at hu h1 h2
      simp [sumB] at hu h1 h2
      simp only [decide_eq_false_iff_not]
      rw [hnil]; simp; omega
    refine ⟨L, [], by simp [evictLoop, hroom], hI, rfl, rfl, rfl, by simp, by simp [sumB], by simp, hroom, by simp,
      by simp, by simp⟩
  | succ f ih =>
    intro L hI hF hlen
    by_cases hroom : room L b = true
    · -- a round: take the oldest transit item
      have hex : ∃ e ∈ L.entries, e.cls = .transit := by
        by_cases hc : ∃ e ∈ L.entries, e.cls = .transit
        · exact hc
        · exfalso
          have hall : ∀ e ∈ L.entries, ¬ e.cls = .transit := fun e he ht => hc ⟨e, he, ht⟩
          have hfe : L.entries.filter (fun e => !isTransit e) = L.entries := by
            apply List.filter_eq_self.2
            intro e he; simpa [isTransit] using hall e he
          have h1 := hF.1; have h2 := hF.2
          rw [hfe] at h1 h2
          have hu := hI.used_eq
          unfold room at hroom
          rw [decide_eq_true_iff] at hroom
          omega
      have hmt : (minT L.slots 0).isSome = true := by
        cases h : minT L.slots 0 with
        | none =>
          exfalso
          obtain ⟨e, he, ht⟩ := hex
          exact (((minT_none L.slots 0).1 h) e he) ht
        | some _ => rfl
      obtain ⟨⟨q, j⟩, hmj⟩ := Option.isSome_iff_exists.1 hmt
      obtain ⟨-, e, hge, hec, heq, hmin⟩ := minT_some L.slots 0 q j hmj
      have hge' : L.slots[j]? = some (some e) := by simpa using hge
      have htake : takeAt L j = some ({ L with used := L.used - e.bytes, slots := L.slots.set j none }, e) := by
        simp [takeAt, hge']
      generalize ({ L with used := L.used - e.bytes, slots := L.slots.set j none } : Ledger) = L' at htake
      have hperm := takeAt_perm htake
      have hI' := takeAt_inv hI htake
      obtain ⟨hb', hs', hsl', hu'⟩ := takeAt_facts htake
      have hlen' : L'.entries.length ≤ f := by have := hperm.length_eq; simp at this; omega
      have hF' : FitsSpec L' b := by
        have hnt : (L.entries.filter fun x => !isTransit x).Perm (L'.entries.filter fun x => !isTransit x) := by
          have := hperm.filter (fun x => !isTransit x)
          simpa [List.filter_cons, isTransit, hec] using this
        exact ⟨by rw [← sumB_perm hnt, hb']; exact hF.1, by rw [← hnt.length_eq, hsl']; exact hF.2⟩
      obtain ⟨L2, ev, hev, hI2, hb2, hs2, hsl2, hp2, hu2, htr2, hrm2, hpw2, hlt2, hlast2⟩ := ih L' hI' hF' hlen'
      have hnodup := hI.seqs
      have hmem' : ∀ x ∈ L'.entries, x ∈ L.entries ∧ x.seq ≠ e.seq := by
        intro x hx
        refine ⟨hperm.symm.mem_iff.1 (List.mem_cons_of_mem _ hx), ?_⟩
        have := (hperm.map (·.seq)).nodup_iff.1 hnodup
        simp only [List.map_cons, List.nodup_cons] at this
        intro heq'
        exact this.1 (List.mem_map.2 ⟨x, hx, heq'⟩)
      refine ⟨L2, e :: ev, ?_, hI2, by rw [hb2, hb'], by rw [hs2, hs'], by rw [hsl2, hsl'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [evictLoop, hroom, oldestIdx, hmj, htake, hev]
      · exact hperm.trans (by simpa using hp2.cons e)
      · rw [hu2, hu', sumB_cons]
        have h3 := sumB_perm hp2
        rw [sumB_append] at h3
        have h4 := hI'.used_eq
        have h5 := hI2.used_eq
        have h6 := hI.used_le
        omega
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hec
        · exact htr2 x hx
      · exact hrm2
      · refine List.pairwise_cons.2 ⟨?_, hpw2⟩
        intro x hx
        have hxL : x ∈ L'.entries := hp2.symm.mem_iff.1 (List.mem_append_left _ hx) |> fun h => h
        have hx2 := hmem' x hxL
        have hle := hmin x hx2.1 (htr2 x hx)
        have := hx2.2
        omega
      · intro x hx r hr ht
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · have hrL : r ∈ L'.entries := hp2.symm.mem_iff.1 (List.mem_append_right _ hr)
          have hr2 := hmem' r hrL
          have hle := hmin r hr2.1 ht
          have := hr2.2
          omega
        · exact hlt2 x hx r hr ht
      · intro l hl
        by_cases hnil : ev = []
        · subst hnil
          simp at hl
          subst hl
          have hs := sumB_perm hp2
          have hlen2 := hp2.length_eq
          simp only [List.nil_append] at hs hlen2
          have hs0 := sumB_perm hperm
          rw [sumB_cons] at hs0
          have hu2' : L2.used = L'.used := by
            have := hI2.used_eq; have := hI'.used_eq; omega
          unfold room at hroom
          rw [decide_eq_true_iff] at hroom
          have hlq : L2.entries.length + 1 = L.entries.length := by have := hperm.length_eq; simp at this; omega
          have hsl : L2.slots.length = L.slots.length := by rw [hsl2, hsl']
          have := hI.used_eq
          have := hI.used_le
          rw [hu2', hu']
          rcases hroom with h | h
          · left; omega
          · right; omega
        · have : (e :: ev).getLast? = ev.getLast? := by
            cases ev with
            | nil => exact absurd rfl hnil
            | cons y ys => simp [List.getLast?_cons_cons]
          rw [this] at hl
          have := hlast2 l hl
          rwa [hb'] at this
    · have hr : room L b = false := by simpa using hroom
      refine ⟨L, [], by simp [evictLoop, hr], hI, rfl, rfl, rfl, by simp, by simp [sumB], by simp, hr, by simp,
        by simp, by simp⟩

end Pinc.DtnStore
