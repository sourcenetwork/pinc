import Vinc.DtnCustody

/-!
# Custody: the single-operation theorems

For a ledger with `Inv`, and a book with `NodupB` and `Linked`, each operation of `Vinc.DtnCustody`:

* keeps the invariants (`accept_inv`, `offer_inv`, `onAck_inv`, `delivered_inv`, `bexpire_inv`);
* `accept_err_state`: a refused acceptance changes nothing except the expired items leaving (and their records);
  `accept_capacity_iff`: the book is full exactly when no record is free;
* `onAck_ok_iff`: custody is relieved exactly when the ack is valid, the bundle is held, custody was offered to exactly
  the acknowledging node, and the ledger still holds the item; `onAck_refused_state`: any other ack moves nothing
  (the one exception is documented: a valid, offered ack for an item the ledger already dropped clears the record and
  reports `storeUnknown`);
* `onAck_relief_only`: a relief changes the class of that bundle's item to transit and clears that bundle's record, and
  nothing else;
* `delivered_exits`, `bexpire_exits`: the other exits.
-/

namespace Vinc.DtnStore

theorem expire_noop (L : Ledger) (now : Nat) (h : ∀ x ∈ L.entries, expiredAt now x = false) :
    expire L now = (L, []) := by
  have hnil : L.entries.filter (expiredAt now) = [] := List.filter_eq_nil_iff.2 (fun x hx => by simp [h x hx])
  have hslots : (L.slots.map fun s => s.filter fun e => !expiredAt now e) = L.slots := by
    have : (L.slots.map fun s => s.filter fun e => !expiredAt now e) = L.slots.map id := by
      apply List.map_congr_left
      intro s hs
      cases s with
      | none => simp
      | some v =>
        have : expiredAt now v = false := h v (by simpa [Ledger.entries] using hs)
        simp [Option.filter, this]
    rw [this, List.map_id]
  simp [expire, hnil, hslots, sumB]

theorem expire_idem (L : Ledger) (now : Nat) :
    (expire (expire L now).1 now).1 = (expire L now).1 ∧ (expire (expire L now).1 now).2 = [] := by
  have hent : ∀ x ∈ (expire L now).1.entries, expiredAt now x = false := by
    intro x hx; rw [entries_expire] at hx; simpa using (List.mem_filter.1 hx).2
  rw [expire_noop _ now hent]; exact ⟨rfl, rfl⟩


theorem bkey_inj {a b : Nat} : bkey a = bkey b ↔ a = b := by simp [bkey]

theorem admit_entries_sub {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) :
    ∀ e ∈ (admit L k b c x now).L.entries, e ∈ L.entries ∨ e = ⟨k, b, c, x, L.nextSeq⟩ := by
  intro e he
  have hsub : ∀ y ∈ (expire L now).1.entries, y ∈ L.entries := by
    intro y hy; rw [entries_expire] at hy; exact (List.mem_filter.1 hy).1
  rcases admit_cases hI k b c x now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨hc, hf, L2, ev2, slots', hev, hput, h, hI2, hb2, hs2, hp2, hsl2, htr, hpw, hlt, hrm, hu2, hlast⟩
  · rw [h] at he; exact Or.inl he
  · rw [h] at he; exact Or.inl (hsub e he)
  · rw [h] at he
    have := (put_perm _ _ _ hput).1.mem_iff.1 (by simpa [Ledger.entries] using he)
    simp only [List.mem_cons] at this
    rcases this with rfl | h2
    · right; simp [hs2]
    · left; exact hsub e (hp2.mem_iff.2 (List.mem_append_right _ h2))

theorem set_some_perm (B : Recs) (i : Nat) (r : Record) (h : B[i]? = some none) :
    (recs (B.set i (some r))).Perm (r :: recs B) := by
  have hi : i < B.length := by
    by_cases hc : i < B.length
    · exact hc
    · simp [List.getElem?_eq_none (by omega : B.length ≤ i)] at h
  have hg : B[i] = none := by
    have := List.getElem?_eq_getElem hi
    rw [h] at this; simpa using this.symm
  have hsplit : B = B.take i ++ none :: B.drop (i + 1) := by
    calc B = B.take i ++ B.drop i := (List.take_append_drop i _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hg]
  have hset : B.set i (some r) = B.take i ++ some r :: B.drop (i + 1) := by
    simp [List.set_eq_take_append_cons_drop, hi]
  obtain ⟨A, C, hA, hC⟩ : ∃ A C, B = A ++ none :: C ∧ B.set i (some r) = A ++ some r :: C := ⟨_, _, hsplit, hset ▸ rfl⟩
  have hl : recs B = A.filterMap id ++ C.filterMap id := by
    simp only [recs]; rw [hA]; simp [List.filterMap_append]
  have hr : recs (B.set i (some r)) = A.filterMap id ++ r :: C.filterMap id := by
    simp only [recs]; rw [hC]; simp [List.filterMap_append]
  rw [hr, hl]
  exact List.perm_middle

theorem findIdx_none_slot {B : Recs} {i : Nat} (h : B.findIdx? Option.isNone = some i) : B[i]? = some none := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  have : B[i] = none := by simpa using hp
  rw [List.getElem?_eq_getElem hi, this]

theorem mem_recs_set {B : Recs} {i : Nat} {n r : Record} (h : r ∈ recs (B.set i (some n))) : r = n ∨ r ∈ recs B := by
  simp only [recs, List.mem_filterMap, id] at h ⊢
  obtain ⟨s, hs, hse⟩ := h
  rcases List.mem_or_eq_of_mem_set hs with h | h
  · exact Or.inr ⟨s, h, hse⟩
  · subst h; simp at hse; exact Or.inl hse.symm

/-- Adding a record for a bundle not held yet, whose item is custody, keeps the book well formed. -/
theorem add_rec {X : Recs} {slot : Nat} {n : Record} {L : Ledger} (hslot : X[slot]? = some none) (hn : NodupB X)
    (hfresh : ∀ r ∈ recs X, r.bundle ≠ n.bundle) (hX : Linked X L)
    (hnew : ∀ e ∈ L.entries, e.key = bkey n.bundle → e.cls = .custody) :
    NodupB (X.set slot (some n)) ∧ Linked (X.set slot (some n)) L := by
  refine ⟨?_, ?_⟩
  · unfold NodupB
    have hp := (set_some_perm X slot n hslot).map (·.bundle)
    refine hp.nodup_iff.2 (List.nodup_cons.2 ⟨?_, hn⟩)
    intro hm
    obtain ⟨r, hr, hrb⟩ := List.mem_map.1 hm
    exact hfresh r hr hrb
  · intro r hr e he hk
    rcases mem_recs_set hr with rfl | hr
    · exact hnew e he hk
    · exact hX r hr e he hk

theorem linked_mono {B B' : Recs} {L L' : Ledger} (h : Linked B L) (hb : ∀ r ∈ recs B', r ∈ recs B)
    (hl : ∀ e ∈ L'.entries, e ∈ L.entries) : Linked B' L' :=
  fun r hr e he hk => h r (hb r hr) e (hl e he) hk

theorem sync_slot_none {X : Recs} {L : Ledger} {i : Nat} (h : X[i]? = some none) : (sync X L)[i]? = some none := by
  simp [sync, List.getElem?_map, h]

theorem sync_nodup {B : Recs} (L : Ledger) (h : NodupB B) : NodupB (sync B L) := by
  unfold NodupB at *
  rw [recs_sync]
  exact h.sublist ((List.filter_sublist).map _)

theorem sync_sub (B : Recs) (L : Ledger) : ∀ r ∈ recs (sync B L), r ∈ recs B :=
  fun r hr => (mem_recs_sync.1 hr).1

theorem expire_sub (L : Ledger) (now : Nat) : ∀ e ∈ (expire L now).1.entries, e ∈ L.entries := by
  intro y hy; rw [entries_expire] at hy; exact (List.mem_filter.1 hy).1

/-- The state after the expiry step shared by `accept` and `bexpire`. -/
theorem expire_sync_ok {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L) (now : Nat) :
    Inv (expire L now).1 ∧ NodupB (sync B (expire L now).1) ∧ Linked (sync B (expire L now).1) (expire L now).1 :=
  ⟨expire_inv hI now, sync_nodup _ hn, linked_mono hl (sync_sub _ _) (expire_sub L now)⟩

theorem accept_inv {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L)
    (bundle bytes expires previous now : Nat) :
    Inv (accept B L bundle bytes expires previous now).L ∧ NodupB (accept B L bundle bytes expires previous now).B ∧
      Linked (accept B L bundle bytes expires previous now).B (accept B L bundle bytes expires previous now).L := by
  obtain ⟨hI1, hn1, hl1⟩ := expire_sync_ok hI hn hl now
  unfold accept
  simp only
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp [hh]; exact ⟨hI1, hn1, hl1⟩
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  have hfresh : ∀ r ∈ recs (sync B (expire L now).1), r.bundle ≠ bundle := by
    intro r hr hrb
    have : holds (sync B (expire L now).1) bundle = true := by
      simp only [holds, List.any_eq_true, decide_eq_true_eq]; exact ⟨r, hr, hrb⟩
    simp_all
  simp only [hh']
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp; exact ⟨hI1, hn1, hl1⟩
  | some slot =>
    simp only
    have hslot := findIdx_none_slot hs
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp only [hc, ite_true]
      have hI2 := reclass_inv hI1 (bkey bundle) .custody
      have hent := reclass_entries _ (bkey bundle) .custody hc
      -- the synced book against the reclassed ledger
      have hslot2 : (sync (sync B (expire L now).1) (reclass (expire L now).1 (bkey bundle) .custody).1)[slot]? = some none := by
        exact sync_slot_none hslot
      have hsub2 : ∀ r ∈ recs (sync (sync B (expire L now).1) (reclass (expire L now).1 (bkey bundle) .custody).1),
          r ∈ recs (sync B (expire L now).1) := sync_sub _ _
      have hold : ∀ r ∈ recs (sync B (expire L now).1), ∀ e ∈ (reclass (expire L now).1 (bkey bundle) .custody).1.entries,
          e.key = bkey r.bundle → e.cls = .custody := by
        intro r hr e he hk
        rw [hent] at he
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
        by_cases hyk : y.key = bkey bundle
        · simp [hyk]
        · simp only [hyk, ite_false] at hk ⊢
          exact hl1 r hr y hy hk
      obtain ⟨hn3, hl3⟩ := add_rec (n := ⟨bundle, previous, none⟩) hslot2
        (sync_nodup _ hn1) (fun r hr => hfresh r (hsub2 r hr))
        (fun r hr => hold r (hsub2 r hr))
        (fun e he hk => by
          rw [hent] at he
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
          by_cases hyk : y.key = bkey bundle
          · simp [hyk]
          · exact absurd (by simpa [hyk] using hk) hyk)
      exact ⟨hI2, hn3, hl3⟩
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false]
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h⟩ | ⟨_, _, L2, ev2, slots', _, _, h, _⟩
      · simp_all
      · rw [h]; simp only
        rw [(expire_idem L now).1]
        exact ⟨hI1, hn1, hl1⟩
      · rw [h]; simp only
        obtain ⟨Ln, hLn⟩ : ∃ Ln : Ledger, Ln = ⟨L2.budget, L2.used + bytes, L2.nextSeq + 1, slots'⟩ := ⟨_, rfl⟩
        rw [← hLn]
        have hI2 := admit_inv hI1 (bkey bundle) bytes .custody expires now
        rw [h] at hI2
        simp only at hI2
        rw [← hLn] at hI2
        have hsubE := admit_entries_sub hI1 (bkey bundle) bytes .custody expires now
        rw [h] at hsubE
        simp only at hsubE
        rw [← hLn] at hsubE
        have hkeys := contains_false hc'
        have hslot2 := sync_slot_none (L := Ln) hslot
        obtain ⟨hn3, hl3⟩ := add_rec (n := ⟨bundle, previous, none⟩) (X := sync (sync B (expire L now).1) Ln) (slot := slot)
          hslot2 (sync_nodup _ hn1) (fun r hr => hfresh r (sync_sub _ _ r hr))
          (fun r hr e he hk => by
            have hr1 := sync_sub _ _ r hr
            rcases hsubE e he with he1 | rfl
            · exact hl1 r hr1 e he1 hk
            · exact absurd (bkey_inj.1 hk).symm (hfresh r hr1))
          (fun e he hk => by
            rcases hsubE e he with he1 | rfl
            · exact absurd hk (hkeys e he1)
            · rfl)
        exact ⟨hI2, hn3, hl3⟩


theorem holds_set {X : Recs} {slot : Nat} {n : Record} (h : X[slot]? = some none) :
    holds (X.set slot (some n)) n.bundle = true := by
  simp only [holds, List.any_eq_true, decide_eq_true_eq]
  exact ⟨n, (set_some_perm X slot n h).mem_iff.2 (List.mem_cons_self), rfl⟩

theorem holds_iff {B : Recs} {b : Nat} : holds B b = true ↔ ∃ r ∈ recs B, r.bundle = b := by
  simp [holds]

/-- A refused acceptance changes nothing except the expired items leaving and their records. -/
theorem accept_err_state {B : Recs} {L : Ledger} (hI : Inv L) (bundle bytes expires previous now : Nat) (e : CErr)
    (h : (accept B L bundle bytes expires previous now).err = some e) :
    (e = .capacity ∨ e = .store .custodyRefused) ∧
      (accept B L bundle bytes expires previous now).L = (expire L now).1 ∧
      (accept B L bundle bytes expires previous now).B = sync B (expire L now).1 ∧
      (accept B L bundle bytes expires previous now).ev = (expire L now).2 := by
  have hI1 := expire_inv hI now
  unfold accept at h ⊢
  simp only at h ⊢
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp [hh] at h
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false] at h ⊢
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp [hs] at h ⊢; simp [h]
  | some slot =>
    simp only [hs] at h ⊢
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp [hc] at h
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false] at h ⊢
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · simp_all
      · rw [h2] at h ⊢
        simp only [Option.some.injEq, CErr.store.injEq] at h
        simp only [refusedOf] at h
        subst h
        have := expire_idem L now
        simp [this.1, this.2]
      · rw [h2] at h; simp at h

theorem accept_ok {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L)
    (bundle bytes expires previous now : Nat) (h : (accept B L bundle bytes expires previous now).err = none) :
    holds (accept B L bundle bytes expires previous now).B bundle = true ∧
      ∃ e ∈ (accept B L bundle bytes expires previous now).L.entries, e.key = bkey bundle ∧ e.cls = .custody := by
  obtain ⟨hI1, hn1, hl1⟩ := expire_sync_ok hI hn hl now
  have hinv := accept_inv hI hn hl bundle bytes expires previous now
  unfold accept at h ⊢
  simp only at h ⊢
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp only [hh, ite_true] at h ⊢
    refine ⟨by simp [hh], ?_⟩
    obtain ⟨r, hr, hrb⟩ := holds_iff.1 hh
    obtain ⟨hr1, hr2⟩ := mem_recs_sync.1 hr
    obtain ⟨e, he, hek⟩ := contains_iff.1 hr2
    exact ⟨e, he, by rw [hek, hrb], hl1 r hr e he (by rw [hek, hrb])⟩
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false] at h ⊢
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp [hs] at h
  | some slot =>
    simp only [hs] at h ⊢
    have hslot := findIdx_none_slot hs
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp only [hc, ite_true]
      refine ⟨holds_set (n := ⟨bundle, previous, none⟩) (sync_slot_none hslot), ?_⟩
      have hent := reclass_entries _ (bkey bundle) .custody hc
      obtain ⟨e, he, hek⟩ := contains_iff.1 hc
      refine ⟨{ e with cls := .custody }, ?_, ?_, rfl⟩
      · rw [hent]; exact List.mem_map.2 ⟨e, he, by simp [hek]⟩
      · simpa using hek
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false] at h ⊢
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, hput, h2, _⟩
      · simp_all
      · rw [h2] at h; simp at h
      · rw [h2]
        simp only
        refine ⟨holds_set (n := ⟨bundle, previous, none⟩) (sync_slot_none hslot), ?_⟩
        have hperm := (put_perm _ _ _ hput).1
        exact ⟨_, hperm.mem_iff.2 (List.mem_cons_self), rfl, rfl⟩

theorem accept_capacity_iff {B : Recs} {L : Ledger} (hI : Inv L) (bundle bytes expires previous now : Nat) :
    (accept B L bundle bytes expires previous now).err = some .capacity ↔
      holds (sync B (expire L now).1) bundle = false ∧ ∀ s ∈ sync B (expire L now).1, s.isSome = true := by
  have hI1 := expire_inv hI now
  unfold accept
  simp only
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp [hh]
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false, true_and]
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none =>
    have := List.findIdx?_eq_none_iff.1 hs
    simp only [true_iff]
    intro s hsm; have := this s hsm; simpa using this
  | some slot =>
    simp only [hs]
    constructor
    · intro hc
      by_cases hct : (expire L now).1.contains (bkey bundle) = true
      · simp [hct] at hc
      · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hct
        simp only [hc', Bool.false_eq_true, ite_false] at hc
        rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩ <;>
          simp_all
    · intro hall
      obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hs
      have := hall _ (List.getElem_mem hi)
      simp_all


/-! ## Acknowledgements, delivery, expiry, offers -/

theorem set_none_perm (B : Recs) (i : Nat) (r : Record) (h : B[i]? = some (some r)) :
    (recs B).Perm (r :: recs (B.set i none)) := by
  have hi : i < B.length := by
    by_cases hc : i < B.length
    · exact hc
    · simp [List.getElem?_eq_none (by omega : B.length ≤ i)] at h
  have hg : B[i] = some r := by
    have := List.getElem?_eq_getElem hi
    rw [h] at this; simpa using this.symm
  have hsplit : B = B.take i ++ some r :: B.drop (i + 1) := by
    calc B = B.take i ++ B.drop i := (List.take_append_drop i _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hg]
  have hset : B.set i none = B.take i ++ none :: B.drop (i + 1) := by
    simp [List.set_eq_take_append_cons_drop, hi]
  obtain ⟨A, C, hA, hC⟩ : ∃ A C, B = A ++ some r :: C ∧ B.set i none = A ++ none :: C := ⟨_, _, hsplit, hset ▸ rfl⟩
  have hl : recs B = A.filterMap id ++ r :: C.filterMap id := by
    simp only [recs]; rw [hA]; simp [List.filterMap_append]
  have hr : recs (B.set i none) = A.filterMap id ++ C.filterMap id := by
    simp only [recs]; rw [hC]; simp [List.filterMap_append]
  rw [hr, hl]
  exact List.perm_middle.symm.symm

theorem nodup_map_inj {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: t, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd ⟨y, hy, hxy.symm⟩ h.1
    · exact absurd ⟨x, hx, hxy⟩ h.1
    · exact nodup_map_inj f t (by simpa using h.2) x hx y hy hxy

theorem slotOf_none {B : Recs} {b : Nat} : slotOf B b = none ↔ ∀ r ∈ recs B, r.bundle ≠ b := by
  unfold slotOf
  rw [List.findIdx?_eq_none_iff]
  constructor
  · intro h r hr hrb
    simp only [recs, List.mem_filterMap, id] at hr
    obtain ⟨s, hs, hse⟩ := hr
    have := h s hs
    subst hse
    simp [hrb] at this
  · intro h s hs
    cases s with
    | none => simp
    | some r =>
      have := h r (by simp only [recs, List.mem_filterMap, id]; exact ⟨_, hs, rfl⟩)
      simpa using this

theorem slotOf_some {B : Recs} {b i : Nat} (hn : NodupB B) (h : slotOf B b = some i) :
    ∃ r, B[i]? = some (some r) ∧ r.bundle = b ∧ ∀ r' ∈ recs B, r'.bundle = b → r' = r := by
  unfold slotOf at h
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  cases hs : B[i] with
  | none => rw [hs] at hp; simp at hp
  | some r =>
    rw [hs] at hp
    simp at hp
    refine ⟨r, by rw [List.getElem?_eq_getElem hi, hs], hp, ?_⟩
    intro r' hr' hrb'
    have hr : r ∈ recs B := by
      simp only [recs, List.mem_filterMap, id]; exact ⟨some r, by rw [← hs]; exact List.getElem_mem hi, rfl⟩
    exact nodup_map_inj (fun r : Record => r.bundle) (recs B) hn r' hr' r hr (by rw [hrb', hp])

theorem onAck_ok_iff {B : Recs} {L : Ledger} (hn : NodupB B) (b c : Nat) (v : Bool) :
    (onAck B L b c v).err = none ↔
      v = true ∧ (∃ r ∈ recs B, r.bundle = b ∧ r.offered = some c) ∧ L.contains (bkey b) = true := by
  unfold onAck
  cases v
  · simp
  · simp only [↓reduceIte, if_true, true_and]
    cases hs : slotOf B b with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨⟨r, hr, hrb, _⟩, _⟩
      exact (slotOf_none.1 hs) r hr hrb
    | some i =>
      obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
      simp only [hBi, Option.bind_some, id]
      have hmem : r ∈ recs B := by
        rw [← hrb] at hs
        simp only [recs, List.mem_filterMap, id]
        have := List.mem_of_getElem? hBi
        exact ⟨_, this, rfl⟩
      by_cases ho : r.offered = some c
      · simp only [ho, ne_eq, not_true_eq_false, ite_false]
        have := reclass_ok_iff L (bkey b) .transit
        constructor
        · intro h
          refine ⟨⟨r, hmem, hrb, ho⟩, ?_⟩
          by_cases hc : (reclass L (bkey b) .transit).2 = true
          · rw [this] at hc; exact hc
          · simp [hc] at h
        · rintro ⟨-, hc⟩
          simp [this, hc]
      · simp only [ne_eq, ho, not_false_eq_true, ite_true]
        simp only [reduceCtorEq, false_iff]
        rintro ⟨⟨r', hr', hrb', ho'⟩, _⟩
        have := huniq r' hr' hrb'
        subst this
        exact ho ho'

theorem onAck_state {B : Recs} {L : Ledger} (hn : NodupB B) (b c : Nat) (v : Bool) :
    (onAck B L b c v).ev = [] ∧
    (((onAck B L b c v).err = some .ack ∨ (onAck B L b c v).err = some .unknown ∨
        (onAck B L b c v).err = some .notOffered) →
      (onAck B L b c v).B = B ∧ (onAck B L b c v).L = L) ∧
    ((onAck B L b c v).err = some .storeUnknown →
      (onAck B L b c v).L = L ∧ L.contains (bkey b) = false) ∧
    ((onAck B L b c v).err = none →
      (onAck B L b c v).L.entries = L.entries.map (fun x => if x.key = bkey b then { x with cls := .transit } else x)) := by
  unfold onAck
  cases v
  · simp
  · simp only [↓reduceIte, if_true]
    cases hs : slotOf B b with
    | none => simp
    | some i =>
      obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
      simp only [hBi, Option.bind_some, id]
      by_cases ho : r.offered = some c
      · simp only [ho, ne_eq, not_true_eq_false, ite_false]
        by_cases hc : L.contains (bkey b) = true
        · have := reclass_ok_iff L (bkey b) .transit
          simp [this, hc]
          exact reclass_entries L (bkey b) .transit hc
        · have hc' : L.contains (bkey b) = false := by simpa using hc
          simp [reclass, hc']
      · simp [ho]

theorem onAck_records {B : Recs} {L : Ledger} (hn : NodupB B) (b c : Nat) (v : Bool) :
    (∀ r' ∈ recs (onAck B L b c v).B, r' ∈ recs B) ∧ NodupB (onAck B L b c v).B ∧
    ((onAck B L b c v).err = none → (∀ r' ∈ recs (onAck B L b c v).B, r'.bundle ≠ b) ∧
      ∀ r' ∈ recs B, r'.bundle ≠ b → r' ∈ recs (onAck B L b c v).B) := by
  unfold onAck
  cases v
  · simp [hn]
  · simp only [↓reduceIte, if_true]
    cases hs : slotOf B b with
    | none => simp [hn]
    | some i =>
      obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
      simp only [hBi, Option.bind_some, id]
      have hp := set_none_perm B i r hBi
      have hnd := (hp.map (·.bundle)).nodup_iff.1 (by unfold NodupB at hn; exact hn)
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases ho : r.offered = some c
      · simp only [ho, ne_eq, not_true_eq_false, ite_false]
        refine ⟨fun r' hr' => recs_set_none B i r' hr', hnd.2, ?_⟩
        intro _
        constructor
        · intro r' hr' hrb'
          have hr'B := recs_set_none B i r' hr'
          have := huniq r' hr'B hrb'
          subst this
          exact hnd.1 (List.mem_map.2 ⟨r', hr', rfl⟩)
        · intro r' hr' hne
          have := hp.mem_iff.1 hr'
          simp only [List.mem_cons] at this
          rcases this with rfl | h
          · exact absurd hrb hne
          · exact h
      · simp only [ho, ne_eq, not_false_eq_true, ite_true]
        exact ⟨fun r' hr' => hr', hn, by simp⟩

theorem onAck_inv {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L) (b c : Nat) (v : Bool) :
    Inv (onAck B L b c v).L ∧ NodupB (onAck B L b c v).B ∧ Linked (onAck B L b c v).B (onAck B L b c v).L := by
  obtain ⟨hev, hsame, hunk, hok⟩ := onAck_state (L := L) hn b c v
  obtain ⟨hsub, hnd, hrel⟩ := onAck_records (L := L) hn b c v
  -- the shape of the result
  have hshape : (onAck B L b c v).L = L ∨ ((onAck B L b c v).err = none ∧
      (onAck B L b c v).L = (reclass L (bkey b) .transit).1) := by
    unfold onAck
    cases v
    · simp
    · simp only [↓reduceIte, if_true]
      cases hs : slotOf B b with
      | none => simp
      | some i =>
        obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
        simp only [hBi, Option.bind_some, id]
        by_cases ho : r.offered = some c
        · simp only [ho, ne_eq, not_true_eq_false, ite_false]
          by_cases hc : (reclass L (bkey b) .transit).2 = true
          · right; simp [hc]
          · left
            have : L.contains (bkey b) = false := by rw [← reclass_ok_iff]; simpa using hc
            simp [hc, reclass, this]
        · simp [ho]
  refine ⟨?_, hnd, ?_⟩
  · rcases hshape with h | ⟨_, h⟩
    · rw [h]; exact hI
    · rw [h]; exact reclass_inv hI _ _
  · rcases hshape with h | ⟨herr, h⟩
    · rw [h]; exact linked_mono hl hsub (fun _ he => he)
    · rw [h]
      intro r hr e he hk
      have hne := (hrel herr).1 r hr
      have hen := hok herr
      rw [h] at hen
      rw [hen] at he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      by_cases hxk : x.key = bkey b
      · simp only [hxk, ite_true] at hk
        exact absurd (bkey_inj.1 (by rw [← hk])).symm hne
      · simp only [hxk, ite_false] at hk ⊢
        exact hl r (hsub r hr) x hx hk


theorem delivered_cases {B : Recs} (hn : NodupB B) (L : Ledger) (b : Nat) :
    ((delivered B L b).err = some .unknown ∧ (delivered B L b).B = B ∧ (delivered B L b).L = L ∧
      ∀ r ∈ recs B, r.bundle ≠ b) ∨
    ((delivered B L b).err = none ∧ (delivered B L b).L = (release L (bkey b)).1 ∧
      (∀ r ∈ recs (delivered B L b).B, r ∈ recs B ∧ r.bundle ≠ b) ∧ NodupB (delivered B L b).B ∧
      ∀ r ∈ recs B, r.bundle ≠ b → r ∈ recs (delivered B L b).B) := by
  unfold delivered
  cases hs : slotOf B b with
  | none => left; exact ⟨rfl, rfl, rfl, slotOf_none.1 hs⟩
  | some i =>
    right
    obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
    have hp := set_none_perm B i r hBi
    have hnd := (hp.map (·.bundle)).nodup_iff.1 (by unfold NodupB at hn; exact hn)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine ⟨rfl, rfl, ?_, hnd.2, ?_⟩
    · intro r' hr'
      have hr'B := recs_set_none B i r' hr'
      refine ⟨hr'B, fun hrb' => ?_⟩
      have := huniq r' hr'B hrb'
      subst this
      exact hnd.1 (List.mem_map.2 ⟨r', hr', rfl⟩)
    · intro r' hr' hne
      have := hp.mem_iff.1 hr'
      simp only [List.mem_cons] at this
      rcases this with rfl | h
      · exact absurd hrb hne
      · exact h

theorem delivered_inv {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L) (b : Nat) :
    Inv (delivered B L b).L ∧ NodupB (delivered B L b).B ∧ Linked (delivered B L b).B (delivered B L b).L := by
  rcases delivered_cases hn L b with ⟨_, hB, hL, _⟩ | ⟨_, hL, hr, hnd, _⟩
  · rw [hB, hL]; exact ⟨hI, hn, hl⟩
  · rw [hL]
    refine ⟨release_inv hI _, hnd, ?_⟩
    refine linked_mono hl (fun r h => (hr r h).1) ?_
    intro e he
    rcases release_exits L (bkey b) with ⟨_, h2, _⟩ | ⟨x, _, _, hp⟩
    · rw [h2] at he; exact he
    · exact hp.symm.mem_iff.1 (List.mem_cons_of_mem _ he)

/-- Delivery removes the bundle's record and its ledger item, and nothing else. -/
theorem delivered_exits {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (b : Nat)
    (h : (delivered B L b).err = none) :
    (∀ e ∈ (delivered B L b).L.entries, e ∈ L.entries) ∧
    (∀ e ∈ L.entries, e.key ≠ bkey b → e ∈ (delivered B L b).L.entries) ∧
    (∀ e ∈ L.entries, e ∉ (delivered B L b).L.entries → e.key = bkey b) ∧
    (∀ r ∈ recs B, r.bundle ≠ b → r ∈ recs (delivered B L b).B) ∧
    (∀ r ∈ recs (delivered B L b).B, r.bundle ≠ b) := by
  rcases delivered_cases hn L b with ⟨h1, _⟩ | ⟨_, hL, hr, _, hback⟩
  · rw [h1] at h; simp at h
  · rw [hL]
    rcases release_exits L (bkey b) with ⟨_, h2, h3⟩ | ⟨x, _, hxk, hp⟩
    · rw [h2]
      refine ⟨fun e he => he, fun e he _ => he, ?_, hback, fun r h => (hr r h).2⟩
      intro e he hne; exact absurd he hne
    · refine ⟨fun e he => hp.symm.mem_iff.1 (List.mem_cons_of_mem _ he), ?_, ?_, hback, fun r h => (hr r h).2⟩
      · intro e he hk
        have := hp.mem_iff.1 he
        simp only [List.mem_cons] at this
        rcases this with rfl | h
        · exact absurd hxk hk
        · exact h
      · intro e he hne
        have := hp.mem_iff.1 he
        simp only [List.mem_cons] at this
        rcases this with rfl | h
        · exact hxk
        · exact absurd h hne

theorem bexpire_inv {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L) (now : Nat) :
    Inv (bexpire B L now).L ∧ NodupB (bexpire B L now).B ∧ Linked (bexpire B L now).B (bexpire B L now).L :=
  expire_sync_ok hI hn hl now

/-- After the book's expiry every record has its item in the ledger (the book never holds a record for an item the
ledger no longer holds), and the ledger changes only by the expired items leaving. -/
theorem bexpire_exits (B : Recs) (L : Ledger) (now : Nat) :
    (∀ r ∈ recs (bexpire B L now).B, (bexpire B L now).L.contains (bkey r.bundle) = true) ∧
    (bexpire B L now).ev = L.entries.filter (expiredAt now) ∧
    (bexpire B L now).L.entries = L.entries.filter (fun e => !expiredAt now e) :=
  ⟨fun r hr => (mem_recs_sync.1 hr).2, rfl, entries_expire L now⟩

theorem setOffered_bundles (b to : Nat) : ∀ (B B' : Recs), setOffered b to B = some B' →
    (recs B').map (·.bundle) = (recs B).map (·.bundle) ∧ ∃ r ∈ recs B', r.bundle = b ∧ r.offered = some to
  | [], B', h => by simp [setOffered] at h
  | s :: t, B', h => by
    cases s with
    | none =>
      simp only [setOffered, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', rfl⟩ := h
      obtain ⟨h1, r, hr, h2⟩ := setOffered_bundles b to t t' ht'
      refine ⟨by simpa [recs] using h1, r, ?_, h2⟩
      simpa [recs] using hr
    | some x =>
      by_cases hx : x.bundle = b
      · simp only [setOffered, hx, ite_true, Option.some.injEq] at h
        subst h
        refine ⟨?_, { x with offered := some to }, by simp [recs]; exact Or.inl hx, hx, rfl⟩
        simp only [recs, List.filterMap_cons, id, List.map_cons]
        rw [hx]
      · simp only [setOffered, hx, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨t', ht', rfl⟩ := h
        obtain ⟨h1, r, hr, h2⟩ := setOffered_bundles b to t t' ht'
        refine ⟨by simpa [recs] using h1, r, ?_, h2⟩
        simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr ⊢
        exact Or.inr hr

theorem offer_inv {B : Recs} {L : Ledger} (hn : NodupB B) (hl : Linked B L) (b to : Nat) :
    NodupB (offer B b to).2 ∧ Linked (offer B b to).2 L := by
  unfold offer
  cases h : setOffered b to B with
  | none => exact ⟨hn, hl⟩
  | some B' =>
    obtain ⟨hb, -⟩ := setOffered_bundles b to B B' h
    refine ⟨by unfold NodupB at *; rw [hb]; exact hn, ?_⟩
    intro r hr e he hk
    have : r.bundle ∈ (recs B).map (·.bundle) := by rw [← hb]; exact List.mem_map.2 ⟨r, hr, rfl⟩
    obtain ⟨r0, hr0, hr0b⟩ := List.mem_map.1 this
    exact hl r0 hr0 e he (by rw [hr0b]; exact hk)

/-- Offering custody to a node records it for a held bundle, and refuses an unknown one. -/
theorem offer_ok_iff (B : Recs) (b to : Nat) :
    (offer B b to).1 = none ↔ holds B b = true := by
  unfold offer
  cases h : setOffered b to B with
  | none =>
    simp only [reduceCtorEq, false_iff]
    intro hh
    obtain ⟨r, hr, hrb⟩ := holds_iff.1 hh
    -- an unsuccessful search means no record of the bundle
    have : ∀ (B : Recs), setOffered b to B = none → ∀ r ∈ recs B, r.bundle ≠ b := by
      intro B
      induction B with
      | nil => intro _ r hr; simp [recs] at hr
      | cons s t ih =>
        intro hB r hr
        cases s with
        | none =>
          simp only [setOffered, Option.map_eq_none_iff] at hB
          simp only [recs, List.filterMap_cons, id] at hr
          exact ih hB r hr
        | some x =>
          by_cases hx : x.bundle = b
          · simp [setOffered, hx] at hB
          · simp only [setOffered, hx, ite_false, Option.map_eq_none_iff] at hB
            simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr
            rcases hr with rfl | hr
            · exact hx
            · exact ih hB r hr
    exact this B h r hr hrb
  | some B' =>
    obtain ⟨-, r, hr, hrb, -⟩ := setOffered_bundles b to B B' h
    simp only [true_iff]
    have hmem : b ∈ (recs B').map (·.bundle) := List.mem_map.2 ⟨r, hr, hrb⟩
    rw [(setOffered_bundles b to B B' h).1] at hmem
    obtain ⟨r0, hr0, hr0b⟩ := List.mem_map.1 hmem
    exact holds_iff.2 ⟨r0, hr0, hr0b⟩

end Vinc.DtnStore
