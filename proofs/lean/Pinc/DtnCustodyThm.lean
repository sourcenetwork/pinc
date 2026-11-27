import Pinc.DtnCustody

/-!
# Custody: the single-operation theorems

For a ledger with `Inv`, and a book with `NodupB` and `Linked`, each operation of `Pinc.DtnCustody`:

* keeps the invariants (`accept_inv`, `offer_inv`, `onAck_inv`, `delivered_inv`, `bexpire_inv`);
* `accept_err_state`: a refused acceptance (full book, custody refused, or an incoming bundle that is already
  expired) changes nothing except the expired items leaving (and their records);
  `accept_held_cancels`: accepting a bundle already held (a hand-back or a repeated offer) keeps the record and its
  previous custodian and cancels this node's outstanding offer; `handback_blocks_ack`: so every later ack is stale;
  `accept_expired_refused`: an expired incoming bundle is refused with the store's `expired`;
  `accept_capacity_iff`: the book is full exactly when no record is free;
* `onAck_ok_iff`: custody is relieved exactly when the ack is valid, the bundle is held, custody was offered to exactly
  the acknowledging node under exactly the ack's offer id, and the ledger still holds the item; `onAck_stale`: any
  other ack of a held bundle is `notOffered` and moves nothing; `onAck_state`: any other ack moves nothing
  (the one exception is documented: a valid, offered ack for an item the ledger already dropped clears the record and
  reports `storeUnknown`);
* `onAck_state` and `onAck_records`: a relief changes the class of that bundle's item to transit and clears that bundle's record, and
  nothing else;
* `delivered_exits`, `bexpire_exits`: the other exits.
-/

namespace Pinc.DtnStore

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


/-! ## Changing one record -/

theorem modFirst_spec (b : Nat) (f : Record → Record) (hf : ∀ r, (f r).bundle = r.bundle) :
    ∀ (B B' : Recs), modFirst b f B = some B' →
      (recs B').map (·.bundle) = (recs B).map (·.bundle) ∧
      (∀ r ∈ recs B', r ∈ recs B ∨ ∃ r0 ∈ recs B, r0.bundle = b ∧ r = f r0) ∧
      ∃ r0 ∈ recs B, r0.bundle = b ∧ f r0 ∈ recs B'
  | [], B', h => by simp [modFirst] at h
  | s :: t, B', h => by
    cases s with
    | none =>
      simp only [modFirst, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', rfl⟩ := h
      obtain ⟨h1, h2, r0, hr0, hr0b, hr0'⟩ := modFirst_spec b f hf t t' ht'
      refine ⟨by simpa [recs] using h1, ?_, r0, by simpa [recs] using hr0, hr0b, by simpa [recs] using hr0'⟩
      intro r hr
      have hr' : r ∈ recs t' := by simpa [recs] using hr
      rcases h2 r hr' with h | ⟨r1, hr1, hb, he⟩
      · left; simpa [recs] using h
      · right; exact ⟨r1, by simpa [recs] using hr1, hb, he⟩
    | some x =>
      by_cases hx : x.bundle = b
      · simp only [modFirst, hx, ite_true, Option.some.injEq] at h
        subst h
        refine ⟨?_, ?_, x, by simp [recs], hx, by simp [recs]⟩
        · simp [recs, hf]
        · intro r hr
          simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr
          rcases hr with rfl | hr
          · right; exact ⟨x, by simp [recs], hx, rfl⟩
          · left; simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr hr
      · simp only [modFirst, hx, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨t', ht', rfl⟩ := h
        obtain ⟨h1, h2, r0, hr0, hr0b, hr0'⟩ := modFirst_spec b f hf t t' ht'
        refine ⟨by simpa [recs] using h1, ?_, r0, ?_, hr0b, ?_⟩
        · intro r hr
          simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr
          rcases hr with rfl | hr
          · left; simp [recs]
          · rcases h2 r hr with h | ⟨r1, hr1, hb, he⟩
            · left; simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr h
            · right; exact ⟨r1, by simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr hr1, hb, he⟩
        · simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr hr0
        · simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr hr0'

theorem modFirst_none (b : Nat) (f : Record → Record) :
    ∀ (B : Recs), modFirst b f B = none ↔ ∀ r ∈ recs B, r.bundle ≠ b
  | [] => by simp [modFirst, recs]
  | s :: t => by
    cases s with
    | none =>
      simp only [modFirst, Option.map_eq_none_iff, modFirst_none b f t]
      simp [recs]
    | some x =>
      by_cases hx : x.bundle = b
      · simp only [modFirst, hx, ite_true, reduceCtorEq, false_iff]
        intro h
        exact h x (by simp [recs]) hx
      · simp only [modFirst, hx, ite_false, Option.map_eq_none_iff, modFirst_none b f t]
        constructor
        · intro h r hr
          simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hx
          · exact h r hr
        · intro h r hr
          exact h r (by simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr hr)

theorem cancel_some {B : Recs} {b : Nat} (h : holds B b = true) :
    ∃ B', modFirst b cancelRec B = some B' := by
  cases hm : modFirst b cancelRec B with
  | some B' => exact ⟨B', rfl⟩
  | none =>
    exfalso
    have := (modFirst_none b cancelRec B).1 hm
    simp only [holds, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨r, hr, hb⟩ := h
    exact this r hr hb

/-- A change that keeps the set of bundles keeps the book well formed. -/
theorem book_of_bundles {B B' : Recs} {L : Ledger} (hb : (recs B').map (·.bundle) = (recs B).map (·.bundle))
    (hn : NodupB B) (hl : Linked B L) : NodupB B' ∧ Linked B' L := by
  refine ⟨by unfold NodupB at *; rw [hb]; exact hn, ?_⟩
  intro r hr e he hk
  have : r.bundle ∈ (recs B).map (·.bundle) := by rw [← hb]; exact List.mem_map.2 ⟨r, hr, rfl⟩
  obtain ⟨r0, hr0, hr0b⟩ := List.mem_map.1 this
  exact hl r0 hr0 e he (by rw [hr0b]; exact hk)

theorem bkey_inj {a b : Nat} : bkey a = bkey b ↔ a = b := by simp [bkey]

theorem admit_entries_sub {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) :
    ∀ e ∈ (admitItem L k b c x now).L.entries, e ∈ L.entries ∨ e = ⟨k, b, c, x, L.nextSeq⟩ := by
  intro e he
  have hsub : ∀ y ∈ (expire L now).1.entries, y ∈ L.entries := by
    intro y hy; rw [entries_expire] at hy; exact (List.mem_filter.1 hy).1
  rcases admit_cases hI k b c x now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨hc, hf, L2, ev2, slots', hev, hput, h, hI2, hb2, hs2, hp2, hsl2, htr, hpw, hlt, hrm, hu2, hlast⟩
  · rw [h] at he; exact Or.inl (hsub e he)
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
  · obtain ⟨B', hB'⟩ := cancel_some hh
    simp only [hh, ite_true, hB', Option.getD_some]
    obtain ⟨h1, -⟩ := modFirst_spec bundle cancelRec (fun _ => rfl) _ B' hB'
    exact ⟨hI1, (book_of_bundles h1 hn1 hl1).1, (book_of_bundles h1 hn1 hl1).2⟩
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
      obtain ⟨hn3, hl3⟩ := add_rec (n := ⟨bundle, previous, none, 0⟩) hslot2
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
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, L2, ev2, slots', _, _, h, _⟩
      · rw [h]; simp only
        rw [(expire_idem L now).1]
        exact ⟨hI1, hn1, hl1⟩
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
        obtain ⟨hn3, hl3⟩ := add_rec (n := ⟨bundle, previous, none, 0⟩) (X := sync (sync B (expire L now).1) Ln) (slot := slot)
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
    (e = .capacity ∨ e = .store .custodyRefused ∨ e = .store .expired) ∧
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
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · rw [h2] at h ⊢
        simp only [Option.some.injEq] at h
        subst h
        have hi := expire_idem L now
        simp [hi.1, hi.2, hc']
      · rw [h2] at h ⊢
        simp only [Option.some.injEq] at h
        subst h
        have hi := expire_idem L now
        simp [hi.1, hi.2, refusedOf]
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
  · obtain ⟨B', hB'⟩ := cancel_some hh
    simp only [hh, ite_true, hB', Option.getD_some] at h ⊢
    obtain ⟨-, -, r0, hr0, hr0b, hr0'⟩ := modFirst_spec bundle cancelRec (fun _ => rfl) _ B' hB'
    refine ⟨holds_iff.2 ⟨_, hr0', hr0b⟩, ?_⟩
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
      refine ⟨holds_set (n := ⟨bundle, previous, none, 0⟩) (sync_slot_none hslot), ?_⟩
      have hent := reclass_entries _ (bkey bundle) .custody hc
      obtain ⟨e, he, hek⟩ := contains_iff.1 hc
      refine ⟨{ e with cls := .custody }, ?_, ?_, rfl⟩
      · rw [hent]; exact List.mem_map.2 ⟨e, he, by simp [hek]⟩
      · simpa using hek
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false] at h ⊢
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, hput, h2, _⟩
      · rw [h2] at h; simp at h
      · rw [h2] at h; simp at h
      · rw [h2]
        simp only
        refine ⟨holds_set (n := ⟨bundle, previous, none, 0⟩) (sync_slot_none hslot), ?_⟩
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

theorem onAck_ok_iff {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (v : Bool) :
    (onAck B L b c o v).err = none ↔
      v = true ∧ (∃ r ∈ recs B, r.bundle = b ∧ r.offered = some c ∧ r.oid = o) ∧ L.contains (bkey b) = true := by
  unfold onAck
  cases v
  · simp
  · simp only [↓reduceIte, true_and]
    cases hs : slotOf B b with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨⟨r, hr, hrb, _⟩, _⟩
      exact (slotOf_none.1 hs) r hr hrb
    | some i =>
      obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
      simp only [hBi]
      have hmem : r ∈ recs B := by
        rw [← hrb] at hs
        simp only [recs, List.mem_filterMap, id]
        have := List.mem_of_getElem? hBi
        exact ⟨_, this, rfl⟩
      by_cases ho : r.offered = some c ∧ r.oid = o
      · simp only [ho.1, ho.2, and_self, ite_true]
        have := reclass_ok_iff L (bkey b) .transit
        constructor
        · intro h
          refine ⟨⟨r, hmem, hrb, ho⟩, ?_⟩
          by_cases hc : (reclass L (bkey b) .transit).2 = true
          · rw [this] at hc; exact hc
          · simp [hc] at h
        · rintro ⟨-, hc⟩
          simp [this, hc]
      · simp only [show (_ ∧ _) = False from eq_false ho, ite_false]
        simp only [reduceCtorEq, false_iff]
        rintro ⟨⟨r', hr', hrb', ho'⟩, _⟩
        have := huniq r' hr' hrb'
        subst this
        exact ho ho'

theorem onAck_state {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (v : Bool) :
    (onAck B L b c o v).ev = [] ∧
    (((onAck B L b c o v).err = some .ack ∨ (onAck B L b c o v).err = some .unknown ∨
        (onAck B L b c o v).err = some .notOffered) →
      (onAck B L b c o v).B = B ∧ (onAck B L b c o v).L = L) ∧
    ((onAck B L b c o v).err = some .storeUnknown →
      (onAck B L b c o v).L = L ∧ L.contains (bkey b) = false) ∧
    ((onAck B L b c o v).err = none →
      (onAck B L b c o v).L.entries = L.entries.map (fun x => if x.key = bkey b then { x with cls := .transit } else x)) := by
  unfold onAck
  cases v
  · simp
  · simp only [↓reduceIte]
    cases hs : slotOf B b with
    | none => simp
    | some i =>
      obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
      simp only [hBi]
      by_cases ho : r.offered = some c ∧ r.oid = o
      · simp only [ho.1, ho.2, and_self, ite_true]
        by_cases hc : L.contains (bkey b) = true
        · have := reclass_ok_iff L (bkey b) .transit
          simp [this, hc]
          exact reclass_entries L (bkey b) .transit hc
        · have hc' : L.contains (bkey b) = false := by simpa using hc
          simp [reclass, hc']
      · simp [show (_ ∧ _) = False from eq_false ho]

theorem onAck_records {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (v : Bool) :
    (∀ r' ∈ recs (onAck B L b c o v).B, r' ∈ recs B) ∧ NodupB (onAck B L b c o v).B ∧
    ((onAck B L b c o v).err = none → (∀ r' ∈ recs (onAck B L b c o v).B, r'.bundle ≠ b) ∧
      ∀ r' ∈ recs B, r'.bundle ≠ b → r' ∈ recs (onAck B L b c o v).B) := by
  unfold onAck
  cases v
  · simp [hn]
  · simp only [↓reduceIte]
    cases hs : slotOf B b with
    | none => simp [hn]
    | some i =>
      obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
      simp only [hBi]
      have hp := set_none_perm B i r hBi
      have hnd := (hp.map (·.bundle)).nodup_iff.1 (by unfold NodupB at hn; exact hn)
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases ho : r.offered = some c ∧ r.oid = o
      · simp only [ho.1, ho.2, and_self, ite_true]
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
      · simp only [show (_ ∧ _) = False from eq_false ho, ite_false]
        exact ⟨fun r' hr' => hr', hn, by simp⟩

theorem onAck_inv {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L) (b c o : Nat) (v : Bool) :
    Inv (onAck B L b c o v).L ∧ NodupB (onAck B L b c o v).B ∧ Linked (onAck B L b c o v).B (onAck B L b c o v).L := by
  obtain ⟨hev, hsame, hunk, hok⟩ := onAck_state (L := L) hn b c o v
  obtain ⟨hsub, hnd, hrel⟩ := onAck_records (L := L) hn b c o v
  -- the shape of the result
  have hshape : (onAck B L b c o v).L = L ∨ ((onAck B L b c o v).err = none ∧
      (onAck B L b c o v).L = (reclass L (bkey b) .transit).1) := by
    unfold onAck
    cases v
    · simp
    · simp only [↓reduceIte]
      cases hs : slotOf B b with
      | none => simp
      | some i =>
        obtain ⟨r, hBi, hrb, huniq⟩ := slotOf_some hn hs
        simp only [hBi]
        by_cases ho : r.offered = some c ∧ r.oid = o
        · simp only [ho.1, ho.2, and_self, ite_true]
          by_cases hc : (reclass L (bkey b) .transit).2 = true
          · right; simp [hc]
          · left
            have : L.contains (bkey b) = false := by rw [← reclass_ok_iff]; simpa using hc
            simp [hc, reclass, this]
        · simp [show (_ ∧ _) = False from eq_false ho]
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

theorem offerRec_bundle (to id : Nat) (r : Record) : (offerRec to id r).bundle = r.bundle := rfl

theorem cancelRec_bundle (r : Record) : (cancelRec r).bundle = r.bundle := rfl

theorem offer_inv {B : Recs} {L : Ledger} (hn : NodupB B) (hl : Linked B L) (nx b to : Nat) :
    NodupB (offer B nx b to).B ∧ Linked (offer B nx b to).B L := by
  unfold offer
  cases h : modFirst b (offerRec to nx) B with
  | none => exact ⟨hn, hl⟩
  | some B' =>
    obtain ⟨hb, -⟩ := modFirst_spec b (offerRec to nx) (offerRec_bundle to nx) B B' h
    exact book_of_bundles hb hn hl

/-- Offering custody to a node records it for a held bundle, and refuses an unknown one. -/
theorem offer_ok_iff (B : Recs) (nx b to : Nat) :
    (offer B nx b to).err = none ↔ holds B b = true := by
  unfold offer
  cases h : modFirst b (offerRec to nx) B with
  | none =>
    have := (modFirst_none b _ B).1 h
    simp only [reduceCtorEq, false_iff]
    intro hh
    simp only [holds, List.any_eq_true, decide_eq_true_eq] at hh
    obtain ⟨r, hr, hrb⟩ := hh
    exact this r hr hrb
  | some B' =>
    obtain ⟨-, -, r0, hr0, hr0b, -⟩ := modFirst_spec b (offerRec to nx) (offerRec_bundle to nx) B B' h
    simp only [true_iff]
    simp only [holds, List.any_eq_true, decide_eq_true_eq]
    exact ⟨r0, hr0, hr0b⟩

/-- The counter: a successful offer returns the counter as the id and increments it; a failed offer leaves it. -/
theorem offer_counter (B : Recs) (nx b to : Nat) :
    ((offer B nx b to).err = none → (offer B nx b to).id = nx ∧ (offer B nx b to).nx = nx + 1) ∧
    ((offer B nx b to).err ≠ none → (offer B nx b to).nx = nx ∧ (offer B nx b to).B = B) := by
  unfold offer
  cases modFirst b (offerRec to nx) B <;> simp

/-- Changing one record: the other records stay, and the changed record is unique in the new book. -/
theorem modFirst_unique {b : Nat} {f : Record → Record} (hf : ∀ r, (f r).bundle = r.bundle) {B B' : Recs}
    (hm : modFirst b f B = some B') (hn : NodupB B) :
    ∃ r0 ∈ recs B, r0.bundle = b ∧ f r0 ∈ recs B' ∧ (∀ r ∈ recs B', r.bundle = b → r = f r0) ∧
      (∀ r ∈ recs B, r.bundle ≠ b → r ∈ recs B') ∧ (∀ r ∈ recs B', r.bundle ≠ b → r ∈ recs B) := by
  obtain ⟨hb, hsub, r0, hr0, hr0b, hr0'⟩ := modFirst_spec b f hf B B' hm
  have hnd : NodupB B' := by unfold NodupB at *; rw [hb]; exact hn
  refine ⟨r0, hr0, hr0b, hr0', ?_, ?_, ?_⟩
  · intro r hr hrb
    exact (nodup_map_inj (fun r : Record => r.bundle) (recs B') hnd (f r0) hr0' r hr
      (by simp [hf, hrb, hr0b])).symm
  · intro r hr hne
    have hp : r.bundle ∈ (recs B').map (·.bundle) := by
      rw [hb]; exact List.mem_map.2 ⟨r, hr, rfl⟩
    obtain ⟨r', hr', hrb'⟩ := List.mem_map.1 hp
    rcases hsub r' hr' with h1 | ⟨r1, hr1, hb1, rfl⟩
    · have := nodup_map_inj (fun r : Record => r.bundle) (recs B) hn r' h1 r hr hrb'
      subst this; exact hr'
    · exact absurd (by rw [← hrb', hf, hb1]) hne
  · intro r hr hne
    rcases hsub r hr with h1 | ⟨r1, hr1, hb1, rfl⟩
    · exact h1
    · exact absurd (by rw [hf, hb1]) hne

/-- A new offer replaces the outstanding one: the held bundle's record carries exactly `(to, id)` afterwards, and every
other record is unchanged. -/
theorem offer_sets {B : Recs} (hn : NodupB B) (nx b to : Nat) (h : (offer B nx b to).err = none) :
    (∀ r ∈ recs (offer B nx b to).B, r.bundle = b → r.offered = some to ∧ r.oid = nx) ∧
    (∀ r ∈ recs B, r.bundle ≠ b → r ∈ recs (offer B nx b to).B) ∧
    (∀ r ∈ recs (offer B nx b to).B, r.bundle ≠ b → r ∈ recs B) := by
  unfold offer at h ⊢
  cases hm : modFirst b (offerRec to nx) B with
  | none => simp [hm] at h
  | some B' =>
    simp only [hm]
    obtain ⟨r0, -, -, -, hu, h2, h3⟩ := modFirst_unique (offerRec_bundle to nx) hm hn
    exact ⟨fun r hr hrb => by rw [hu r hr hrb]; simp [offerRec], h2, h3⟩

/-- A stale acknowledgement never relieves and changes nothing: the bundle is held but its record does not offer
custody to `c` under the offer id `o` (another node, another id, or no offer at all after a cancel). -/
theorem onAck_stale {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (hheld : holds B b = true)
    (hst : ∀ r ∈ recs B, r.bundle = b → ¬ (r.offered = some c ∧ r.oid = o)) :
    onAck B L b c o true = ⟨some .notOffered, B, L, []⟩ := by
  obtain ⟨r0, hr0, hb⟩ := holds_iff.1 hheld
  cases hs : slotOf B b with
  | none => exact absurd hb ((slotOf_none.1 hs) r0 hr0)
  | some i =>
    obtain ⟨r, hBi, hrb, -⟩ := slotOf_some hn hs
    have hmem : r ∈ recs B := by
      simp only [recs, List.mem_filterMap, id]
      exact ⟨_, List.mem_of_getElem? hBi, rfl⟩
    have h' : (r.offered = some c ∧ r.oid = o) = False := eq_false (hst r hmem hrb)
    simp [onAck, hs, hBi, h']

/-- The same, for an ack that names the wrong node or a wrong offer id of an outstanding offer. -/
theorem onAck_wrong_offer {B : Recs} {L : Ledger} (hn : NodupB B) (b c o : Nat) (r : Record) (hr : r ∈ recs B)
    (hb : r.bundle = b) (hne : r.offered ≠ some c ∨ r.oid ≠ o) :
    onAck B L b c o true = ⟨some .notOffered, B, L, []⟩ :=
  onAck_stale hn b c o (holds_iff.2 ⟨r, hr, hb⟩) (fun r' hr' hb' => by
    have := nodup_map_inj (fun r : Record => r.bundle) (recs B) hn r' hr' r hr (by simp [hb', hb])
    subst this
    rintro ⟨h1, h2⟩
    rcases hne with h | h <;> contradiction)

/-- A hand-back (accept of a bundle already held): the record stays, with its previous custodian, and the outstanding
offer of this node is cancelled; nothing in the ledger changes except the expired items leaving. -/
theorem accept_held_cancels {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (bundle bytes expires previous now : Nat)
    (hh : holds (sync B (expire L now).1) bundle = true) :
    (accept B L bundle bytes expires previous now).err = none ∧
    (accept B L bundle bytes expires previous now).L = (expire L now).1 ∧
    (accept B L bundle bytes expires previous now).ev = (expire L now).2 ∧
    (∃ r0 ∈ recs (sync B (expire L now).1), r0.bundle = bundle ∧
      cancelRec r0 ∈ recs (accept B L bundle bytes expires previous now).B ∧
      (∀ r ∈ recs (accept B L bundle bytes expires previous now).B, r.bundle = bundle → r = cancelRec r0) ∧
      (∀ r ∈ recs (sync B (expire L now).1), r.bundle ≠ bundle →
        r ∈ recs (accept B L bundle bytes expires previous now).B)) ∧
    (∀ r ∈ recs (accept B L bundle bytes expires previous now).B, r.bundle = bundle → r.offered = none ∧ r.oid = 0) := by
  obtain ⟨B', hB'⟩ := cancel_some hh
  have hn1 : NodupB (sync B (expire L now).1) := sync_nodup _ hn
  have hacc : accept B L bundle bytes expires previous now =
      ⟨none, B', (expire L now).1, (expire L now).2⟩ := by
    simp [accept, hh, hB']
  rw [hacc]
  obtain ⟨r0, hr0, hr0b, hr0', hu, h2, -⟩ := modFirst_unique cancelRec_bundle hB' hn1
  refine ⟨rfl, rfl, rfl, ⟨r0, hr0, hr0b, hr0', hu, h2⟩, fun r hr hrb => ?_⟩
  rw [hu r hr hrb]; simp [cancelRec]

/-- After a hand-back every acknowledgement of the bundle is stale: whichever node and offer id it names, it neither
relieves nor changes anything. -/
theorem handback_blocks_ack {B : Recs} {L : Ledger} (hI : Inv L) (hn : NodupB B) (hl : Linked B L)
    (bundle bytes expires previous now : Nat) (hh : holds (sync B (expire L now).1) bundle = true) (c o : Nat) :
    onAck (accept B L bundle bytes expires previous now).B (accept B L bundle bytes expires previous now).L bundle c o true
      = ⟨some .notOffered, (accept B L bundle bytes expires previous now).B, (accept B L bundle bytes expires previous now).L, []⟩ := by
  obtain ⟨-, -, -, ⟨r0, hr0, hr0b, hr0', -, -⟩, hoff⟩ := accept_held_cancels hI hn bundle bytes expires previous now hh
  exact onAck_stale (accept_inv hI hn hl bundle bytes expires previous now).2.1 bundle c o
    (holds_iff.2 ⟨_, hr0', hr0b⟩) (fun r hr hrb => by
      obtain ⟨h1, -⟩ := hoff r hr hrb
      simp [h1])

/-- An incoming bundle that is already expired is refused with the store's `expired` when the book has a free record
and the ledger holds no item of the bundle after the sweep (nothing but the expired items leaves). -/
theorem accept_expired_refused {B : Recs} {L : Ledger} (hI : Inv L) (bundle bytes expires previous now : Nat)
    (hh : holds (sync B (expire L now).1) bundle = false) {slot : Nat}
    (hs : (sync B (expire L now).1).findIdx? Option.isNone = some slot)
    (hc : (expire L now).1.contains (bkey bundle) = false) (hx : expires ≤ now) :
    accept B L bundle bytes expires previous now =
      ⟨some (.store .expired), sync B (expire L now).1, (expire L now).1, (expire L now).2⟩ := by
  have hI1 := expire_inv hI now
  have hid := expire_idem L now
  have hr := (admit_expired_refused hI1 (bkey bundle) bytes .custody expires now hx).2.2.2
    (by rw [hid.1]; exact hc)
  simp only [accept, hh, hs, hc, Bool.false_eq_true, ite_false]
  rw [hr]
  simp [hid.1, hid.2]

/-- An ack addressed to the book's own node is `onAck`. -/
theorem onAckTo_self (me : Nat) (B : Recs) (L : Ledger) (b c o : Nat) (v : Bool) :
    onAckTo me me B L b c o v = onAck B L b c o v := by
  simp [onAckTo]

/-- **An ack addressed to another node moves nothing and is an error**, whatever its custodian and offer id. -/
theorem onAckTo_other {me p : Nat} (h : p ≠ me) (B : Recs) (L : Ledger) (b c o : Nat) (v : Bool) :
    (onAckTo me p B L b c o v).B = B ∧ (onAckTo me p B L b c o v).L = L ∧
      (onAckTo me p B L b c o v).err ≠ none := by
  unfold onAckTo
  rw [if_neg h]
  cases v
  · simp
  · cases hs : slotOf B b <;> simp

/-- **Relief exactly by a valid ack addressed to this node, from the node offered to, for the offer outstanding.** -/
theorem onAckTo_ok_iff {B : Recs} {L : Ledger} (hn : NodupB B) (me p b c o : Nat) (v : Bool) :
    (onAckTo me p B L b c o v).err = none ↔
      p = me ∧ v = true ∧ (∃ r ∈ recs B, r.bundle = b ∧ r.offered = some c ∧ r.oid = o) ∧
        L.contains (bkey b) = true := by
  by_cases h : p = me
  · subst h
    rw [onAckTo_self, onAck_ok_iff hn]
    simp
  · simp only [h, false_and, iff_false]
    exact (onAckTo_other h B L b c o v).2.2

end Pinc.DtnStore
