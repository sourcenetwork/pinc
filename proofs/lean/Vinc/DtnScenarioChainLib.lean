import Vinc.DtnScenarioAcct

/-!
# Records and entries after one custody operation

What the chain theorem needs of the book and the ledger of one node:

* `accept_recs_sub`: the records after an accept are the old ones or the one new record (offered to nobody);
* `accept_entries_exp`: an entry of the bundle's key after an accept is an old entry, an old entry promoted to
  custody, or the entry just admitted with the given expiry;
* `offer_recs`: after an offer the records are the old ones or the one offered to the named node;
* `delivered_recs_sub`, `bexpire_recs_sub`: those two only remove records.
-/

namespace Vinc.DtnStore

theorem accept_recs_sub (B : Recs) (L : Ledger) (bundle bytes expires previous now : Nat) :
    ∀ r ∈ recs (accept B L bundle bytes expires previous now).B,
      r ∈ recs B ∨ r = ⟨bundle, previous, none⟩ := by
  intro r hr
  unfold accept at hr
  simp only at hr
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp only [hh, ite_true] at hr; exact Or.inl (sync_sub _ _ r hr)
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false] at hr
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp only [hs] at hr; exact Or.inl (sync_sub _ _ r hr)
  | some slot =>
    simp only [hs] at hr
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp only [hc, ite_true] at hr
      rcases mem_recs_set hr with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (sync_sub _ _ r (sync_sub _ _ r h))
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false] at hr
      cases hr0 : (admitItem (expire L now).1 (bkey bundle) bytes .custody expires now).err with
      | some e =>
        simp only [hr0] at hr
        exact Or.inl (sync_sub _ _ r hr)
      | none =>
        simp only [hr0] at hr
        rcases mem_recs_set hr with rfl | h
        · exact Or.inr rfl
        · exact Or.inl (sync_sub _ _ r (sync_sub _ _ r h))

theorem accept_entries_exp {L : Ledger} (hI : Inv L) (B : Recs) (bundle bytes expires previous now : Nat) :
    ∀ e' ∈ (accept B L bundle bytes expires previous now).L.entries,
      e' ∈ L.entries ∨ (∃ y ∈ L.entries, e' = { y with cls := .custody }) ∨
        (e'.key = bkey bundle ∧ e'.expires = expires) := by
  intro e' he'
  have hsub := expire_sub L now
  have hI1 := expire_inv hI now
  unfold accept at he'
  simp only at he'
  by_cases hh : holds (sync B (expire L now).1) bundle = true
  · simp only [hh, ite_true] at he'; exact Or.inl (hsub e' he')
  have hh' : holds (sync B (expire L now).1) bundle = false := by simpa using hh
  simp only [hh', Bool.false_eq_true, ite_false] at he'
  cases hs : (sync B (expire L now).1).findIdx? Option.isNone with
  | none => simp only [hs] at he'; exact Or.inl (hsub e' he')
  | some slot =>
    simp only [hs] at he'
    by_cases hc : (expire L now).1.contains (bkey bundle) = true
    · simp only [hc, ite_true] at he'
      rw [reclass_entries _ _ _ hc] at he'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he'
      by_cases hyk : y.key = bkey bundle
      · right; left; exact ⟨y, hsub y hy, by simp [hyk]⟩
      · left; simp only [hyk, ite_false]; exact hsub y hy
    · have hc' : (expire L now).1.contains (bkey bundle) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ite_false] at he'
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · simp_all
      · rw [h2] at he'; simp only at he'
        rw [(expire_idem L now).1] at he'
        exact Or.inl (hsub e' he')
      · rw [h2] at he'; simp only at he'
        have := admit_entries_sub hI1 (bkey bundle) bytes .custody expires now e'
        rw [h2] at this
        rcases this he' with h | h
        · exact Or.inl (hsub e' h)
        · right; right; subst h; exact ⟨rfl, rfl⟩

theorem setOffered_recs (b to : Nat) : ∀ (B B' : Recs), setOffered b to B = some B' →
    ∀ r ∈ recs B', r ∈ recs B ∨ (r.bundle = b ∧ r.offered = some to)
  | [], B', h => by simp [setOffered] at h
  | s :: t, B', h => by
    cases s with
    | none =>
      simp only [setOffered, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', rfl⟩ := h
      intro r hr
      have hr' : r ∈ recs t' := by simpa [recs] using hr
      rcases setOffered_recs b to t t' ht' r hr' with h | h
      · left; simpa [recs] using h
      · right; exact h
    | some x =>
      by_cases hx : x.bundle = b
      · simp only [setOffered, hx, ite_true, Option.some.injEq] at h
        subst h
        intro r hr
        simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr
        rcases hr with rfl | hr
        · right; exact ⟨rfl, rfl⟩
        · left; simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr hr
      · simp only [setOffered, hx, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨t', ht', rfl⟩ := h
        intro r hr
        simp only [recs, List.filterMap_cons, id, List.mem_cons] at hr
        rcases hr with rfl | hr
        · left; simp [recs]
        · have hr' : r ∈ recs t' := hr
          rcases setOffered_recs b to t t' ht' r hr' with h | h
          · left; simp only [recs, List.filterMap_cons, id, List.mem_cons]; exact Or.inr h
          · right; exact h

theorem offer_recs (B : Recs) (b to : Nat) :
    ∀ r ∈ recs (offer B b to).2, r ∈ recs B ∨ (r.bundle = b ∧ r.offered = some to) := by
  unfold offer
  cases h : setOffered b to B with
  | none => intro r hr; exact Or.inl hr
  | some B' => exact setOffered_recs b to B B' h

theorem delivered_recs_sub (B : Recs) (L : Ledger) (b : Nat) : ∀ r ∈ recs (delivered B L b).B, r ∈ recs B := by
  unfold delivered
  cases h : slotOf B b with
  | none => intro r hr; exact hr
  | some i => intro r hr; exact recs_set_none B i r hr

theorem delivered_entries_sub (B : Recs) (L : Ledger) (b : Nat) : ∀ e ∈ (delivered B L b).L.entries, e ∈ L.entries := by
  unfold delivered
  cases h : slotOf B b with
  | none => intro e he; exact he
  | some i =>
    intro e he
    exact release_sub L (bkey b) e he

theorem bexpire_recs_sub (B : Recs) (L : Ledger) (now : Nat) : ∀ r ∈ recs (bexpire B L now).B, r ∈ recs B :=
  fun r hr => sync_sub B _ r hr

end Vinc.DtnStore
