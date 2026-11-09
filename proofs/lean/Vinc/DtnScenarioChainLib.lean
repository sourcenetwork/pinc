import Vinc.DtnScenarioAcct

/-!
# Records and entries after one custody operation

What the chain theorem needs of the book and the ledger of one node:

* `accept_recs_sub`: the records after an accept are old ones or have no outstanding offer (the new record, or a held
  record whose offer the accept cancelled);
* `accept_entries_exp`: an entry of the bundle's key after an accept is an old entry, an old entry promoted to
  custody, or the entry just admitted with the given expiry;
* `offer_recs`: after an offer the records are the old ones or the one offered to the named node;
* `delivered_recs_sub`, `bexpire_recs_sub`: those two only remove records.
-/

namespace Vinc.DtnStore

theorem accept_recs_sub (B : Recs) (L : Ledger) (bundle bytes expires previous now : Nat) :
    ∀ r ∈ recs (accept B L bundle bytes expires previous now).B, r ∈ recs B ∨ r.offered = none :=
  accept_recs_shape B L bundle bytes expires previous now

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
      rcases admit_cases hI1 (bkey bundle) bytes .custody expires now with ⟨_, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, L2, ev2, slots', _, _, h2, _⟩
      · rw [h2] at he'; simp only at he'
        rw [(expire_idem L now).1] at he'
        exact Or.inl (hsub e' he')
      · rw [h2] at he'; simp only at he'
        rw [(expire_idem L now).1] at he'
        exact Or.inl (hsub e' he')
      · rw [h2] at he'; simp only at he'
        have := admit_entries_sub hI1 (bkey bundle) bytes .custody expires now e'
        rw [h2] at this
        rcases this he' with h | h
        · exact Or.inl (hsub e' h)
        · right; right; subst h; exact ⟨rfl, rfl⟩

theorem offer_recs (B : Recs) (nx b to : Nat) :
    ∀ r ∈ recs (offer B nx b to).B, r ∈ recs B ∨ (r.bundle = b ∧ r.offered = some to) := by
  intro r hr
  unfold offer at hr
  cases h : modFirst b (offerRec to nx) B with
  | none => simp only [h] at hr; exact Or.inl hr
  | some B' =>
    simp only [h] at hr
    obtain ⟨-, hsub, -⟩ := modFirst_spec b (offerRec to nx) (offerRec_bundle to nx) B B' h
    rcases hsub r hr with h1 | ⟨r0, _, hb, rfl⟩
    · exact Or.inl h1
    · right; exact ⟨hb, rfl⟩

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
