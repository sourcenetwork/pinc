import Vinc.DtnStoreThm

/-!
# The charged store: the properties

The statements of the task about the ledger, each for every ledger satisfying `Inv` and every call:

* `admit_ok_iff`, `admit_refused_state`, `admit_budget`: an admission is accepted exactly when the key is new and the
  non-evictable items leave room; a refusal moves nothing but the expired items; the bytes charged never exceed the
  budget.
* `admit_keeps_live_custody` (and the mailbox form): live custody is never evicted, by any admission.
* `admit_eviction_order`, `admit_eviction_minimal`: expired items first, then transit items oldest admission first,
  and no more than needed.
* `expire_exits`, `release_exits`, `reclass_only_class`: the other ways an item can leave or change.
* `used_by_space`: the bytes of every space are charged to one budget; `mailbox_evicts_bundle_transit` shows that a
  mailbox admission can take the room of a bundle in transit, and `mailbox_refused_by_bundle_custody` that it cannot
  take the room of bundle custody.
-/

namespace Vinc.DtnStore

theorem admit_ok_iff {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) :
    (admit L k b c x now).err = none ↔ L.contains k = false ∧ FitsSpec (expire L now).1 b := by
  rcases admit_cases hI k b c x now with ⟨h1, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, _, _, _, _, _, h, _⟩
  · simp [h, h1]
  · simp [h, h1, h2]
  · simp [h, h1, h2]

theorem admit_refused_state {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) (e : AErr)
    (h : (admit L k b c x now).err = some e) :
    (e = .dup ∧ L.contains k = true ∧ (admit L k b c x now).L = L ∧ (admit L k b c x now).ev = []) ∨
    (e = refusedOf c ∧ L.contains k = false ∧ (admit L k b c x now).L = (expire L now).1 ∧
      (admit L k b c x now).ev = (expire L now).2) := by
  rcases admit_cases hI k b c x now with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨_, _, _, _, _, _, _, h3, _⟩
  · left; rw [h2] at h ⊢; simp at h; simp [h, h1]
  · right; rw [h3] at h ⊢; simp at h; simp [h, h1]
  · rw [h3] at h; simp at h

theorem admit_budget {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) :
    (admit L k b c x now).L.used ≤ (admit L k b c x now).L.budget :=
  (admit_inv hI k b c x now).used_le

theorem admit_keeps_live_custody {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat)
    (e : Entry) (he : e ∈ L.entries) (hc : e.cls = .custody) (hlive : expiredAt now e = false) :
    e ∈ (admit L k b c x now).L.entries := by
  have h1 : e ∈ (expire L now).1.entries := by
    rw [entries_expire]; exact List.mem_filter.2 ⟨he, by simp [hlive]⟩
  rcases admit_cases hI k b c x now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨hc', hf, L2, ev2, slots', hev, hput, h, hI2, hb2, hs2, hp2, hsl2, htr, hpw, hlt, hrm, hu2, hlast⟩
  · rw [h]; exact he
  · rw [h]; exact h1
  · rw [h]
    have hn : e ∉ ev2 := fun hm => by have := htr e hm; rw [hc] at this; cases this
    have h2 : e ∈ L2.entries := by
      have := hp2.mem_iff.1 h1
      simp only [List.mem_append] at this
      exact this.resolve_left hn
    have := (put_perm _ _ _ hput).1.mem_iff.2 (List.mem_cons_of_mem _ h2)
    simpa [Ledger.entries] using this

/-- The mailbox form: an admission of a mailbox key never evicts live custody of either space. -/
theorem admit_mailbox_keeps_live_custody {L : Ledger} (hI : Inv L) (k : Key) (_ : k.space = 2) (b : Nat) (c : Class)
    (x now : Nat) (e : Entry) (he : e ∈ L.entries) (hc : e.cls = .custody) (hlive : expiredAt now e = false) :
    e ∈ (admit L k b c x now).L.entries :=
  admit_keeps_live_custody hI k b c x now e he hc hlive

theorem admit_eviction_order {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat)
    (hok : (admit L k b c x now).err = none) :
    ∃ ev2, (admit L k b c x now).ev = L.entries.filter (expiredAt now) ++ ev2 ∧
      (∀ e ∈ ev2, e.cls = .transit ∧ expiredAt now e = false) ∧
      ev2.Pairwise (fun p q => p.seq < q.seq) ∧
      (∀ e ∈ ev2, ∀ r ∈ (admit L k b c x now).L.entries, r.cls = .transit → e.seq < r.seq) := by
  rcases admit_cases hI k b c x now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨hc', hf, L2, ev2, slots', hev, hput, h, hI2, hb2, hs2, hp2, hsl2, htr, hpw, hlt, hrm, hu2, hlast⟩
  · rw [h] at hok; simp at hok
  · rw [h] at hok; simp at hok
  · refine ⟨ev2, by rw [h]; simp [expire], ?_, hpw, ?_⟩
    · intro e he
      refine ⟨htr e he, ?_⟩
      have h1 : e ∈ (expire L now).1.entries := hp2.mem_iff.2 (List.mem_append_left _ he)
      rw [entries_expire] at h1
      simpa using (List.mem_filter.1 h1).2
    · intro e he r hr ht
      rw [h] at hr
      have hr' := (put_perm _ _ _ hput).1.mem_iff.1 (by simpa [Ledger.entries] using hr)
      simp only [List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · have h1 : e ∈ (expire L now).1.entries := hp2.mem_iff.2 (List.mem_append_left _ he)
        rw [entries_expire] at h1
        have := hI.seq_lt e (List.mem_filter.1 h1).1
        simp only [hs2]; simp [expire] at *; omega
      · exact hlt e he r hr' ht

/-- The last eviction was needed: without it the item would not have fit. -/
theorem admit_eviction_minimal {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat)
    (hok : (admit L k b c x now).err = none) :
    ∃ ev2, (admit L k b c x now).ev = L.entries.filter (expiredAt now) ++ ev2 ∧
      ∀ l, ev2.getLast? = some l →
        L.budget - ((admit L k b c x now).L.used - b + l.bytes) < b ∨
          (admit L k b c x now).L.entries.length = (admit L k b c x now).L.slots.length := by
  rcases admit_cases hI k b c x now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨hc', hf, L2, ev2, slots', hev, hput, h, hI2, hb2, hs2, hp2, hsl2, htr, hpw, hlt, hrm, hu2, hlast⟩
  · rw [h] at hok; simp at hok
  · rw [h] at hok; simp at hok
  · refine ⟨ev2, by rw [h]; simp [expire], ?_⟩
    intro l hl
    have hlen := (put_perm _ _ _ hput).2
    have hper := (put_perm _ _ _ hput).1.length_eq
    rw [h]
    simp only [Nat.add_sub_cancel]
    rcases hlast l hl with h1 | h1
    · left; exact h1
    · right
      simp only [Ledger.entries] at *
      simp at hper
      omega

theorem expire_exits (L : Ledger) (now : Nat) :
    (expire L now).2 = L.entries.filter (expiredAt now) ∧
      (expire L now).1.entries = L.entries.filter (fun e => !expiredAt now e) :=
  ⟨rfl, entries_expire L now⟩

theorem release_exits (L : Ledger) (k : Key) :
    ((release L k).2 = none ∧ (release L k).1 = L ∧ L.contains k = false) ∨
    (∃ e, (release L k).2 = some e ∧ e.key = k ∧ L.entries.Perm (e :: (release L k).1.entries)) := by
  unfold release
  cases hf : L.slots.findIdx? (fun s => s.any fun e => decide (e.key = k)) with
  | none =>
    left
    refine ⟨rfl, rfl, ?_⟩
    have hn := List.findIdx?_eq_none_iff.1 hf
    cases hc : L.contains k
    · rfl
    · exfalso
      unfold Ledger.contains Ledger.entries at hc
      simp only [List.any_eq_true, decide_eq_true_eq, List.mem_filterMap, id] at hc
      obtain ⟨e, ⟨s, hs, hse⟩, hk⟩ := hc
      have := hn s hs
      subst hse
      simp [hk] at this
  | some i =>
    right
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    cases hs : L.slots[i] with
    | none => rw [hs] at hp; simp at hp
    | some e =>
      rw [hs] at hp
      simp at hp
      have htake : takeAt L i = some ({ L with used := L.used - e.bytes, slots := L.slots.set i none }, e) := by
        have hs' : L.slots[i]? = some (some e) := by rw [List.getElem?_eq_getElem hi, hs]
        simp [takeAt, hs']
      exact ⟨e, by simp [htake], hp, by simpa [htake] using takeAt_perm htake⟩

theorem reclass_only_class (L : Ledger) (k : Key) (c : Class) (h : L.contains k = true) :
    (reclass L k c).1.entries = L.entries.map fun e => if e.key = k then { e with cls := c } else e :=
  reclass_entries L k c h

theorem used_by_space {L : Ledger} (hI : Inv L) :
    L.used = sumB (L.entries.filter fun e => decide (e.key.space = 1)) +
      sumB (L.entries.filter fun e => !decide (e.key.space = 1)) := by
  rw [sumB_filter]; exact hI.used_eq


/-- A bundle in transit and a mailbox item share one budget: the mailbox admission evicts the bundle's transit item. -/
theorem mailbox_evicts_bundle_transit :
    let L : Ledger := ⟨10, 6, 1, [some ⟨⟨1, 1⟩, 6, .transit, 100, 0⟩, none]⟩
    let r := admit L ⟨2, 7⟩ 6 .transit 100 0
    r.err = none ∧ r.ev = [⟨⟨1, 1⟩, 6, .transit, 100, 0⟩] ∧ r.L.used = 6 := by
  decide

/-- Bundle custody is not evicted by a mailbox admission: the admission is refused and nothing moves. -/
theorem mailbox_refused_by_bundle_custody :
    let L : Ledger := ⟨10, 6, 1, [some ⟨⟨1, 1⟩, 6, .custody, 100, 0⟩, none]⟩
    let r := admit L ⟨2, 7⟩ 6 .transit 100 0
    r.err = some .full ∧ r.ev = [] ∧ r.L.used = 6 ∧ r.L.entries = L.entries := by
  decide

/-- A mailbox item and a bundle with the same 32 bytes are different keys. -/
theorem spaces_are_distinct_keys : (⟨1, 5⟩ : Key) ≠ ⟨2, 5⟩ := by decide

#audit_axioms Vinc.DtnStore.admit_inv
#audit_axioms Vinc.DtnStore.admit_ok_iff
#audit_axioms Vinc.DtnStore.admit_refused_state
#audit_axioms Vinc.DtnStore.admit_budget
#audit_axioms Vinc.DtnStore.admit_keeps_live_custody
#audit_axioms Vinc.DtnStore.admit_mailbox_keeps_live_custody
#audit_axioms Vinc.DtnStore.admit_eviction_order
#audit_axioms Vinc.DtnStore.admit_eviction_minimal
#audit_axioms Vinc.DtnStore.expire_inv
#audit_axioms Vinc.DtnStore.release_inv
#audit_axioms Vinc.DtnStore.reclass_inv
#audit_axioms Vinc.DtnStore.release_exits
#audit_axioms Vinc.DtnStore.used_by_space
#audit_axioms Vinc.DtnStore.mailbox_evicts_bundle_transit
#audit_axioms Vinc.DtnStore.mailbox_refused_by_bundle_custody

end Vinc.DtnStore
