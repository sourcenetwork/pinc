import Vinc.DtnStoreLoop

/-!
# The charged store: admission

`admitItem` of `store.rs`, and its theorems (see `Vinc.DtnStoreAdmit` for the list). The result of an admission is the
error (if any), the ledger after it and the evictions in the order the callback saw them. The order of the checks is the
code's: the expired items leave first, then a key still kept is `dup`, then an item that is expired itself is `expired`,
then the fit test; so every refusal returns the swept ledger and the expired items, and a key that expired but was not
yet swept is admitted fresh.

The two exits of the code that its own logic makes unreachable (`evictLoop` returning `none`, and `put` finding no free
slot after the loop) are modelled as the refusal the code returns; `admit_cases` proves they are not taken: once the fit test passes, `evictLoop` returns a ledger and `put` finds a slot.
-/

namespace Vinc.DtnStore

/-- Why an admission was refused. -/
inductive AErr where
  | dup
  | expired
  | custodyRefused
  | full
  deriving DecidableEq, Repr

/-- The refusal for a class. -/
def refusedOf : Class → AErr
  | .custody => .custodyRefused
  | .transit => .full

/-- The result of an admission. -/
structure AOut where
  err : Option AErr
  L : Ledger
  ev : List Entry

/-- the ledger admission (`admitItem`): the expired items leave first; then a key still kept is `dup`; then an item
that is itself expired (`expires ≤ now`) is `expired`; then the fit test and the rest. Every refusal returns the swept
ledger and the expired items as the evictions. -/
def admitItem (L : Ledger) (k : Key) (bytes : Nat) (cls : Class) (expires now : Nat) : AOut :=
  let L1 := (expire L now).1
  let ev1 := (expire L now).2
  if L1.contains k then ⟨some .dup, L1, ev1⟩ else
  if expires ≤ now then ⟨some .expired, L1, ev1⟩ else
  if !fits L1 bytes then ⟨some (refusedOf cls), L1, ev1⟩ else
  match evictLoop bytes L1.slots.length L1 with
  | none => ⟨some (refusedOf cls), L1, ev1⟩
  | some (L2, ev2) =>
    match put L2.slots ⟨k, bytes, cls, expires, L2.nextSeq⟩ with
    | none => ⟨some (refusedOf cls), L2, ev1 ++ ev2⟩
    | some slots' =>
      ⟨none, { L2 with used := L2.used + bytes, nextSeq := L2.nextSeq + 1, slots := slots' }, ev1 ++ ev2⟩

theorem put_some (l : List (Option Entry)) (e : Entry) (h : (l.filterMap id).length < l.length) :
    ∃ l', put l e = some l' := by
  induction l with
  | nil => simp at h
  | cons s l ih =>
    cases s with
    | none => exact ⟨_, rfl⟩
    | some x =>
      have : (l.filterMap id).length < l.length := by simpa using h
      obtain ⟨l', hl'⟩ := ih this
      exact ⟨some x :: l', by simp [put, hl']⟩

theorem put_perm (l : List (Option Entry)) (e : Entry) (l' : List (Option Entry)) (h : put l e = some l') :
    (l'.filterMap id).Perm (e :: l.filterMap id) ∧ l'.length = l.length := by
  induction l generalizing l' with
  | nil => simp [put] at h
  | cons s l ih =>
    cases s with
    | none => simp only [put, Option.some.injEq] at h; subst h; simp
    | some x =>
      simp only [put, Option.map_eq_some_iff] at h
      obtain ⟨l2, hl2, rfl⟩ := h
      obtain ⟨hp, hlen⟩ := ih l2 hl2
      refine ⟨?_, by simp [hlen]⟩
      simp only [List.filterMap_cons, id]
      exact (hp.cons x).trans (List.Perm.swap e x _)

theorem contains_false {L : Ledger} {k : Key} (h : L.contains k = false) : ∀ x ∈ L.entries, x.key ≠ k := by
  intro x hx hk
  have : L.contains k = true := by
    unfold Ledger.contains; simp only [List.any_eq_true, decide_eq_true_eq]; exact ⟨x, hx, hk⟩
  simp_all

/-- The three shapes of an admission: a refusal before the fit test (the key is kept after the sweep, or the item is
itself expired), a refusal by the fit test, and an acceptance. Every refusal returns the swept ledger and the expired
items; `admit_refused_state` states the refusals exactly. -/
theorem admit_cases {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) :
    (((expire L now).1.contains k = true ∨ x ≤ now) ∧
      admitItem L k b c x now = ⟨some (if (expire L now).1.contains k = true then .dup else .expired),
        (expire L now).1, (expire L now).2⟩) ∨
    (((expire L now).1.contains k = false ∧ now < x) ∧ ¬ FitsSpec (expire L now).1 b ∧
      admitItem L k b c x now = ⟨some (refusedOf c), (expire L now).1, (expire L now).2⟩) ∨
    (((expire L now).1.contains k = false ∧ now < x) ∧ FitsSpec (expire L now).1 b ∧
      ∃ L2 ev2 slots', evictLoop b (expire L now).1.slots.length (expire L now).1 = some (L2, ev2) ∧
        put L2.slots ⟨k, b, c, x, L2.nextSeq⟩ = some slots' ∧
        admitItem L k b c x now = ⟨none, { L2 with used := L2.used + b, nextSeq := L2.nextSeq + 1, slots := slots' },
          (expire L now).2 ++ ev2⟩ ∧
        Inv L2 ∧ L2.budget = L.budget ∧ L2.nextSeq = L.nextSeq ∧
        (expire L now).1.entries.Perm (ev2 ++ L2.entries) ∧ L2.slots.length = L.slots.length ∧
        (∀ e ∈ ev2, e.cls = .transit) ∧ ev2.Pairwise (fun x y => x.seq < y.seq) ∧
        (∀ e ∈ ev2, ∀ r ∈ L2.entries, r.cls = .transit → e.seq < r.seq) ∧ room L2 b = false ∧
        L2.used = (expire L now).1.used - sumB ev2 ∧
        (∀ l, ev2.getLast? = some l → L.budget - (L2.used + l.bytes) < b ∨ L2.entries.length + 1 = L2.slots.length)) := by
  have hI1 := expire_inv hI now
  by_cases hc : (expire L now).1.contains k = true
  · left; exact ⟨Or.inl hc, by simp [admitItem, hc]⟩
  have hc' : (expire L now).1.contains k = false := by simpa using hc
  by_cases hx : x ≤ now
  · left; exact ⟨Or.inr hx, by simp [admitItem, hc', hx]⟩
  have hx' : now < x := by omega
  right
  by_cases hf : FitsSpec (expire L now).1 b
  · right
    refine ⟨⟨hc', hx'⟩, hf, ?_⟩
    obtain ⟨L2, ev2, hev, hI2, hb2, hs2, hsl2, hp2, hu2, htr, hrm, hpw, hlt, hlast⟩ :=
      evictLoop_spec b (expire L now).1.slots.length (expire L now).1 hI1 hf (List.length_filterMap_le _ _)
    have hsl1 : (expire L now).1.slots.length = L.slots.length := by simp [expire]
    have hfree : (L2.entries.length < L2.slots.length) := by
      have hl := List.length_filterMap_le id L2.slots
      have : ¬ (L2.entries.length = L2.slots.length) := by
        intro h; unfold room at hrm; simp [h] at hrm
      unfold Ledger.entries at *; omega
    obtain ⟨slots', hput⟩ := put_some L2.slots ⟨k, b, c, x, L2.nextSeq⟩ hfree
    refine ⟨L2, ev2, slots', hev, hput, ?_, hI2, by rw [hb2]; simp [expire], by rw [hs2]; simp [expire], hp2,
      by rw [hsl2, hsl1], htr, hpw, hlt, hrm, hu2, ?_⟩
    · have hfit : fits (expire L now).1 b = true := (fits_iff hI1 b).2 hf
      simp [admitItem, hc', hx, hfit, hev, hput]
    · intro l hl; simpa [expire] using hlast l hl
  · left
    refine ⟨⟨hc', hx'⟩, hf, ?_⟩
    have : fits (expire L now).1 b = false := by
      cases h : fits (expire L now).1 b
      · rfl
      · exact absurd ((fits_iff hI1 b).1 h) hf
    simp [admitItem, hc', hx, this]

theorem admit_inv {L : Ledger} (hI : Inv L) (k : Key) (b : Nat) (c : Class) (x now : Nat) :
    Inv (admitItem L k b c x now).L := by
  rcases admit_cases hI k b c x now with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨⟨hc, _⟩, hf, L2, ev2, slots', hev, hput, h, hI2, hb2, hs2, hp2, hsl2, htr, hpw, hlt, hrm, hu2, hlast⟩
  · rw [h]; exact expire_inv hI now
  · rw [h]; exact expire_inv hI now
  · rw [h]
    simp only
    have hperm := (put_perm _ _ _ hput).1
    have hsum : sumB ({ L2 with used := L2.used + b, nextSeq := L2.nextSeq + 1, slots := slots' } : Ledger).entries =
        b + sumB L2.entries := by
      have := sumB_perm (show ({ L2 with used := L2.used + b, nextSeq := L2.nextSeq + 1, slots := slots' } : Ledger).entries.Perm
        (⟨k, b, c, x, L2.nextSeq⟩ :: L2.entries) from hperm)
      rw [this, sumB_cons]
    have hroom : L2.used + b ≤ L2.budget := by
      have := hI2.used_le; have := hI2.used_eq; unfold room at hrm; simp at hrm; omega
    have hkeys := contains_false hc
    have hnewk : k ∉ L2.entries.map (·.key) := by
      intro hm
      obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hm
      have hy1 : y ∈ (expire L now).1.entries := hp2.mem_iff.2 (List.mem_append_right _ hy)
      exact hkeys y hy1 hyk
    have hnews : L2.nextSeq ∉ L2.entries.map (·.seq) := by
      intro hm
      obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hm
      have := hI2.seq_lt y hy
      omega
    refine ⟨by rw [hsum]; have := hI2.used_eq; simp only; omega, by simp only; omega,
      by simp only; have := hI2.budget_le; exact this, ?_, ?_, ?_⟩
    · have := (hperm.map (·.key)).nodup_iff.2 (List.nodup_cons.2 ⟨hnewk, hI2.keys⟩)
      exact this
    · have := (hperm.map (·.seq)).nodup_iff.2 (List.nodup_cons.2 ⟨hnews, hI2.seqs⟩)
      exact this
    · intro e he
      have he' := hperm.mem_iff.1 he
      simp only [List.mem_cons] at he'
      simp only
      rcases he' with rfl | he'
      · simp
      · have := hI2.seq_lt e he'; omega

end Vinc.DtnStore
