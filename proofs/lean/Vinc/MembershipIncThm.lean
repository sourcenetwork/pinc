import Vinc.MembershipInc

/-!
# Membership: the incarnation theorems

Unbounded theorems about `Vinc.MemInc` (`MembershipInc.lean`, the model of `incarnation.rs`):

* `nextRecord_word_lt`, `observe_word_lt`: the word strictly increases through every record and every moving observe;
* `start_epoch_gt_*`: a new life starts strictly above the persisted counter, the host floor and (with the clock fallback)
  the clock: the persistent counter is `max(remembered, floor) + 1`, the hybrid clock is never at or below a remembered
  epoch (`start_hlc_gt_floor`);
* `Inv`: the invariant "the epoch is within 48 bits and a persistent store holds the epoch in use", kept by `start`,
  `nextRecord` and `observe` (`start_inv`, `nextRecord_inv`, `observe_inv`), which is the seal-before-use property;
* `restart_word_gt`: across a restart the words of the new life are strictly above every word of the old life, whatever
  the wall clock does (a clock that jumped back included), for a persistent store;
* `start_exhausted`, `nextRecord_exhausted`, `observe_exhausted`: the epoch space running out is reported, never wrapped;
* the address tag: `moved_twice`, `moves_lt`, `tag_changes`, `tag_settles`.

The theorems are over every state; the traces (`trace_membership`) tie the model to the code.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace Vinc.MemInc

theorem word_lt_of_epoch_lt {i j : Inc} (hi : i.seq < 65536) (h : i.epoch < j.epoch) : i.word < j.word := by
  unfold Inc.word; have := Nat.mul_le_mul_right 65536 (Nat.succ_le_of_lt h); omega

/-- The invariant: the sequence is a `u16`, the epoch is within 48 bits, and a persistent store holds the epoch in use. -/
def Inv (l : Local) (i : Inc) : Prop :=
  i.seq < 65536 ∧ i.epoch ≤ EPOCH_MAX ∧ (l.persistent = true → l.sealed = some i.epoch)

theorem satAdd_one_of_le {a : Nat} (h : a + 1 ≤ EPOCH_MAX) : satAdd a 1 = a + 1 := by
  unfold satAdd U64MAX EPOCH_MAX at *; omega

theorem sealEpoch_ok {l l' : Local} {e : Nat} (h : sealEpoch l e = .ok l') :
    e ≤ EPOCH_MAX ∧ l'.persistent = l.persistent ∧ (l.persistent = true → l'.sealed = some e) ∧
      (l.persistent = false → l' = l) := by
  unfold sealEpoch at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · rename_i h2
      split at h
      · cases h
      · injection h with h; subst h
        exact ⟨by omega, rfl, fun _ => rfl, fun h => by simp_all⟩
    · rename_i h2
      injection h with h; subst h
      exact ⟨by omega, rfl, fun h => by simp_all, fun _ => rfl⟩

theorem sealEpoch_exhausted {l : Local} {e : Nat} (h : EPOCH_MAX < e) : sealEpoch l e = .error .exhausted := by
  simp [sealEpoch, h]

/-! ## nextRecord -/

theorem nextRecord_small {l : Local} {i : Inc} (h : i.seq + 1 ≤ 65535) :
    nextRecord l i = .ok ({ i with seq := i.seq + 1 }.word, { i with seq := i.seq + 1 }, l) := by
  unfold nextRecord; rw [if_pos h]

theorem nextRecord_full {l : Local} {i : Inc} (h : ¬ i.seq + 1 ≤ 65535) :
    nextRecord l i = (sealEpoch l (satAdd i.epoch 1)).map
      (fun l' => (({ epoch := satAdd i.epoch 1, seq := 0 } : Inc).word, { epoch := satAdd i.epoch 1, seq := 0 }, l')) := by
  unfold nextRecord; rw [if_neg h]; dsimp only; cases sealEpoch l (satAdd i.epoch 1) <;> rfl

theorem nextRecord_word_lt {l l' : Local} {i i' : Inc} {w : Nat} (hi : i.seq < 65536)
    (h : nextRecord l i = .ok (w, i', l')) : i.word < w ∧ w = i'.word := by
  by_cases h1 : i.seq + 1 ≤ 65535
  · rw [nextRecord_small h1] at h
    injection h with h; injection h with h1' h2; injection h2 with h2 h3
    subst h1'; subst h2
    refine ⟨?_, rfl⟩
    simp only [Inc.word]; omega
  · rw [nextRecord_full h1] at h
    cases hs : sealEpoch l (satAdd i.epoch 1) with
    | error e => rw [hs] at h; cases h
    | ok l2 =>
      rw [hs] at h
      injection h with h; injection h with h1' h2; injection h2 with h2 h3
      subst h1'; subst h2
      obtain ⟨hle, _⟩ := sealEpoch_ok hs
      refine ⟨?_, rfl⟩
      have hs1 : satAdd i.epoch 1 = i.epoch + 1 := satAdd_one_of_le (by unfold satAdd U64MAX EPOCH_MAX at *; omega)
      simp only [Inc.word, hs1]
      have : i.seq = 65535 := by omega
      omega

theorem nextRecord_inv {l l' : Local} {i i' : Inc} {w : Nat} (hI : Inv l i)
    (h : nextRecord l i = .ok (w, i', l')) : Inv l' i' := by
  obtain ⟨hs, he, hp⟩ := hI
  by_cases h1 : i.seq + 1 ≤ 65535
  · rw [nextRecord_small h1] at h
    injection h with h; injection h with h1' h2; injection h2 with h2 h3
    subst h2; subst h3
    exact ⟨by simp; omega, he, hp⟩
  · rw [nextRecord_full h1] at h
    cases hs' : sealEpoch l (satAdd i.epoch 1) with
    | error e => rw [hs'] at h; cases h
    | ok l2 =>
      rw [hs'] at h
      injection h with h; injection h with h1' h2; injection h2 with h2 h3
      subst h2; subst h3
      obtain ⟨hle, hper, hseal, _⟩ := sealEpoch_ok hs'
      exact ⟨by simp, hle, fun hp' => hseal (by rw [← hper]; exact hp')⟩

theorem nextRecord_exhausted {l : Local} {i : Inc} (hs : ¬ i.seq + 1 ≤ 65535) (he : i.epoch = EPOCH_MAX) :
    nextRecord l i = .error .exhausted := by
  have : EPOCH_MAX < satAdd i.epoch 1 := by unfold satAdd U64MAX EPOCH_MAX at *; omega
  rw [nextRecord_full hs, sealEpoch_exhausted this]; rfl

/-! ## observe -/

theorem observe_noop {l : Local} {i : Inc} {seen : Nat} (h : seen ≤ i.word) : observe l i seen = .ok (false, i, l) := by
  unfold observe; rw [if_pos h]

theorem observe_move {l : Local} {i : Inc} {seen : Nat} (h : ¬ seen ≤ i.word) :
    observe l i seen = (sealEpoch l (satAdd (max (seen / 65536) i.epoch) 1)).map
      (fun l' => (true, ({ epoch := satAdd (max (seen / 65536) i.epoch) 1, seq := 0 } : Inc), l')) := by
  unfold observe; rw [if_neg h]; dsimp only; cases sealEpoch l (satAdd (max (seen / 65536) i.epoch) 1) <;> rfl

theorem observe_false {l l' : Local} {i i' : Inc} {seen : Nat} (h : observe l i seen = .ok (false, i', l')) :
    seen ≤ i.word ∧ i' = i ∧ l' = l := by
  by_cases h1 : seen ≤ i.word
  · rw [observe_noop h1] at h
    injection h with h; injection h with _ h; injection h with h2 h3
    exact ⟨h1, h2.symm, h3.symm⟩
  · rw [observe_move h1] at h
    cases hs : sealEpoch l (satAdd (max (seen / 65536) i.epoch) 1) with
    | error e => rw [hs] at h; cases h
    | ok l2 => rw [hs] at h; injection h with h; injection h with h; cases h

theorem observe_word_lt {l l' : Local} {i i' : Inc} {seen : Nat} (hi : i.seq < 65536)
    (h : observe l i seen = .ok (true, i', l')) : seen < i'.word ∧ i.word < i'.word := by
  by_cases h1 : seen ≤ i.word
  · rw [observe_noop h1] at h; injection h with h; injection h with h; cases h
  · rw [observe_move h1] at h
    cases hs : sealEpoch l (satAdd (max (seen / 65536) i.epoch) 1) with
    | error e => rw [hs] at h; cases h
    | ok l2 =>
      rw [hs] at h
      injection h with h; injection h with _ h; injection h with h2 h3
      subst h2
      obtain ⟨hle, _⟩ := sealEpoch_ok hs
      have hs1 : satAdd (max (seen / 65536) i.epoch) 1 = max (seen / 65536) i.epoch + 1 := by
        unfold satAdd U64MAX EPOCH_MAX at *; omega
      simp only [Inc.word, hs1]
      have hd := Nat.div_add_mod seen 65536
      have hm := Nat.mod_lt seen (show 65536 > 0 by omega)
      have h3 := Nat.mul_le_mul_right 65536 (show seen / 65536 + 1 ≤ max (seen / 65536) i.epoch + 1 by omega)
      have h4 := Nat.mul_le_mul_right 65536 (show i.epoch + 1 ≤ max (seen / 65536) i.epoch + 1 by omega)
      simp only [Inc.word] at h1
      constructor <;> omega

theorem observe_inv {l l' : Local} {i i' : Inc} {seen : Nat} (hI : Inv l i) (b : Bool)
    (h : observe l i seen = .ok (b, i', l')) : Inv l' i' := by
  obtain ⟨hs, he, hp⟩ := hI
  by_cases h1 : seen ≤ i.word
  · rw [observe_noop h1] at h
    injection h with h; injection h with _ h; injection h with h2 h3
    subst h2; subst h3
    exact ⟨hs, he, hp⟩
  · rw [observe_move h1] at h
    cases hs' : sealEpoch l (satAdd (max (seen / 65536) i.epoch) 1) with
    | error e => rw [hs'] at h; cases h
    | ok l2 =>
      rw [hs'] at h
      injection h with h; injection h with _ h; injection h with h2 h3
      subst h2; subst h3
      obtain ⟨hle, hper, hseal, _⟩ := sealEpoch_ok hs'
      exact ⟨by simp, hle, fun hp' => hseal (by rw [← hper]; exact hp')⟩

theorem observe_exhausted {l : Local} {i : Inc} {seen : Nat} (hs : i.word < seen) (hbig : EPOCH_MAX ≤ seen / 65536) :
    observe l i seen = .error .exhausted := by
  have h1 : ¬ seen ≤ i.word := by omega
  have : EPOCH_MAX < satAdd (max (seen / 65536) i.epoch) 1 := by
    have := Nat.le_max_left (seen / 65536) i.epoch
    unfold satAdd U64MAX EPOCH_MAX at *; omega
  rw [observe_move h1, sealEpoch_exhausted this]; rfl

/-! ## start -/

theorem start_persistent {l : Local} {w f : Nat} (hp : l.persistent = true) (hr : l.readFails = false) :
    start l w f = (sealEpoch l (satAdd (max (l.sealed.getD 0) f) 1)).map
      (fun l' => (({ epoch := satAdd (max (l.sealed.getD 0) f) 1, seq := 0 } : Inc), l')) := by
  unfold start
  simp only [hp, hr, if_true, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure]
  cases sealEpoch l (satAdd (max (l.sealed.getD 0) f) 1) <;> rfl

theorem start_hlc {l : Local} {w f : Nat} (hp : l.persistent = false) :
    start l w f = (sealEpoch l (max (satAdd w 1) (satAdd (max 0 f) 1))).map
      (fun l' => (({ epoch := max (satAdd w 1) (satAdd (max 0 f) 1), seq := 0 } : Inc), l')) := by
  unfold start
  simp only [hp, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure]
  cases sealEpoch l (max (satAdd w 1) (satAdd (max 0 f) 1)) <;> rfl

theorem start_ok {l l' : Local} {i : Inc} {w f : Nat} (h : start l w f = .ok (i, l')) :
    i.seq = 0 ∧ i.epoch ≤ EPOCH_MAX ∧ Inv l' i ∧ l'.persistent = l.persistent ∧
    (l.persistent = true → l.readFails = false ∧ i.epoch = satAdd (max (l.sealed.getD 0) f) 1) ∧
    (l.persistent = false → i.epoch = max (satAdd w 1) (satAdd f 1) ∧ l' = l) := by
  by_cases hp : l.persistent = true
  · by_cases hr : l.readFails = true
    · unfold start at h; simp [hp, hr, bind, Except.bind] at h
    · have hr' : l.readFails = false := by simpa using hr
      rw [start_persistent hp hr'] at h
      cases hs : sealEpoch l (satAdd (max (l.sealed.getD 0) f) 1) with
      | error e => rw [hs] at h; cases h
      | ok l2 =>
        rw [hs] at h
        injection h with h; injection h with h1 h2; subst h1; subst h2
        obtain ⟨hle, hper, hseal, _⟩ := sealEpoch_ok hs
        exact ⟨rfl, hle, ⟨by simp, hle, fun _ => hseal hp⟩, hper, fun _ => ⟨hr', rfl⟩, fun hh => by simp_all⟩
  · have hp' : l.persistent = false := by simpa using hp
    rw [start_hlc hp'] at h
    cases hs : sealEpoch l (max (satAdd w 1) (satAdd (max 0 f) 1)) with
    | error e => rw [hs] at h; cases h
    | ok l2 =>
      rw [hs] at h
      injection h with h; injection h with h1 h2; subst h1; subst h2
      obtain ⟨hle, hper, _, hnp⟩ := sealEpoch_ok hs
      have := hnp hp'
      subst this
      refine ⟨rfl, hle, ⟨by simp, hle, fun h => by simp_all⟩, rfl, fun h => by simp_all, fun _ => ⟨by simp, rfl⟩⟩

/-- A persistent life starts strictly above the remembered counter and the host floor. -/
theorem start_epoch_gt {l l' : Local} {i : Inc} {w f : Nat} (hp : l.persistent = true)
    (h : start l w f = .ok (i, l')) : (∀ s, l.sealed = some s → s < i.epoch) ∧ f < i.epoch := by
  obtain ⟨-, hle, -, -, hper, -⟩ := start_ok h
  obtain ⟨-, he⟩ := hper hp
  have hs1 : satAdd (max (l.sealed.getD 0) f) 1 = max (l.sealed.getD 0) f + 1 := by
    unfold satAdd U64MAX EPOCH_MAX at *; omega
  rw [he, hs1]
  refine ⟨fun s hs => ?_, ?_⟩
  · simp only [hs, Option.getD_some]; omega
  · omega

/-- The hybrid clock (no persistent store) is never at or below the host floor, and is above the wall clock. -/
theorem start_hlc_gt_floor {l l' : Local} {i : Inc} {w f : Nat} (hp : l.persistent = false)
    (h : start l w f = .ok (i, l')) : f < i.epoch ∧ w < i.epoch := by
  obtain ⟨-, hle, -, -, -, hn⟩ := start_ok h
  obtain ⟨he, -⟩ := hn hp
  unfold satAdd U64MAX EPOCH_MAX at *
  omega

theorem start_inv {l l' : Local} {i : Inc} {w f : Nat} (h : start l w f = .ok (i, l')) : Inv l' i :=
  (start_ok h).2.2.1

theorem start_exhausted {l : Local} {w f : Nat} (hp : l.persistent = true) (hr : l.readFails = false)
    (hbig : EPOCH_MAX ≤ max (l.sealed.getD 0) f) : start l w f = .error .exhausted := by
  have : EPOCH_MAX < satAdd (max (l.sealed.getD 0) f) 1 := by unfold satAdd U64MAX EPOCH_MAX at *; omega
  rw [start_persistent hp hr, sealEpoch_exhausted this]; rfl

/-- Across a restart the words of the new life are above every word of the old life, whatever the wall clock does:
the old life's epoch is the sealed counter (`Inv`), the new epoch is above it, and every word of the old life is below
`(epoch + 1) * 65536`. -/
theorem restart_word_gt {l l' : Local} {i j : Inc} {w f : Nat} (hp : l.persistent = true) (hI : Inv l i)
    (h : start l w f = .ok (j, l')) : i.word < j.word := by
  obtain ⟨hs, he, hseal⟩ := hI
  have hgt := (start_epoch_gt hp h).1 i.epoch (hseal hp)
  exact word_lt_of_epoch_lt hs hgt

/-! ## The address tag -/

theorem moved_twice (t : Tag) (now : Nat) : (t.moved now).moved now = t.moved now := by
  simp [Tag.moved]

theorem moves_lt (t : Tag) (now : Nat) (h : t.moves < 256) : (t.moved now).moves < 256 := by
  unfold Tag.moved; split <;> simp_all <;> omega

theorem moved_counts (t : Tag) (now : Nat) (h : t.movedAt ≠ some now) (hm : t.moves < 256) :
    (t.moved now).moves = (t.moves + 1) % 256 := by
  simp [Tag.moved, h]

theorem moved_same_instant (t : Tag) (now : Nat) (h : t.movedAt = some now) : (t.moved now).moves = t.moves := by
  simp [Tag.moved, h]

/-- The previous tag is kept while settling. -/
theorem tag_settles (t : Tag) (now : Nat) (refl : Bool) (hash : Nat → List Nat) (prev : List Nat)
    (hc : t.current = some prev) (hs : t.settling now refl = true) : (t.tag now refl hash).1 = prev := by
  simp [Tag.tag, hc, hs]

/-- Once settling is over, the tag is the hash of the move counter. -/
theorem tag_adopts (t : Tag) (now : Nat) (refl : Bool) (hash : Nat → List Nat)
    (hs : t.settling now refl = false) : (t.tag now refl hash).1 = hash t.moves := by
  unfold Tag.tag; cases hc : t.current <;> simp [hs]

/-- The reflexive address being known ends the settle at once. -/
theorem settling_known (t : Tag) (now : Nat) : t.settling now true = false := by
  unfold Tag.settling; cases t.movedAt <;> simp

/-- After the settle time the previous tag is gone. -/
theorem settling_expired (t : Tag) (now m : Nat) (refl : Bool) (hm : t.movedAt = some m)
    (h : m + MOVE_SETTLE ≤ now) : t.settling now refl = false := by
  unfold Tag.settling MOVE_SETTLE at *; simp [hm]; omega

/-- A handover changes the tag, once the settle is over: the hash differs for the new counter value. -/
theorem tag_changes (t : Tag) (now : Nat) (hash : Nat → List Nat) (m : Nat)
    (hinj : ∀ a b, a < 256 → b < 256 → hash a = hash b → a = b)
    (hmoves : t.moves < 256) (hnew : t.movedAt ≠ some now) (hne : (t.moves + 1) % 256 ≠ t.moves) :
    hash ((t.moved now).moves) ≠ hash t.moves := by
  intro h
  have := hinj _ _ (by rw [moved_counts t now hnew hmoves]; exact Nat.mod_lt _ (by omega)) hmoves h
  rw [moved_counts t now hnew hmoves] at this
  exact hne this

end Vinc.MemInc
