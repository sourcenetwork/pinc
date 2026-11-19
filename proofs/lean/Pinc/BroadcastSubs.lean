import Pinc.Axioms

/-!
# Subscriptions on a hub: hold, restore, release, and the SUBS frame

The unbounded counterpart of `proofs/tla/BroadcastSubs.tla` (`subs.rs`, `gap.rs` `on_sub`, `on_unsub`) and of
`build_list`. A table is a list of entries `(topic, member, live)`; the invariant `Ok` says an entry is the only one
of its `(topic, member)` and no topic has more than `max` entries. Facts, for every table: a push goes to exactly
the live entries (`pushed_iff`); a hold keeps every entry and makes none live (`hold_keeps`); a restore tells the
member each topic it had held, once, and none else (`told_iff`, `told_nodup`), and leaves none held
(`restore_none_held`); a release forgets the member (`release_forgets`) and touches no other (`release_others`);
every operation keeps `Ok` (`sub_ok`, `unsub_ok`, `hold_ok`, `restore_ok`, `release_ok`). The SUBS frame is the
sorted, duplicate-free union of the candidates cut at `max` (`buildSubs_sorted`, `buildSubs_len`,
`buildSubs_mem`), and exactly the union when it has at most `max` nodes (`buildSubs_exact`).
-/

namespace Pinc.BroadcastSubs

/-- An entry of the subscriber table: topic, member, live (otherwise held). -/
structure E where
  t : Nat
  m : Nat
  live : Bool
  deriving DecidableEq, Repr

/-- The entries of one topic. -/
def count (tb : List E) (t : Nat) : Nat := (tb.filter (fun e => e.t == t)).length

/-- The entry of `(t, m)` is present. -/
def Has (tb : List E) (t m : Nat) : Prop := ∃ e ∈ tb, e.t = t ∧ e.m = m

/-- The invariant: one entry per key, at most `max` entries per topic. -/
structure Ok (max : Nat) (tb : List E) : Prop where
  uniq : (tb.map fun e => (e.t, e.m)).Nodup
  cap : ∀ t, count tb t ≤ max

/-- `on_sub`: record the subscriber live; an unknown member only if the topic has room. -/
def sub (max : Nat) (tb : List E) (t m : Nat) : List E :=
  if tb.any (fun e => e.t == t && e.m == m) then tb.map (fun e => if e.t = t ∧ e.m = m then {e with live := true} else e)
  else if count tb t < max then tb ++ [⟨t, m, true⟩] else tb

/-- `on_unsub`. -/
def unsub (tb : List E) (t m : Nat) : List E := tb.filter (fun e => !(e.t == t && e.m == m))

/-- `hold`: the live entries of the member become held. -/
def hold (tb : List E) (m : Nat) : List E := tb.map fun e => if e.m = m then {e with live := false} else e

/-- `restore`: the held entries of the member become live. -/
def restore (tb : List E) (m : Nat) : List E := tb.map fun e => if e.m = m then {e with live := true} else e

/-- The topics `restore` sends a RESTORED frame for: those the member holds. -/
def told (tb : List E) (m : Nat) : List Nat := (tb.filter fun e => e.m == m && !e.live).map (·.t)

/-- `release`: forget the member. -/
def release (tb : List E) (m : Nat) : List E := tb.filter (fun e => e.m != m)

/-- The members a push on `t` goes to. -/
def pushed (tb : List E) (t : Nat) : List Nat := (tb.filter fun e => e.t == t && e.live).map (·.m)

theorem count_map_key (tb : List E) (f : E → E) (hf : ∀ e, (f e).t = e.t) (t : Nat) :
    count (tb.map f) t = count tb t := by
  induction tb with
  | nil => simp [count]
  | cons a l ih => simp [count, List.filter_cons, hf] at ih ⊢; split <;> simp_all

theorem map_key_same (tb : List E) (f : E → E) (hf : ∀ e, (f e).t = e.t) (hm : ∀ e, (f e).m = e.m) :
    (tb.map f).map (fun e => (e.t, e.m)) = tb.map (fun e => (e.t, e.m)) := by
  simp [List.map_map, Function.comp_def, hf, hm]

theorem ok_map {max : Nat} {tb : List E} (h : Ok max tb) (f : E → E) (hf : ∀ e, (f e).t = e.t)
    (hm : ∀ e, (f e).m = e.m) : Ok max (tb.map f) :=
  ⟨by rw [map_key_same tb f hf hm]; exact h.uniq, fun t => by rw [count_map_key tb f hf]; exact h.cap t⟩

theorem hold_ok {max : Nat} {tb : List E} (h : Ok max tb) (m : Nat) : Ok max (hold tb m) :=
  ok_map h (fun e => if e.m = m then {e with live := false} else e) (fun e => by split <;> rfl)
    (fun e => by split <;> rfl)

theorem restore_ok {max : Nat} {tb : List E} (h : Ok max tb) (m : Nat) : Ok max (restore tb m) :=
  ok_map h (fun e => if e.m = m then {e with live := true} else e) (fun e => by split <;> rfl)
    (fun e => by split <;> rfl)

theorem ok_sublist {max : Nat} {tb tb' : List E} (h : Ok max tb) (s : tb'.Sublist tb) : Ok max tb' :=
  ⟨h.uniq.sublist (s.map _), fun t => Nat.le_trans (s.filter (fun e => e.t == t)).length_le (h.cap t)⟩

theorem release_ok {max : Nat} {tb : List E} (h : Ok max tb) (m : Nat) : Ok max (release tb m) :=
  ok_sublist h List.filter_sublist

theorem unsub_ok {max : Nat} {tb : List E} (h : Ok max tb) (t m : Nat) : Ok max (unsub tb t m) :=
  ok_sublist h List.filter_sublist

theorem sub_ok {max : Nat} {tb : List E} (h : Ok max tb) (t m : Nat) : Ok max (sub max tb t m) := by
  unfold sub
  split
  · refine ok_map h _ (fun e => ?_) (fun e => ?_) <;> split <;> simp_all
  · split
    · rename_i hn hc
      refine ⟨?_, fun t' => ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h.uniq, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        intro hxy
        simp only [List.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        simp only [Bool.not_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true, not_exists, not_and] at hn
        exact hn e he (by simpa using (Prod.mk.inj hxy).1) (by simpa using (Prod.mk.inj hxy).2)
      · by_cases ht : t' = t
        · subst ht; simp [count, List.filter_append] at hc ⊢; omega
        · have := h.cap t'
          simp [count, List.filter_append, Ne.symm ht] at this ⊢
          omega
    · exact h

/-- A push reaches exactly the members whose entry for the topic is live. -/
theorem pushed_iff {max : Nat} {tb : List E} (_ : Ok max tb) (t m : Nat) :
    m ∈ pushed tb t ↔ ∃ e ∈ tb, e.t = t ∧ e.m = m ∧ e.live = true := by
  simp [pushed, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨e, ⟨he, h1, h2⟩, rfl⟩; exact ⟨e, he, h1, rfl, h2⟩
  · rintro ⟨e, he, h1, rfl, h2⟩; exact ⟨e, ⟨he, h1, h2⟩, rfl⟩

/-- A hold keeps the entries of the member (held) and leaves every other entry as it was. -/
theorem hold_keeps (tb : List E) (m : Nat) (e : E) :
    e ∈ hold tb m ↔ ∃ e0 ∈ tb, e = (if e0.m = m then {e0 with live := false} else e0) := by
  simp [hold, List.mem_map]
  constructor <;> rintro ⟨x, hx, h⟩ <;> exact ⟨x, hx, h.symm ▸ rfl⟩ <;> exact h.symm

theorem hold_none_live (tb : List E) (m : Nat) : ∀ e ∈ hold tb m, e.m = m → e.live = false := by
  intro e he hm
  simp only [hold, List.mem_map] at he
  obtain ⟨x, _, rfl⟩ := he
  split <;> simp_all

theorem hold_others (tb : List E) (m : Nat) : ∀ e ∈ tb, e.m ≠ m → e ∈ hold tb m := by
  intro e he hm
  simp only [hold, List.mem_map]
  exact ⟨e, he, by simp [hm]⟩

theorem hold_members (tb : List E) (m : Nat) (t : Nat) :
    (∃ e ∈ hold tb m, e.t = t ∧ e.m = m) ↔ ∃ e ∈ tb, e.t = t ∧ e.m = m := by
  simp only [hold, List.mem_map]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, h1, h2⟩; exact ⟨x, hx, by split at h1 <;> simp_all, by split at h2 <;> simp_all⟩
  · rintro ⟨e, he, h1, h2⟩; exact ⟨_, ⟨e, he, rfl⟩, by simp [h2, h1], by simp [h2]⟩

/-- A restore tells the member exactly the topics it holds. -/
theorem told_iff (tb : List E) (m t : Nat) : t ∈ told tb m ↔ ∃ e ∈ tb, e.t = t ∧ e.m = m ∧ e.live = false := by
  simp [told, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨e, ⟨he, h1, h2⟩, rfl⟩; exact ⟨e, he, rfl, h1, h2⟩
  · rintro ⟨e, he, rfl, h1, h2⟩; exact ⟨e, ⟨he, h1, h2⟩, rfl⟩

/-- One frame per topic: no topic is told twice. -/
theorem told_nodup {max : Nat} {tb : List E} (h : Ok max tb) (m : Nat) : (told tb m).Nodup := by
  have hu := h.uniq
  unfold told
  have h1 : ((tb.filter fun e => e.m == m && !e.live).map fun e => (e.t, e.m)).Nodup :=
    hu.sublist (List.filter_sublist.map _)
  have h2 : (tb.filter fun e => e.m == m && !e.live).map (fun e => (e.t, e.m)) =
      ((tb.filter fun e => e.m == m && !e.live).map (·.t)).map (fun t => (t, m)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at he
    simp [Function.comp, he.2.1]
  rw [h2] at h1
  exact List.Pairwise.of_map (fun t => (t, m)) (fun a b hab e => hab (by rw [e])) h1

theorem restore_none_held (tb : List E) (m : Nat) : ∀ e ∈ restore tb m, e.m = m → e.live = true := by
  intro e he hm
  simp only [restore, List.mem_map] at he
  obtain ⟨x, _, rfl⟩ := he
  split <;> simp_all

theorem release_forgets (tb : List E) (m : Nat) : ∀ e ∈ release tb m, e.m ≠ m := by
  intro e he; simp [release, List.mem_filter] at he; exact he.2

theorem release_others (tb : List E) (m : Nat) : ∀ e ∈ tb, e.m ≠ m → e ∈ release tb m := by
  intro e he hm; simp [release, List.mem_filter]; exact ⟨he, hm⟩

/-! ## The SUBS frame -/

/-- Insert into a strictly sorted list (the binary search insert of `build_list`). -/
def insSorted (n : Nat) : List Nat → List Nat
  | [] => [n]
  | x :: xs => if n < x then n :: x :: xs else if n = x then x :: xs else x :: insSorted n xs

/-- `build_list`: the candidates in order, each added unless present or the list is full. -/
def buildSubs (max : Nat) (cands : List Nat) : List Nat :=
  cands.foldl (fun acc n => if acc.contains n || max ≤ acc.length then acc else insSorted n acc) []

theorem mem_insSorted (n x : Nat) : ∀ l : List Nat, x ∈ insSorted n l ↔ x = n ∨ x ∈ l := by
  intro l
  induction l with
  | nil => simp [insSorted]
  | cons a l ih =>
    unfold insSorted
    split
    · simp
    · split
      · rename_i h1 h2; subst h2; simp
      · simp only [ih, List.mem_cons]
        constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem insSorted_sorted (n : Nat) : ∀ l : List Nat, l.Pairwise (· < ·) → (insSorted n l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; simp [insSorted]
  | cons a l ih =>
    intro h
    rw [List.pairwise_cons] at h
    unfold insSorted
    split
    · rename_i hn
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, h⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hn
      · exact Nat.lt_trans hn (h.1 y hy)
    · split
      · rw [List.pairwise_cons]; exact h
      · rename_i h1 h2
        rw [List.pairwise_cons]
        refine ⟨?_, ih h.2⟩
        intro y hy
        rw [mem_insSorted] at hy
        rcases hy with rfl | hy
        · omega
        · exact h.1 y hy

theorem insSorted_len (n : Nat) : ∀ l : List Nat, n ∉ l → (insSorted n l).length = l.length + 1 := by
  intro l
  induction l with
  | nil => intro _; simp [insSorted]
  | cons a l ih =>
    intro h
    simp only [List.mem_cons, not_or] at h
    unfold insSorted
    split
    · simp
    · split
      · exact absurd ‹n = a› h.1
      · simp [ih h.2]

/-- The state of the fold: sorted, within `max`, drawn from what was seen, and complete unless full. -/
structure Fold (max : Nat) (seen acc : List Nat) : Prop where
  sorted : acc.Pairwise (· < ·)
  len : acc.length ≤ max
  sub : ∀ x ∈ acc, x ∈ seen
  full : ∀ x ∈ seen, x ∈ acc ∨ acc.length = max

theorem fold_step {max : Nat} {seen acc : List Nat} (h : Fold max seen acc) (n : Nat) :
    Fold max (seen ++ [n]) (if acc.contains n || decide (max ≤ acc.length) then acc else insSorted n acc) := by
  by_cases hc : acc.contains n = true
  · simp only [hc, Bool.true_or, ite_true]
    refine ⟨h.sorted, h.len, fun x hx => List.mem_append_left _ (h.sub x hx), ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h.full x hx
    · simp at hx; subst hx; exact Or.inl (by simpa using hc)
  · have hn : n ∉ acc := by simpa using hc
    by_cases hf : max ≤ acc.length
    · simp only [hc, hf, Bool.false_or, decide_true, ite_true]
      refine ⟨h.sorted, h.len, fun x hx => List.mem_append_left _ (h.sub x hx), ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h.full x hx
      · exact Or.inr (by have := h.len; omega)
    · have hf' : acc.length < max := by omega
      have hd : decide (max ≤ acc.length) = false := by simpa using hf
      have hc' : acc.contains n = false := by simpa using hc
      rw [hc', hd]
      simp only [Bool.or_false, Bool.false_eq_true, ite_false]
      refine ⟨insSorted_sorted n acc h.sorted, by rw [insSorted_len n acc hn]; omega, ?_, ?_⟩
      · intro x hx; rw [mem_insSorted] at hx
        rcases hx with rfl | hx
        · exact List.mem_append_right _ (by simp)
        · exact List.mem_append_left _ (h.sub x hx)
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · rcases h.full x hx with h1 | h1
          · exact Or.inl ((mem_insSorted n x acc).2 (Or.inr h1))
          · exact absurd h1 (by omega)
        · simp at hx; subst hx; exact Or.inl ((mem_insSorted _ _ _).2 (Or.inl rfl))

theorem fold_run (max : Nat) :
    ∀ (cands seen acc : List Nat), Fold max seen acc →
      Fold max (seen ++ cands)
        (cands.foldl (fun acc n => if acc.contains n || decide (max ≤ acc.length) then acc else insSorted n acc) acc) := by
  intro cands
  induction cands with
  | nil => intro seen acc h; simpa using h
  | cons c cs ih =>
    intro seen acc h
    have := ih (seen ++ [c]) _ (fold_step h c)
    simpa [List.foldl_cons, List.append_assoc] using this

theorem buildSubs_fold (max : Nat) (cands : List Nat) : Fold max cands (buildSubs max cands) := by
  have := fold_run max cands [] [] ⟨by simp, by simp, by simp, by simp⟩
  simpa [buildSubs] using this

theorem buildSubs_sorted (max : Nat) (cands : List Nat) : (buildSubs max cands).Pairwise (· < ·) :=
  (buildSubs_fold max cands).sorted

theorem buildSubs_len (max : Nat) (cands : List Nat) : (buildSubs max cands).length ≤ max :=
  (buildSubs_fold max cands).len

theorem buildSubs_mem (max : Nat) (cands : List Nat) : ∀ x ∈ buildSubs max cands, x ∈ cands :=
  (buildSubs_fold max cands).sub

/-- With at most `max` distinct candidates (no duplicate-free sublist of the candidates is longer than `max`) the
frame is exactly their union. -/
theorem buildSubs_exact (max : Nat) (cands : List Nat)
    (h : ∀ l : List Nat, l.Nodup → (∀ y ∈ l, y ∈ cands) → l.length ≤ max) :
    ∀ x, x ∈ buildSubs max cands ↔ x ∈ cands := by
  intro x
  refine ⟨fun hx => buildSubs_mem max cands x hx, fun hx => ?_⟩
  have F := buildSubs_fold max cands
  rcases F.full x hx with h1 | h1
  · exact h1
  · refine Classical.byContradiction fun hx' => ?_
    have hnd : (x :: buildSubs max cands).Nodup := by
      refine List.nodup_cons.2 ⟨hx', ?_⟩
      exact F.sorted.imp (fun h => Nat.ne_of_lt h)
    have := h _ hnd (fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact F.sub y hy)
    simp at this
    omega

#audit_axioms Pinc.BroadcastSubs.sub_ok
#audit_axioms Pinc.BroadcastSubs.hold_ok
#audit_axioms Pinc.BroadcastSubs.restore_ok
#audit_axioms Pinc.BroadcastSubs.release_ok
#audit_axioms Pinc.BroadcastSubs.pushed_iff
#audit_axioms Pinc.BroadcastSubs.told_iff
#audit_axioms Pinc.BroadcastSubs.told_nodup
#audit_axioms Pinc.BroadcastSubs.buildSubs_exact

end Pinc.BroadcastSubs
