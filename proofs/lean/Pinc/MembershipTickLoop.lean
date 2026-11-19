import Pinc.MembershipTickHeld

/-!
# Hub tick, part 3: lease expiry over the whole tick (property 2, hub side)

`hub_tick` visits every roster key (the fold `forKeys`), then every held member. With the step lemmas of
`MembershipTick.lean`, `MembershipTickSusp.lean` and `MembershipTickHeld.lean`:

* `hubTick_fresh` (headline, property 2): after `N.hubTick`, every roster entry has been renewed within `LEASE`:
  the lease is never kept past its expiry. Entries kept were fresh after the refresh from transport evidence,
  `carrier_watch` only raises the renewal time, and a returning carrier renews to `now`. Hubs are no exception: the
  expiry test does not look at who the member is.
* `hubTick_expires`: a roster entry whose lease, after the refresh from transport evidence, is older than `LEASE`
  when the tick starts (and which the hub does not also hold as a dropped member) is gone when the tick ends, and
  the subscriptions are released (`Bc.release`) in the call's output. The `Down` delta is the one `push_delta`
  builds from the lease (`htStep_expired`, `MembershipTick.lean`).
* `loop1_spec`: the first loop never adds a roster entry (`hubTick_susp` keeps `SuspOk`).
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

theorem forKeys_cons (ks : List Nat) (k : Nat) (f : Nat → N → N) (n : N) : forKeys (k :: ks) f n = forKeys ks f (f k n) := rfl
theorem forKeys_nil (f : Nat → N → N) (n : N) : forKeys [] f n = n := rfl

theorem htPulse_snd_indep (e : Env) (n n' : N) (now m : Nat) (l0 : Lease) :
    (N.htPulse e n now m l0).2 = (N.htPulse e n' now m l0).2 := by
  unfold N.htPulse
  cases hev : e.evidence m with
  | none => rfl
  | some ev => simp only []; split <;> simp_all

/-- The loop over the roster keys. -/
theorem loop1_obg (e : Env) (now : Nat) (L : List Nat) (n : N) : CW2 n (forKeys L (N.htStep e now) n) := by
  induction L generalizing n with
  | nil => exact CW2.refl n
  | cons k r ih => rw [forKeys_cons]; exact (htStep_cw2 e now k n).trans (ih _)

/-- A key the loop has not reached keeps its entry; one with no entry never gets one. -/
theorem loop1_none (e : Env) (now : Nat) (L : List Nat) (j : Nat) (n : N) (h : n.roster.get? j = none) :
    (forKeys L (N.htStep e now) n).roster.get? j = none ∧ (forKeys L (N.htStep e now) n).downed.get? j = n.downed.get? j := by
  induction L generalizing n with
  | nil => exact ⟨h, rfl⟩
  | cons k r ih =>
    rw [forKeys_cons]
    by_cases hk : j = k
    · subst hk
      have : N.htStep e now j n = n := by unfold N.htStep; rw [h]
      rw [this]; exact ih n h
    · have h1 : (N.htStep e now k n).roster.get? j = none := ((htStep_rm e now k n).1 j hk).trans h
      obtain ⟨a, b⟩ := ih _ h1
      exact ⟨a, b.trans (htStep_rd e now k n j hk)⟩

theorem loop1_spec (e : Env) (now : Nat) (L : List Nat) (n : N) :
    (∀ j, j ∉ L → (forKeys L (N.htStep e now) n).roster.get? j = n.roster.get? j) ∧
    (∀ j, j ∈ L → (forKeys L (N.htStep e now) n).roster.get? j = none ∨
      ∃ l, (forKeys L (N.htStep e now) n).roster.get? j = some l ∧ now - l.renewed ≤ LEASE) ∧
    (∀ j, j ∈ L → ∀ l0, n.roster.get? j = some l0 → LEASE < now - (N.htPulse e n now j l0).2.renewed →
      (forKeys L (N.htStep e now) n).roster.get? j = none ∧ Bc.release j ∈ (forKeys L (N.htStep e now) n).outBc ∧
      ((n.downed.get? j = none) → (forKeys L (N.htStep e now) n).downed.get? j = none)) := by
  induction L generalizing n with
  | nil => exact ⟨fun _ _ => rfl, fun j hj => absurd hj (by simp), fun j hj => absurd hj (by simp)⟩
  | cons k r ih =>
    rw [forKeys_cons]
    obtain ⟨i1, i2, i3⟩ := ih (N.htStep e now k n)
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hjk : j ≠ k := fun h => hj (h ▸ List.mem_cons_self)
      have hjr : j ∉ r := fun h => hj (List.mem_cons_of_mem _ h)
      rw [i1 j hjr]; exact (htStep_rm e now k n).1 j hjk
    · intro j hj
      by_cases hjr : j ∈ r
      · exact i2 j hjr
      · have hjk : j = k := by
          rcases List.mem_cons.mp hj with h | h
          · exact h
          · exact absurd h hjr
        subst hjk
        rw [i1 j hjr]
        exact htStep_fresh e now j n
    · intro j hj l0 hl hx
      by_cases hjk : j = k
      · subst hjk
        obtain ⟨s1, s2, s3⟩ := htStep_expired e now j n l0 hl hx
        obtain ⟨hn, hd⟩ := loop1_none e now r j _ s1
        refine ⟨hn, ?_, ?_⟩
        · obtain ⟨-, ⟨ex, hex⟩⟩ := loop1_obg e now r (N.htStep e now j n)
          rw [hex, s2]; simp
        · intro hd0
          rw [hd]
          rw [s3]
          have : (N.htExpire e (N.htPulse e n now j l0).1 now j (N.htPulse e n now j l0).2).downed = n.downed := by
            rw [(htExpire_spec e _ now j _).2.2]
            unfold N.htPulse
            cases hev : e.evidence j with
            | none => rfl
            | some ev => simp only []; split <;> simp
          rw [this]; exact hd0
      · have hjr : j ∈ r := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd h hjk
          · exact h
        have hl' : (N.htStep e now k n).roster.get? j = some l0 := by rw [(htStep_rm e now k n).1 j hjk]; exact hl
        have hx' : LEASE < now - (N.htPulse e (N.htStep e now k n) now j l0).2.renewed := by
          rw [← htPulse_snd_indep e n _]; exact hx
        obtain ⟨a, b, c⟩ := i3 j hjr l0 hl' hx'
        exact ⟨a, b, fun hd0 => c (by rw [htStep_rd e now k n j hjk]; exact hd0)⟩


/-! ## The second loop and the whole tick -/

theorem AMap.get?_insert_cases {α : Type} (m : AMap α) (k j : Nat) (v x : α) (h : (m.insert k v).get? j = some x) :
    m.get? j = some x ∨ (j = k ∧ x = v) := by
  by_cases hj : j = k
  · subst hj; rw [AMap.get?_insert_self] at h; injection h with h; exact Or.inr ⟨rfl, h.symm⟩
  · rw [AMap.get?_insert_ne _ _ _ _ hj] at h; exact Or.inl h

@[simp] theorem pushDelta_roster' (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : (N.pushDelta e n now m rc a).roster = n.roster :=
  (pushDelta_ht e n now m rc a).1
@[simp] theorem pushDelta_downed' (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : (N.pushDelta e n now m rc a).downed = n.downed :=
  (pushDelta_ht e n now m rc a).2.2.1

theorem carrierReturn_cases (e : Env) (n : N) (now m : Nat) :
    (∀ j, j ≠ m → (N.carrierReturn e n now m).roster.get? j = n.roster.get? j) ∧
    (∀ l', (N.carrierReturn e n now m).roster.get? m = some l' → n.roster.get? m = some l' ∨ l'.renewed = now) ∧
    RD m n (N.carrierReturn e n now m) := by
  have key : ∀ x : N, x.roster = n.roster → RD m n x → (∀ j, j ≠ m → x.roster.get? j = n.roster.get? j) ∧
      (∀ l', x.roster.get? m = some l' → n.roster.get? m = some l' ∨ l'.renewed = now) ∧ RD m n x := fun x h1 h2 =>
    ⟨fun j _ => by rw [h1], fun l' h => Or.inl (by rw [h1] at h; exact h), h2⟩
  have erd : RD m n { n with downed := n.downed.erase m } := fun j hj => AMap.get?_erase_ne _ _ _ hj
  unfold N.carrierReturn
  split
  · exact key _ (by simp) (RD.of_eq (by simp))
  · rename_i l t0 hd
    dsimp only
    split
    · exact key _ rfl erd
    · split
      · exact key _ (by simp) (by intro j hj; simp [AMap.get?_erase_ne _ _ _ hj])
      · refine ⟨fun j hj => ?_, fun l' h => ?_, fun j hj => ?_⟩
        · simp
          exact AMap.get?_insert_ne _ _ _ _ hj
        · simp at h
          rcases AMap.get?_insert_cases _ _ _ _ _ h with h | ⟨-, rfl⟩
          · exact Or.inl h
          · exact Or.inr rfl
        · simp [AMap.get?_erase_ne _ _ _ hj]

theorem htDown_cases (e : Env) (now m : Nat) (n : N) :
    (∀ j, j ≠ m → (N.htDown e now m n).roster.get? j = n.roster.get? j) ∧
    (∀ l', (N.htDown e now m n).roster.get? m = some l' → n.roster.get? m = some l' ∨ l'.renewed = now) ∧
    RD m n (N.htDown e now m n) := by
  unfold N.htDown
  cases hd : n.downed.get? m with
  | none => exact ⟨fun _ _ => rfl, fun l' h => Or.inl h, RD.refl _ _⟩
  | some p =>
    obtain ⟨l, t0⟩ := p
    simp only []
    split
    · exact ⟨fun j _ => rfl, fun l' h => Or.inl h, fun j hj => by simp [AMap.get?_erase_ne _ _ _ hj]⟩
    · split
      · exact carrierReturn_cases e n now m
      · exact ⟨fun _ _ => rfl, fun l' h => Or.inl h, RD.refl _ _⟩

theorem loop2_cw2 (e : Env) (now : Nat) (L : List Nat) (n : N) : CW2 n (forKeys L (N.htDown e now) n) := by
  induction L generalizing n with
  | nil => exact CW2.refl n
  | cons k r ih => rw [forKeys_cons]; exact (htDown_cw2 e now k n).trans (ih _)

theorem loop2_fresh (e : Env) (now : Nat) (L : List Nat) (n : N) (h : ∀ j l, n.roster.get? j = some l → now - l.renewed ≤ LEASE) :
    ∀ j l, (forKeys L (N.htDown e now) n).roster.get? j = some l → now - l.renewed ≤ LEASE := by
  induction L generalizing n with
  | nil => exact h
  | cons k r ih =>
    rw [forKeys_cons]
    apply ih
    intro j l hl
    obtain ⟨c1, c2, -⟩ := htDown_cases e now k n
    by_cases hj : j = k
    · subst hj
      rcases c2 l hl with h' | h'
      · exact h j l h'
      · omega
    · rw [c1 j hj] at hl; exact h j l hl

theorem loop2_gone (e : Env) (now m : Nat) (L : List Nat) (n : N) (h1 : n.roster.get? m = none) (h2 : n.downed.get? m = none) :
    (forKeys L (N.htDown e now) n).roster.get? m = none ∧ (forKeys L (N.htDown e now) n).downed.get? m = none := by
  induction L generalizing n with
  | nil => exact ⟨h1, h2⟩
  | cons k r ih =>
    rw [forKeys_cons]
    by_cases hk : m = k
    · subst hk
      have : N.htDown e now m n = n := by unfold N.htDown; rw [h2]
      rw [this]; exact ih n h1 h2
    · obtain ⟨c1, -, c3⟩ := htDown_cases e now k n
      exact ih _ ((c1 m hk).trans h1) ((c3 m hk).trans h2)

theorem loop1_fresh (e : Env) (now : Nat) (n : N) :
    ∀ j l, (forKeys n.roster.keys (N.htStep e now) n).roster.get? j = some l → now - l.renewed ≤ LEASE := by
  intro j l hl
  obtain ⟨i1, i2, -⟩ := loop1_spec e now n.roster.keys n
  by_cases hj : j ∈ n.roster.keys
  · rcases i2 j hj with h | ⟨l', h, hle⟩
    · rw [h] at hl; cases hl
    · rw [h] at hl; injection hl with hl; subst hl; exact hle
  · rw [i1 j hj] at hl
    exact absurd ((AMap.has_keys _ _).1 (AMap.get?_has _ _ _ hl)) hj

/-- Property 2, hub side (headline): after `hub_tick`, no roster entry is older than `LEASE`. -/
theorem hubTick_fresh (e : Env) (n : N) (now : Nat) :
    ∀ j l, (N.hubTick e n now).roster.get? j = some l → now - l.renewed ≤ LEASE := by
  rw [hubTick_eq]
  exact loop2_fresh e now _ _ (loop1_fresh e now n)

/-- Property 2, hub side: an entry whose lease (after the refresh from the transport's evidence) is older than `LEASE`
when the tick starts is removed by the tick, and its subscriptions are released in the call's output. The member
must not also be in the held table (the two tables are disjoint in every reachable state). -/
theorem hubTick_expires (e : Env) (n : N) (now m : Nat) (l0 : Lease) (hl : n.roster.get? m = some l0)
    (hx : LEASE < now - (N.htPulse e n now m l0).2.renewed) (hd : n.downed.get? m = none) :
    (N.hubTick e n now).roster.get? m = none ∧ Bc.release m ∈ (N.hubTick e n now).outBc := by
  rw [hubTick_eq]
  obtain ⟨-, -, i3⟩ := loop1_spec e now n.roster.keys n
  obtain ⟨a, b, c⟩ := i3 m ((AMap.has_keys _ _).1 (AMap.get?_has _ _ _ hl)) l0 hl hx
  obtain ⟨g1, g2⟩ := loop2_gone e now m (forKeys n.roster.keys (N.htStep e now) n).downed.keys _ a (c hd)
  refine ⟨g1, ?_⟩
  obtain ⟨-, ⟨ex, hex⟩⟩ := loop2_cw2 e now (forKeys n.roster.keys (N.htStep e now) n).downed.keys (forKeys n.roster.keys (N.htStep e now) n)
  rw [hex]; simp [b]

/-- The suspicion table stays well formed through the whole tick. -/
theorem hubTick_susp (e : Env) (n : N) (now : Nat) (hs : n.SuspOk) : (N.hubTick e n now).SuspOk := by
  rw [hubTick_eq]
  exact (loop2_cw2 e now _ _).1 ((loop1_obg e now _ n).1 hs)

end Pinc.Membership
