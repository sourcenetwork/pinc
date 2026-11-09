import Vinc.MembershipModelNode
import Vinc.MembershipIncThm

/-!
# Membership, system level: incarnations across restarts, and the address tag

The system-level counterparts of the incarnation scenarios (properties 1 and 10: crash and restart, MOVE_TAG), over
every schedule of restarts, records, observed words and address moves of one node, whatever the wall clock does.

* `lineage_word_mono` (property 1, crash and restart): along any sequence of restarts (`Vinc.MemInc.start` on the
  store the previous life left), records and observed words of a node whose host keeps a persistent counter, the
  announced word never goes down, and every restart is strictly above everything the old life announced
  (`restart_word_gt`), whatever wall clock or floor the restart is given. The invariant `MemInc.Inv` (epoch within 48
  bits, the store holds the epoch in use) is kept along the whole sequence (`LStep.inv`).
* `lineage_witness`: the hypotheses are satisfiable (a concrete lineage of two restarts with a wall clock that went back).
* `start_inc`, `restart_node_word_gt`: `N.start`, the node's own start, issues exactly the `MemInc.start` incarnation, so the
  theorems above are about the node's announced word.
* `addressChanged_tag`, `handover_counts_once`, `handover_changes_tag` (property 10, MOVE_TAG): `N.addressChanged` is
  `Tag.moved`; several changes at one instant count once; a handover at a new instant advances the counter by one
  modulo 256 and, once the settle is over, changes the tag whenever the host's `address_hash` tells counters apart.

Not covered here (see the report): completeness within 145 s, accuracy and convergence over a whole network, the
primary-hub hysteresis and PULSE suppression over schedules.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

theorem trace_inc (n : N) (t : Tr) : (n.trace t).inc = n.inc := by
  unfold N.trace; split <;> (try split) <;> rfl

/-- The node's start issues the incarnation of `MemInc.start` on the host's store. -/
theorem start_inc {e : Env} {me : Nat} {isHub : Bool} {hubs : List Nat} {tr : Bool} {now wall floor : Nat} {n : N}
    (h : N.start e me isHub hubs tr now wall floor = .ok n) :
    ∃ l', Vinc.MemInc.start e.loc wall floor = .ok (n.inc, l') := by
  unfold N.start at h
  generalize hs : Vinc.MemInc.start e.loc wall floor = r at h
  rcases r with er | ⟨inc, loc⟩
  · exfalso
    cases er <;> (dsimp only at h; repeat' split at h) <;> cases h
  · refine ⟨loc, ?_⟩
    dsimp only at h
    repeat' split at h
    all_goals first | (cases h; done) | (cases h; simp [trace_inc]; done)

/-- A restart of the node on a persistent counter is strictly above every word of the old life. -/
theorem restart_node_word_gt {e : Env} {me : Nat} {isHub : Bool} {hubs : List Nat} {tr : Bool} {now wall floor : Nat}
    {n : N} {i : Inc} (hp : e.loc.persistent = true) (hI : Inv e.loc i)
    (h : N.start e me isHub hubs tr now wall floor = .ok n) : i.word < n.inc.word := by
  obtain ⟨l', hs⟩ := start_inc h
  exact restart_word_gt hp hI hs

/-! ## Lineages -/

/-- One step of a node's incarnation: a restart (with any wall clock and floor), a record, an observed word. -/
inductive LStep : Local × Inc → Local × Inc → Prop where
  | restart {l i l' j : _} (w f : Nat) : Vinc.MemInc.start l w f = .ok (j, l') → LStep (l, i) (l', j)
  | record {l i l' j : _} (w : Nat) : nextRecord l i = .ok (w, j, l') → LStep (l, i) (l', j)
  | observe {l i l' j : _} (seen : Nat) (b : Bool) : observe l i seen = .ok (b, j, l') → LStep (l, i) (l', j)

theorem LStep.persistent {a b : Local × Inc} (h : LStep a b) : b.1.persistent = a.1.persistent := by
  cases h with
  | restart w f hs => exact (start_ok hs).2.2.2.1
  | record w hs =>
    rename_i l i l' j
    by_cases h1 : i.seq + 1 ≤ 65535
    · rw [nextRecord_small h1] at hs
      injection hs with hs; injection hs with _ hs; injection hs with _ h3; subst h3; rfl
    · rw [nextRecord_full h1] at hs
      cases hq : sealEpoch l (MemInc.satAdd i.epoch 1) with
      | error e => rw [hq] at hs; cases hs
      | ok l2 =>
        rw [hq] at hs
        injection hs with hs; injection hs with _ hs; injection hs with _ h3; subst h3
        exact (sealEpoch_ok hq).2.1
  | observe seen b hs =>
    rename_i l i l' j
    by_cases h1 : seen ≤ i.word
    · rw [observe_noop h1] at hs
      injection hs with hs; injection hs with _ hs; injection hs with _ h3; subst h3; rfl
    · rw [observe_move h1] at hs
      cases hq : sealEpoch l (MemInc.satAdd (max (seen / 65536) i.epoch) 1) with
      | error e => rw [hq] at hs; cases hs
      | ok l2 =>
        rw [hq] at hs
        injection hs with hs; injection hs with _ hs; injection hs with _ h3; subst h3
        exact (sealEpoch_ok hq).2.1

theorem LStep.inv {a b : Local × Inc} (h : LStep a b) (hI : Inv a.1 a.2) : Inv b.1 b.2 := by
  cases h with
  | restart w f hs => exact start_inv hs
  | record w hs => exact nextRecord_inv hI hs
  | observe seen bb hs => exact observe_inv hI bb hs

/-- Along every step of a persistent node the announced word does not go down. -/
theorem LStep.word_mono {a b : Local × Inc} (h : LStep a b) (hI : Inv a.1 a.2) (hp : a.1.persistent = true) :
    a.2.word ≤ b.2.word := by
  obtain ⟨hs, he, hseal⟩ := hI
  cases h with
  | restart w f hs' => exact Nat.le_of_lt (restart_word_gt hp ⟨hs, he, hseal⟩ hs')
  | record w hs' =>
    obtain ⟨h1, h2⟩ := nextRecord_word_lt hs hs'
    exact Nat.le_of_lt (Nat.lt_of_lt_of_eq h1 h2)
  | observe seen bb hs' =>
    by_cases hb : bb = true
    · subst hb; exact Nat.le_of_lt (observe_word_lt hs hs').2
    · have hf : bb = false := by simpa using hb
      subst hf
      obtain ⟨_, rfl, _⟩ := observe_false hs'
      exact Nat.le_refl _

/-- A schedule of any number of steps. -/
inductive LRun : Local × Inc → Local × Inc → Prop where
  | refl (a) : LRun a a
  | step {a b c} : LStep a b → LRun b c → LRun a c

/-- Property 1 over every schedule: with a persistent counter the word never goes down along any sequence of restarts
(with any wall clock, floor and failures that return no state), records and observed words, and the invariant holds. -/
theorem lineage_word_mono {a b : Local × Inc} (h : LRun a b) (hI : Inv a.1 a.2) (hp : a.1.persistent = true) :
    Inv b.1 b.2 ∧ a.2.word ≤ b.2.word := by
  induction h with
  | refl a => exact ⟨hI, Nat.le_refl _⟩
  | @step a b c hs _ ih =>
    have hI' := hs.inv hI
    have hp' : b.1.persistent = true := by rw [hs.persistent]; exact hp
    obtain ⟨h1, h2⟩ := ih hI' hp'
    exact ⟨h1, Nat.le_trans (hs.word_mono hI hp) h2⟩

/-- The hypotheses are satisfiable: a persistent store, a restart whose wall clock went back, and a record. -/
theorem lineage_witness :
    ∃ b, LRun (⟨true, some 5, false, false⟩, ⟨5, 0⟩) b ∧ b.2.word > (⟨5, 0⟩ : Inc).word := by
  refine ⟨(⟨true, some 6, false, false⟩, ⟨6, 1⟩), ?_, by decide⟩
  refine LRun.step (b := (⟨true, some 6, false, false⟩, ⟨6, 0⟩)) (LStep.restart 0 0 (by rfl)) ?_
  exact LRun.step (LStep.record (l' := ⟨true, some 6, false, false⟩) (j := ⟨6, 1⟩) 393217 (by rfl)) (LRun.refl _)

/-! ## MOVE_TAG -/

theorem addressChanged_tag (n : N) (now : Nat) : (n.addressChanged now).tag = n.tag.moved now := rfl

/-- Several changes at one instant count once. -/
theorem handover_counts_once (n : N) (now : Nat) :
    ((n.addressChanged now).addressChanged now).tag = (n.addressChanged now).tag := by
  simp [N.addressChanged, moved_twice]

/-- A handover at a new instant advances the counter by one modulo 256, and, with an injective `address_hash`, changes
the tag (once the previous tag is no longer kept). -/
theorem handover_changes_tag (n : N) (now : Nat) (hash : Nat → List Nat)
    (hinj : ∀ a b, a < 256 → b < 256 → hash a = hash b → a = b)
    (hmoves : n.tag.moves < 256) (hnew : n.tag.movedAt ≠ some now) (hne : (n.tag.moves + 1) % 256 ≠ n.tag.moves) :
    ((n.addressChanged now).tag.moves = (n.tag.moves + 1) % 256) ∧
      hash (n.addressChanged now).tag.moves ≠ hash n.tag.moves :=
  ⟨moved_counts n.tag now hnew hmoves, tag_changes n.tag now hash 0 hinj hmoves hnew hne⟩

end Vinc.Membership
