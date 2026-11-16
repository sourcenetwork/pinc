import Vinc.Axioms
import Vinc.BroadcastSubs

/-!
# The subscriber list sent as changes: a change applied gives the new list

The unbounded counterpart of `delta` and `apply` in `crates/vinc-broadcast/src/subs.rs`, which
`proofs/tla/BroadcastSubsDelta.tla` takes as given (`Apply(P, a, r)`).

The story. A hub keeps a subscriber list: ids in increasing order, at most `max` of them. When the list changes from
`old` to `new`, the hub sends the change instead of the whole list: `delta old new` is the ids only `new` has (added)
and the ids only `old` has (removed). A member that holds `old` applies it with `apply`: it drops the removed ids,
inserts the added ones in order, and keeps the first `max`. What must hold: the member ends with exactly `new`
(`apply_delta`). Lists here are of numbers standing for node ids; the code orders ids the same way, byte by byte.

Versions. Every list has a version `(e, s)`: the hub's incarnation and the number of the change. A change frame names
the version it makes, `(e, s + 1)`, and a member takes it (`recvDelta`, the DELTA arm of `on_subs`) only when it holds
`(e, s)`, the version just before. What must hold: on that base the member ends with the hub's list at the new version
and holds the new version (`recv_on_base`); on any other base it applies nothing, holds no version (it waits for a
whole list) and asks for one if it held a version (`recv_off_base`); a whole list at version `v` replaces the
member's list with the hub's list at `v` and makes it hold `v`, waiting or not (`recv_full`).

One limit. `max` is the hub's limit and the member's alike: `apply_delta` needs `new.length ≤ max`. A member whose limit is
under its hub's holds a cut list, and the code (`peers_cut`) takes a change that removes an id as one on another base
(it asks for the whole list); that case is not stated here.
-/

namespace Vinc.BroadcastSubsDelta

open Vinc.BroadcastSubs (insSorted mem_insSorted insSorted_sorted)

/-- `delta` in subs.rs: the ids of `new` not in `old` (added), and the ids of `old` not in `new` (removed). The code
finds an id with a binary search of the sorted list; `contains` is the same answer. -/
def delta (old new : List Nat) : List Nat × List Nat :=
  -- added: in new and not in old; removed: in old and not in new
  (new.filter (fun x => !old.contains x), old.filter (fun x => !new.contains x))

/-- `apply` in subs.rs: drop the removed ids, insert each added id where it belongs (nothing if it is there), keep the
first `max`. -/
def apply (l add rem : List Nat) (max : Nat) : List Nat :=
  -- keep what is not removed, insert the added in order, cut at max
  (add.foldl (fun acc n => insSorted n acc) (l.filter (fun x => !rem.contains x))).take max

/-- Inserting a list of ids one by one into a sorted list keeps it sorted, and it then holds exactly what it held and
the ids inserted. -/
theorem fold_ins (add : List Nat) : ∀ acc : List Nat, acc.Pairwise (· < ·) →
    (add.foldl (fun acc n => insSorted n acc) acc).Pairwise (· < ·) ∧
    ∀ x, x ∈ add.foldl (fun acc n => insSorted n acc) acc ↔ x ∈ acc ∨ x ∈ add := by
  induction add with
  | nil => intro acc h; simp [h]
  | cons a t ih =>
    intro acc h
    -- one insertion, then the rest
    obtain ⟨hs, hm⟩ := ih (insSorted a acc) (insSorted_sorted a acc h)
    refine ⟨by simpa [List.foldl_cons] using hs, fun x => ?_⟩
    simp only [List.foldl_cons, hm, mem_insSorted, List.mem_cons]
    constructor
    · rintro ((h1 | h1) | h1) <;> simp [h1]
    · rintro (h1 | h1 | h1) <;> simp [h1]

/-- Two lists in strictly increasing order that hold the same ids are the same list. -/
theorem eq_of_sorted_mem : ∀ l1 l2 : List Nat, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ h
    cases l2 with
    | nil => rfl
    | cons b u => exact absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | cons a t ih =>
    intro l2 h1 h2 h
    cases l2 with
    | nil => exact absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
    | cons b u =>
      rw [List.pairwise_cons] at h1 h2
      -- the heads are equal: each is the least id of the same set
      have hab : a = b := by
        rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | ha
        · exact e
        rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e | hb
        · exact e.symm
        exact absurd (Nat.lt_trans (h2.1 a ha) (h1.1 b hb)) (Nat.lt_irrefl _)
      subst hab
      -- and the tails hold the same ids, since the head is in neither
      congr 1
      refine ih u h1.2 h2.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
        · exact absurd (h1.1 x hx) (by omega)
        · exact e
      · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
        · exact absurd (h2.1 x hx) (by omega)
        · exact e

/-- What `delta` sends: an id is added exactly when only the new list has it, removed exactly when only the old one
has it. -/
theorem delta_mem (old new : List Nat) (x : Nat) :
    (x ∈ (delta old new).1 ↔ x ∈ new ∧ x ∉ old) ∧ (x ∈ (delta old new).2 ↔ x ∈ old ∧ x ∉ new) := by
  simp [delta, List.mem_filter]

/-- A member holding the old list that applies the change ends with exactly the new list: for lists in strictly
increasing order, the new one at most `max` long. -/
theorem apply_delta (old new : List Nat) (max : Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·))
    (hl : new.length ≤ max) : apply old (delta old new).1 (delta old new).2 max = new := by
  unfold apply
  -- what is left of the old list after the removals: sorted, and exactly the ids both lists have
  have hb : (old.filter (fun x => !(delta old new).2.contains x)).Pairwise (· < ·) := ho.filter _
  obtain ⟨hs, hm⟩ := fold_ins (delta old new).1 _ hb
  -- after the insertions the list is sorted and holds exactly the ids of the new list
  have he : (delta old new).1.foldl (fun acc n => insSorted n acc)
      (old.filter (fun x => !(delta old new).2.contains x)) = new := by
    refine eq_of_sorted_mem _ _ hs hn (fun x => ?_)
    rw [hm]
    have d := delta_mem old new x
    simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, d.1, d.2]
    by_cases h1 : x ∈ old <;> by_cases h2 : x ∈ new <;> simp [h1, h2]
  rw [he]
  -- the new list is within max, so the cut keeps it whole
  exact List.take_of_length_le hl

/-- What a member holds of a hub's list: the list and its version, `none` while it waits for a whole list. -/
structure Member where
  peers : List Nat
  ver : Option (Nat × Nat)

/-- The DELTA arm of `on_subs` for a frame from the member's own hub: the change making version `(e, s + 1)`. On the
base `(e, s)` it is applied and the member holds the new version; otherwise nothing is applied, the member waits, and
the second component says whether it sends an ASK (it does when it held a version, so it asks once). -/
def recvDelta (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) : Member × Bool :=
  -- on its base: apply and take the new version
  if m.ver = some (e, s) then (⟨apply m.peers add rem max, some (e, s + 1)⟩, false)
  -- on another base: keep the list, drop the version, ask if a version was held
  else (⟨m.peers, none⟩, m.ver.isSome)

/-- On a matching base, a member holding the hub's list at `(e, s)` that takes the change from that list to the hub's
list at `(e, s + 1)` holds exactly the new list and the new version, and asks for nothing. -/
theorem recv_on_base (old new : List Nat) (max e s : Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·))
    (hl : new.length ≤ max) :
    recvDelta ⟨old, some (e, s)⟩ e s (delta old new).1 (delta old new).2 max = (⟨new, some (e, s + 1)⟩, false) := by
  simp [recvDelta, apply_delta old new max ho hn hl]

/-- On any other base a change is never applied: the list is unchanged, no version is held, and the member asks for
the whole list exactly when it held a version. -/
theorem recv_off_base (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) (h : m.ver ≠ some (e, s)) :
    (recvDelta m e s add rem max).1.peers = m.peers ∧ (recvDelta m e s add rem max).1.ver = none ∧
      (recvDelta m e s add rem max).2 = m.ver.isSome := by
  simp [recvDelta, h]

/-- The FULL arm of `on_subs` for a member: the whole list at version `v` replaces the member's list and version,
whatever it held, so a waiting member holds a version again. -/
def recvFull (_m : Member) (v : Nat × Nat) (list : List Nat) (max : Nat) : Member :=
  -- the list (cut at max, as the code takes at most max ids) and its version replace the member's
  ⟨list.take max, some v⟩

/-- A whole list at version `v`, the hub's list at `v` (at most `max` long), leaves the member holding exactly that
list and version `v`, whether it was waiting or held any other version: recovery from a gap. -/
theorem recv_full (m : Member) (v : Nat × Nat) (list : List Nat) (max : Nat) (hl : list.length ≤ max) :
    recvFull m v list max = ⟨list, some v⟩ := by
  simp [recvFull, List.take_of_length_le hl]

#audit_axioms Vinc.BroadcastSubsDelta.recv_full
#audit_axioms Vinc.BroadcastSubsDelta.recv_on_base
#audit_axioms Vinc.BroadcastSubsDelta.recv_off_base
#audit_axioms Vinc.BroadcastSubsDelta.delta_mem
#audit_axioms Vinc.BroadcastSubsDelta.apply_delta
#audit_axioms Vinc.BroadcastSubsDelta.eq_of_sorted_mem

end Vinc.BroadcastSubsDelta
