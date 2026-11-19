import Pinc.Axioms
import Pinc.BroadcastSubs

/-!
# The subscriber list sent as changes: a change applied gives the new list

The unbounded counterpart of `delta` and `apply` in `crates/pinc-broadcast/src/subs.rs`, which
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

Two more arms. A change at or below the version held, of the same incarnation, is a late copy: it is ignored, and the
member keeps its list and version and asks for nothing (`recv_old`). A member whose limit is under its hub's holds a
cut list (`cut`, `peers_cut` in the code): it is cut by a whole list longer than its limit, or by an applied change
that had to truncate. On a cut list a change that removes an id the member holds is not applied: the id past the cut
that would take its place is not in the change, so the member takes the off-base path and asks for the whole list
(`recv_cut`). A removal of an id the member does not hold changes nothing and is applied.

The member's primary. The source of a member's list is the hub it came from, and only that hub's changes apply
(`from`, in the TLA+ model). In the code a change from the member's primary hub, when the list came from another hub,
makes the primary the source: the member drops its version and asks it for the whole list. That rule is about which
hub a frame came from, not about a list, so it is not stated here; the model has no primary (a change from another hub
is ignored for good there).

One limit in the model. `apply_delta` needs `new.length ≤ max` for the member's own limit; with the member's limit
under its hub's the new list may be longer than `max`, and `recv_cut` is what keeps such a member right.
-/

namespace Pinc.BroadcastSubsDelta

open Pinc.BroadcastSubs (insSorted mem_insSorted insSorted_sorted)

/-- `delta` in subs.rs: the ids of `new` not in `old` (added), and the ids of `old` not in `new` (removed). The code
finds an id with a binary search of the sorted list; `contains` is the same answer. -/
def delta (old new : List Nat) : List Nat × List Nat :=
  -- added: in new and not in old; removed: in old and not in new
  (new.filter (fun x => !old.contains x), old.filter (fun x => !new.contains x))

/-- The change applied before the cut: drop the removed ids, insert each added id where it belongs (nothing if it is
there). -/
def applyAll (l add rem : List Nat) : List Nat :=
  -- keep what is not removed, insert the added in order
  add.foldl (fun acc n => insSorted n acc) (l.filter (fun x => !rem.contains x))

/-- `apply` in subs.rs: [`applyAll`] cut at the first `max` ids. -/
def apply (l add rem : List Nat) (max : Nat) : List Nat :=
  (applyAll l add rem).take max

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

/-- The change applied to the old list, before any cut, gives exactly the new list: for lists in strictly increasing
order. -/
theorem applyAll_delta (old new : List Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·)) :
    applyAll old (delta old new).1 (delta old new).2 = new := by
  unfold applyAll
  -- what is left of the old list after the removals: sorted, and exactly the ids both lists have
  have hb : (old.filter (fun x => !(delta old new).2.contains x)).Pairwise (· < ·) := ho.filter _
  obtain ⟨hs, hm⟩ := fold_ins (delta old new).1 _ hb
  -- after the insertions the list is sorted and holds exactly the ids of the new list
  refine eq_of_sorted_mem _ _ hs hn (fun x => ?_)
  rw [hm]
  have d := delta_mem old new x
  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, d.1, d.2]
  by_cases h1 : x ∈ old <;> by_cases h2 : x ∈ new <;> simp [h1, h2]

/-- A member holding the old list that applies the change ends with exactly the new list: for lists in strictly
increasing order, the new one at most `max` long. -/
theorem apply_delta (old new : List Nat) (max : Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·))
    (hl : new.length ≤ max) : apply old (delta old new).1 (delta old new).2 max = new := by
  unfold apply
  rw [applyAll_delta old new ho hn]
  -- the new list is within max, so the cut keeps it whole
  exact List.take_of_length_le hl

/-- What a member holds of a hub's list: the list, its version (`none` while it waits for a whole list), and whether the
list was cut to the member's limit. -/
structure Member where
  peers : List Nat
  ver : Option (Nat × Nat)
  cut : Bool

/-- Whether a change making version `(e, s + 1)` is not newer than the version the member holds: the same incarnation
and a number at or below the held one. -/
def isOld (m : Member) (e s : Nat) : Bool :=
  m.ver.any (fun v => decide (v.1 = e ∧ s + 1 ≤ v.2))

/-- The DELTA arm of `on_subs` for a frame from the member's own hub: the change making version `(e, s + 1)`. A change
not newer than the version held is ignored. On the base `(e, s)` it is applied (unless it removes an id the member
holds from a cut list) and the member holds the new version, cut if the change had to truncate; otherwise nothing is
applied, the member waits, and the second component says whether it sends an ASK (it does when it held a version, so it
asks once). -/
def recvDelta (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) : Member × Bool :=
  -- a late copy: nothing changes
  if isOld m e s then (m, false)
  -- on its base, and not a removal from a cut list: apply and take the new version
  else if decide (m.ver = some (e, s)) && !(m.cut && rem.any (fun r => m.peers.contains r)) then
    (⟨apply m.peers add rem max, some (e, s + 1), m.cut || decide (max < (applyAll m.peers add rem).length)⟩, false)
  -- on another base, or a removal from a cut list: keep the list, drop the version, ask if a version was held
  else (⟨m.peers, none, m.cut⟩, m.ver.isSome)

/-- On a matching base, a member holding the hub's list at `(e, s)` that takes the change from that list to the hub's
list at `(e, s + 1)` holds exactly the new list and the new version, uncut, and asks for nothing. -/
theorem recv_on_base (old new : List Nat) (max e s : Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·))
    (hl : new.length ≤ max) :
    recvDelta ⟨old, some (e, s), false⟩ e s (delta old new).1 (delta old new).2 max =
      (⟨new, some (e, s + 1), false⟩, false) := by
  have hc : ¬ max < new.length := Nat.not_lt.2 hl
  simp [recvDelta, isOld, apply_delta old new max ho hn hl, applyAll_delta old new ho hn, hc]

/-- A change at or below the version held, of the same incarnation, changes nothing and asks for nothing. -/
theorem recv_old (m : Member) (e h s : Nat) (add rem : List Nat) (max : Nat) (hv : m.ver = some (e, h))
    (hs : s + 1 ≤ h) : recvDelta m e s add rem max = (m, false) := by
  simp [recvDelta, isOld, hv, hs]

/-- On a cut list, a change on the member's base that removes an id the member holds is not applied: the list is
unchanged, no version is held, and the member asks for the whole list. -/
theorem recv_cut (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) (hv : m.ver = some (e, s)) (hc : m.cut = true)
    (r : Nat) (hr : r ∈ rem) (hp : r ∈ m.peers) :
    recvDelta m e s add rem max = (⟨m.peers, none, true⟩, true) := by
  have hno : ¬ ∀ x : Nat, x ∈ rem → ¬ x ∈ m.peers := fun h => h r hr hp
  simp [recvDelta, isOld, hv, hc, hno]

/-- On any other base a change that is not old is never applied: the list is unchanged, no version is held, and the
member asks for the whole list exactly when it held a version. -/
theorem recv_off_base (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) (hold : isOld m e s = false)
    (h : m.ver ≠ some (e, s)) :
    (recvDelta m e s add rem max).1.peers = m.peers ∧ (recvDelta m e s add rem max).1.ver = none ∧
      (recvDelta m e s add rem max).2 = m.ver.isSome := by
  simp [recvDelta, hold, h]

/-- The FULL arm of `on_subs` for a member: the whole list at version `v` replaces the member's list and version,
whatever it held, so a waiting member holds a version again; it is cut when the list is longer than the member's limit. -/
def recvFull (_m : Member) (v : Nat × Nat) (list : List Nat) (max : Nat) : Member :=
  -- the list (cut at max, as the code takes at most max ids) and its version replace the member's
  ⟨list.take max, some v, decide (max < list.length)⟩

/-- A whole list at version `v`, the hub's list at `v` (at most `max` long), leaves the member holding exactly that
list and version `v`, uncut, whether it was waiting or held any other version: recovery from a gap. -/
theorem recv_full (m : Member) (v : Nat × Nat) (list : List Nat) (max : Nat) (hl : list.length ≤ max) :
    recvFull m v list max = ⟨list, some v, false⟩ := by
  simp [recvFull, List.take_of_length_le hl, Nat.not_lt.2 hl]

#audit_axioms Pinc.BroadcastSubsDelta.recv_old
#audit_axioms Pinc.BroadcastSubsDelta.recv_cut
#audit_axioms Pinc.BroadcastSubsDelta.applyAll_delta
#audit_axioms Pinc.BroadcastSubsDelta.recv_full
#audit_axioms Pinc.BroadcastSubsDelta.recv_on_base
#audit_axioms Pinc.BroadcastSubsDelta.recv_off_base
#audit_axioms Pinc.BroadcastSubsDelta.delta_mem
#audit_axioms Pinc.BroadcastSubsDelta.apply_delta
#audit_axioms Pinc.BroadcastSubsDelta.eq_of_sorted_mem

end Pinc.BroadcastSubsDelta
