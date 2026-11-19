import Pinc.DtnScenarioHeld

/-!
# Sums over the nodes and the network

`heldAll s` is the copies held by all nodes of the list of ids, `inflight s` the copies in fresh bundle messages
(retransmissions carry copies that were counted when first sent). Replacing one node moves `heldAll` by the change of
that node's held copies (`heldAll_set_delta`), and taking a message out of the network moves `inflight` by its fresh
copies (`inflight_erase`).
-/

namespace Pinc.DtnScenario

/-- The copies held by every node. -/
def Sys.heldAll (s : Sys) : Nat := (s.cfg.ids.map fun n => DtnForward.heldSum (s.nodes n).f bid).sum

/-- The fresh copies of a message. -/
def Msg.freshCopies : Msg → Nat
  | .bun _ _ _ c true _ => c
  | _ => 0

/-- The copies in flight: those of the fresh bundle messages of the network. -/
def Sys.inflight (s : Sys) : Nat := (s.msgs.map Msg.freshCopies).sum

theorem heldAll_set_eq (s : Sys) (n : Nat) (x : Node)
    (h : DtnForward.heldSum x.f bid = DtnForward.heldSum (s.nodes n).f bid) : (s.set n x).heldAll = s.heldAll := by
  unfold Sys.heldAll
  show (s.cfg.ids.map fun k => DtnForward.heldSum ((s.set n x).nodes k).f bid).sum = _
  congr 1
  apply List.map_congr_left
  intro k _
  by_cases hk : k = n
  · subst hk; rw [set_nodes_self]; exact h
  · rw [set_nodes_same _ _ _ _ hk]

theorem heldAll_set_delta (s : Sys) (n : Nat) (x : Node) (hn : s.cfg.ids.Nodup) (hm : n ∈ s.cfg.ids) :
    (s.set n x).heldAll + DtnForward.heldSum (s.nodes n).f bid = s.heldAll + DtnForward.heldSum x.f bid := by
  unfold Sys.heldAll
  show ((s.cfg.ids.map fun k => DtnForward.heldSum ((s.set n x).nodes k).f bid).sum) + _ = _
  generalize s.cfg.ids = ids at hn hm
  induction ids with
  | nil => simp at hm
  | cons a r ih =>
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = n
    · subst ha
      have : (r.map fun k => DtnForward.heldSum ((s.set a x).nodes k).f bid) = r.map fun k => DtnForward.heldSum (s.nodes k).f bid := by
        apply List.map_congr_left
        intro k hk
        have : k ≠ a := fun e => hn.1 (e ▸ hk)
        rw [set_nodes_same _ _ _ _ this]
      rw [this, set_nodes_self]
      omega
    · have hm' : n ∈ r := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm ha
        · exact h
      have ih' := ih hn.2 hm'
      have : DtnForward.heldSum ((s.set n x).nodes a).f bid = DtnForward.heldSum (s.nodes a).f bid := by
        rw [set_nodes_same _ _ _ _ ha]
      rw [this]
      omega

theorem sum_fresh_erase (m : Msg) : ∀ (l : List Msg), m ∈ l →
    ((l.erase m).map Msg.freshCopies).sum + m.freshCopies = (l.map Msg.freshCopies).sum
  | [], h => by simp at h
  | a :: r, h => by
    by_cases ha : a = m
    · subst ha; simp; omega
    · have hm : m ∈ r := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm ha
        · exact e
      have := sum_fresh_erase m r hm
      have hne : (a == m) = false := by simpa using ha
      simp only [List.erase_cons, List.map_cons, List.sum_cons, hne]
      simp
      omega

theorem inflight_erase (s : Sys) (m : Msg) (h : m ∈ s.msgs) :
    ({ s with msgs := s.msgs.erase m } : Sys).inflight + m.freshCopies = s.inflight :=
  sum_fresh_erase m s.msgs h

end Pinc.DtnScenario
