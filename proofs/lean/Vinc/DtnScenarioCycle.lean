import Vinc.DtnScenarioTime

/-!
# Without the ranking, the old cycle run no longer loses custody

The chain theorem (`custody_chain`) needs custody to be offered only to a higher node id. Without that ranking a hand
back can close a cycle. This file keeps the run that once lost custody there. Three nodes, the origin 1 and the
destination 3, four copies; nothing but contacts, sends, deliveries and acks between nodes 1 and 2, in this order:

1. nodes 1 and 2 meet;
2. node 1 sprays half its copies to node 2 and offers it custody (offer id 0);
3. node 2 accepts custody and answers with an ack (`ack 1`, kept in the network, delayed);
4. node 2 sprays one copy back to node 1 and offers it custody (its own offer id 0);
5. node 1 already holds the bundle: the copy is ignored, its offer to node 2 is cancelled, and it answers with an ack
   (`ack 3`);
6. node 2 receives `ack 3`: custody was offered to node 1 under that id, so node 2 is relieved;
7. node 1 receives the old `ack 1`: its offer to node 2 is no longer outstanding, so the ack is refused.

Before the ack carried an offer id, step 7 relieved node 1 too and no node kept custody. Now node 1 keeps it
(`cycle_keeps_custody`); the model checker agrees (`DtnScenario_cycle.cfg`, `CustodyAlive`).
-/

namespace Vinc.DtnScenario

/-- Three nodes, custody offered to anyone. -/
def cyc : Cfg :=
  { ids := [1, 2, 3], src := 1, dest := 3, copies := 4, exp := 100, retry := 5, maxSends := 3, fb := 1, fl := 2,
    ft := 2, fd := 1, lbud := 4, lslots := 2, bslots := 1, tight := 0, pb := 1, ranked := false }

/-- The seven events. -/
def cycEvents : List Ev :=
  [.contact 1 2 true, .poll 1, .bun (.bun 0 1 2 2 true 0), .poll 2, .bun (.bun 2 2 1 1 true 0),
   .ack (.ack 3 1 2 0), .ack (.ack 1 2 1 0)]

def cycRun : Sys := cycEvents.foldl exec (Sys.init cyc)

/-- Whether a node's ledger keeps a custody item of the bundle. -/
def custBool (s : Sys) (n : Nat) : Bool :=
  (s.nodes n).L.entries.any fun e => decide (e.key = DtnStore.bkey bid) && decide (e.cls = .custody)

theorem cycle_final : cycRun.cfg.ranked = false ∧ cycRun.delivered = false ∧ cycRun.fin = false ∧ cycRun.t = 0 ∧
    custBool cycRun 1 = true ∧ custBool cycRun 2 = false ∧ custBool cycRun 3 = false := by
  decide

/-- Before the two acks both nodes keep custody: the loss is the acks' doing. -/
theorem cycle_before_acks :
    custBool ((cycEvents.take 5).foldl exec (Sys.init cyc)) 1 = true ∧
      custBool ((cycEvents.take 5).foldl exec (Sys.init cyc)) 2 = true := by
  decide

theorem cyc_reach : Reach cycRun := by
  have h0 : Reach (Sys.init cyc) := Reach.init cyc (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1 := Reach.step (.contact 1 2 true) h0 (by unfold En; decide)
  have h2 := Reach.step (.poll 1) h1 (by unfold En; decide)
  have h3 := Reach.step (.bun (.bun 0 1 2 2 true 0)) h2 (by simp [En]; decide)
  have h4 := Reach.step (.poll 2) h3 (by unfold En; decide)
  have h5 := Reach.step (.bun (.bun 2 2 1 1 true 0)) h4 (by simp [En]; decide)
  have h6 := Reach.step (.ack (.ack 3 1 2 0)) h5 (by simp [En]; decide)
  exact Reach.step (.ack (.ack 1 2 1 0)) h6 (by simp [En]; decide)

/-- **The old cycle run keeps custody.** The same seven events, neither delivered nor expired, leave node 1 with the
custody item: the stale ack is refused, so the two acks no longer relieve both nodes. -/
theorem cycle_keeps_custody :
    ∃ s, Reach s ∧ s.cfg.ranked = false ∧ ¬ Ended s ∧ ∃ n ∈ s.cfg.ids, Cust s n := by
  refine ⟨cycRun, cyc_reach, cycle_final.1, ?_, 1, by decide, ?_⟩
  · rintro (h | h | h)
    · have := cycle_final.2.1; rw [this] at h; cases h
    · have := cycle_final.2.2.1; rw [this] at h; cases h
    · have := cycle_final.2.2.2.1
      have hc : cycRun.cfg.exp = 100 := by decide
      omega
  · have := cycle_final.2.2.2.2.1
    unfold custBool at this
    rw [List.any_eq_true] at this
    obtain ⟨e, he, h⟩ := this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨e, he, h.1, h.2⟩

#audit_axioms Vinc.DtnScenario.cycle_keeps_custody

end Vinc.DtnScenario
