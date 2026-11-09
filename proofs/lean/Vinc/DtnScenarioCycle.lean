import Vinc.DtnScenarioTime

/-!
# Without the ranking, custody can be lost: a concrete run

The chain theorem (`custody_chain`) needs custody to be offered only to a higher node id. This file keeps the run that
shows why. Three nodes, the origin 1 and the destination 3, four copies; nothing but contacts, sends, deliveries
and acks between nodes 1 and 2, in this order:

1. nodes 1 and 2 meet;
2. node 1 sprays half its copies to node 2 and offers it custody;
3. node 2 accepts custody and answers with an ack (`ack 1`, kept in the network, delayed);
4. node 2 sprays one copy back to node 1 and offers it custody;
5. node 1 already holds the bundle (the copy is ignored) and answers with an ack (`ack 3`);
6. node 2 receives `ack 3`: custody was offered to node 1, so node 2 is relieved;
7. node 1 receives the old `ack 1`: custody was offered to node 2, so node 1 is relieved.

Now no node keeps custody (the bundle stays in both ledgers as transit, evictable), though it is neither delivered nor
expired. The acknowledgement carries no sequence: `CustodyBook::on_ack` accepts it from the node custody was offered
to however old it is. The ranked offer policy rules the cycle out (`custody_chain`); the model checker finds the same
run (`DtnScenario_cycle.cfg`).
-/

namespace Vinc.DtnScenario

/-- Three nodes, custody offered to anyone. -/
def cyc : Cfg :=
  { ids := [1, 2, 3], src := 1, dest := 3, copies := 4, exp := 100, retry := 5, maxSends := 3, fb := 1, fl := 2,
    ft := 2, lbud := 4, lslots := 2, bslots := 1, tight := 0, pb := 1, ranked := false }

/-- The seven events. -/
def cycEvents : List Ev :=
  [.contact 1 2 true, .poll 1, .bun (.bun 0 1 2 2 true), .poll 2, .bun (.bun 2 2 1 1 true),
   .ack (.ack 3 1 2), .ack (.ack 1 2 1)]

def cycRun : Sys := cycEvents.foldl exec (Sys.init cyc)

/-- Whether a node's ledger keeps a custody item of the bundle. -/
def custBool (s : Sys) (n : Nat) : Bool :=
  (s.nodes n).L.entries.any fun e => decide (e.key = DtnStore.bkey bid) && decide (e.cls = .custody)

theorem cycle_final : cycRun.cfg.ranked = false ∧ cycRun.delivered = false ∧ cycRun.fin = false ∧ cycRun.t = 0 ∧
    custBool cycRun 1 = false ∧ custBool cycRun 2 = false ∧ custBool cycRun 3 = false := by
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
  have h3 := Reach.step (.bun (.bun 0 1 2 2 true)) h2 (by simp [En]; decide)
  have h4 := Reach.step (.poll 2) h3 (by unfold En; decide)
  have h5 := Reach.step (.bun (.bun 2 2 1 1 true)) h4 (by simp [En]; decide)
  have h6 := Reach.step (.ack (.ack 3 1 2)) h5 (by simp [En]; decide)
  exact Reach.step (.ack (.ack 1 2 1)) h6 (by simp [En]; decide)

/-- **The ranking is necessary.** Without it there is a reachable system, neither delivered nor expired, in which no
node keeps custody. -/
theorem cycle_loses_custody :
    ∃ s, Reach s ∧ s.cfg.ranked = false ∧ ¬ Ended s ∧ ∀ n ∈ s.cfg.ids, ¬ Cust s n := by
  refine ⟨cycRun, cyc_reach, cycle_final.1, ?_, ?_⟩
  · rintro (h | h | h)
    · have := cycle_final.2.1; rw [this] at h; cases h
    · have := cycle_final.2.2.1; rw [this] at h; cases h
    · have := cycle_final.2.2.2.1
      have hc : cycRun.cfg.exp = 100 := by decide
      omega
  · intro n hn hcu
    obtain ⟨e, he, hk, hc⟩ := hcu
    have hall : ∀ m ∈ cycRun.cfg.ids, custBool cycRun m = false := by
      intro m hm
      have : cycRun.cfg.ids = [1, 2, 3] := by decide
      rw [this] at hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact cycle_final.2.2.2.2.1
      · exact cycle_final.2.2.2.2.2.1
      · exact cycle_final.2.2.2.2.2.2
    have := hall n hn
    unfold custBool at this
    rw [List.any_eq_false] at this
    exact this e he (by simp [hk, hc])

#audit_axioms Vinc.DtnScenario.cycle_loses_custody

end Vinc.DtnScenario
