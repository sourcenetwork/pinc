import Pinc.KeyRollSysStage

namespace Pinc.KeyRollSys
open Pinc.KeyRoll

/-! ## `Deliver` keeps the invariant, and so every step does -/

theorem deliverOk_spec {P : Params} {S : Sys} {n : Bool} {p : Pkt} {f : Bool} (h : deliverOk P S n p f = true) :
    p ∈ S.net ∧ p.src = !n := by
  unfold deliverOk at h
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := h
  exact ⟨h1, h2⟩

/-- What the body of a packet does to the node, case by case. -/
theorem inv_rekey {P : Params} {S : Sys} {n : Bool} {s1 : Node} {p : Pkt} {m : Msg}
    (h1 : Inv P (S.setNode n s1)) (hp : p ∈ S.net) (hsrc : p.src = !n) (hpl : p.pl = some m)
    (hdep : p.sec.depth = s1.cur.g ∨ p.sec.depth + 1 = s1.cur.g) :
    Inv P { S.setNode n (rekeyRx s1 m n p.sec.depth).s with
      comp := addOpt (rekeyRx s1 m n p.sec.depth).comp S.comp
      stl := addOpt (rekeyRx s1 m n p.sec.depth).st S.stl } := by
  have e1 : (S.setNode n s1).nd n = s1 := Sys.setNode_same _ _ _
  have hp1 : p ∈ (S.setNode n s1).net := hp
  have same : ∀ X : Node, Inv P (S.setNode n X) → Inv P (S.setNode n X) := fun _ h => h
  by_cases ha : m.answer = true
  · cases hok : (s1.roll.onAnswer m).2 with
    | ok c' =>
      obtain ⟨seed, rq, b, hst, _, hsh, hto, _⟩ := onAnswer_ok_st s1.roll m c' hok
      rw [rekeyRx_consume s1 m n _ seed rq b ha hst hsh hto]
      have := inv_consume h1 hp1 hsrc hpl ha seed rq b (by rw [e1]; exact hst) hsh hto
      rw [e1, Sys.setNode_setNode] at this
      exact this
    | error e =>
      rw [rekeyRx_answer_refused s1 m n _ ha (by intro c'' hc; rw [hok] at hc; cases hc)]
      exact h1
  · have ha' : m.answer = false := by simpa using ha
    by_cases hg : gated s1 m = true
    · rw [rekeyRx_gated s1 m n _ ha' hg]; exact h1
    · have hg' : gated s1 m = false := by simpa using hg
      rcases onRequest_split s1.roll m ha' with hd | ⟨hn, hb⟩ | ⟨hn, hf⟩
      · obtain ⟨ans, hl⟩ := isDup_last s1.roll m hd
        rw [rekeyRx_dup s1 m n _ ha' hg' ans hl]
        have := inv_dup h1 m.share ans (by rw [e1]; exact hl)
        rw [e1, Sys.setNode_setNode] at this
        exact this
      · rw [rekeyRx_busy s1 m n _ ha' hg' hn hb]; exact h1
      · have hmok := h1.netMsg p hp1 m hpl
        rw [hsrc] at hmok
        obtain ⟨_, k, hk, _⟩ := hmok.req ha'
        rw [rekeyRx_stage s1 m n _ (atomOf (!n) k) ha' hg' hn hf hk]
        have := inv_stage h1 hp1 hsrc hpl ha' (atomOf (!n) k) hk (by rw [e1]; exact hg') (by rw [e1]; exact hn)
          (by rw [e1]; exact hf) (by rw [e1]; exact hdep)
        rw [e1, Sys.setNode_setNode] at this
        exact this

theorem NodeInv.requeue {P : Params} {n : Bool} {s : Node} (h : NodeInv P n s) :
    NodeInv P n { s with out := s.lastAns, reqAt := s.reqAt } := by
  node_inv
  case outMsg => intro m hm; exact (h.ansLast m hm).1
  case outReq => intro m hm hq; have := (h.ansLast m hm).2; rw [this] at hq; cases hq
  all_goals close_same h

/-- A lost answer is queued again. -/
theorem inv_requeue {P : Params} {S : Sys} {n : Bool} (h : Inv P S) : Inv P (requeueUpd S n) := by
  unfold requeueUpd
  refine inv_setOut h (S.nd n).lastAns (S.nd n).reqAt (h.node n).requeue ?_ ?_
  · intro a ha _; exact h.ansLastStl n a ha
  · intro a ha hq; have := ((h.node n).ansLast a ha).2; rw [this] at hq; cases hq

/-- A lost request is marked: only the time of the last send changes. -/
theorem inv_reqLost {P : Params} {S : Sys} {n : Bool} (h : Inv P S) : Inv P (reqLostUpd S n) := by
  unfold reqLostUpd
  exact inv_setOut h (S.nd n).out none
    ((h.node n).setOut (S.nd n).out none (S.nd n).lastAns (Or.inr rfl) (Or.inl rfl))
    (fun a ha hans => h.outAns n a ha hans) (fun a ha hq p hp => h.unsent n a ha hq p hp)

theorem inv_deliver {P : Params} {S : Sys} {n : Bool} {p : Pkt} {f : Bool} (h : Inv P S)
    (hok : deliverOk P S n p f = true) : Inv P (deliverUpd P S n p f) := by
  obtain ⟨hp, hsrc⟩ := deliverOk_spec hok
  have h1 := inv_recv (f := f) h hp hsrc
  have hdepth := afterRecv_depth (h.node n) p f S.now
  unfold deliverUpd
  dsimp only
  generalize hr : (S.nd n).afterRecv P p f S.now = r at h1 hdepth ⊢
  obtain ⟨s1, pr⟩ := r
  simp only at h1 hdepth ⊢
  have e1 : (S.setNode n s1).nd n = s1 := Sys.setNode_same _ _ _
  rcases hpl : p.pl with _ | m
  · exact h1
  · by_cases hproc : pr = true
    · by_cases hact : acts m ((S.nd n).rxSel P p f S.now) = true
      · simp only [hproc, hact, Bool.and_self, if_true]
        exact inv_rekey h1 hp hsrc hpl (hdepth hproc)
      · have hno : (pr && acts m ((S.nd n).rxSel P p f S.now)) = false := by simp [hact]
        simp only [hno]; exact h1
    · simp only [hproc]; exact h1

theorem inv_step {P : Params} {S S' : Sys} (h : Inv P S) (hs : Step P S S') : Inv P S' := by
  cases hs with
  | begin n hok => exact inv_begin h hok
  | send n w hok => exact inv_send h hok
  | deliver n p f hok => exact inv_deliver h hok
  | tick => exact inv_tick h
  | requeue n _ => exact inv_requeue h
  | reqLost n _ => exact inv_reqLost h

/-- Every reachable state satisfies the invariant. -/
theorem Reach.inv {P : Params} {S : Sys} (h : Reach P S) : Inv P S := by
  induction h with
  | init => exact Inv.init P
  | step S S' _ hs ih => exact inv_step ih hs

end Pinc.KeyRollSys
