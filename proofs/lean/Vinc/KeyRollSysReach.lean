import Vinc.KeyRollSysStage

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-! ## `Deliver` keeps the invariant, and so every step does -/

theorem deliverOk_spec {P : Params} {S : Sys} {n : Bool} {p : Pkt} {f : Bool} (h : deliverOk P S n p f = true) :
    p ∈ S.net ∧ p.src = !n ∧
      (∀ m, p.pl = some m → ((S.nd n).afterRecv P p f S.now).2 = true →
        (P.bindAnswers = true → m.answer = true → ((S.nd n).afterRecv P p f S.now).1.roll.isIdle = false →
          ∃ rq, ((S.nd n).afterRecv P p f S.now).1.roll.pending = some rq ∧ m.to = rq.share)) := by
  unfold deliverOk at h
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, _⟩, h4⟩ := h
  refine ⟨h1, h2, ?_⟩
  intro m hpl hproc hb hma hidle
  rw [hpl] at h4
  simp only [hproc, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at h4
  obtain ⟨h5, _⟩ := h4
  rcases h5 with h5 | h5
  · simp [hb, hma, hidle] at h5
  · cases hp : ((S.nd n).afterRecv P p f S.now).1.roll.pending with
    | none => rw [hp] at h5; simp at h5
    | some rq => rw [hp] at h5; simp at h5; exact ⟨rq, rfl, h5⟩

/-- What the body of a packet does to the node, case by case. -/
theorem inv_rekey {P : Params} {S : Sys} {n : Bool} {s1 : Node} {p : Pkt} {m : Msg}
    (h1 : Inv P (S.setNode n s1)) (hp : p ∈ S.net) (hsrc : p.src = !n) (hpl : p.pl = some m)
    (hbind : m.answer = true → s1.roll.isIdle = false → ∃ rq, s1.roll.pending = some rq ∧ m.to = rq.share)
    (hdep : p.sec.depth = s1.cur.g ∨ p.sec.depth + 1 = s1.cur.g) :
    Inv P { S.setNode n (rekeyRx P s1 m n p.sec.depth).s with
      comp := addOpt (rekeyRx P s1 m n p.sec.depth).comp S.comp
      stl := addOpt (rekeyRx P s1 m n p.sec.depth).st S.stl } := by
  have e1 : (S.setNode n s1).nd n = s1 := Sys.setNode_same _ _ _
  have hp1 : p ∈ (S.setNode n s1).net := hp
  have same : ∀ X : Node, Inv P (S.setNode n X) → Inv P (S.setNode n X) := fun _ h => h
  by_cases ha : m.answer = true
  · cases hok : (s1.roll.onAnswer m).2 with
    | ok c' =>
      obtain ⟨seed, rq, b, hst, _, hsh, _⟩ := onAnswer_ok_st s1.roll m c' hok
      have hidle : s1.roll.isIdle = false := by simp [Roll.isIdle, hst]
      obtain ⟨rq', hrq', hto⟩ := hbind ha hidle
      have hrq : rq' = rq := by
        have : s1.roll.pending = some rq := by simp [Roll.pending, hst]
        rw [this] at hrq'; exact (Option.some.inj hrq').symm
      subst hrq
      rw [rekeyRx_consume P s1 m n _ seed rq' b ha hst hsh]
      have := inv_consume h1 hp1 hsrc hpl ha seed rq' b (by rw [e1]; exact hst) hsh hto
      rw [e1, Sys.setNode_setNode] at this
      exact this
    | error e =>
      rw [rekeyRx_answer_refused P s1 m n _ ha (by intro c'' hc; rw [hok] at hc; cases hc)]
      exact h1
  · have ha' : m.answer = false := by simpa using ha
    by_cases hg : gated P s1 m = true
    · rw [rekeyRx_gated P s1 m n _ ha' hg]; exact h1
    · have hg' : gated P s1 m = false := by simpa using hg
      rcases onRequest_split s1.roll m ha' with hd | ⟨hn, hb⟩ | ⟨hn, hf⟩
      · obtain ⟨ans, hl⟩ := isDup_last s1.roll m hd
        rw [rekeyRx_dup P s1 m n _ ha' hg' ans hl]
        have := inv_dup h1 m.share ans (by rw [e1]; exact hl)
        rw [e1, Sys.setNode_setNode] at this
        exact this
      · rw [rekeyRx_busy P s1 m n _ ha' hg' hn hb]; exact h1
      · have hmok := h1.netMsg p hp1 m hpl
        rw [hsrc] at hmok
        obtain ⟨_, k, hk, _⟩ := hmok.req ha'
        rw [rekeyRx_stage P s1 m n _ (atomOf (!n) k) ha' hg' hn hf hk]
        have := inv_stage h1 hp1 hsrc hpl ha' (atomOf (!n) k) hk (by rw [e1]; exact hg') (by rw [e1]; exact hn)
          (by rw [e1]; exact hf) (by rw [e1]; exact hdep)
        rw [e1, Sys.setNode_setNode] at this
        exact this

theorem inv_deliver {P : Params} {S : Sys} {n : Bool} {p : Pkt} {f : Bool} (hb : P.bindAnswers = true) (h : Inv P S)
    (hok : deliverOk P S n p f = true) : Inv P (deliverUpd P S n p f) := by
  obtain ⟨hp, hsrc, hg⟩ := deliverOk_spec hok
  have h1 := inv_recv (f := f) h hp hsrc
  have hdepth := afterRecv_depth (h.node n) p f S.now
  unfold deliverUpd
  dsimp only
  generalize hr : (S.nd n).afterRecv P p f S.now = r at hg h1 hdepth ⊢
  obtain ⟨s1, pr⟩ := r
  simp only at hg h1 hdepth ⊢
  have e1 : (S.setNode n s1).nd n = s1 := Sys.setNode_same _ _ _
  rcases hpl : p.pl with _ | m
  · exact h1
  · by_cases hproc : pr = true
    · simp only [hproc, if_true]
      have hg' := hg m hpl hproc hb
      have hdep := hdepth hproc
      exact inv_rekey h1 hp hsrc hpl hg' hdep
    · simp only [hproc]; exact h1

theorem inv_step {P : Params} (hb : P.bindAnswers = true) {S S' : Sys} (h : Inv P S) (hs : Step P S S') : Inv P S' := by
  cases hs with
  | begin n hok => exact inv_begin h hok
  | send n w hok => exact inv_send h hok
  | deliver n p f hok => exact inv_deliver hb h hok
  | tick => exact inv_tick h

/-- Every reachable state satisfies the invariant (with `bindAnswers`). -/
theorem Reach.inv {P : Params} (hb : P.bindAnswers = true) {S : Sys} (h : Reach P S) : Inv P S := by
  induction h with
  | init => exact Inv.init P
  | step S S' _ hs ih => exact inv_step hb ih hs

end Vinc.KeyRollSys
