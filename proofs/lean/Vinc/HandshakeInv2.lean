import Vinc.HandshakeInv

/-!
# No early acceptance, for unboundedly many sessions

A second inductive invariant of the system of `HandshakeSys`, proved over every reachable state, for any number of
sessions, tickets and any store capacity:

* a session that raised Established (or, for an initiator, that signed) authenticated its peer first: the initiator
  only after the responder's signature (or, resumed, the confirmation of the reply) verified, the responder only after
  the Finish verified or the binder of the ticket verified.
-/

namespace Vinc.Hs
open Term

structure Inv2 (g : G) : Prop where
  iEst : ∀ s, ((g.ist s).est = true → (g.ist s).auth = true) ∧ ((g.ist s).ph = .sign → (g.ist s).auth = true)
  rEst : ∀ s, (g.rst s).est = true → (g.rst s).auth = true
  rClean : ∀ s, ((g.rst s).ph = .idle ∨ (g.rst s).ph = .sign ∨ (g.rst s).ph = .finish) → (g.rst s).est = false

theorem Inv2_init (K C : Nat) : Inv2 (G0 K C) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro s <;> simp [G0]

theorem Inv2_congr {g g' : G} (hi : g'.ist = g.ist) (hr : g'.rst = g.rst) (h : Inv2 g) : Inv2 g' := by
  cases g; cases g'; simp only at hi hr; subst hi hr
  exact ⟨h.iEst, h.rEst, h.rClean⟩

theorem iupd2 {g g' : G} (h : Inv2 g) (s : Nat × Nat) (st' : IState)
    (hist : g'.ist = upd g.ist s st') (hrst : g'.rst = g.rst)
    (hloc : (st'.est = true → st'.auth = true) ∧ (st'.ph = .sign → st'.auth = true)) : Inv2 g' := by
  refine ⟨?_, ?_, ?_⟩
  · intro s'; rw [hist]; by_cases hh : s' = s
    · subst hh; simpa [upd_same] using hloc
    · rw [upd_ne _ _ _ _ hh]; exact h.iEst s'
  · intro s'; rw [hrst]; exact h.rEst s'
  · intro s'; rw [hrst]; exact h.rClean s'

theorem rupd2 {g g' : G} (h : Inv2 g) (s : Nat × Nat) (st' : RState)
    (hist : g'.ist = g.ist) (hrst : g'.rst = upd g.rst s st')
    (hl : (st'.est = true → st'.auth = true) ∧ ((st'.ph = .idle ∨ st'.ph = .sign ∨ st'.ph = .finish) → st'.est = false)) :
    Inv2 g' := by
  refine ⟨?_, ?_, ?_⟩
  · intro s'; rw [hist]; exact h.iEst s'
  · intro s'; rw [hrst]; by_cases hh : s' = s
    · subst hh; simpa [upd_same] using hl.1
    · rw [upd_ne _ _ _ _ hh]; exact h.rEst s'
  · intro s'; rw [hrst]; by_cases hh : s' = s
    · subst hh; simpa [upd_same] using hl.2
    · rw [upd_ne _ _ _ _ hh]; exact h.rClean s'

theorem iStep2 {g g' : G} (h1 : Inv1 g) (h : Inv2 g) (hs : Step g g') : Inv2 g' := by
  cases hs with
  | iStart s peer al short take _ hn _ =>
    refine iupd2 h s (INew s.1 s.2 peer al short (if take then (CTake (g.cli s.1) peer al).tk else none)).st
      (by cases take <;> rfl) (by cases take <;> rfl) ?_
    unfold INew
    cases (if take then (CTake (g.cli s.1) peer al).tk else none) <;> simp [IBeginFull, IBeginResume, Ok]
  | iRecv s m _ hd =>
    have hl := h.iEst s
    refine iupd2 h s _ rfl rfl ?_
    rcases IHandle_cases (g.ist s) s.1 m with ⟨c1, -⟩ | ⟨-, -, -, c1, -⟩ | ⟨-, -, -, -, c1, -⟩
      | ⟨-, -, -, c1, -⟩ | ⟨-, -, -, -, c1, -⟩ | ⟨-, -, -, c1, -⟩
    · rw [c1]; exact hl
    · rw [c1]; exact ⟨hl.1, by simp⟩
    · rw [c1]; exact hl
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [rrFall, IBeginFull, Ok]; exact hl.1
  | iAnswer s kind _ _ =>
    have hl := h.iEst s
    refine iupd2 h s _ rfl rfl ?_
    rcases IKey_cases (g.ist s) s.1 kind with ⟨c1, -⟩ | ⟨-, c1, -⟩ | ⟨-, -, -, -, -, -, -, c1, -⟩ | ⟨hp, -, c1, -⟩ |
      ⟨-, -, -, c1, -⟩
    · rw [c1]; exact hl
    · rw [c1]; exact ⟨hl.1, by simp⟩
    · rw [c1]; simp [ikSignSt]
    · rw [c1]; simp [ikDoneSt]; exact hl.2 hp
    · rw [c1]; exact ⟨hl.1, by simp [ikBackSt]⟩
  | iRetrans s _ _ =>
    have hl := h.iEst s
    refine iupd2 h s _ rfl rfl ?_
    rcases IRetransmit_cases s.1 (g.ist s) with ⟨-, -, c1, -⟩ | ⟨-, -, c1, -⟩ | ⟨-, -, c1, -⟩ | ⟨c1, -⟩
    · rw [c1]; simpa using hl
    · rw [c1]; simpa using hl
    · rw [c1]; simp [lateFall, lateFallB, IBeginFull, Ok]; exact hl.1
    · rw [c1]; exact hl
  | iShed s _ _ => exact iupd2 h s _ rfl rfl (by simpa [IShed] using h.iEst s)
  | iAccept s tids _ _ _ _ _ => exact iupd2 h s _ rfl rfl (by simpa using h.iEst s)
  | rRecv s m cs _ hd =>
    have hl := h.rEst s
    have hc := h.rClean s
    have hi := h1.rIdle s
    refine rupd2 h s _ rfl rfl ?_
    rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m cs with
        ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, ⟨sp, nr, c1⟩, -⟩ | ⟨hp, -, c1, -⟩ | ⟨hp, -, c1, -⟩
      | ⟨hp, -, -, -, -, c1, -⟩ | ⟨hp, -, -, -, -, -, c1, -⟩ | ⟨hp, -, -, -, -, -, c1, -⟩
      | ⟨hp, -, -, -, -, c1, -⟩ | ⟨hp, -, -, -, -, -, c1, -⟩ | ⟨hp, -, -, -, -, -, c1, -⟩
    · rw [c1]; exact ⟨hl, hc⟩
    · rw [c1]; have := hc (by rcases hp with hp | hp <;> simp [hp]); simp [this]
    · rw [c1]; simp [hp]; exact hl
    · rw [c1]; exact ⟨hl, hc⟩
    · rw [c1]; exact ⟨hl, hc⟩
    · rw [c1]; have := hc (by simp [hp]); simp [rInitSt, this]
    · rw [c1]; simp [rfSt]
    · rw [c1]; have := hc (by simp [hp]); simp [this]
    · rw [c1]; exact ⟨hl, hc⟩
    · rw [c1]; simp [rhSt]
    · rw [c1]; have := hc (by simp [hp]); simp [this]
  | rAnswer s kind _ _ =>
    have hl := h.rEst s
    have hc := h.rClean s
    refine rupd2 h s _ rfl rfl ?_
    rcases RKey_cases (g.rst s) s.1 s.2 (g.sto s.1) kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
    · rw [c1]; exact ⟨hl, hc⟩
    · rw [c1]; have := hc (by simp [hp]); simp [this]
    · rw [c1]; have := hc (by simp [hp]); simp [rkSt, this]
  | rRetrans s _ _ => exact Inv2_congr (g := g) rfl rfl h
  | rShed s _ =>
    have hl := h.rEst s
    have hc := h.rClean s
    refine rupd2 h s _ rfl rfl ?_
    by_cases hp : (g.rst s).ph = .resumed
    · simp [RShed, hp]; exact hl
    · simp [RShed, hp]; exact ⟨hl, hc⟩
  | expire n i sl _ _ _ _ => exact Inv2_congr (g := g) rfl rfl h
  | expireC n i sl _ _ _ _ => exact Inv2_congr (g := g) rfl rfl h
  | «export» n mx _ => exact Inv2_congr (g := g) rfl rfl h
  | restore n drop _ => exact Inv2_congr (g := g) rfl rfl h
  | restart n _ => exact Inv2_congr (g := g) rfl rfl h

theorem Inv2_reach {K C : Nat} {g : G} (h : Reach K C g) : Inv2 g := by
  induction h with
  | init => exact Inv2_init K C
  | step hr hs ih => exact iStep2 (Inv1_reach hr) ih hs

/-- No early acceptance, initiator: it raised Established only after the peer was authenticated. -/
theorem noEarlyI {K C : Nat} {g : G} (h : Reach K C g) (s : Nat × Nat) (he : (g.ist s).est = true) :
    (g.ist s).auth = true := ((Inv2_reach h).iEst s).1 he

/-- No early acceptance, responder: it raised Established only after the Finish or the ticket binder verified. -/
theorem noEarlyR {K C : Nat} {g : G} (h : Reach K C g) (s : Nat × Nat) (he : (g.rst s).est = true) :
    (g.rst s).auth = true := (Inv2_reach h).rEst s he

#audit_axioms Vinc.Hs.Inv2_reach
#audit_axioms Vinc.Hs.noEarlyI
#audit_axioms Vinc.Hs.noEarlyR

end Vinc.Hs
