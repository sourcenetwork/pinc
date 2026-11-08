import Vinc.HandshakeStore

/-!
# Rejects only cause a fallback, for unboundedly many sessions

A forged or genuine reject (`PRej`, `RRej`) delivered to any initiator session of any reachable state either is
dropped or moves the session to a full Initial under the same dialed peer, without establishing or authenticating
anything; the short Initial keeps its transcript, and a rejected resumption starts a fresh full handshake. A reject
a responder sends leaves the responder's state and store as they were (a rejected Hello only removes an expired slot).
-/

namespace Vinc.Hs
open Term

/-- An initiator that is waiting for a reply has not authenticated or established. -/
def InvI (ist : Nat × Nat → IState) : Prop :=
  ∀ s, ((ist s).ph = .reply ∨ (ist s).ph = .resume) → (ist s).est = false ∧ (ist s).auth = false

theorem InvI_init (K : Nat) : InvI (G0 K).ist := by
  intro s h; simp [G0] at h

theorem InvI_upd {ist : Nat × Nat → IState} (h : InvI ist) (s : Nat × Nat) (st' : IState)
    (hn : (st'.ph = .reply ∨ st'.ph = .resume) → st'.est = false ∧ st'.auth = false) : InvI (upd ist s st') := by
  intro s' hs'
  by_cases hh : s' = s
  · subst hh; simp only [upd_same] at hs' ⊢; exact hn hs'
  · simp only [upd_ne _ _ _ _ hh] at hs' ⊢; exact h s' hs'

theorem IBeginFull_clean (n : Nat) (x : Atom) (peer : Nat) (short : Bool) (a b : Term) :
    (IBeginFull n x peer short a b).st.est = false ∧ (IBeginFull n x peer short a b).st.auth = false := by
  simp [IBeginFull, Ok]

theorem InvI_iHandle {ist : Nat × Nat → IState} (h : InvI ist) (s : Nat × Nat) (m : Msg) :
    InvI (upd ist s (IHandle (ist s) s.1 m).st) := by
  have hs := h s
  refine InvI_upd h s _ ?_
  rcases IHandle_cases (ist s) s.1 m with ⟨c1, -⟩ | ⟨-, c1, -⟩ | ⟨-, -, -, c1, -⟩ | ⟨hp, -, -, -, c1, -⟩
    | ⟨-, -, c1, -⟩ | ⟨-, -, -, c1, -⟩
  · rw [c1]; exact hs
  · rw [c1]; intro e; simp at e
  · rw [c1]; intro e; simp at e
  · rw [c1]; intro _; exact hs (Or.inl hp)
  · rw [c1]; intro e; simp [rrDone] at e
  · rw [c1]; intro _; simp [rrFall, IBeginFull, Ok]

theorem InvI_iKey {ist : Nat × Nat → IState} (h : InvI ist) (s : Nat × Nat) (kind : KRes) :
    InvI (upd ist s (IKey (ist s) s.1 kind).st) := by
  have hs := h s
  refine InvI_upd h s _ ?_
  rcases IKey_cases (ist s) s.1 kind with ⟨c1, -⟩ | ⟨-, c1, -⟩ | ⟨hp, -, -, -, -, -, c1, -⟩ | ⟨hp, -, c1, -⟩
  · rw [c1]; exact hs
  · rw [c1]; intro e; simp at e
  · rw [c1]; intro e; simp [ikSignSt, hp] at e
  · rw [c1]; intro e; simp [ikDoneSt] at e

/-- The initiator invariant holds in every reachable state. -/
theorem InvI_reach {K : Nat} {g : G} (hr : Reach K g) : InvI g.ist := by
  induction hr with
  | init => exact InvI_init K
  | step _ hs ih =>
    cases hs with
    | startFull s peer short _ hn _ =>
      exact InvI_upd ih s _ (fun _ => IBeginFull_clean _ _ _ _ _ _)
    | startResume s tk _ hn _ =>
      exact InvI_upd ih s _ (fun _ => by simp [IBeginResume, Ok])
    | iRecv s m _ _ => exact InvI_iHandle ih s m
    | iAnswer s kind _ => exact InvI_iKey ih s kind
    | iRetransmit => exact ih
    | iAcceptFull s r hd _ _ _ _ _ _ =>
      exact InvI_upd ih s _ (by intro e; rw [hd] at e; simp at e)
    | iAcceptResumed s t hd _ _ _ _ =>
      exact InvI_upd ih s _ (by intro e; rw [hd] at e; simp at e)
    | rRecv => exact ih
    | rAnswer => exact ih
    | expire => exact ih

/-- RejectsOnlyFallback, initiator side, for every state satisfying the initiator invariant and every message. -/
theorem rejectInit_of {ist : Nat × Nat → IState} (h : InvI ist) (s : Nat × Nat) (m : Msg)
    (hm : m.ty = .prej ∨ m.ty = .rrej) :
    (IHandle (ist s) s.1 m).st = ist s ∨
    ((IHandle (ist s) s.1 m).st.ph = .reply ∧ (IHandle (ist s) s.1 m).st.short = false ∧
      (IHandle (ist s) s.1 m).st.peer = (ist s).peer ∧ (IHandle (ist s) s.1 m).st.est = false ∧
      (IHandle (ist s) s.1 m).st.auth = false ∧ (ist s).est = false ∧
      ((ist s).ph = .reply → (IHandle (ist s) s.1 m).st.th0 = (ist s).th0) ∧
      ((ist s).ph = .resume → (IHandle (ist s) s.1 m).st.fell = true)) := by
  have hs := h s
  by_cases hf : (ist s).ph = .failed
  · left; simp [IHandle, hf, Drop]
  · rcases hm with hm | hm
    · have e : IHandle (ist s) s.1 m = if ¬((ist s).ph = .reply ∧ (ist s).short = true) ∨ m.echo ≠ (ist s).th0
          then Drop (ist s) else Ok { ist s with short := false }
            [{ ty := .init, form := .full, e := pub (ist s).x, pk := ek s.1 }] [] := by
        simp [IHandle, hf, hm]
      rw [e]
      by_cases hc : ¬((ist s).ph = .reply ∧ (ist s).short = true) ∨ m.echo ≠ (ist s).th0
      · left; simp only [hc, ite_true, Drop]
      · right
        have hc' : (ist s).ph = .reply ∧ (ist s).short = true := by
          exact Decidable.byContradiction (fun hh => hc (Or.inl hh))
        have he := hs (Or.inl hc'.1)
        simp only [hc, ite_false, Ok]
        simp [hc'.1, he.1, he.2]
    · have e : IHandle (ist s) s.1 m = if (ist s).ph ≠ .resume ∨ m.echo ≠ (ist s).thh
          then Drop (ist s) else Ok (rrFall (ist s) s.1) (IBeginFull s.1 (atom 1 (ist s).x.n (ist s).x.k) (ist s).peer false (ist s).thh nil).out [.rejected] := by
        simp [IHandle, hf, hm]
      rw [e]
      by_cases hc : (ist s).ph ≠ .resume ∨ m.echo ≠ (ist s).thh
      · left; simp only [hc, ite_true, Drop]
      · right
        have hc' : (ist s).ph = .resume := by
          exact Decidable.byContradiction (fun hh => hc (Or.inl hh))
        have he := hs (Or.inr hc')
        simp only [hc, ite_false, Ok]
        simp [hc', he.1, rrFall, IBeginFull, Ok]

theorem rejectInit {K : Nat} {g : G} (hr : Reach K g) (s : Nat × Nat) (m : Msg)
    (hm : m.ty = .prej ∨ m.ty = .rrej) :
    (IHandle (g.ist s) s.1 m).st = g.ist s ∨
    ((IHandle (g.ist s) s.1 m).st.ph = .reply ∧ (IHandle (g.ist s) s.1 m).st.short = false ∧
      (IHandle (g.ist s) s.1 m).st.peer = (g.ist s).peer ∧ (IHandle (g.ist s) s.1 m).st.est = false ∧
      (IHandle (g.ist s) s.1 m).st.auth = false ∧ (g.ist s).est = false ∧
      ((g.ist s).ph = .reply → (IHandle (g.ist s) s.1 m).st.th0 = (g.ist s).th0) ∧
      ((g.ist s).ph = .resume → (IHandle (g.ist s) s.1 m).st.fell = true)) :=
  rejectInit_of (InvI_reach hr) s m hm

/-- RejectsOnlyFallback, responder side, for a prekey reject: the responder and its store are unchanged. -/
theorem rejectRespPrej {K : Nat} {g : G} (hr : Reach K g) (n k : Nat) (m : Msg) :
    ∀ o ∈ (RHandle (g.rst (n, k)) n k (g.sto n) m).out, o.ty = .prej →
      (RHandle (g.rst (n, k)) n k (g.sto n) m).st = g.rst (n, k) ∧
      (RHandle (g.rst (n, k)) n k (g.sto n) m).sto = g.sto n := by
  have hfin := (InvRT_reach hr).fR (n, k)
  rcases RHandle_cases (g.rst (n, k)) n k (g.sto n) m with ⟨c1, c2, c3, c4, c5⟩
    | ⟨hp, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, c1, c2, c3, c4, c5⟩
    | ⟨hp, hty, hpr, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, hk, had, hsig, c1, c2, c3, c4, c5⟩
    | ⟨hp, hty, hpr, c1, c2, c4, c5⟩ | ⟨hp, hty, hpr, i0, hfi, hexp, hbind, c1, c2, c3, c4, c5⟩
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho e
    have := hfin hp
    rw [c2] at ho; simp at ho; subst ho; simp [this] at e
  · intro o ho _; exact ⟨c1, c3⟩
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho e
    rw [c2] at ho; simp at ho; subst ho; simp at e
  · intro o ho e
    rw [c2] at ho; simp [rhMsg] at ho; subst ho; simp at e

/-- A resume reject leaves the responder as it was, the store as it was or with one slot removed, and issues
nothing. -/
theorem rejectRespRrej {K : Nat} {g : G} (hr : Reach K g) (n k : Nat) (m : Msg) :
    ∀ o ∈ (RHandle (g.rst (n, k)) n k (g.sto n) m).out, o.ty = .rrej →
      (RHandle (g.rst (n, k)) n k (g.sto n) m).st = g.rst (n, k) ∧
      ((RHandle (g.rst (n, k)) n k (g.sto n) m).sto = g.sto n ∨
        ∃ i, (RHandle (g.rst (n, k)) n k (g.sto n) m).sto = RemoveSlot (g.sto n) i) ∧
      (RHandle (g.rst (n, k)) n k (g.sto n) m).iss = [] := by
  have hfin := (InvRT_reach hr).fR (n, k)
  rcases RHandle_cases (g.rst (n, k)) n k (g.sto n) m with ⟨c1, c2, c3, c4, c5⟩
    | ⟨hp, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, c1, c2, c3, c4, c5⟩
    | ⟨hp, hty, hpr, c1, c2, c3, c4, c5⟩ | ⟨hp, hty, hk, had, hsig, c1, c2, c3, c4, c5⟩
    | ⟨hp, hty, hpr, c1, c2, c4, c5⟩ | ⟨hp, hty, hpr, i0, hfi, hexp, hbind, c1, c2, c3, c4, c5⟩
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho e
    have := hfin hp
    rw [c2] at ho; simp at ho; subst ho; simp [this] at e
  · intro o ho e
    rw [c2] at ho; simp at ho; subst ho; simp at e
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho _
    have hf : (g.rst (n, k)).ph ≠ .failed := by rw [hp]; simp
    have hr2 := RHello_rej _ n k (g.sto n) m hp hpr (by rw [← RHandle_hello _ n k _ m hf hty]; exact c2)
    rw [RHandle_hello _ n k _ m hf hty] at c1 c4 ⊢
    exact ⟨hr2.1, hr2.2, c4⟩
  · intro o ho e
    rw [c2] at ho; simp [rhMsg] at ho; subst ho; simp at e

#audit_axioms Vinc.Hs.InvI_reach
#audit_axioms Vinc.Hs.rejectInit
#audit_axioms Vinc.Hs.rejectRespPrej
#audit_axioms Vinc.Hs.rejectRespRrej

end Vinc.Hs
