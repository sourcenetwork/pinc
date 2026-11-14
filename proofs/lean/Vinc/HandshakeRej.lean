import Vinc.HandshakeStore

/-!
# Rejects only cause a fallback, for unboundedly many sessions

A forged or genuine reject (`PRej`, `RRej`) delivered to any initiator session of any reachable state never
establishes or authenticates anything and never changes the dialed peer: a prekey reject leaves a session that waits
for a Reply as it was, but for noting that a full Initial went out for a reject (once, and again only after the
reject gap), and a rejected resumption starts a fresh full handshake. A reject
a responder sends leaves the responder's state as it was and its store as it was or with one slot removed (an
expired one), and issues nothing (`RejectsOnlyFallback` of `Handshake.tla`).

No message stops an initiator, and a Reply that fails a check before the responder's signature verified is dropped
with the initiator waiting for the next one, unauthenticated (`ihandleNeverFatal`, `replyOfferDropped`,
`replyUnauthDropped`).
-/

namespace Vinc.Hs
open Term

/-- An initiator that is waiting for a reply has not authenticated or established. -/
def InvI (ist : Nat × Nat → IState) : Prop :=
  ∀ s, ((ist s).ph = .reply ∨ (ist s).ph = .resume ∨ (ist s).ph = .decap) → (ist s).est = false ∧ (ist s).auth = false

theorem InvI_upd {ist : Nat × Nat → IState} (h : InvI ist) (s : Nat × Nat) (st' : IState)
    (hn : (st'.ph = .reply ∨ st'.ph = .resume ∨ st'.ph = .decap) → st'.est = false ∧ st'.auth = false) : InvI (upd ist s st') := by
  intro s' hs'
  by_cases hh : s' = s
  · subst hh; simp only [upd_same] at hs' ⊢; exact hn hs'
  · simp only [upd_ne _ _ _ _ hh] at hs' ⊢; exact h s' hs'

theorem InvI_ihandle (st : IState) (n : Nat) (m : Msg) (h : (st.ph = .reply ∨ st.ph = .resume ∨ st.ph = .decap) → st.est = false ∧ st.auth = false) :
    ((IHandle st n m).st.ph = .reply ∨ (IHandle st n m).st.ph = .resume ∨ (IHandle st n m).st.ph = .decap) →
      (IHandle st n m).st.est = false ∧ (IHandle st n m).st.auth = false := by
  rcases IHandle_cases st n m with ⟨c, -⟩ | ⟨hp, -, -, c, -⟩ | ⟨hp, -, -, -, c, -⟩ | ⟨-, -, -, c, -⟩ |
    ⟨-, -, -, -, c, -⟩ | ⟨hp, -, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; intro _; have := h (Or.inl hp); simp [this]
  · rw [c]; intro _; exact h (Or.inl hp)
  · rw [c]; intro e; simp [IResumed] at e
  · rw [c]; intro e; simp [IResumed] at e
  · rw [c]; intro _; have := h (Or.inr (Or.inl hp)); simp [rrFall, IBeginFull, Ok, this]

theorem InvI_ikey (st : IState) (n : Nat) (kind : KRes) (h : (st.ph = .reply ∨ st.ph = .resume ∨ st.ph = .decap) → st.est = false ∧ st.auth = false) :
    ((IKey st n kind).st.ph = .reply ∨ (IKey st n kind).st.ph = .resume ∨ (IKey st n kind).st.ph = .decap) →
      (IKey st n kind).st.est = false ∧ (IKey st n kind).st.auth = false := by
  rcases IKey_cases st n kind with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨hp, -, -, -, -, -, -, c, -⟩ | ⟨hp, -, c, -⟩ |
    ⟨hp, -, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; intro e; simp at e
  · rw [c]; intro e; simp [ikSignSt, hp] at e
  · rw [c]; intro e; simp [ikDoneSt, hp] at e
  · rw [c]; intro _; have := h (Or.inr (Or.inr hp)); simp [ikBackSt, this]

theorem InvI_iretrans (st : IState) (n : Nat) (h : (st.ph = .reply ∨ st.ph = .resume ∨ st.ph = .decap) → st.est = false ∧ st.auth = false) :
    ((IRetransmit n st).st.ph = .reply ∨ (IRetransmit n st).st.ph = .resume ∨ (IRetransmit n st).st.ph = .decap) →
      (IRetransmit n st).st.est = false ∧ (IRetransmit n st).st.auth = false := by
  rcases IRetransmit_cases n st with ⟨hp, -, c, -⟩ | ⟨hp, -, c, -⟩ | ⟨hp, -, c, -⟩ | ⟨c, -⟩
  · rw [c]; intro _; exact h (Or.inl hp)
  · rw [c]; intro _; exact h (Or.inr (Or.inl hp))
  · rw [c]; intro _; have := h (Or.inr (Or.inl hp)); simp [lateFall, lateFallB, IBeginFull, Ok, this]
  · rw [c]; exact h

theorem InvI_new (n k peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) :
    ((INew n k peer al short tk).st.ph = .reply ∨ (INew n k peer al short tk).st.ph = .resume ∨ (INew n k peer al short tk).st.ph = .decap) →
      (INew n k peer al short tk).st.est = false ∧ (INew n k peer al short tk).st.auth = false := by
  intro _
  unfold INew
  cases tk <;> simp [IBeginResume, IBeginFull, Ok]

theorem InvI_step {g g' : G} (h : InvI g.ist) (hs : Step g g') : InvI g'.ist := by
  cases hs with
  | iStart s peer al short take _ _ _ => exact InvI_upd h s _ (InvI_new _ _ _ _ _ _)
  | iRecv s m _ _ => exact InvI_upd h s _ (InvI_ihandle _ _ _ (h s))
  | iAnswer s kind _ _ => exact InvI_upd h s _ (InvI_ikey _ _ _ (h s))
  | iRetrans s _ _ => exact InvI_upd h s _ (InvI_iretrans _ _ (h s))
  | iShed s _ _ => exact InvI_upd h s _ (by intro e; simpa [IShed] using h s e)
  | iAccept s tids _ hd _ _ _ => exact InvI_upd h s _ (by intro e; rw [hd] at e; simp at e)
  | rRecv => exact h
  | rAnswer => exact h
  | rRetrans => exact h
  | rShed => exact h
  | expire => exact h
  | expireC => exact h
  | «export» => exact h
  | restore => exact h
  | restart => exact h

theorem InvI_reach {K C : Nat} {g : G} (hr : Reach K C g) : InvI g.ist := by
  induction hr with
  | init => intro s h; simp [G0] at h
  | step _ hs ih => exact InvI_step ih hs

/-! ## A dialing side drops a Reply that fails a check before it authenticated

Nothing in a Reply has authenticated until the responder's signature verified, so a Reply that fails any check
before that is dropped and the initiator keeps waiting for the real one (`initiator.rs`). -/

/-- No message stops an initiator: whatever it receives, the step takes it or drops it. -/
theorem ihandleNeverFatal (st : IState) (n : Nat) (m : Msg) : (IHandle st n m).err ≠ .fatal := by
  unfold IHandle
  repeat' split
  all_goals simp [Drop, Ok]

/-- A Reply whose AEAD is outside the offer is dropped: the initiator is left exactly as it was. -/
theorem replyOfferDropped (st : IState) (n : Nat) (m : Msg) (hp : st.ph = .reply) (hty : m.ty = .reply)
    (ho : ¬ InOffer st.of m.ad) : IHandle st n m = Drop st := by
  have hf : st.ph ≠ .failed := by simp [hp]
  simp [IHandle, hf, hty, hp, ho]

/-- A Reply taken in that does not authenticate (its sealed part does not open, or holds no credit record, another
identity than the dialed one or a signature that does not verify) is dropped: nothing is sent or raised, the
initiator waits for the next Reply, and it has not authenticated or taken the peer's credit record. -/
theorem replyUnauthDropped (st : IState) (n : Nat) (hp : st.ph = .decap) (ha : ¬ ikAuth st n) :
    (IKey st n .ok).err = .drop ∧ (IKey st n .ok).st = ikBackSt st ∧ (IKey st n .ok).out = []
      ∧ (IKey st n .ok).ev = [] ∧ (IKey st n .ok).sg = []
      ∧ (ikBackSt st).ph = .reply ∧ (ikBackSt st).pcr = st.pcr ∧ (ikBackSt st).auth = st.auth
      ∧ (ikBackSt st).est = st.est := by
  simp [IKey, hp, ha, ikBackSt]

/-- RejectsOnlyFallback, initiator side: a reject delivered to any session is dropped or taken without a change, or
leaves a session that waited for a reply as it was but for noting the full Initial it sent for a prekey reject, or
moves a resumption to a fresh full handshake to the same peer, unauthenticated and marked as fallen back. -/
theorem rejectInit {K C : Nat} {g : G} (hr : Reach K C g) (s : Nat × Nat) (m : Msg)
    (hm : m.ty = .prej ∨ m.ty = .rrej) :
    (IHandle (g.ist s) s.1 m).st = g.ist s ∨
    ((g.ist s).ph = .reply ∧ (IHandle (g.ist s) s.1 m).st = { g.ist s with rgap := true } ∧
      (g.ist s).est = false ∧ (g.ist s).auth = false) ∨
    ((IHandle (g.ist s) s.1 m).st.ph = .reply ∧
      (IHandle (g.ist s) s.1 m).st.peer = (g.ist s).peer ∧ (IHandle (g.ist s) s.1 m).st.est = false ∧
      (IHandle (g.ist s) s.1 m).st.auth = false ∧ (g.ist s).est = false ∧
      (g.ist s).ph = .resume ∧ (IHandle (g.ist s) s.1 m).st.fell = true) := by
  have hs := InvI_reach hr s
  by_cases hf : (g.ist s).ph = .failed
  · left; simp [IHandle, hf, Drop]
  rcases hm with hm | hm
  · by_cases hc : (g.ist s).ph = .reply ∧ m.echo = (g.ist s).th0
    · have he := hs (Or.inl hc.1)
      have hn : ¬((g.ist s).ph ≠ .reply ∨ m.echo ≠ (g.ist s).th0) := by
        rintro (h | h)
        · exact h hc.1
        · exact h hc.2
      by_cases hg : (g.ist s).rgap = true ∧ m.gap = false
      · left
        have e : IHandle (g.ist s) s.1 m = Ok (g.ist s) [] [] := by
          unfold IHandle; rw [if_neg hf]; simp only [hm]; rw [if_neg hn, if_pos hg]
        rw [e]; rfl
      · right; left
        have e : IHandle (g.ist s) s.1 m = Ok { g.ist s with rgap := true } [IInitMsg s.1 (g.ist s) false] [] := by
          unfold IHandle; rw [if_neg hf]; simp only [hm]; rw [if_neg hn, if_neg hg]
        rw [e]; exact ⟨hc.1, rfl, he.1, he.2⟩
    · left
      have : (g.ist s).ph ≠ .reply ∨ m.echo ≠ (g.ist s).th0 := by
        by_cases h1 : (g.ist s).ph = .reply
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      have e : IHandle (g.ist s) s.1 m = Drop (g.ist s) := by
        unfold IHandle; rw [if_neg hf]; simp only [hm]; rw [if_pos this]
      rw [e]; rfl
  · by_cases hc : (g.ist s).ph = .resume ∧ m.echo = (g.ist s).thh
    · right; right
      have he := hs (Or.inr (Or.inl hc.1))
      simp [IHandle, hf, hm, hc.1, hc.2, Ok, he.1, he.2, IBeginFull]
    · left
      have : (g.ist s).ph ≠ .resume ∨ m.echo ≠ (g.ist s).thh := by
        by_cases h1 : (g.ist s).ph = .resume
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      have e : IHandle (g.ist s) s.1 m = Drop (g.ist s) := by
        unfold IHandle; rw [if_neg hf]; simp only [hm]; rw [if_pos this]
      rw [e]; rfl

/-- The reply a responder holds while it waits for the Finish or repeats a Hello is of the right kind. -/
def RplOK (st : RState) : Prop :=
  (st.ph = .finish → st.reply.ty = .reply) ∧ (st.ph = .resumed → st.reply.ty = .rreply)

theorem RplOK_handle (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) (h : RplOK st) :
    RplOK (RHandle st n k sto m cs).st := by
  rcases RHandle_cases st n k sto m cs with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, ⟨sp, nr, c⟩, -⟩ | ⟨-, -, c, -⟩ | ⟨-, -, c, -⟩ |
    ⟨-, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, c, -⟩ |
    ⟨-, -, -, -, -, -, c, -⟩ | ⟨-, -, -, -, -, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp, by simp⟩
  · rw [c]; exact h
  · rw [c]; exact h
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp [rInitSt], by simp [rInitSt]⟩
  · rw [c]; exact ⟨by simp [rfSt], by simp [rfSt]⟩
  · rw [c]; exact ⟨by simp, by simp⟩
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp [rhSt], by simp [rhSt, rhReply]⟩
  · rw [c]; exact ⟨by simp, by simp⟩

theorem RplOK_key (st : RState) (n k : Nat) (sto : Store) (kind : KRes) (h : RplOK st) :
    RplOK (RKey st n k sto kind).st := by
  rcases RKey_cases st n k sto kind with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp, by simp⟩
  · rw [c]; exact ⟨by simp [rkSt, rkReply], by simp [rkSt]⟩

theorem RplOK_reach {K C : Nat} {g : G} (hr : Reach K C g) : ∀ s, RplOK (g.rst s) := by
  induction hr with
  | init => intro s; exact ⟨by simp [G0], by simp [G0]⟩
  | @step g0 g1 _ hs ih =>
    cases hs with
    | rRecv s m cs _ _ =>
      intro r; by_cases e : r = s
      · subst e; simpa [stepRRecv, upd_same] using RplOK_handle (g0.rst r) r.1 r.2 (g0.sto r.1) m cs (ih r)
      · show RplOK (upd _ s _ r); rw [upd_ne _ _ _ _ e]; exact ih r
    | rAnswer s kind _ _ =>
      intro r; by_cases e : r = s
      · subst e; simpa [stepRAnswer, upd_same] using RplOK_key (g0.rst r) r.1 r.2 (g0.sto r.1) kind (ih r)
      · show RplOK (upd _ s _ r); rw [upd_ne _ _ _ _ e]; exact ih r
    | rShed s _ =>
      intro r; by_cases e : r = s
      · subst e
        show RplOK (upd _ r _ r); rw [upd_same]
        have := ih r
        unfold RShed; split
        · exact ⟨by simp, by simp⟩
        · exact this
      · show RplOK (upd _ s _ r); rw [upd_ne _ _ _ _ e]; exact ih r
    | _ => exact ih

/-- RejectsOnlyFallback, responder side, for a prekey reject: the responder and its store are unchanged. -/
theorem rejectRespPrej {K C : Nat} {g : G} (hr : Reach K C g) (n k : Nat) (m : Msg) (cs : List (List Nat)) :
    ∀ o ∈ (RHandle (g.rst (n, k)) n k (g.sto n) m cs).out, o.ty = .prej →
      (RHandle (g.rst (n, k)) n k (g.sto n) m cs).st = g.rst (n, k) ∧
      (RHandle (g.rst (n, k)) n k (g.sto n) m cs).sto = g.sto n := by
  have hp := RplOK_reach hr (n, k)
  rcases RHandle_cases (g.rst (n, k)) n k (g.sto n) m cs with ⟨c1, c2, c3, c4, c5⟩
    | ⟨hph, c1, c2, c3, c4, c5⟩ | ⟨hph, ⟨sp, nr, c1⟩, c2, c3, c4, c5⟩ | ⟨hph, hty, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, c1, c2, c3, c4, c5⟩ | ⟨hph, hty, hv, hs, ha, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, hk, ha, hs, hok, c1, c2, c3, c4, c5⟩ | ⟨hph, hty, hk, ha, hs, hok, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, hv, hs, hu, c1, c2, c3, c4, c5⟩ | ⟨hph, hty, hv, hs, hu, hok, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, hv, hs, hu, hok, c1, c2, c3, c4, c5⟩
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho e
    rcases c2 with c2 | c2
    · rw [c2] at ho; cases ho
    · rw [c2] at ho; simp at ho; subst ho; simp [hp.2 hph] at e
  · intro o ho e
    rw [c2] at ho; simp at ho; subst ho; simp [hp.1 hph] at e
  · intro o ho _; exact ⟨c1, c3⟩
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho e; rw [c2] at ho; simp at ho; subst ho; simp at e
  · intro o ho e; rw [c2] at ho; simp [rhReply] at ho; subst ho; simp at e
  · intro o ho; rw [c2] at ho; cases ho

/-- A resume reject leaves the responder as it was, the store as it was or with one slot removed, and issues
nothing. -/
theorem rejectRespRrej {K C : Nat} {g : G} (hr : Reach K C g) (n k : Nat) (m : Msg) (cs : List (List Nat)) :
    ∀ o ∈ (RHandle (g.rst (n, k)) n k (g.sto n) m cs).out, o.ty = .rrej →
      (RHandle (g.rst (n, k)) n k (g.sto n) m cs).st = g.rst (n, k) ∧
      ((RHandle (g.rst (n, k)) n k (g.sto n) m cs).sto = g.sto n ∨
        ∃ i, (RHandle (g.rst (n, k)) n k (g.sto n) m cs).sto = RemoveSlot (g.sto n) i) ∧
      (RHandle (g.rst (n, k)) n k (g.sto n) m cs).iss = [] := by
  have hp := RplOK_reach hr (n, k)
  rcases RHandle_cases (g.rst (n, k)) n k (g.sto n) m cs with ⟨c1, c2, c3, c4, c5⟩
    | ⟨hph, c1, c2, c3, c4, c5⟩ | ⟨hph, ⟨sp, nr, c1⟩, c2, c3, c4, c5⟩ | ⟨hph, hty, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, c1, c2, c3, c4, c5⟩ | ⟨hph, hty, hv, hs, ha, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, hk, ha, hs, hok, c1, c2, c3, c4, c5⟩ | ⟨hph, hty, hk, ha, hs, hok, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, hv, hs, hu, c1, c2, c3, c4, c5⟩ | ⟨hph, hty, hv, hs, hu, hok, c1, c2, c3, c4, c5⟩
    | ⟨hph, hty, hv, hs, hu, hok, c1, c2, c3, c4, c5⟩
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho e
    rcases c2 with c2 | c2
    · rw [c2] at ho; cases ho
    · rw [c2] at ho; simp at ho; subst ho; simp [hp.2 hph] at e
  · intro o ho e
    rw [c2] at ho; simp at ho; subst ho; simp [hp.1 hph] at e
  · intro o ho e; rw [c2] at ho; simp at ho; subst ho; simp at e
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho; rw [c2] at ho; cases ho
  · intro o ho _
    refine ⟨c1, ?_, c4⟩
    rw [c3]; unfold rhStoRej; split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · intro o ho e; rw [c2] at ho; simp [rhReply] at ho; subst ho; simp at e
  · intro o ho; rw [c2] at ho; cases ho

/-! ## A19 and A21: the fallback keeps the destination id, a resumed responder resends within its budgets -/

/-- A resuming initiator, or one that gave up its Hello for a full Initial, holds the destination id it chose. -/
def InvD (s : Nat × Nat) (st : IState) : Prop :=
  (st.ph = .resume → st.dc = cid 1 s.1 s.2) ∧ (st.late.on = true → st.dc = cid 1 s.1 s.2)

theorem InvD_none (s : Nat × Nat) : InvD s ({} : IState) := ⟨by simp, by simp [Late]⟩

theorem InvD_ihandle (s : Nat × Nat) (st : IState) (m : Msg) (h : InvD s st) : InvD s (IHandle st s.1 m).st := by
  rcases IHandle_cases st s.1 m with ⟨c, -⟩ | ⟨-, -, -, c, -⟩ | ⟨-, -, -, -, c, -⟩ | ⟨-, -, -, c, -⟩ |
    ⟨-, -, -, -, c, -⟩ | ⟨-, -, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp, h.2⟩
  · rw [c]; exact ⟨fun e => h.1 e, h.2⟩
  · rw [c]; exact ⟨by simp [IResumed], by simp [IResumed, NoLate]⟩
  · rw [c]; exact ⟨by simp [IResumed], by simp [IResumed, NoLate]⟩
  · rw [c]; exact ⟨by simp [rrFall, IBeginFull, Ok], by simp [rrFall, IBeginFull, Ok, NoLate]⟩

theorem InvD_ikey (s : Nat × Nat) (st : IState) (kind : KRes) (h : InvD s st) : InvD s (IKey st s.1 kind).st := by
  rcases IKey_cases st s.1 kind with ⟨c, -⟩ | ⟨-, c, -⟩ | ⟨-, -, -, -, -, -, -, c, -⟩ | ⟨-, -, c, -⟩ | ⟨-, -, -, c, -⟩
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp, h.2⟩
  · rw [c]; exact ⟨by simp [ikSignSt], h.2⟩
  · rw [c]; exact ⟨by simp [ikDoneSt], h.2⟩
  · rw [c]; exact ⟨by simp [ikBackSt], h.2⟩

theorem InvD_iretrans (s : Nat × Nat) (st : IState) (h : InvD s st) : InvD s (IRetransmit s.1 st).st := by
  rcases IRetransmit_cases s.1 st with ⟨hp, -, c, -⟩ | ⟨hp, -, c, -⟩ | ⟨hp, -, c, -⟩ | ⟨c, -⟩
  · rw [c]; exact h
  · rw [c]; exact h
  · rw [c]; exact ⟨by simp [lateFall, lateFallB, IBeginFull, Ok], fun _ => by
      simp [lateFall, lateFallB, IBeginFull, Ok]; exact h.1 hp⟩
  · rw [c]; exact h

theorem InvD_new (s : Nat × Nat) (peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) :
    InvD s (INew s.1 s.2 peer al short tk).st := by
  unfold INew
  cases tk <;> simp [IBeginResume, IBeginFull, Ok, InvD]

theorem InvD_reach {K C : Nat} {g : G} (hr : Reach K C g) : ∀ s, InvD s (g.ist s) := by
  induction hr with
  | init => intro s; exact InvD_none s
  | @step g0 g1 _ hs ih =>
    have key : ∀ (s : Nat × Nat) (st' : IState), InvD s st' → ∀ r, InvD r (upd g0.ist s st' r) := by
      intro s st' hst r
      by_cases e : r = s
      · subst e; rw [upd_same]; exact hst
      · rw [upd_ne _ _ _ _ e]; exact ih r
    cases hs with
    | iStart s peer al short take _ _ _ => exact key s _ (InvD_new s _ _ _ _)
    | iRecv s m _ _ => exact key s _ (InvD_ihandle s _ m (ih s))
    | iAnswer s kind _ _ => exact key s _ (InvD_ikey s _ kind (ih s))
    | iRetrans s _ _ => exact key s _ (InvD_iretrans s _ (ih s))
    | iShed s _ _ =>
      exact key s _ ⟨fun e => (ih s).1 e, by simp [IShed, NoLate]⟩
    | iAccept s tids _ _ _ _ _ => exact key s _ (ih s)
    | _ => exact ih

/-- A19: a Hello that gave way to a full Initial kept its destination id. -/
theorem fallbackKeepsDcid {K C : Nat} {g : G} (hr : Reach K C g) (s : Nat × Nat) (h : (g.ist s).late.on = true) :
    (g.ist s).dc = cid 1 s.1 s.2 :=
  (InvD_reach hr s).2 h

/-- A21 for every responder state and every message: a resumed responder sends its Reply again only within the byte
budgets. A repeated Hello of the same transcript while the bytes it was sent total at most `RB`; an Initial under
the same connection ids only when the Reply is at most three times its size and the bytes total at most `LB`. -/
theorem resendWithinBudget (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat))
    (hp : st.ph = .resumed) (ho : st.reply ∈ (RHandle st n k sto m cs).out) :
    (m.ty = .hello ∧ (RHandle st n k sto m cs).st.thh = st.thh ∧ (RHandle st n k sto m cs).st.spent ≤ RB) ∨
    (m.ty = .init ∧ m.dc = st.dc ∧ m.sc = st.sc ∧ st.reply.len ≤ 3 * m.len ∧
      (RHandle st n k sto m cs).st.spent ≤ LB) := by
  have hf : st.ph ≠ .failed := by rw [hp]; simp
  have hr : ∀ r : RRes, r.out = [] → st.reply ∈ r.out → False := fun r h1 h2 => by rw [h1] at h2; cases h2
  cases hty : m.ty
  case init =>
    have e : RHandle st n k sto m cs = RInitial st n k sto m := by simp [RHandle, hf, hty]
    rw [e] at ho ⊢
    by_cases h3 : st.dc = m.dc ∧ st.sc = m.sc
    · by_cases h4 : st.reply.len ≤ 3 * m.len ∧ st.spent + m.len ≤ LB
      · right; simp [RInitial, hp, h3, h4, ROk]
      · exfalso; simp [RInitial, hp, h3, h4] at ho
    · exfalso; simp [RInitial, hp, h3, RDrop] at ho
  case hello =>
    have e : RHandle st n k sto m cs = RRepeat st sto m := by simp [RHandle, hf, hty, RHello, hp]
    rw [e] at ho ⊢
    unfold RRepeat at ho ⊢
    dsimp only at ho ⊢
    by_cases hc : st.thh ≠ thH m.ver m.al m.dc m.sc m.ad m.tid m.e m.cr ∨ st.spent + m.len > RB
    · exfalso; rw [if_pos hc] at ho; simp at ho
    · rw [if_neg hc]
      left
      refine ⟨rfl, rfl, ?_⟩
      have := (not_or.mp hc).2
      show st.spent + m.len ≤ RB
      omega
  all_goals
    exfalso
    first
      | (have e : RHandle st n k sto m cs = RDrop st sto := by simp [RHandle, hf, hty, RFinish, hp, RDrop]
         rw [e] at ho; simp [RDrop] at ho)
      | (simp [RHandle, hf, hty, RDrop] at ho)

#audit_axioms Vinc.Hs.fallbackKeepsDcid
#audit_axioms Vinc.Hs.resendWithinBudget
#audit_axioms Vinc.Hs.InvI_reach
#audit_axioms Vinc.Hs.ihandleNeverFatal
#audit_axioms Vinc.Hs.replyOfferDropped
#audit_axioms Vinc.Hs.replyUnauthDropped
#audit_axioms Vinc.Hs.rejectInit
#audit_axioms Vinc.Hs.RplOK_reach
#audit_axioms Vinc.Hs.rejectRespPrej
#audit_axioms Vinc.Hs.rejectRespRrej

end Vinc.Hs
