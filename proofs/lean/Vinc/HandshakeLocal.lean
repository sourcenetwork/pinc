import Vinc.HandshakeCases

/-!
# Local consistency of the sessions

A third inductive invariant of the system of `HandshakeSys`, for any number of sessions: every session's stored
transcripts, keys and identities are the ones its own steps computed (the formulas of the step functions), and a
session with a node other than the attacker's. It is a property of each session alone, so it is proved by the step
lemmas of one session (`IHandle`, `IKey`, `RHandle`, `RKey`, the two begins), and it is the bridge from the
authentication witnesses of `HandshakeInv` to agreement and secrecy: two sessions that hold the same transcript hash
hold the same fields, by injectivity of the free term algebra.
-/

namespace Vinc.Hs
open Term

/-- The first fields of an initiator after its Initial: the transcript hash and the owner of the ephemeral. -/
def IBase (n : Nat) (st : IState) : Prop :=
  st.th0 = th0 ok (pub st.x) (hash (ek n)) ∧ st.x.n = n ∧ st.resumed = false

/-- After the Reply was accepted. -/
def IFlow (n : Nat) (st : IState) : Prop :=
  IBase n st ∧ st.reply.rprm = ok ∧ st.th1 = th1 st.th0 ok st.reply.e st.reply.ct ∧
  st.ssx = Dh st.x (atomOf st.reply.e)

/-- After the responder's identity and signature verified (the initiator is to sign). -/
def ISign (n : Nat) (st : IState) : Prop :=
  IFlow n st ∧ st.ck1 = ikCk1 st n ∧ st.reply.sealed.id = st.peer ∧ st.th2 = th2 st.th1 st.peer ∧
  st.th3 = th3 st.th2 st.reply.sealed.sig ∧ st.th4 = th4 st.th3 n ∧ st.ath = st.th2 ∧
  st.reply.sealed.sig = sig st.peer true st.th2 ∧ st.hsi = hs st.ck1 true st.th1

/-- After the initiator signed: the keys. -/
def IDone (n : Nat) (st : IState) : Prop :=
  ISign n st ∧ st.thf = th5 st.th4 (sig n false st.th4) ∧ st.send = app (ck2 st.ck1 st.thf) true st.thf ∧
  st.recv = app (ck2 st.ck1 st.thf) false st.thf ∧ st.res = res (ck2 st.ck1 st.thf) st.thf

/-- An initiator that resumes: its ticket's key, its Hello transcript and binder. -/
def IResume (n : Nat) (st : IState) : Prop :=
  ∃ p, st.ckpsk = ckpsk p ∧ st.thh = thH ok st.tid (pub st.x) ∧ st.binder = binder p st.thh ∧ st.x.n = n ∧ st.th4 = nil ∧
    st.early = early st.ckpsk st.thh

/-- After the resumption reply verified. -/
def IResDone (st : IState) : Prop :=
  ∃ rp e, st.thf = thR st.thh st.binder rp e ∧ st.ath = st.thf ∧
    st.send = app (ck2 (ck1r st.ckpsk (Dh st.x (atomOf e))) st.thf) true st.thf ∧
    st.recv = app (ck2 (ck1r st.ckpsk (Dh st.x (atomOf e))) st.thf) false st.thf ∧
    st.res = res (ck2 (ck1r st.ckpsk (Dh st.x (atomOf e))) st.thf) st.thf

def ICl (s : Nat × Nat) (st : IState) : Prop :=
  (st.ph ≠ .none → s.1 ≠ att) ∧
  (st.ph = .reply → IBase s.1 st) ∧
  (st.ph = .decap → IFlow s.1 st) ∧
  (st.ph = .sign → ISign s.1 st) ∧
  (st.ph = .done → st.resumed = false → IDone s.1 st) ∧
  ((st.ph = .resume ∨ (st.ph = .done ∧ st.resumed = true)) → IResume s.1 st) ∧
  (st.ph = .done → st.resumed = true → IResDone st)

theorem ICl_none (s : Nat × Nat) : ICl s ({} : IState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all

theorem ICl_acc (s : Nat × Nat) (st : IState) (h : ICl s st) : ICl s { st with acc := true } := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem ICl_begin_full (s : Nat × Nat) (x : Atom) (peer : Nat) (short : Bool) (thh early : Term)
    (hx : x.n = s.1) (hs : s.1 ≠ att) :
    ICl s (IBeginFull s.1 x peer short thh early).st := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [IBeginFull, Ok, IBase] at * <;> simp_all

theorem ICl_begin_resume (s : Nat × Nat) (x : Atom) (tk : Tk) (hx : x.n = s.1) (hs : s.1 ≠ att) :
    ICl s (IBeginResume s.1 x tk).st := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [IBeginResume, Ok, IResume] at * <;> simp_all

theorem ICl_ihandle (s : Nat × Nat) (st : IState) (m : Msg) (h : ICl s st) :
    ICl s (IHandle st s.1 m).st := by
  rcases IHandle_cases st s.1 m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hr, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, c1, -, hc⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> simp_all <;> (try (rcases hp with hp | hp <;> simp_all))
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    have hb := b hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> simp_all [IFlow, IBase]
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    have hb := b hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> simp_all [IBase]
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    have hb := f (Or.inl hp)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact a (by simp [hp])
    · intro hh; simp [rrDone] at hh
    · intro hh; simp [rrDone] at hh
    · intro hh; simp [rrDone] at hh
    · intro _ hh; simp [rrDone] at hh
    · intro _; simpa [rrDone, IResume] using hb
    · intro _ _; exact ⟨m.rprm, m.e, rfl, rfl, rfl, rfl, rfl⟩
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    obtain ⟨p, h1, h2, h3, h4, h5, h6⟩ := f (Or.inl hp)
    have hs : s.1 ≠ att := a (by simp [hp])
    have hfull := ICl_begin_full s (atom 1 st.x.n st.x.k) st.peer false st.thh nil (by simpa [atom] using h4) hs
    obtain ⟨a', b', c', d', e', f', g'⟩ := hfull
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; exact b' (by simpa [rrFall] using hh) |> fun x => by simpa [rrFall, IBase] using x
    · intro hh; simp [rrFall, IBeginFull, Ok] at hh
    · intro hh; simp [rrFall, IBeginFull, Ok] at hh
    · intro hh; simp [rrFall, IBeginFull, Ok] at hh
    · intro hh; simp [rrFall, IBeginFull, Ok] at hh
    · intro hh; simp [rrFall, IBeginFull, Ok] at hh

theorem ICl_ikey (s : Nat × Nat) (st : IState) (kind : KRes) (h : ICl s st) :
    ICl s (IKey st s.1 kind).st := by
  rcases IKey_cases st s.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, k1, k2, k3, k4, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    have hs : s.1 ≠ att := a (by rcases hp with hp | hp <;> simp [hp])
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> simp_all
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    have hf := c hp
    obtain ⟨hb, hr, ht1, hssx⟩ := hf
    have hs : s.1 ≠ att := a (by simp [hp])
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; simp [ikSignSt] at hh
    · intro hh; simp [ikSignSt] at hh
    · intro _
      refine ⟨⟨hb, hr, ht1, hssx⟩, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl⟩
      · simpa [ikSignSt] using k3
      · simp [ikSignSt, k3]
      · simp [ikSignSt]
      · simp [ikSignSt, k3]
      · simpa [ikSignSt, k3] using k4
    · intro hh; simp [ikSignSt] at hh
    · intro hh; rcases hh with hh | ⟨hh, -⟩ <;> simp [ikSignSt] at hh
    · intro hh; simp [ikSignSt] at hh
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g⟩ := h
    have hf := d hp
    have hs : s.1 ≠ att := a (by simp [hp])
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; simp [ikDoneSt] at hh
    · intro hh; simp [ikDoneSt] at hh
    · intro hh; simp [ikDoneSt] at hh
    · intro _ _
      refine ⟨hf, ?_, ?_, ?_, ?_⟩
      · simp [ikDoneSt, ikT5, ikSig]
      · simp [ikDoneSt, ikCk2, ikT5, ikSig]
      · simp [ikDoneSt, ikCk2, ikT5, ikSig]
      · simp [ikDoneSt, ikCk2, ikT5, ikSig]
    · intro hh
      have hr : st.resumed = false := hf.1.1.2.2
      rcases hh with hh | ⟨-, hh⟩ <;> simp [ikDoneSt, hr] at hh
    · intro _ hh
      have hr : st.resumed = false := hf.1.1.2.2
      simp [ikDoneSt, hr] at hh

/-! ## The responder -/

/-- What a responder stored from the Initial it accepted. -/
def RInitM (n k : Nat) (st : RState) (m : Msg) : Prop :=
  m.prm = ok ∧ st.th0 = rT0 m ∧ st.hpk = rHpk m ∧ st.ek = rEk m ∧ st.ct = rC n k m ∧
    st.th1 = rT1 n k m ∧ st.th2 = th2 st.th1 n ∧ st.ath = st.th2 ∧ st.ck1 = rCk1 n k m ∧
    st.hsr = hs st.ck1 false st.th1 ∧ st.hsi = hs st.ck1 true st.th1 ∧ st.fresh = decide (m.form = .full) ∧
    st.resumed = false

def RInit (n k : Nat) (st : RState) : Prop := ∃ m : Msg, RInitM n k st m

/-- After the responder signed its Reply. -/
def RFin (n : Nat) (st : RState) : Prop := st.th3 = th3 st.th2 (sig n true st.th2)

/-- After the Finish verified: the initiator's transcript and the keys. -/
def RDone (st : RState) : Prop :=
  st.th4 = th4 st.th3 st.peer ∧ st.thf = th5 st.th4 (sig st.peer false st.th4) ∧
  st.send = app (ck2 st.ck1 st.thf) false st.thf ∧ st.recv = app (ck2 st.ck1 st.thf) true st.thf ∧
  st.res = res (ck2 st.ck1 st.thf) st.thf

/-- After a resumption Hello was accepted. -/
def RResDone (n k : Nat) (st : RState) : Prop :=
  ∃ p e b, st.thh = thH ok st.tid e ∧ st.thf = thR st.thh b ok (pub (ry n k)) ∧ st.ath = st.thf ∧
    b = binder p st.thh ∧
    st.send = app (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) false st.thf ∧
    st.recv = app (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) true st.thf ∧
    st.res = res (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) st.thf ∧
    st.early = early (ckpsk p) st.thh ∧ st.mytid = tid n k ∧ st.sgn = true ∧ st.resumed = true

def RCl (s : Nat × Nat) (st : RState) : Prop :=
  (st.ph ≠ .idle → s.1 ≠ att) ∧
  (st.ph = .idle → st = {}) ∧
  (st.ph = .sign → RInit s.1 s.2 st) ∧
  (st.sgn = true → st.resumed = false → RInit s.1 s.2 st ∧ RFin s.1 st) ∧
  (st.ph = .finish → st.sgn = true ∧ RInit s.1 s.2 st ∧ RFin s.1 st) ∧
  (st.ph = .done → st.sgn = true) ∧
  (st.ph = .done → st.resumed = false → RDone st) ∧
  (st.ph = .done → st.resumed = true → RResDone s.1 s.2 st) ∧
  (st.resumed = true → st.ph = .done) ∧
  (st.ph = .done → st.mytid = tid s.1 s.2) ∧
  (st.ph = .finish → st.reply.conf = nil ∧ st.reply.binder = nil)

theorem RCl_none (s : Nat × Nat) : RCl s ({} : RState) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all

theorem RCl_failed (s : Nat × Nat) (st : RState) (hs : s.1 ≠ att) (hnd : st.ph ≠ .done) (h : RCl s st) :
    RCl s { st with ph := .failed } := by
  obtain ⟨a, b, c, d, e, f, g, i, j, l, l2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact hs
  · intro hh; simp at hh
  · intro hh; simp at hh
  · exact d
  · intro hh; simp at hh
  · intro hh; simp at hh
  · intro hh; simp at hh
  · intro hh; simp at hh
  · intro hh; exact absurd (j hh) hnd
  · intro hh; simp at hh
  · intro hh; simp at hh

theorem RCl_rkey (s : Nat × Nat) (st : RState) (sto : Store) (kind : KRes) (hs : s.1 ≠ att) (h : RCl s st) :
    RCl s (RKey st s.1 s.2 sto kind).st := by
  rcases RKey_cases st s.1 s.2 sto kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]; exact RCl_failed s st hs (by simp [hp]) h
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g, i, j, l, l2⟩ := h
    have hi := c hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; simp [rkSt] at hh
    · intro hh; simp [rkSt] at hh
    · intro hh hr
      refine ⟨?_, ?_⟩
      · obtain ⟨m, hm⟩ := hi; exact ⟨m, by simpa [RInitM, rkSt] using hm⟩
      · simp [RFin, rkSt, rkSig]
    · intro _
      refine ⟨by simp [rkSt], ?_, ?_⟩
      · obtain ⟨m, hm⟩ := hi; exact ⟨m, by simpa [RInitM, rkSt] using hm⟩
      · simp [RFin, rkSt, rkSig]
    · intro hh; simp [rkSt] at hh
    · intro hh; simp [rkSt] at hh
    · intro hh; simp [rkSt] at hh
    · intro hh; obtain ⟨m, hm⟩ := hi; simp [rkSt, hm.2.2.2.2.2.2.2.2.2.2.2.2] at hh
    · intro hh; simp [rkSt] at hh
    · intro _; simp [rkSt, rkReply]

theorem RCl_rhandle (s : Nat × Nat) (st : RState) (sto : Store) (m : Msg) (hs : s.1 ≠ att) (h : RCl s st) :
    RCl s (RHandle st s.1 s.2 sto m).st := by
  rcases RHandle_cases st s.1 s.2 sto m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, c1, -⟩ | ⟨hp, hty, c1, -⟩
    | ⟨hp, hty, hprm, c1, -⟩ | ⟨hp, hty, hk, had, hsg, c1, -⟩ | ⟨hp, hty, hprm, c1, -⟩
    | ⟨hp, hty, hprm, i0, hf, he, hb, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]; exact RCl_failed s st hs (by rcases hp with hp | hp <;> simp [hp]) h
  · rw [c1]; exact h
  · rw [c1]; exact h
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g, i, j, l, l2⟩ := h
    have h0 := b hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; simp [rInitSt] at hh
    · intro _
      refine ⟨m, hprm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      simp [rInitSt, h0]
    · intro hh; simp [rInitSt, h0] at hh
    · intro hh; simp [rInitSt] at hh
    · intro hh; simp [rInitSt] at hh
    · intro hh; simp [rInitSt] at hh
    · intro hh; simp [rInitSt] at hh
    · intro hh; simp [rInitSt, h0] at hh
    · intro hh; simp [rInitSt] at hh
    · intro hh; simp [rInitSt] at hh
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g, i, j, l, l2⟩ := h
    obtain ⟨hsgn, hri, hfin⟩ := e hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; simp [rfSt] at hh
    · intro hh; simp [rfSt] at hh
    · intro _ _
      refine ⟨?_, ?_⟩
      · obtain ⟨m', hm⟩ := hri; exact ⟨m', by simpa [RInitM, rfSt] using hm⟩
      · simpa [RFin, rfSt] using hfin
    · intro hh; simp [rfSt] at hh
    · intro _; simp [rfSt, hsgn]
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [rfSt, rfT4]
      · simp [rfSt, rfT5, rfT4, hsg]
      · simp [rfSt, rfCk2, rfT5, rfT4]
      · simp [rfSt, rfCk2, rfT5, rfT4]
      · simp [rfSt, rfRes, rfCk2, rfT5, rfT4]
    · intro _ hr
      obtain ⟨m', hm⟩ := hri
      have hrr : st.resumed = false := hm.2.2.2.2.2.2.2.2.2.2.2.2
      simp [rfSt, hrr] at hr
    · intro _; simp [rfSt]
    · intro _; simp [rfSt]
    · intro hh; simp [rfSt] at hh
  · rw [c1]; exact h
  · rw [c1]
    obtain ⟨a, b, c, d, e, f, g, i, j, l, l2⟩ := h
    have h0 := b hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact hs
    · intro hh; simp [rhSt] at hh
    · intro hh; simp [rhSt] at hh
    · intro _ hr; simp [rhSt] at hr
    · intro hh; simp [rhSt] at hh
    · intro _; simp [rhSt]
    · intro _ hr; simp [rhSt] at hr
    · intro _ _
      refine ⟨(rhSlot sto i0).psk, m.e, m.binder, ?_, ?_, ?_, hb.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [rhSt, rhThh, hprm]
      · simp [rhSt, rhThr, rhThh, hprm]
      · simp [rhSt]
      · simp [rhSt, rhCk2]
      · simp [rhSt, rhCk2]
      · simp [rhSt, rhCk2]
      · simp [rhSt, rhThh, hprm]
      · simp [rhSt]
      · simp [rhSt]
      · simp [rhSt]
    · intro _; simp [rhSt]
    · intro _; simp [rhSt]
    · intro hh; simp [rhSt] at hh

end Vinc.Hs
