import Vinc.HandshakeCases

/-!
# Local consistency of the sessions

A third inductive invariant of the system of `HandshakeSys`, for any number of sessions: every session's stored
transcripts, keys and identities are the ones its own steps computed (the formulas of the step functions), and a
session with a node other than the attacker's. It is a property of each session alone, so it is proved by the step
lemmas of one session (`IHandle`, `IKey`, `IRetransmit`, `RHandle`, `RKey`, the begins), and it is the bridge from the
authentication witnesses of `HandshakeInv` to agreement and secrecy: two sessions that hold the same transcript hash
hold the same fields, by injectivity of the free term algebra.
-/

namespace Vinc.Hs
open Term

/-- The first fields of an initiator after its Initial: the transcript hash and the owner of the ephemeral. -/
def IBase (n : Nat) (st : IState) : Prop :=
  st.th0 = th0 ok st.al st.dc st.sc st.cr st.of (pub st.x) (hash (ek n)) ∧ st.x.n = n ∧ st.resumed = false

/-- After the Reply was accepted. -/
def IFlow (n : Nat) (st : IState) : Prop :=
  IBase n st ∧ InOffer st.of st.reply.ad ∧ st.ad = st.reply.ad ∧
  st.th1 = th1 st.th0 st.reply.sc st.reply.ad st.reply.e st.reply.ct ∧ st.ssx = Dh st.x (atomOf st.reply.e)

/-- After the responder's identity, signature and credit record verified (the initiator is to sign). -/
def ISign (n : Nat) (st : IState) : Prop :=
  IFlow n st ∧ st.ck1 = ikCk1 st n ∧ st.reply.sealed.id = st.peer ∧ st.reply.sealed.cr ≠ nil ∧
  st.pcr = st.reply.sealed.cr ∧ st.th2 = th2 st.th1 st.peer st.pcr ∧
  st.th3 = th3 st.th2 st.reply.sealed.sig ∧ st.th4 = th4 st.th3 n ∧ st.ath = st.th2 ∧
  st.reply.sealed.sig = sig st.peer true st.th2 ∧ st.hsi = hs st.ck1 true st.th1

/-- After the initiator signed: the keys. -/
def IDone (n : Nat) (st : IState) : Prop :=
  ISign n st ∧ st.thf = th5 st.th4 (sig n false st.th4) ∧ st.send = app (ck2 st.ck1 st.thf) true st.thf ∧
  st.recv = app (ck2 st.ck1 st.thf) false st.thf ∧ st.res = res (ck2 st.ck1 st.thf) st.thf ∧
  st.cid = cids (ck2 st.ck1 st.thf) st.thf ∧ st.rcr = nil

/-- The context of a resumption Hello of node `n`: the ephemeral, the key of the ticket, the Hello transcript and
binder, and the AEAD of the ticket. -/
def ResCtx (n : Nat) (st : IState) (x : Atom) (ckp thh b ad : Term) : Prop :=
  ∃ p, ckp = ckpsk p ∧ thh = thH ok st.al st.dc st.sc ad st.tid (pub x) st.cr ∧ b = binder p thh ∧ x.n = n

/-- An initiator that resumes: its ticket's key, its Hello transcript and binder. -/
def IResume (n : Nat) (st : IState) : Prop :=
  ResCtx n st st.x st.ckpsk st.thh st.binder st.ad ∧ st.early = early st.ckpsk st.thh ∧ st.th4 = nil

/-- After the resumption reply verified (against the Hello of the session or, late, the Hello that gave way to a
full Initial): the context used and the keys. -/
def IResDone (n : Nat) (st : IState) : Prop :=
  ∃ x ckp thh b rsc e, ResCtx n st x ckp thh b st.ad ∧ st.thf = thR thh b rsc e st.pcr ∧ st.ath = st.thf ∧
    st.send = app (ck2 (ck1r ckp (Dh x (atomOf e))) st.thf) true st.thf ∧
    st.recv = app (ck2 (ck1r ckp (Dh x (atomOf e))) st.thf) false st.thf ∧
    st.res = res (ck2 (ck1r ckp (Dh x (atomOf e))) st.thf) st.thf ∧
    st.cid = cids (ck2 (ck1r ckp (Dh x (atomOf e))) st.thf) st.thf

/-- The local clauses of an initiator session `s`. -/
structure ICl (s : Nat × Nat) (st : IState) : Prop where
  ne : st.ph ≠ .none → s.1 ≠ att ∧ st.cr = crd s.1 ∧ st.of = off s.1
  reply : st.ph = .reply → IBase s.1 st
  decap : st.ph = .decap → IFlow s.1 st
  sign : st.ph = .sign → ISign s.1 st
  done : st.ph = .done → st.resumed = false → IDone s.1 st
  resume : st.ph = .resume → IResume s.1 st
  resDone : st.ph = .done → st.resumed = true → IResDone s.1 st
  resFlag : st.resumed = true → st.ph = .done
  late : st.late.on = true → ResCtx s.1 st st.late.x st.late.ckpsk st.late.thh st.late.binder st.late.ad

theorem ICl_none (s : Nat × Nat) : ICl s ({} : IState) :=
  ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp [Late.on]⟩

theorem ICl_new (s : Nat × Nat) (peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) (hs : s.1 ≠ att) :
    ICl s (INew s.1 s.2 peer al short tk).st := by
  unfold INew
  cases tk with
  | none =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
      simp_all [IBeginFull, Ok, IBase, atom]
  | some t =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
      simp_all [IBeginResume, Ok, IResume, ResCtx, atom]

theorem ICl_ihandle (s : Nat × Nat) (st : IState) (m : Msg) (h : ICl s st) :
    ICl s (IHandle st s.1 m).st := by
  rcases IHandle_cases st s.1 m with ⟨c1, -⟩ | ⟨hp, hty, hio, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, hc, c1, -⟩ | ⟨hp, hl, hty, hc, c1, -⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]
    have hb := h.reply hp
    have hr0 : st.resumed = false := hb.2.2
    refine ⟨fun _ => h.ne (by simp [hp]), ?_, fun _ => ⟨hb, hio, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, h.late⟩ <;>
      intro hh
    · cases hh
    · cases hh
    · cases hh
    · cases hh
    · cases hh
    · have := h.resFlag hh; rw [hp] at this; cases this
  · rw [c1]
    have hb := h.reply hp
    refine ⟨fun _ => h.ne (by simp [hp]), fun _ => hb, ?_, ?_, ?_, ?_, ?_, ?_, h.late⟩ <;> intro hh
    · exact absurd (hp.symm.trans hh) (by decide)
    · exact absurd (hp.symm.trans hh) (by decide)
    · exact absurd (hp.symm.trans hh) (by decide)
    · exact absurd (hp.symm.trans hh) (by decide)
    · exact absurd (hp.symm.trans hh) (by decide)
    · have := h.resFlag hh; exact absurd (hp.symm.trans this) (by decide)
  · rw [c1]
    have hb := h.resume hp
    refine ⟨fun _ => h.ne (by simp [hp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> simp [IResumed, NoLate] at hh ⊢
    · exact ⟨_, _, _, _, _, _, hb.1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [c1]
    have hb := h.late hl
    refine ⟨fun _ => h.ne (by rcases hp with hp | hp | hp <;> simp [hp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro hh <;> simp [IResumed, NoLate] at hh ⊢
    · exact ⟨_, _, _, _, _, _, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [c1]
    have hr := h.resume hp
    have hne := h.ne (by simp [hp])
    have hr0 : st.resumed = false := by
      cases hv : st.resumed
      · rfl
      · have := h.resFlag hv; rw [hp] at this; cases this
    obtain ⟨⟨p, h1, h2, h3, h4⟩, -, -⟩ := hr
    refine ⟨fun _ => hne, fun _ => ⟨rfl, h4, hr0⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh
    · cases hh
    · cases hh
    · cases hh
    · cases hh
    · cases hh
    · have : (rrFall st s.1).resumed = false := hr0
      rw [this] at hh; cases hh
    · simp [rrFall, IBeginFull, Ok, NoLate] at hh

theorem ICl_sends (s : Nat × Nat) (st : IState) (k : Nat) (h : ICl s st) : ICl s { st with sends := k } :=
  ⟨h.ne, h.reply, h.decap, h.sign, h.done, h.resume, h.resDone, h.resFlag, h.late⟩

theorem ICl_iretransmit (s : Nat × Nat) (st : IState) (h : ICl s st) : ICl s (IRetransmit s.1 st).st := by
  rcases IRetransmit_cases s.1 st with ⟨hp, hsh, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨c1, -⟩
  · rw [c1]; exact ICl_sends s st _ h
  · rw [c1]; exact ICl_sends s st _ h
  · rw [c1]
    have hr := h.resume hp
    have hne := h.ne (by simp [hp])
    have hr0 : st.resumed = false := by
      cases hv : st.resumed
      · rfl
      · have := h.resFlag hv; rw [hp] at this; cases this
    obtain ⟨hc, -, -⟩ := hr
    obtain ⟨p, hp1, hp2, hp3, hp4⟩ := hc
    refine ⟨fun _ => hne, fun _ => ⟨rfl, hp4, hr0⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨p, hp1, hp2, hp3, hp4⟩⟩ <;> intro hh
    · cases hh
    · cases hh
    · cases hh
    · cases hh
    · cases hh
    · have : (lateFall st s.1).resumed = false := hr0
      rw [this] at hh; cases hh
  · rw [c1]; exact h

theorem ICl_ished (s : Nat × Nat) (st : IState) (h : ICl s st) : ICl s (IShed st) :=
  ⟨h.ne, h.reply, h.decap, h.sign, h.done, h.resume, h.resDone, h.resFlag, fun hh => by simp [IShed, NoLate] at hh⟩

theorem ICl_acc (s : Nat × Nat) (st : IState) (h : ICl s st) : ICl s { st with acc := true } :=
  ⟨h.ne, h.reply, h.decap, h.sign, h.done, h.resume, h.resDone, h.resFlag, h.late⟩

theorem ICl_ikey (s : Nat × Nat) (st : IState) (kind : KRes) (h : ICl s st) : ICl s (IKey st s.1 kind).st := by
  rcases IKey_cases st s.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, k1, k2, k2', k3, k4, c1, -⟩ | ⟨hp, hk, c1, -⟩ |
    ⟨hp, hk, -, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]
    have hne := h.ne (by rcases hp with hp | hp <;> simp [hp])
    have hnd : st.ph ≠ .done := by rcases hp with hp | hp <;> simp [hp]
    refine ⟨fun _ => hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.late⟩ <;> intro hh
    all_goals first | (cases hh; done) | skip
    exact absurd (h.resFlag hh) hnd
  · rw [c1]
    have hf := h.decap hp
    have hne := h.ne (by simp [hp])
    obtain ⟨hb, hio, had, ht1, hssx⟩ := hf
    refine ⟨fun _ => hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.late⟩ <;> intro hh
    all_goals first | (cases hh; done) | skip
    · exact ⟨⟨hb, hio, had, ht1, hssx⟩, rfl, k3, k2', rfl, by simp [ikSignSt, ikTh2, k3], rfl, rfl, rfl,
        by simp [ikSignSt, k3] at k4 ⊢; exact k4, rfl⟩
    · have := h.resFlag hh; rw [hp] at this; cases this
  · rw [c1]
    have hf := h.sign hp
    have hne := h.ne (by simp [hp])
    refine ⟨fun _ => hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.late⟩ <;> intro hh
    all_goals first | (cases hh; done) | skip
    · intro _; refine ⟨hf, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro hr; have := hf.1.1.2.2; have h2 : (ikDoneSt st s.1).resumed = false := this; rw [h2] at hr; cases hr
    · rfl
  · rw [c1]
    have hf := h.decap hp
    have hne := h.ne (by simp [hp])
    refine ⟨fun _ => hne, fun _ => hf.1, ?_, ?_, ?_, ?_, ?_, ?_, h.late⟩ <;> intro hh
    all_goals first | (cases hh; done) | skip
    · have := h.resFlag hh; rw [hp] at this; cases this

/-! ## The responder -/

/-- What a responder stored from the Initial it accepted. -/
def RInitM (n k : Nat) (st : RState) (m : Msg) : Prop :=
  m.ver = ok ∧ Served m.al ∧ rAd n m ≠ nil ∧ st.th0 = rT0 m ∧ st.hpk = rHpk m ∧ st.ek = rEk m ∧ st.ct = rC n k m ∧
    st.th1 = rT1 n k m ∧ st.th2 = rT2 n k m ∧ st.ath = st.th2 ∧ st.ck1 = rCk1 n k m ∧
    st.hsr = hs st.ck1 false st.th1 ∧ st.hsi = hs st.ck1 true st.th1 ∧ st.fresh = decide (m.form = .full) ∧
    st.resumed = false ∧ st.al = m.al ∧ st.ad = rAd n m ∧ st.dc = m.dc ∧ st.sc = m.sc ∧ st.pcr = m.cr ∧ st.rcr = nil

def RInit (n k : Nat) (st : RState) : Prop := ∃ m : Msg, RInitM n k st m

/-- After the responder signed its Reply. -/
def RFin (n k : Nat) (st : RState) : Prop := st.th3 = th3 st.th2 (sig n true st.th2) ∧ st.reply = rkReply st n k

/-- After the Finish verified: the initiator's transcript and the keys. -/
def RDone (st : RState) : Prop :=
  st.th4 = th4 st.th3 st.peer ∧ st.thf = th5 st.th4 (sig st.peer false st.th4) ∧
  st.send = app (ck2 st.ck1 st.thf) false st.thf ∧ st.recv = app (ck2 st.ck1 st.thf) true st.thf ∧
  st.res = res (ck2 st.ck1 st.thf) st.thf ∧ st.cid = cids (ck2 st.ck1 st.thf) st.thf

/-- After a resumption Hello was accepted: the Hello's transcript, the key of the ticket used, the keys and the Reply. -/
def RResDone (n k : Nat) (st : RState) : Prop :=
  ∃ p e, st.thh = thH ok st.al st.dc st.sc st.ad st.tid e st.pcr ∧
    st.thf = thR st.thh (binder p st.thh) (RCid n k) (pub (ry n k)) (RCr n) ∧ st.ath = st.thf ∧
    st.send = app (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) false st.thf ∧
    st.recv = app (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) true st.thf ∧
    st.res = res (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) st.thf ∧
    st.cid = cids (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) st.thf ∧
    st.early = early (ckpsk p) st.thh ∧ st.tpsk = p ∧ st.sgn = true ∧ st.resumed = true ∧
    st.reply.ty = .rreply ∧ st.reply.sc = RCid n k ∧ st.reply.e = pub (ry n k) ∧ st.reply.tids = st.mytids ∧
    st.reply.cr = RCr n ∧ st.reply.binder = nil ∧
    st.reply.conf = conf (cfk (ck2 (ck1r (ckpsk p) (Dh (ry n k) (atomOf e))) st.thf) st.thf)
      (thT st.thf (tlist st.mytids))

/-- The local clauses of a responder session `s`. -/
structure RCl (s : Nat × Nat) (st : RState) : Prop where
  ne : st.ph ≠ .idle → s.1 ≠ att
  idle : st.ph = .idle → st = {}
  sign : st.ph = .sign → RInit s.1 s.2 st
  signed : st.sgn = true → st.resumed = false → RInit s.1 s.2 st ∧ RFin s.1 s.2 st
  finish : st.ph = .finish → st.sgn = true ∧ RInit s.1 s.2 st ∧ RFin s.1 s.2 st
  doneSgn : st.ph = .done → st.sgn = true
  done : st.ph = .done → st.resumed = false → RDone st
  res : (st.ph = .resumed ∨ (st.ph = .done ∧ st.resumed = true)) → RResDone s.1 s.2 st
  resFlag : st.resumed = true → st.ph = .resumed ∨ st.ph = .done
  resPh : st.ph = .resumed → st.resumed = true

theorem RCl_none (s : Nat × Nat) : RCl s ({} : RState) :=
  ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem RCl_spent (s : Nat × Nat) (st : RState) (sp nr : Nat) (hp : st.ph = .resumed) (h : RCl s st) :
    RCl s { st with spent := sp, nre := nr } :=
  ⟨h.ne, fun hh => absurd (hp.symm.trans hh) (by decide), h.sign, h.signed, h.finish, h.doneSgn, h.done, h.res, h.resFlag, h.resPh⟩

theorem RCl_failed (s : Nat × Nat) (st : RState) (hs : s.1 ≠ att) (hnd : st.ph ≠ .done) (hnr : st.ph ≠ .resumed)
    (h : RCl s st) : RCl s { st with ph := .failed } := by
  refine ⟨fun _ => hs, ?_, ?_, h.signed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh
  · cases hh
  · cases hh
  · cases hh
  · cases hh
  · cases hh
  · rcases hh with hh | ⟨hh, -⟩ <;> cases hh
  · rcases h.resFlag hh with e | e
    · exact absurd e hnr
    · exact absurd e hnd
  · cases hh

theorem RCl_rkey (s : Nat × Nat) (st : RState) (sto : Store) (kind : KRes) (hs : s.1 ≠ att) (h : RCl s st) :
    RCl s (RKey st s.1 s.2 sto kind).st := by
  rcases RKey_cases st s.1 s.2 sto kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]; exact RCl_failed s st hs (by simp [hp]) (by simp [hp]) h
  · rw [c1]
    obtain ⟨m, hm⟩ := h.sign hp
    have hr0 : st.resumed = false := hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hI : RInit s.1 s.2 (rkSt st s.1 s.2) := ⟨m, by simpa [RInitM, rkSt] using hm⟩
    have hF : RFin s.1 s.2 (rkSt st s.1 s.2) := by simp [RFin, rkSt, rkReply, rkSig]
    refine ⟨fun _ => hs, ?_, ?_, fun _ _ => ⟨hI, hF⟩, fun _ => ⟨rfl, hI, hF⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; rcases hh with hh | ⟨hh, -⟩ <;> cases hh
    · intro hh
      have : (rkSt st s.1 s.2).resumed = false := hr0
      rw [this] at hh; cases hh
    · intro hh; cases hh

theorem RCl_rshed (s : Nat × Nat) (st : RState) (h : RCl s st) : RCl s (RShed st) := by
  by_cases hp : st.ph = .resumed
  · have hrd := h.res (Or.inl hp)
    have hres := h.resPh hp
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hrd
    have hrd : RResDone s.1 s.2 st := ⟨p, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    simp only [RShed, hp, ite_true]
    refine ⟨fun _ => h.ne (by simp [hp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hh; cases hh
    · intro hh; cases hh
    · intro _ hr; exact absurd (hres.symm.trans hr) (by decide)
    · intro hh; cases hh
    · intro _; exact h10
    · intro _ hr; exact absurd (hres.symm.trans hr) (by decide)
    · intro _; exact hrd
    · intro _; exact Or.inr rfl
    · intro hh; cases hh
  · simp only [RShed, hp, ite_false]; exact h

theorem RCl_rhandle (s : Nat × Nat) (st : RState) (sto : Store) (m : Msg) (cs : List (List Nat)) (hs : s.1 ≠ att)
    (h : RCl s st) : RCl s (RHandle st s.1 s.2 sto m cs).st := by
  rcases RHandle_cases st s.1 s.2 sto m cs with
      ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, ⟨sp, nr, c1⟩, -⟩ | ⟨hp, hty, c1, -⟩ | ⟨hp, hty, c1, -⟩
    | ⟨hp, hty, hv, hsv, had, c1, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, -⟩
    | ⟨hp, hty, hv, hsv, hu, c1, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]; exact RCl_failed s st hs (by rcases hp with hp | hp <;> simp [hp]) (by rcases hp with hp | hp <;> simp [hp]) h
  · rw [c1]; exact RCl_spent s st sp nr hp h
  · rw [c1]; exact h
  · rw [c1]; exact h
  · rw [c1]
    have h0 := h.idle hp
    refine ⟨fun _ => hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hh; cases hh
    · intro _
      refine ⟨m, hv, hsv, had, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
      · simp [rInitSt, h0]
      · simp [rInitSt, h0]
    · intro hh; simp [rInitSt, h0] at hh
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; rcases hh with hh | ⟨hh, -⟩ <;> cases hh
    · intro hh; simp [rInitSt, h0] at hh
    · intro hh; cases hh
  · rw [c1]
    obtain ⟨hsgn, hri, hfin⟩ := h.finish hp
    obtain ⟨m', hm⟩ := hri
    have hr0 : st.resumed = false := hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hI : RInit s.1 s.2 (rfSt st s.1 sto m cs) := ⟨m', by simpa [RInitM, rfSt] using hm⟩
    have hF : RFin s.1 s.2 (rfSt st s.1 sto m cs) := by
      obtain ⟨f1, f2⟩ := hfin
      simp [RFin, rfSt, rkReply, rkSig] at f1 f2 ⊢; exact ⟨f1, by simpa [rkReply, rkSig] using f2⟩
    refine ⟨fun _ => hs, ?_, ?_, fun _ _ => ⟨hI, hF⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; cases hh
    · intro _; simp [rfSt, hsgn]
    · intro _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [rfSt, rfT4]
      · simp [rfSt, rfT5, rfT4, hsg]
      · simp [rfSt, rfCk2, rfT5, rfT4]
      · simp [rfSt, rfCk2, rfT5, rfT4]
      · simp [rfSt, rfRes, rfCk2, rfT5, rfT4]
      · simp [rfSt, rfCk2, rfT5, rfT4]
    · intro hh
      rcases hh with hh | ⟨-, hr⟩
      · cases hh
      · have : (rfSt st s.1 sto m cs).resumed = false := hr0
        rw [this] at hr; cases hr
    · intro hh
      have : (rfSt st s.1 sto m cs).resumed = false := hr0
      rw [this] at hh; cases hh
    · intro hh; cases hh
  · rw [c1]; exact RCl_failed s st hs (by simp [hp]) (by simp [hp]) h
  · rw [c1]; exact h
  · rw [c1]
    have h0 := h.idle hp
    have hb : binder (rhSlot sto m).psk (rhThh m) = m.binder := hu.2.2.2.2
    have had' : (rhSlot sto m).ad = m.ad := hu.2.2.2.1
    refine ⟨fun _ => hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hh; cases hh
    · intro hh; cases hh
    · intro _ hr; simp [rhSt] at hr
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; cases hh
    · intro _
      refine ⟨(rhSlot sto m).psk, m.e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [rhSt, rhThh, hv, had']
      · simp [rhSt, rhThr, hb]
      all_goals simp [rhSt, rhReply, rhCk2, rhThr, hb]
    · intro _; exact Or.inl rfl
    · intro _; simp [rhSt]
  · rw [c1]; exact RCl_failed s st hs (by simp [hp]) (by simp [hp]) h

end Vinc.Hs
