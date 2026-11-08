import Vinc.HandshakeSys

/-!
# What each step function can answer

The case analysis of the step functions of `HandshakeModel`, stated once as disjunctions of explicit results, so the
invariant proofs of `HandshakeInv` reason over the few shapes a step can take.
-/

namespace Vinc.Hs
open Term

theorem IHandle_cases (st : IState) (n : Nat) (m : Msg) :
    ((IHandle st n m).st = st ∧ (IHandle st n m).out = [])
    ∨ ((st.ph = .reply ∨ st.ph = .resume) ∧ (IHandle st n m).st = { st with ph := .failed } ∧ (IHandle st n m).out = [])
    ∨ (st.ph = .reply ∧ m.ty = .reply ∧ m.rprm = ok ∧
        (IHandle st n m).st = { st with ph := .decap, reply := m, th1 := th1 st.th0 m.rprm m.e m.ct,
                                        ssx := Dh st.x (atomOf m.e) } ∧ (IHandle st n m).out = [])
    ∨ (st.ph = .reply ∧ st.short = true ∧ m.ty = .prej ∧ m.echo = st.th0 ∧
        (IHandle st n m).st = { st with short := false } ∧
        (IHandle st n m).out = [{ ty := .init, form := .full, e := pub st.x, pk := ek n }])
    ∨ (st.ph = .resume ∧ m.ty = .rreply ∧ (IHandle st n m).st = rrDone st m ∧ (IHandle st n m).out = []
        ∧ m.conf = conf (cfk (rrCk2 st m) (rrThr st m)) (thT (rrThr st m) m.tids))
    ∨ (st.ph = .resume ∧ m.ty = .rrej ∧ m.echo = st.thh ∧ (IHandle st n m).st = rrFall st n
        ∧ (IHandle st n m).out = (IBeginFull n (atom 1 st.x.n st.x.k) st.peer false st.thh nil).out) := by
  unfold IHandle
  by_cases hf : st.ph = .failed
  · left; simp [hf, Drop]
  · simp only [hf, ite_false]
    cases hty : m.ty
    · left; simp [Drop]
    · left; simp [Drop]
    · by_cases h1 : st.ph = .reply ∧ st.short = true
      · by_cases h2 : m.echo = st.th0
        · right; right; right; left; simp [h1, h2, Ok, hty]
        · left; simp [h2, Drop]
      · left; simp [h1, hty, Drop]
    · by_cases h1 : st.ph = .reply
      · by_cases h2 : m.rprm = ok
        · right; right; left; simp [h1, h2, Ok, hty]
        · right; left; simp [h1, h2, Fatal]
      · left; simp [h1, Drop]
    · left; simp [Drop]
    · left; simp [Drop]
    · by_cases h1 : st.ph = .resume
      · by_cases h2 : m.conf = conf (cfk (rrCk2 st m) (rrThr st m)) (thT (rrThr st m) m.tids)
        · right; right; right; right; left; simp [h1, h2, Ok, hty, rrDone, rrCk2, rrThr]
        · right; left; simp [h1, rrCk2, rrThr] at h2 ⊢; simp [h2, Fatal]
      · left; simp [h1, Drop]
    · by_cases h1 : st.ph = .resume
      · by_cases h2 : m.echo = st.thh
        · right; right; right; right; right; simp [h1, h2, Ok, hty, rrFall]
        · left; simp [h2, Drop]
      · left; simp [h1, Drop]



theorem IKey_cases (st : IState) (n : Nat) (kind : KRes) :
    ((IKey st n kind).st = st ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = [])
    ∨ ((st.ph = .decap ∨ st.ph = .sign) ∧ (IKey st n kind).st = { st with ph := .failed } ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = [])
    ∨ (st.ph = .decap ∧ kind = .ok ∧ st.reply.sealed.k = hs (ikCk1 st n) false st.th1 ∧ st.reply.sealed.ad = st.th1
        ∧ st.reply.sealed.id = st.peer ∧ st.reply.sealed.sig = sig st.reply.sealed.id true (th2 st.th1 st.reply.sealed.id)
        ∧ (IKey st n kind).st = ikSignSt st n
        ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = [])
    ∨ (st.ph = .sign ∧ kind = .ok ∧
        (IKey st n kind).st = ikDoneSt st n
        ∧ (IKey st n kind).out = [{ ty := .fin, sealed := ⟨st.hsi, st.th3, n, ikSig st n⟩ }]
        ∧ (IKey st n kind).sg = [⟨n, false, st.th4⟩]) := by
  unfold IKey
  by_cases h1 : st.ph = .decap ∧ kind = .ok
  · obtain ⟨hp, hk⟩ := h1
    simp only [hp, hk, and_self, ite_true]
    by_cases ca : st.reply.sealed.k = hs (ikCk1 st n) false st.th1
    · by_cases cb : st.reply.sealed.ad = st.th1
      · by_cases c2 : st.reply.sealed.id = st.peer
        · by_cases c3 : st.reply.sealed.sig = sig st.reply.sealed.id true (th2 st.th1 st.reply.sealed.id)
          · right; right; left
            simp [ca, cb, c2, c3, Ok, hp, ikSignSt, ikCk1, ikSsk]
          · right; left; simp [ikCk1, ikSsk] at ca; rw [c2] at c3; simp [ca, cb, c2, c3, Fatal, ikCk1, ikSsk]
        · right; left; simp [ikCk1, ikSsk] at ca; simp [ca, cb, c2, Fatal, ikCk1, ikSsk]
      · right; left; simp [ikCk1, ikSsk] at ca; simp [ca, cb, Fatal, ikCk1, ikSsk]
    · right; left; simp [ikCk1, ikSsk] at ca; simp [ca, Fatal, ikCk1, ikSsk]
  · by_cases h2 : st.ph = .sign ∧ kind = .ok
    · obtain ⟨hp, hk⟩ := h2
      right; right; right; simp [hp, hk, ikDoneSt, ikCk2, ikT5, ikSig]
    · by_cases h3 : (st.ph = .decap ∨ st.ph = .sign) ∧ kind = .fail
      · right; left; simp [h1, h2, h3, Fatal]
      · left; simp [h1, h2, h3, Drop]



/-! ## The responder -/

theorem RKey_cases (st : RState) (n k : Nat) (sto : Store) (kind : KRes) :
    ((RKey st n k sto kind).st = st ∧ (RKey st n k sto kind).out = [] ∧ (RKey st n k sto kind).sg = []
      ∧ (RKey st n k sto kind).sto = sto ∧ (RKey st n k sto kind).iss = [])
    ∨ (st.ph = .sign ∧ (RKey st n k sto kind).st = { st with ph := .failed } ∧ (RKey st n k sto kind).out = []
      ∧ (RKey st n k sto kind).sg = [] ∧ (RKey st n k sto kind).sto = sto ∧ (RKey st n k sto kind).iss = [])
    ∨ (st.ph = .sign ∧ kind = .ok ∧
        (RKey st n k sto kind).st = rkSt st n k
        ∧ (RKey st n k sto kind).out = [rkReply st n k]
        ∧ (RKey st n k sto kind).sg = [⟨n, true, st.th2⟩] ∧ (RKey st n k sto kind).sto = sto
        ∧ (RKey st n k sto kind).iss = []) := by
  unfold RKey
  by_cases h1 : st.ph = .sign ∧ kind = .ok
  · right; right; simp [h1, rkSt, rkReply, rkSig]
  · by_cases h2 : st.ph = .sign ∧ kind = .fail
    · right; left; simp [h1, h2, RFatal]
    · left; simp [h1, h2, RDrop]

theorem RHandle_cases (st : RState) (n k : Nat) (sto : Store) (m : Msg) :
    ((RHandle st n k sto m).st = st ∧ (RHandle st n k sto m).out = [] ∧ (RHandle st n k sto m).sto = sto
      ∧ (RHandle st n k sto m).iss = [] ∧ (RHandle st n k sto m).sg = [])
    ∨ ((st.ph = .idle ∨ st.ph = .finish) ∧ (RHandle st n k sto m).st = { st with ph := .failed } ∧ (RHandle st n k sto m).out = []
      ∧ (RHandle st n k sto m).sto = sto ∧ (RHandle st n k sto m).iss = [] ∧ (RHandle st n k sto m).sg = [])
    ∨ (st.ph = .finish ∧ m.ty = .init ∧ (RHandle st n k sto m).st = st ∧ (RHandle st n k sto m).out = [st.reply]
      ∧ (RHandle st n k sto m).sto = sto ∧ (RHandle st n k sto m).iss = [] ∧ (RHandle st n k sto m).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .init ∧ (RHandle st n k sto m).st = st
      ∧ (RHandle st n k sto m).out = [{ ty := .prej, echo := rT0 m }]
      ∧ (RHandle st n k sto m).sto = sto ∧ (RHandle st n k sto m).iss = [] ∧ (RHandle st n k sto m).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .init ∧ m.prm = ok ∧ (RHandle st n k sto m).st = rInitSt st n k m
      ∧ (RHandle st n k sto m).out = [] ∧ (RHandle st n k sto m).sto = sto ∧ (RHandle st n k sto m).iss = []
      ∧ (RHandle st n k sto m).sg = [])
    ∨ (st.ph = .finish ∧ m.ty = .fin ∧ st.hsi = m.sealed.k ∧ st.th3 = m.sealed.ad
        ∧ m.sealed.sig = sig m.sealed.id false (rfT4 st m)
      ∧ (RHandle st n k sto m).st = rfSt st n k m ∧ (RHandle st n k sto m).out = []
      ∧ (RHandle st n k sto m).sto = rfSto st n k sto m
      ∧ (RHandle st n k sto m).iss = [⟨tid n k, psk (rfRes st m) (tid n k), m.sealed.id⟩]
      ∧ (RHandle st n k sto m).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .hello ∧ m.prm = ok ∧ (RHandle st n k sto m).st = st
      ∧ (RHandle st n k sto m).out = [{ ty := .rrej, echo := rhThh m }]
      ∧ (RHandle st n k sto m).iss = [] ∧ (RHandle st n k sto m).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .hello ∧ m.prm = ok ∧ ∃ i0 : Nat,
        (sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid)) = some i0
        ∧ (rhSlot sto i0).exp = false ∧ binder (rhSlot sto i0).psk (rhThh m) = m.binder
        ∧ (RHandle st n k sto m).st = rhSt st n k sto i0 m
        ∧ (RHandle st n k sto m).out = [rhMsg n k sto i0 m]
        ∧ (RHandle st n k sto m).sto = rhSto n k sto i0 m
        ∧ (RHandle st n k sto m).iss = [⟨tid n k, psk (res (rhCk2 n k sto i0 m) (rhThr n k m)) (tid n k), (rhSlot sto i0).peer⟩]
        ∧ (RHandle st n k sto m).sg = []) := by
  unfold RHandle
  by_cases hf : st.ph = .failed
  · left; simp [hf, RDrop]
  · simp only [hf, ite_false]
    cases hty : m.ty
    all_goals (try (left; simp [RDrop]; done))
    · simp only [RInitial]
      repeat' split
      all_goals (simp_all [RDrop, RFatal, ROk])
    · simp only [RFinish]
      repeat' split
      all_goals (simp_all [RDrop, RFatal])
    · simp only [RHello]
      generalize sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid) = fd
      cases fd with
      | none =>
        repeat' split
        all_goals (simp_all [RDrop, RFatal, ROk])
      | some i0 =>
        repeat' split
        all_goals (simp_all [RDrop, RFatal, ROk])

end Vinc.Hs
