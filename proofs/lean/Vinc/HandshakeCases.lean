import Vinc.HandshakeSys

/-!
# What each step function can answer

The case analysis of the step functions of `HandshakeModel`, stated once as disjunctions of explicit results, so the
invariant proofs of `HandshakeInv`, `HandshakeLocal` and the others reason over the few shapes a step can take.
-/

namespace Vinc.Hs
open Term

/-- The state `IBeginFull` returns for the fallback of a resumption that got a reject (a fresh destination id). -/
def rrFall (st : IState) (n : Nat) : IState :=
  { (IBeginFull n { st with late := NoLate } (atom 1 st.x.n st.x.k) (cid 2 n st.x.k) st.short st.thh).st with
    mode := .fallback, fell := true }

/-- The `IBeginFull` result of the fallback of an unanswered Hello. -/
def lateFallB (n : Nat) (st : IState) : IRes :=
  IBeginFull n { st with late := { on := true, x := st.x, thh := st.thh, binder := st.binder, ckpsk := st.ckpsk, rcr := st.rcr, ad := st.ad } } (atom 1 st.x.n st.x.k) st.dc st.short st.thh

/-- The state of the fallback of an unanswered Hello: a full Initial under the same destination id, the Hello kept as
the late context. -/
def lateFall (st : IState) (n : Nat) : IState :=
  { (lateFallB n st).st with mode := .fallback, fell := true }

theorem IHandle_cases (st : IState) (n : Nat) (m : Msg) :
    ((IHandle st n m).st = st ∧ (IHandle st n m).out = [])
    ∨ (st.ph = .reply ∧ m.ty = .reply ∧ InOffer st.of m.ad ∧
        (IHandle st n m).st = { st with ph := .decap, reply := m, ad := m.ad, th1 := th1 st.th0 m.sc m.ad m.e m.ct,
                                        ssx := Dh st.x (atomOf m.e) } ∧ (IHandle st n m).out = [])
    ∨ (st.ph = .reply ∧ (st.rgap = false ∨ m.gap = true) ∧ m.ty = .prej ∧ m.echo = st.th0 ∧
        (IHandle st n m).st = { st with rgap := true } ∧
        (IHandle st n m).out = [IInitMsg n st false])
    ∨ (st.ph = .resume ∧ m.ty = .rreply ∧ RrConfOK st.x st.ckpsk st.thh st.binder m ∧
        (IHandle st n m).st = IResumed st st.x st.ckpsk st.thh st.binder st.rcr st.ad m ∧ (IHandle st n m).out = [])
    ∨ ((st.ph = .reply ∨ st.ph = .decap ∨ st.ph = .sign) ∧ st.late.on = true ∧ m.ty = .rreply ∧
        RrConfOK st.late.x st.late.ckpsk st.late.thh st.late.binder m ∧
        (IHandle st n m).st = IResumed st st.late.x st.late.ckpsk st.late.thh st.late.binder st.late.rcr st.late.ad m ∧
        (IHandle st n m).out = [])
    ∨ (st.ph = .resume ∧ m.ty = .rrej ∧ m.echo = st.thh ∧ (IHandle st n m).st = rrFall st n
        ∧ (IHandle st n m).out = (IBeginFull n { st with late := NoLate } (atom 1 st.x.n st.x.k) (cid 2 n st.x.k) st.short st.thh).out) := by
  unfold IHandle
  by_cases hf : st.ph = .failed
  · left; simp [hf, Drop]
  · simp only [hf, ite_false]
    cases hty : m.ty
    · left; simp [Drop]
    · left; simp [Drop]
    · by_cases h1 : st.ph = .reply
      · by_cases h2 : m.echo = st.th0
        · by_cases hr : st.rgap = true
          · by_cases hg : m.gap = true
            · right; right; left; simp [h1, h2, hr, hg, Ok]
            · have hg' : m.gap = false := by simpa using hg
              left; simp [h1, h2, hr, hg', Ok]
          · have hr' : st.rgap = false := by simpa using hr
            right; right; left; simp [h1, h2, hr', Ok]
        · left; simp [h2, Drop]
      · left; simp [h1, Drop]
    · by_cases h1 : st.ph = .reply
      · by_cases h2 : InOffer st.of m.ad
        · right; left; simp [h1, h2, Ok]
        · left; simp [h1, h2, Drop]
      · left; simp [h1, Drop]
    · left; simp [Drop]
    · left; simp [Drop]
    · by_cases h1 : st.ph = .resume
      · by_cases h2 : RrConfOK st.x st.ckpsk st.thh st.binder m
        · right; right; right; left; simp [h1, h2, Ok]
        · left; simp [h1, h2, Drop]
      · by_cases h3 : (st.ph = .reply ∨ st.ph = .decap ∨ st.ph = .sign) ∧ st.late.on = true
        · by_cases h2 : RrConfOK st.late.x st.late.ckpsk st.late.thh st.late.binder m
          · right; right; right; right; left
            simp [h1, h3, h2, Ok]
          · left; simp [h1, h3, h2, Drop]
        · left; simp [h1, h3, Drop]
    · by_cases h1 : st.ph = .resume
      · by_cases h2 : m.echo = st.thh
        · right; right; right; right; right; simp [h1, h2, Ok, rrFall]
        · left; simp [h2, Drop]
      · left; simp [h1, Drop]
    
theorem IRetransmit_cases (n : Nat) (st : IState) :
    (st.ph = .reply ∧ st.short = true ∧ (IRetransmit n st).st = { st with sends := st.sends + 1 } ∧
      (IRetransmit n st).out = [IInitMsg n st (decide ((st.sends + 1) % 3 ≠ 0))])
    ∨ (st.ph = .resume ∧ st.sends + 1 < 3 ∧ (IRetransmit n st).st = { st with sends := st.sends + 1 } ∧
      (IRetransmit n st).out = [IHello st])
    ∨ (st.ph = .resume ∧ 3 ≤ st.sends + 1 ∧ (IRetransmit n st).st = lateFall st n ∧
      (IRetransmit n st).out = (lateFallB n st).out)
    ∨ ((IRetransmit n st).st = st ∧
      ((IRetransmit n st).out = [] ∨ (IRetransmit n st).out = [IInitMsg n st false] ∨
        (st.ph = .done ∧ st.fin ≠ {} ∧ (IRetransmit n st).out = [st.fin]))) := by
  unfold IRetransmit
  by_cases h1 : st.ph = .reply ∧ st.short = true
  · left; simp [h1, Ok]
  · by_cases h2 : st.ph = .resume
    · by_cases h3 : st.sends + 1 ≥ 3
      · right; right; left; simp [h1, h2, h3, Ok, lateFall, lateFallB]
      · right; left; simp [h1, h2, h3, Ok]; omega
    · right; right; right
      by_cases h4 : st.ph = .reply
      · have hs : st.short ≠ true := fun e => h1 ⟨h4, e⟩
        simp [h1, h2, h4, hs, Ok]
      · by_cases h5 : st.ph = .done ∧ st.fin ≠ {}
        · simp [h1, h2, h4, h5, Ok]
        · simp [h1, h2, h4, h5, Ok]

theorem IKey_cases (st : IState) (n : Nat) (kind : KRes) :
    ((IKey st n kind).st = st ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = [])
    ∨ ((st.ph = .decap ∨ st.ph = .sign) ∧ (IKey st n kind).st = { st with ph := .failed } ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = [])
    ∨ (st.ph = .decap ∧ kind = .ok ∧ st.reply.sealed.k = hs (ikCk1 st n) false st.th1 ∧ st.reply.sealed.ad = st.th1
        ∧ st.reply.sealed.cr ≠ nil
        ∧ st.reply.sealed.id = st.peer ∧ st.reply.sealed.sig = sig st.reply.sealed.id true (ikTh2 st)
        ∧ (IKey st n kind).st = ikSignSt st n
        ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = [])
    ∨ (st.ph = .sign ∧ kind = .ok ∧
        (IKey st n kind).st = ikDoneSt st n
        ∧ (IKey st n kind).out = [ikFin st n]
        ∧ (IKey st n kind).sg = [⟨n, false, st.th4⟩])
    ∨ (st.ph = .decap ∧ kind = .ok ∧ ¬ ikAuth st n
        ∧ (IKey st n kind).st = ikBackSt st ∧ (IKey st n kind).out = [] ∧ (IKey st n kind).sg = []) := by
  unfold IKey
  by_cases h1 : st.ph = .decap ∧ kind = .ok
  · obtain ⟨hp, hk⟩ := h1
    simp only [hp, hk, and_self, ite_true]
    by_cases ca : ikAuth st n
    · right; right; left
      obtain ⟨c1, c2, c3, c4, c5⟩ := ca
      simp [ikAuth, c1, c2, c3, c4, c5, Ok, hp]
    · right; right; right; right
      simp [ca, ikBackSt, hp]
  · by_cases h2 : st.ph = .sign ∧ kind = .ok
    · obtain ⟨hp, hk⟩ := h2
      right; right; right; left; simp [hp, hk]
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
  · right; right; simp [h1]
  · by_cases h2 : st.ph = .sign ∧ kind = .fail
    · right; left; simp [h1, h2, RFatal]
    · left; simp [h1, h2, RDrop]

theorem RRepeat_cases (st : RState) (sto : Store) (m : Msg) :
    (∃ sp nr, (RRepeat st sto m).st = { st with spent := sp, nre := nr })
    ∧ ((RRepeat st sto m).out = [] ∨ (RRepeat st sto m).out = [st.reply])
    ∧ (RRepeat st sto m).sto = sto ∧ (RRepeat st sto m).iss = [] ∧ (RRepeat st sto m).sg = [] := by
  unfold RRepeat
  dsimp only
  split
  · exact ⟨⟨_, st.nre, rfl⟩, Or.inl rfl, rfl, rfl, rfl⟩
  · exact ⟨⟨_, _, rfl⟩, Or.inr rfl, rfl, rfl, rfl⟩

theorem RHandle_cases (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    ((RHandle st n k sto m cs).st = st ∧ (RHandle st n k sto m cs).out = [] ∧ (RHandle st n k sto m cs).sto = sto
      ∧ (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sg = [])
    ∨ ((st.ph = .idle ∨ st.ph = .finish) ∧ (RHandle st n k sto m cs).st = { st with ph := .failed }
      ∧ (RHandle st n k sto m cs).out = [] ∧ (RHandle st n k sto m cs).sto = sto
      ∧ (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .resumed ∧ (∃ sp nr, (RHandle st n k sto m cs).st = { st with spent := sp, nre := nr })
      ∧ ((RHandle st n k sto m cs).out = [] ∨ (RHandle st n k sto m cs).out = [st.reply])
      ∧ (RHandle st n k sto m cs).sto = sto ∧ (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .finish ∧ m.ty = .init ∧ (RHandle st n k sto m cs).st = st ∧ (RHandle st n k sto m cs).out = [st.reply]
      ∧ (RHandle st n k sto m cs).sto = sto ∧ (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .init ∧ (RHandle st n k sto m cs).st = st
      ∧ (RHandle st n k sto m cs).out = [{ ty := .prej, echo := rT0 m }]
      ∧ (RHandle st n k sto m cs).sto = sto ∧ (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .init ∧ m.ver = ok ∧ Served m.al ∧ rAd n m ≠ nil
      ∧ (RHandle st n k sto m cs).st = rInitSt st n k m
      ∧ (RHandle st n k sto m cs).out = [] ∧ (RHandle st n k sto m cs).sto = sto ∧ (RHandle st n k sto m cs).iss = []
      ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .finish ∧ m.ty = .fin ∧ st.hsi = m.sealed.k ∧ st.th3 = m.sealed.ad
        ∧ m.sealed.sig = sig m.sealed.id false (rfT4 st m) ∧ (rfIs st n sto m cs).ok = true
      ∧ (RHandle st n k sto m cs).st = rfSt st n sto m cs ∧ (RHandle st n k sto m cs).out = []
      ∧ (RHandle st n k sto m cs).sto = rfSto2 st n sto m cs
      ∧ (RHandle st n k sto m cs).iss = rfIss st n sto m cs
      ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .finish ∧ m.ty = .fin ∧ st.hsi = m.sealed.k ∧ st.th3 = m.sealed.ad
        ∧ m.sealed.sig = sig m.sealed.id false (rfT4 st m) ∧ (rfIs st n sto m cs).ok = false
      ∧ (RHandle st n k sto m cs).st = { st with ph := .failed } ∧ (RHandle st n k sto m cs).out = []
      ∧ (RHandle st n k sto m cs).sto = rfSto1 st n sto m cs
      ∧ (RHandle st n k sto m cs).iss = rfIss st n sto m cs
      ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .hello ∧ m.ver = ok ∧ Served m.al ∧ ¬ rhUsable sto m ∧ (RHandle st n k sto m cs).st = st
      ∧ (RHandle st n k sto m cs).out = [{ ty := .rrej, echo := rhThh m }]
      ∧ (RHandle st n k sto m cs).sto = rhStoRej sto m
      ∧ (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .hello ∧ m.ver = ok ∧ Served m.al ∧ rhUsable sto m ∧ (rhIs n k sto m cs).ok = true
        ∧ (RHandle st n k sto m cs).st = rhSt st n k sto m cs
        ∧ (RHandle st n k sto m cs).out = [rhReply n k sto m cs]
        ∧ (RHandle st n k sto m cs).sto = rhSto1 n k sto m cs
        ∧ (RHandle st n k sto m cs).iss = rhIss n k sto m cs
        ∧ (RHandle st n k sto m cs).sg = [])
    ∨ (st.ph = .idle ∧ m.ty = .hello ∧ m.ver = ok ∧ Served m.al ∧ rhUsable sto m ∧ (rhIs n k sto m cs).ok = false
        ∧ (RHandle st n k sto m cs).st = { st with ph := .failed }
        ∧ (RHandle st n k sto m cs).out = []
        ∧ (RHandle st n k sto m cs).sto = rhSto1 n k sto m cs
        ∧ (RHandle st n k sto m cs).iss = rhIss n k sto m cs
        ∧ (RHandle st n k sto m cs).sg = []) := by
  unfold RHandle
  by_cases hf : st.ph = .failed
  · left; simp [hf, RDrop]
  · simp only [hf, ite_false]
    cases hty : m.ty
    all_goals (try (left; simp [RDrop]; done))
    · simp only [RInitial]
      by_cases h1 : st.ph = .finish
      · by_cases h2 : st.th0 = rT0 m
        · right; right; right; left; simp [h1, h2, ROk, hty]
        · left; simp [h1, h2, RDrop]
      · by_cases h2 : st.ph = .resumed
        · by_cases h3 : st.dc = m.dc ∧ st.sc = m.sc
          · right; right; left
            refine ⟨h2, ?_⟩
            by_cases h4 : st.reply.len ≤ 3 * m.len ∧ st.spent + m.len ≤ LB
            · exact ⟨⟨st.spent + m.len, st.nre + 1, by simp [h1, h2, h3, h4, ROk]⟩, Or.inr (by simp [h1, h2, h3, h4, ROk]), by simp [h1, h2, h3, h4, ROk], by simp [h1, h2, h3, h4, ROk], by simp [h1, h2, h3, h4, ROk]⟩
            · exact ⟨⟨st.spent + m.len, st.nre, by simp [h1, h2, h3, h4, ROk]⟩, Or.inl (by simp [h1, h2, h3, h4, ROk]), by simp [h1, h2, h3, h4, ROk], by simp [h1, h2, h3, h4, ROk], by simp [h1, h2, h3, h4, ROk]⟩
          · left; simp [h1, h2, h3, RDrop]
        · by_cases h3 : st.ph = .idle
          · by_cases h4 : m.ver = ok
            · by_cases h5 : Served m.al
              · by_cases h6 : rAd n m = nil
                · right; left; simp [h1, h2, h3, h4, h5, h6, RFatal]
                · by_cases h7 : m.form = .short ∧ rHpk m ∉ sto.pkc
                  · right; right; right; right; left; simp [h1, h2, h3, h4, h5, h6, h7, ROk, hty]
                  · right; right; right; right; right; left; simp [h1, h2, h3, h4, h5, h6, h7, ROk, hty]
              · right; left; simp [h1, h2, h3, h4, h5, RFatal]
            · right; left; simp [h1, h2, h3, h4, RFatal]
          · left; simp [h1, h2, h3, RDrop]
    · simp only [RFinish]
      by_cases h1 : st.ph = .finish
      · by_cases h2 : st.hsi = m.sealed.k ∧ st.th3 = m.sealed.ad
        · by_cases h3 : m.sealed.sig = sig m.sealed.id false (rfT4 st m)
          · by_cases h4 : (rfIs st n sto m cs).ok = true
            · right; right; right; right; right; right; left
              simp [h1, h2, h3, h4, hty]
            · right; right; right; right; right; right; right; left
              have h4' : (rfIs st n sto m cs).ok = false := by simpa using h4
              simp [h1, h2, h3, h4', hty]
          · right; left; simp [h1, h3, RFatal, h2]
        · left
          have : m.sealed.k ≠ st.hsi ∨ m.sealed.ad ≠ st.th3 := by
            by_cases hh : m.sealed.k = st.hsi
            · exact Or.inr (fun x => h2 ⟨hh.symm, x.symm⟩)
            · exact Or.inl hh
          simp [h1, this, RDrop]
      · left; simp [h1, RDrop]
    · by_cases h2 : st.ph = .resumed
      · right; right; left
        have hr : RHello st n k sto m cs = RRepeat st sto m := by simp [RHello, h2, hf]
        rw [hr]
        exact ⟨h2, RRepeat_cases st sto m⟩
      · simp only [RHello]
        by_cases h3 : st.ph = .idle
        · by_cases h4 : m.ver = ok
          · by_cases h5 : Served m.al
            · by_cases h6 : rhUsable sto m
              · by_cases h7 : (rhIs n k sto m cs).ok = false
                · right; right; right; right; right; right; right; right; right; right
                  simp [h2, h3, h4, h5, h6, h7, hty]
                · right; right; right; right; right; right; right; right; right; left
                  have h7' : (rhIs n k sto m cs).ok = true := by simpa using h7
                  simp [h2, h3, h4, h5, h6, h7', hty]
              · right; right; right; right; right; right; right; right; left
                simp [h2, h3, h4, h5, h6, hty, ROk]
            · right; left; simp [h2, h3, h4, h5, RFatal]
          · right; left; simp [h2, h3, h4, RFatal]
        · left; simp [h2, h3, RDrop]

end Vinc.Hs
