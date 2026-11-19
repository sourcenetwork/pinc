import Pinc.HandshakeCases

/-!
# Authentication of the full handshake, for unboundedly many sessions

Inductive invariants of the system of `HandshakeSys` (any number of honest nodes, sessions and tickets, any store
capacity, the Dolev-Yao attacker `Derivable`), proved over every reachable state.
-/

namespace Pinc.Hs
open Term

/-- The invariant of the signature ledger and of the sessions that sign. -/
structure Inv1 (g : G) : Prop where
  netSigned : ∀ m, g.net m → ∀ id r th, m.sealed.sig = Term.sig id r th → g.signed id r th
  signedResp : ∀ id th, g.signed id true th →
    ∃ k, (g.rst (id, k)).sgn = true ∧ (g.rst (id, k)).th2 = th ∧ (g.rst (id, k)).ath = th
  signedInit : ∀ id th, g.signed id false th →
    ∃ k, (g.ist (id, k)).ph = .done ∧ (g.ist (id, k)).th4 = th ∧ (g.ist (id, k)).resumed = false
  decapGood : ∀ s, (g.ist s).ph = .decap → SigGood g (g.ist s).reply.sealed
  iAuth : ∀ s, ((g.ist s).ph = .sign ∨ (g.ist s).ph = .done) → (g.ist s).resumed = false → (g.ist s).peer ≠ att →
    ∃ k, (g.rst ((g.ist s).peer, k)).sgn = true ∧ (g.rst ((g.ist s).peer, k)).ath = (g.ist s).ath
  rAuth : ∀ s, (g.rst s).ph = .done → (g.rst s).resumed = false → (g.rst s).peer ≠ att →
    ∃ k, (g.ist ((g.rst s).peer, k)).ph = .done ∧ (g.ist ((g.rst s).peer, k)).th4 = (g.rst s).th4
      ∧ (g.ist ((g.rst s).peer, k)).resumed = false
  rIdle : ∀ s, (g.rst s).ph = .idle → g.rst s = {}
  rSign : ∀ s, (g.rst s).ph = .sign → (g.rst s).sgn = false ∧ (g.rst s).ath = (g.rst s).th2
  rFinish : ∀ s, ((g.rst s).ph = .finish ∨ (g.rst s).ph = .resumed) → g.net (g.rst s).reply
  iFin : ∀ s, (g.ist s).fin ≠ {} → g.net (g.ist s).fin
  iRes : ∀ s, (g.ist s).resumed = true → (g.ist s).ph = .done
  rRes : ∀ s, (g.rst s).ph = .resumed → (g.rst s).resumed = true

theorem Inv1_init (K C : Nat) : Inv1 (G0 K C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [G0]

/-- The message has no signature on its blob. -/
def NoSig (m : Msg) : Prop := ∀ id r th, m.sealed.sig ≠ Term.sig id r th

theorem NoSig_default (m : Msg) (h : m.sealed = BadBlob) : NoSig m := by
  intro id r th; simp [h, BadBlob]

theorem SigGood_mono {g g' : G} (h : ∀ id r th, g.signed id r th → g'.signed id r th) {b : Blob}
    (hb : SigGood g b) : SigGood g' b := fun id r th e => (hb id r th e).elim Or.inl (fun x => Or.inr (h id r th x))

theorem NoSig_IInitMsg (n : Nat) (st : IState) (b : Bool) : NoSig (IInitMsg n st b) :=
  NoSig_default _ rfl

theorem NoSig_IHello (st : IState) : NoSig (IHello st) := NoSig_default _ rfl

theorem IBeginFull_props (n : Nat) (st0 : IState) (x : Atom) (dcid : Term) (short : Bool) (thh : Term) :
    (IBeginFull n st0 x dcid short thh).st.ph = .reply ∧ (IBeginFull n st0 x dcid short thh).st.resumed = st0.resumed
    ∧ (IBeginFull n st0 x dcid short thh).st.fin = st0.fin
    ∧ ∀ m ∈ (IBeginFull n st0 x dcid short thh).out, NoSig m := by
  refine ⟨by simp [IBeginFull, Ok], by simp [IBeginFull, Ok], by simp [IBeginFull, Ok], ?_⟩
  intro m hm; simp [IBeginFull, Ok] at hm; subst hm; exact NoSig_IInitMsg _ _ _

theorem INew_props (n k peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) :
    ((INew n k peer al short tk).st.ph = .reply ∨ (INew n k peer al short tk).st.ph = .resume)
    ∧ (INew n k peer al short tk).st.resumed = false ∧ (INew n k peer al short tk).st.fin = {}
    ∧ ∀ m ∈ (INew n k peer al short tk).out, NoSig m := by
  unfold INew
  cases tk with
  | none =>
    obtain ⟨a, b, c, d⟩ := IBeginFull_props n { peer := peer, al := al, sc := cid 0 n k, of := off n, cr := crd n }
      (atom 0 n k) (cid 1 n k) short nil
    exact ⟨Or.inl a, b, c, d⟩
  | some t =>
    refine ⟨Or.inr (by simp [IBeginResume, Ok]), by simp [IBeginResume, Ok], by simp [IBeginResume, Ok], ?_⟩
    intro m hm; simp [IBeginResume, Ok] at hm; subst hm; exact NoSig_default _ rfl

/-- An update of one initiator session that is not a finished one, whose new state satisfies the session clauses. -/
theorem upd_inv0 {g : G} (h : Inv1 g) (s : Nat × Nat) (st' : IState) (out : List Msg)
    (hold : (g.ist s).ph ≠ .done)
    (hdec : st'.ph = .decap → SigGood g st'.reply.sealed)
    (hauth : (st'.ph = .sign ∨ st'.ph = .done) → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.rst (st'.peer, k)).sgn = true ∧ (g.rst (st'.peer, k)).ath = st'.ath)
    (hfin : st'.fin ≠ {} → g.net st'.fin)
    (hres : st'.resumed = true → st'.ph = .done)
    (hout : ∀ m ∈ out, NoSig m) :
    Inv1 { g with ist := upd g.ist s st', net := addNet g out } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm id r th e
    rcases hm with hm | hm
    · exact h.netSigned m hm id r th e
    · exact absurd e (hout m hm id r th)
  · intro id th hs; exact h.signedResp id th hs
  · intro id th hs
    obtain ⟨k, hk1, hk2, hk3⟩ := h.signedInit id th hs
    have hk : (id, k) ≠ s := fun e => hold (e ▸ hk1)
    refine ⟨k, ?_, ?_, ?_⟩ <;> simp [upd, hk, hk1, hk2, hk3]
  · intro s' hs'
    by_cases hh : s' = s
    · subst hh; simp only [upd_same] at hs'; simp only [upd_same]; exact hdec hs'
    · simp only [upd_ne _ _ _ _ hh] at hs' ⊢; exact SigGood_mono (fun _ _ _ x => x) (h.decapGood s' hs')
  · intro s' hs' hr hp
    by_cases hh : s' = s
    · subst hh; simp only [upd_same] at *; exact hauth hs' hr hp
    · simp only [upd_ne _ _ _ _ hh] at *; exact h.iAuth s' hs' hr hp
  · intro s' hd hr hp
    obtain ⟨k, hk1, hk2, hk3⟩ := h.rAuth s' hd hr hp
    have hk : ((g.rst s').peer, k) ≠ s := fun e => hold (e ▸ hk1)
    refine ⟨k, ?_, ?_, ?_⟩ <;> simp [upd, hk, hk1, hk2, hk3]
  · exact h.rIdle
  · exact h.rSign
  · intro s' hf; exact Or.inl (h.rFinish s' hf)
  · intro s' hf
    by_cases hh : s' = s
    · subst hh; simp only [upd_same] at *; exact Or.inl (hfin hf)
    · simp only [upd_ne _ _ _ _ hh] at *; exact Or.inl (h.iFin s' hf)
  · intro s' hr
    by_cases hh : s' = s
    · subst hh; simp only [upd_same] at *; exact hres hr
    · simp only [upd_ne _ _ _ _ hh] at *; exact h.iRes s' hr
  · exact h.rRes

theorem Inv1_congr {g g' : G} (hi : g'.ist = g.ist) (hr : g'.rst = g.rst) (hn : g'.net = g.net)
    (hs : g'.signed = g.signed) : Inv1 g' ↔ Inv1 g := by
  cases g; cases g'; simp only at hi hr hn hs; subst hi hr hn hs
  exact ⟨fun h => ⟨h.netSigned, h.signedResp, h.signedInit, h.decapGood, h.iAuth, h.rAuth, h.rIdle, h.rSign, h.rFinish,
      h.iFin, h.iRes, h.rRes⟩,
    fun h => ⟨h.netSigned, h.signedResp, h.signedInit, h.decapGood, h.iAuth, h.rAuth, h.rIdle, h.rSign, h.rFinish,
      h.iFin, h.iRes, h.rRes⟩⟩

theorem upd_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : IState) (out : List Msg)
    (hist : g'.ist = upd g.ist s st') (hnet : g'.net = addNet g out) (hrst : g'.rst = g.rst)
    (hsig : g'.signed = g.signed)
    (hold : (g.ist s).ph ≠ .done)
    (hdec : st'.ph = .decap → SigGood g st'.reply.sealed)
    (hauth : (st'.ph = .sign ∨ st'.ph = .done) → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.rst (st'.peer, k)).sgn = true ∧ (g.rst (st'.peer, k)).ath = st'.ath)
    (hfin : st'.fin ≠ {} → g.net st'.fin)
    (hres : st'.resumed = true → st'.ph = .done)
    (hout : ∀ m ∈ out, NoSig m) : Inv1 g' :=
  (Inv1_congr (g := { g with ist := upd g.ist s st', net := addNet g out }) hist hrst hnet hsig).2
    (upd_inv0 h s st' out hold hdec hauth hfin hres hout)

theorem derivable_sig {kn : Term → Prop} {g : G} (h : Inv1 g) {m : Msg} (hm : DerivableK kn g m) : SigGood g m.sealed := by
  rcases hm with hm | ⟨hs, -⟩
  · exact fun id r th e => Or.inr (h.netSigned m hm id r th e)
  · exact hs

theorem addNet_nil (g : G) : addNet g [] = g.net := by
  funext m; simp [addNet]

theorem upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) : upd f a (f a) = f := by
  funext x; by_cases h : x = a <;> simp [upd, h]

/-- The sessions are changed only in fields the clauses do not read (the output messages carry no signature, or are
already on the network). -/
theorem Inv1_ist_frame {g g' : G} (h : Inv1 g) (out : List Msg)
    (hI : ∀ s, (g'.ist s).ph = (g.ist s).ph ∧ (g'.ist s).th4 = (g.ist s).th4 ∧ (g'.ist s).resumed = (g.ist s).resumed
      ∧ (g'.ist s).peer = (g.ist s).peer ∧ (g'.ist s).ath = (g.ist s).ath ∧ (g'.ist s).reply = (g.ist s).reply
      ∧ ((g'.ist s).fin ≠ {} → (g'.ist s).fin = (g.ist s).fin))
    (hrst : g'.rst = g.rst) (hnet : g'.net = addNet g out) (hsig : g'.signed = g.signed)
    (hout : ∀ m ∈ out, NoSig m ∨ g.net m) : Inv1 g' := by
  have hn' : ∀ m, g.net m → g'.net m := fun m hm => by rw [hnet]; exact Or.inl hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm id r th e
    rw [hnet] at hm; rw [hsig]
    rcases hm with hm | hm
    · exact h.netSigned m hm id r th e
    · rcases hout m hm with ho | ho
      · exact absurd e (ho id r th)
      · exact h.netSigned m ho id r th e
  · intro id th hs; rw [hsig] at hs; rw [hrst]; exact h.signedResp id th hs
  · intro id th hs; rw [hsig] at hs
    obtain ⟨k, hk1, hk2, hk3⟩ := h.signedInit id th hs
    exact ⟨k, by rw [(hI _).1]; exact hk1, by rw [(hI _).2.1]; exact hk2, by rw [(hI _).2.2.1]; exact hk3⟩
  · intro s' hs'; rw [(hI s').1] at hs'; rw [(hI s').2.2.2.2.2.1]
    exact SigGood_mono (fun id r th hh => by rw [hsig]; exact hh) (h.decapGood s' hs')
  · intro s' hs' hr hpe
    rw [(hI s').1] at hs'; rw [(hI s').2.2.1] at hr; rw [(hI s').2.2.2.1] at hpe
    rw [(hI s').2.2.2.1, (hI s').2.2.2.2.1, hrst]; exact h.iAuth s' hs' hr hpe
  · intro s' hd hr hpe
    rw [hrst] at hd hr hpe ⊢
    obtain ⟨k, hk1, hk2, hk3⟩ := h.rAuth s' hd hr hpe
    exact ⟨k, by rw [(hI _).1]; exact hk1, by rw [(hI _).2.1]; exact hk2, by rw [(hI _).2.2.1]; exact hk3⟩
  · intro s' hi; rw [hrst] at hi ⊢; exact h.rIdle s' hi
  · intro s' hi; rw [hrst] at hi ⊢; exact h.rSign s' hi
  · intro s' hi; rw [hrst] at hi ⊢; exact hn' _ (h.rFinish s' hi)
  · intro s' hf
    have := (hI s').2.2.2.2.2.2 hf
    rw [this]; apply hn'; apply h.iFin; rw [← this]; exact hf
  · intro s' hr; rw [(hI s').2.2.1] at hr; rw [(hI s').1]; exact h.iRes s' hr
  · intro s' hr; rw [hrst] at hr ⊢; exact h.rRes s' hr

theorem Inv1_same {g g' : G} (h : Inv1 g) (hist : g'.ist = g.ist)
    (hrst : g'.rst = g.rst) (out : List Msg) (hnet : g'.net = addNet g out)
    (hsig : g'.signed = g.signed) (hout : ∀ m ∈ out, NoSig m ∨ g.net m) : Inv1 g' :=
  Inv1_ist_frame h out (fun s => by simp [hist]) hrst hnet hsig hout

theorem startFull_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (peer : Nat) (al : Term) (short take : Bool)
    (hn : (g.ist s).ph = .none) : Inv1 (stepIStart g s peer al short take) := by
  obtain ⟨hph, hres, hfin, hout⟩ := INew_props s.1 s.2 peer al short
    (if take then (CTake (g.cli s.1) peer al).tk else none)
  unfold stepIStart
  have := upd_inv0 h s (INew s.1 s.2 peer al short (if take then (CTake (g.cli s.1) peer al).tk else none)).st
    (INew s.1 s.2 peer al short (if take then (CTake (g.cli s.1) peer al).tk else none)).out
    (by simp [hn]) (by rcases hph with hph | hph <;> simp [hph]) (by rcases hph with hph | hph <;> simp [hph])
    (by simp [hfin]) (by simp [hres]) hout
  exact (Inv1_congr (g := { g with ist := upd g.ist s (INew s.1 s.2 peer al short (if take then (CTake (g.cli s.1) peer al).tk else none)).st, net := addNet g (INew s.1 s.2 peer al short (if take then (CTake (g.cli s.1) peer al).tk else none)).out }) (g' := stepIStart g s peer al short take) (by cases take <;> rfl) rfl (by cases take <;> rfl) rfl).2 this

theorem iRecv_inv {kn : Term → Prop} {g : G} (h : Inv1 g) (s : Nat × Nat) (m : Msg) (hd : DerivableK kn g m) :
    Inv1 (stepIRecv g s m) := by
  have hF := h.iFin s
  have hR := h.iRes s
  rcases IHandle_cases (g.ist s) s.1 m with ⟨c1, c2⟩ | ⟨hp, hty, hio, c1, c2⟩ | ⟨hp, hsh, hty, he, c1, c2⟩
    | ⟨hp, hty, hc, c1, c2⟩ | ⟨hp, hl, hty, hc, c1, c2⟩ | ⟨hp, hty, he, c1, c2⟩
  · exact Inv1_same h (by show upd g.ist s _ = _; rw [c1, upd_self]) rfl _ rfl rfl (by simp [stepIRecv, c2])
  · have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl rfl hnd ?_ ?_ ?_ ?_ (by simp [c2])
    · rw [c1]; intro _; simpa using derivable_sig h hd
    · rw [c1]; simp
    · rw [c1]; exact hF
    · rw [c1]; intro hr; exact absurd (hR hr) hnd
  · have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl rfl hnd ?_ ?_ ?_ ?_ (by rw [c2]; intro m hm; simp at hm; subst hm; exact NoSig_IInitMsg _ _ _)
    · rw [c1]; simp [hp]
    · rw [c1]; simp [hp]
    · rw [c1]; exact hF
    · rw [c1]; intro hr; exact absurd (hR hr) hnd
  · have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl rfl hnd ?_ ?_ ?_ ?_ (by simp [c2])
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
  · have hnd : (g.ist s).ph ≠ .done := by rcases hp with hp | hp | hp <;> simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl rfl hnd ?_ ?_ ?_ ?_ (by simp [c2])
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
    · rw [c1]; simp [IResumed]
  · have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    have hr0 : (g.ist s).resumed = false := by
      cases hv : (g.ist s).resumed
      · rfl
      · exact absurd (hR hv) hnd
    refine upd_inv h s _ _ rfl rfl rfl rfl hnd ?_ ?_ ?_ ?_ (by rw [c2]; exact (IBeginFull_props _ _ _ _ _ _).2.2.2)
    · rw [c1]; simp [rrFall, IBeginFull, Ok]
    · rw [c1]; simp [rrFall, IBeginFull, Ok]
    · rw [c1]; simp only [rrFall, IBeginFull, Ok]; exact hF
    · rw [c1]; simp only [rrFall, IBeginFull, Ok]; intro hr; rw [hr0] at hr; cases hr

theorem iAnswerSign_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (hp : (g.ist s).ph = .sign) :
    Inv1 (stepIAnswer g s .ok) := by
  have hnd : (g.ist s).ph ≠ .done := by simp [hp]
  have hr0 : (g.ist s).resumed = false := by
    cases hv : (g.ist s).resumed
    · rfl
    · exact absurd (h.iRes s hv) hnd
  have hist : (stepIAnswer g s .ok).ist = upd g.ist s (ikDoneSt (g.ist s) s.1) := by
    simp [stepIAnswer, IKey, hp]
  have hnet : (stepIAnswer g s .ok).net = addNet g [ikFin (g.ist s) s.1] := by
    simp [stepIAnswer, IKey, hp]
  have hsig : (stepIAnswer g s .ok).signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ [(⟨s.1, false, (g.ist s).th4⟩ : SigE)] := by
    simp [stepIAnswer, IKey, hp]
    funext id r th; apply propext; simp [addSig]
  have hrst : (stepIAnswer g s .ok).rst = g.rst := rfl
  have hmono : ∀ id r th, g.signed id r th → (stepIAnswer g s .ok).signed id r th := by
    intro id r th hh; rw [hsig]; exact Or.inl hh
  have hnew : (stepIAnswer g s .ok).signed s.1 false (g.ist s).th4 := by rw [hsig]; right; simp
  have hold : ∀ id r th, (stepIAnswer g s .ok).signed id r th → g.signed id r th ∨ (id = s.1 ∧ r = false ∧ th = (g.ist s).th4) := by
    intro id r th hh; rw [hsig] at hh; rcases hh with hh | hh
    · exact Or.inl hh
    · right; simp at hh; exact ⟨hh.1, hh.2.1, hh.2.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm id r th e
    rw [hnet] at hm; rcases hm with hm | hm
    · exact hmono _ _ _ (h.netSigned m hm id r th e)
    · simp at hm; subst hm
      simp [ikFin, ikSig] at e; obtain ⟨e1, e2, e3⟩ := e; subst e1 e2 e3; exact hnew
  · intro id th hs
    rcases hold _ _ _ hs with hs | ⟨-, hr, -⟩
    · rw [hrst]; exact h.signedResp id th hs
    · exact absurd hr (by simp)
  · intro id th hs
    rcases hold _ _ _ hs with hs | ⟨hid, -, hth⟩
    · obtain ⟨k, hk1, hk2, hk3⟩ := h.signedInit id th hs
      have hk : (id, k) ≠ s := fun e => by rw [e] at hk1; rw [hp] at hk1; cases hk1
      refine ⟨k, ?_, ?_, ?_⟩ <;> simp [hist, upd, hk, hk1, hk2, hk3]
    · subst hid hth; exact ⟨s.2, by simp [hist, upd, ikDoneSt], by simp [hist, upd, ikDoneSt], by simp [hist, upd, ikDoneSt, hr0]⟩
  · intro s' hs'
    by_cases hh : s' = s
    · subst hh; simp [hist, upd, ikDoneSt] at hs'
    · rw [hist, upd_ne _ _ _ _ hh] at hs' ⊢; exact SigGood_mono hmono (h.decapGood s' hs')
  · intro s' hs' hr hpe
    by_cases hh : s' = s
    · subst hh
      simp only [hist, upd_same, ikDoneSt] at *
      exact (by rw [hrst]; exact h.iAuth s' (Or.inl hp) hr hpe)
    · rw [hist, upd_ne _ _ _ _ hh] at *; rw [hrst]; exact h.iAuth s' hs' hr hpe
  · intro s' hd hr hpe
    rw [hrst] at *
    obtain ⟨k, hk1, hk2, hk3⟩ := h.rAuth s' hd hr hpe
    have hk : ((g.rst s').peer, k) ≠ s := fun e => by rw [e] at hk1; rw [hp] at hk1; cases hk1
    refine ⟨k, ?_, ?_, ?_⟩ <;> simp [hist, upd, hk, hk1, hk2, hk3]
  · intro s' hi; rw [hrst] at *; exact h.rIdle s' hi
  · intro s' hi; rw [hrst] at *; exact h.rSign s' hi
  · intro s' hf; rw [hrst] at *; rw [hnet]; exact Or.inl (h.rFinish s' hf)
  · intro s' hf
    rw [hnet]
    by_cases hh : s' = s
    · subst hh; right; simp [hist, upd_same, ikDoneSt]
    · rw [hist, upd_ne _ _ _ _ hh] at hf ⊢; exact Or.inl (h.iFin s' hf)
  · intro s' hr
    by_cases hh : s' = s
    · subst hh; simp [hist, upd_same, ikDoneSt]
    · rw [hist, upd_ne _ _ _ _ hh] at hr ⊢; exact h.iRes s' hr
  · intro s' hr; rw [hrst] at *; exact h.rRes s' hr

theorem iAnswer_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (kind : KRes) :
    Inv1 (stepIAnswer g s kind) := by
  have hF := h.iFin s
  have hR := h.iRes s
  rcases IKey_cases (g.ist s) s.1 kind with ⟨c1, c2, c3⟩ | ⟨hp, c1, c2, c3⟩
    | ⟨hp, hk, k1, k2, k2', k3, k4, c1, c2, c3⟩ | ⟨hp, hk, c1, c2, c3⟩ | ⟨hp, hk, -, c1, c2, c3⟩
  · have hsig' : (stepIAnswer g s kind).signed = g.signed := by
      funext id r th; apply propext; simp [stepIAnswer, addSig, c3]
    exact Inv1_same h (by show upd g.ist s _ = _; rw [c1, upd_self]) rfl _ rfl hsig' (by simp [stepIAnswer, c2])
  · have hsig' : (stepIAnswer g s kind).signed = g.signed := by
      funext id r th; apply propext; simp [stepIAnswer, addSig, c3]
    have hnd : (g.ist s).ph ≠ .done := by rcases hp with hp | hp <;> simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl hsig' hnd ?_ ?_ ?_ ?_ (by simp [c2])
    · simp [c1]
    · simp [c1]
    · rw [c1]; exact hF
    · rw [c1]; intro hr; exact absurd (hR hr) hnd
  · have hsig' : (stepIAnswer g s kind).signed = g.signed := by
      funext id r th; apply propext; simp [stepIAnswer, addSig, c3]
    have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl hsig' hnd ?_ ?_ ?_ ?_ (by simp [c2])
    · rw [c1]; simp [ikSignSt]
    · rw [c1]; intro _ hr hpe
      simp only [ikSignSt] at hr hpe ⊢
      have hs := h.decapGood s hp
      have hsg := hs _ true (ikTh2 (g.ist s)) k4
      rcases hsg with hsg | hsg
      · exact absurd (k3 ▸ hsg) hpe
      · obtain ⟨kk, hk1, hk2, hk3⟩ := h.signedResp _ _ hsg
        refine ⟨kk, ?_, ?_⟩
        · rw [k3] at hk1; exact hk1
        · rw [k3] at hk3; exact hk3
    · rw [c1]; simp only [ikSignSt]; exact hF
    · rw [c1]; simp only [ikSignSt]; intro hr; exact absurd (hR hr) hnd
  · have : kind = .ok := hk
    subst this
    exact iAnswerSign_inv h s hp
  · have hsig' : (stepIAnswer g s kind).signed = g.signed := by
      funext id r th; apply propext; simp [stepIAnswer, addSig, c3]
    have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    refine upd_inv h s _ _ rfl rfl rfl hsig' hnd ?_ ?_ ?_ ?_ (by simp [c2])
    · simp [c1, ikBackSt]
    · simp [c1, ikBackSt]
    · rw [c1]; exact hF
    · rw [c1]; intro hr; exact absurd (hR hr) hnd

theorem iRetrans_inv {g : G} (h : Inv1 g) (s : Nat × Nat) : Inv1 (stepIRetrans g s) := by
  have hF := h.iFin s
  have hR := h.iRes s
  rcases IRetransmit_cases s.1 (g.ist s) with ⟨hp, hsh, c1, c2⟩ | ⟨hp, hl, c1, c2⟩ | ⟨hp, hl, c1, c2⟩
    | ⟨c1, c2⟩
  · refine Inv1_ist_frame h _ (fun s' => ?_) rfl rfl rfl (by rw [c2]; intro m hm; simp at hm; subst hm; exact Or.inl (NoSig_IInitMsg _ _ _))
    by_cases hh : s' = s
    · subst hh; simp [stepIRetrans, upd_same, c1]
    · simp [stepIRetrans, upd_ne _ _ _ _ hh]
  · refine Inv1_ist_frame h _ (fun s' => ?_) rfl rfl rfl (by rw [c2]; intro m hm; simp at hm; subst hm; exact Or.inl (NoSig_IHello _))
    by_cases hh : s' = s
    · subst hh; simp [stepIRetrans, upd_same, c1]
    · simp [stepIRetrans, upd_ne _ _ _ _ hh]
  · have hnd : (g.ist s).ph ≠ .done := by simp [hp]
    have hr0 : (g.ist s).resumed = false := by
      cases hv : (g.ist s).resumed
      · rfl
      · exact absurd (hR hv) hnd
    refine upd_inv h s _ _ rfl rfl rfl rfl hnd ?_ ?_ ?_ ?_ (by rw [c2]; exact (IBeginFull_props _ _ _ _ _ _).2.2.2)
    · rw [c1]; simp [lateFall, lateFallB, IBeginFull, Ok]
    · rw [c1]; simp [lateFall, lateFallB, IBeginFull, Ok]
    · rw [c1]; simp only [lateFall, lateFallB, IBeginFull, Ok]; exact hF
    · rw [c1]; simp only [lateFall, lateFallB, IBeginFull, Ok]; intro hr; rw [hr0] at hr; cases hr
  · refine Inv1_same h (by show upd g.ist s _ = _; rw [c1, upd_self]) rfl _ rfl rfl ?_
    intro m hm
    rcases c2 with c2 | c2 | ⟨hd, hne, c2⟩
    · simp [stepIRetrans, c2] at hm
    · simp [stepIRetrans, c2] at hm; subst hm; exact Or.inl (NoSig_IInitMsg _ _ _)
    · simp [stepIRetrans, c2] at hm; subst hm
      exact Or.inr (hF hne)

theorem iShed_inv {g : G} (h : Inv1 g) (s : Nat × Nat) : Inv1 (stepIShed g s) := by
  refine Inv1_ist_frame h [] (fun s' => ?_) rfl (by simp [addNet_nil, stepIShed]) rfl (by simp)
  by_cases hh : s' = s
  · subst hh; simp [stepIShed, upd_same, IShed]
  · simp [stepIShed, upd_ne _ _ _ _ hh]

theorem iAccept_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (tids : List Term) : Inv1 (stepIAccept g s tids) := by
  refine Inv1_ist_frame h [] (fun s' => ?_) rfl (by simp [addNet_nil, stepIAccept]) rfl (by simp)
  by_cases hh : s' = s
  · subst hh; simp [stepIAccept, upd_same]
  · simp [stepIAccept, upd_ne _ _ _ _ hh]

/-- An update of one responder session, with the ledger entries it adds. -/
theorem rupd_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : RState) (out : List Msg) (sg : List SigE)
    (hist : g'.ist = g.ist) (hrst : g'.rst = upd g.rst s st') (hnet : g'.net = addNet g out)
    (hsig : g'.signed = addSig g sg)
    (hout : ∀ m ∈ out, NoSig m ∨ ∀ id r th, m.sealed.sig = Term.sig id r th → g'.signed id r th)
    (hwit : (g.rst s).sgn = true → st'.sgn = true ∧ st'.th2 = (g.rst s).th2 ∧ st'.ath = (g.rst s).ath)
    (hsg : ∀ e ∈ sg, e.resp = true ∧ e.id = s.1 ∧ st'.sgn = true ∧ st'.th2 = e.th ∧ st'.ath = e.th)
    (hidle : st'.ph = .idle → st' = {})
    (hsign : st'.ph = .sign → st'.sgn = false ∧ st'.ath = st'.th2)
    (hfin : (st'.ph = .finish ∨ st'.ph = .resumed) → g'.net st'.reply)
    (hrauth : st'.ph = .done → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.ist (st'.peer, k)).ph = .done ∧ (g.ist (st'.peer, k)).th4 = st'.th4
        ∧ (g.ist (st'.peer, k)).resumed = false)
    (hres : st'.ph = .resumed → st'.resumed = true) :
    Inv1 g' := by
  have hmono : ∀ id r th, g.signed id r th → g'.signed id r th := by
    intro id r th hh; rw [hsig]; exact Or.inl hh
  have hnet' : ∀ m, g.net m → g'.net m := fun m hm => by rw [hnet]; exact Or.inl hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm id r th e
    rw [hnet] at hm; rcases hm with hm | hm
    · exact hmono _ _ _ (h.netSigned m hm id r th e)
    · rcases hout m hm with ho | ho
      · exact absurd e (ho id r th)
      · exact ho id r th e
  · intro id th hs
    rw [hsig] at hs; rcases hs with hs | hs
    · obtain ⟨k, hk1, hk2, hk3⟩ := h.signedResp id th hs
      by_cases hk : (id, k) = s
      · subst hk
        obtain ⟨a, b, c⟩ := hwit hk1
        exact ⟨k, by simp [hrst, upd_same, a], by simp [hrst, upd_same, b, hk2], by simp [hrst, upd_same, c, hk3]⟩
      · exact ⟨k, by simp [hrst, upd_ne _ _ _ _ hk, hk1], by simp [hrst, upd_ne _ _ _ _ hk, hk2],
          by simp [hrst, upd_ne _ _ _ _ hk, hk3]⟩
    · obtain ⟨-, hid, a, b, c⟩ := hsg _ hs
      simp only at hid b c
      subst hid
      refine ⟨s.2, ?_, ?_, ?_⟩ <;> simp [hrst, upd_same, a, b, c]
  · intro id th hs
    rw [hsig] at hs; rcases hs with hs | hs
    · rw [hist]; exact h.signedInit id th hs
    · exact absurd (hsg _ hs).1 (by simp)
  · intro s' hs'; rw [hist] at hs' ⊢; exact SigGood_mono hmono (h.decapGood s' hs')
  · intro s' hs' hr hpe
    rw [hist] at hs' hr hpe ⊢
    obtain ⟨k, hk1, hk2⟩ := h.iAuth s' hs' hr hpe
    by_cases hk : ((g.ist s').peer, k) = s
    · rw [hk] at hk1 hk2; obtain ⟨a, -, c⟩ := hwit hk1
      refine ⟨k, ?_, ?_⟩ <;> rw [hk] <;> simp [hrst, upd_same, a, c, hk2]
    · exact ⟨k, by simp [hrst, upd_ne _ _ _ _ hk, hk1], by simp [hrst, upd_ne _ _ _ _ hk, hk2]⟩
  · intro s' hd hr hpe
    rw [hist]
    by_cases hh : s' = s
    · subst hh; simp only [hrst, upd_same] at *; exact hrauth hd hr hpe
    · simp only [hrst, upd_ne _ _ _ _ hh] at *; exact h.rAuth s' hd hr hpe
  · intro s' hi
    by_cases hh : s' = s
    · subst hh; simp only [hrst, upd_same] at *; exact hidle hi
    · simp only [hrst, upd_ne _ _ _ _ hh] at *; exact h.rIdle s' hi
  · intro s' hi
    by_cases hh : s' = s
    · subst hh; simp only [hrst, upd_same] at *; exact hsign hi
    · simp only [hrst, upd_ne _ _ _ _ hh] at *; exact h.rSign s' hi
  · intro s' hi
    by_cases hh : s' = s
    · subst hh; simp only [hrst, upd_same] at *; exact hfin hi
    · simp only [hrst, upd_ne _ _ _ _ hh] at *; exact hnet' _ (h.rFinish s' hi)
  · intro s' hf; rw [hist] at hf ⊢; exact hnet' _ (h.iFin s' hf)
  · intro s' hr; rw [hist] at hr ⊢; exact h.iRes s' hr
  · intro s' hi
    by_cases hh : s' = s
    · subst hh; simp only [hrst, upd_same] at *; exact hres hi
    · simp only [hrst, upd_ne _ _ _ _ hh] at *; exact h.rRes s' hi

/-- A responder step that changes no signature ledger. -/
theorem rupd0 {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : RState) (out : List Msg)
    (hist : g'.ist = g.ist) (hrst : g'.rst = upd g.rst s st') (hnet : g'.net = addNet g out)
    (hsig : g'.signed = g.signed)
    (hout : ∀ m ∈ out, NoSig m ∨ g.net m)
    (hwit : (g.rst s).sgn = true → st'.sgn = true ∧ st'.th2 = (g.rst s).th2 ∧ st'.ath = (g.rst s).ath)
    (hidle : st'.ph = .idle → st' = {})
    (hsign : st'.ph = .sign → st'.sgn = false ∧ st'.ath = st'.th2)
    (hfin : (st'.ph = .finish ∨ st'.ph = .resumed) → g'.net st'.reply)
    (hrauth : st'.ph = .done → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.ist (st'.peer, k)).ph = .done ∧ (g.ist (st'.peer, k)).th4 = st'.th4
        ∧ (g.ist (st'.peer, k)).resumed = false)
    (hres : st'.ph = .resumed → st'.resumed = true) : Inv1 g' := by
  have hsig' : g'.signed = addSig g [] := by
    rw [hsig]; funext id r th; apply propext; simp [addSig]
  refine rupd_inv h s st' out [] hist hrst hnet hsig' ?_ hwit (by simp) hidle hsign hfin hrauth hres
  intro m hm
  rcases hout m hm with ho | ho
  · exact Or.inl ho
  · exact Or.inr (fun id r th e => by rw [hsig]; exact h.netSigned m ho id r th e)

theorem rsame_inv {g g' : G} (h : Inv1 g) (hist : g'.ist = g.ist) (hrst : g'.rst = g.rst)
    (out : List Msg) (hnet : g'.net = addNet g out) (hsig : g'.signed = g.signed)
    (hout : ∀ m ∈ out, NoSig m ∨ g.net m) : Inv1 g' :=
  Inv1_same h hist hrst out hnet hsig hout

theorem NoSig_rhReply (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : NoSig (rhReply n k sto m cs) :=
  NoSig_default _ rfl

theorem rRecv_inv {kn : Term → Prop} {g : G} (h : Inv1 g) (s : Nat × Nat) (m : Msg) (cs : List (List Nat))
    (hd : DerivableK kn g m) :
    Inv1 (stepRRecv g s m cs) := by
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m cs with
      ⟨c1, c2, -⟩ | ⟨hp, c1, c2, -⟩ | ⟨hp, ⟨sp, nr, c1⟩, c2, -⟩ | ⟨hp, hty, c1, c2, -⟩ | ⟨hp, hty, c1, c2, -⟩
    | ⟨hp, hty, hv, hsv, had, c1, c2, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, c2, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, c2, -⟩
    | ⟨hp, hty, hv, hsv, hu, c1, c2, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, -⟩
  · exact rsame_inv h rfl (by show upd g.rst s _ = _; rw [c1, upd_self]) _ rfl rfl (by simp [stepRRecv, c2])
  · refine rupd0 h s _ _ rfl rfl rfl rfl (by simp [c2]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
  · have hrf := h.rFinish s (Or.inr hp)
    refine rupd0 h s _ _ rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro m' hm'
      rcases c2 with c2 | c2 <;> rw [c2] at hm'
      · simp at hm'
      · simp at hm'; subst hm'; exact Or.inr hrf
    · rw [c1]; simp
    · rw [c1]; simp [hp]
    · rw [c1]; simp [hp]
    · rw [c1]; intro _; show addNet g _ _; exact Or.inl hrf
    · rw [c1]; simp [hp]
    · rw [c1]; intro _; simpa using h.rRes s hp
  · exact rsame_inv h rfl (by show upd g.rst s _ = _; rw [c1, upd_self]) _ rfl rfl (by
      intro m' hm'; simp [c2] at hm'; subst hm'
      exact Or.inr (h.rFinish s (Or.inl hp)))
  · exact rsame_inv h rfl (by show upd g.rst s _ = _; rw [c1, upd_self]) _ rfl rfl (by
      intro m' hm'; simp [c2] at hm'; subst hm'; exact Or.inl (NoSig_default _ rfl))
  · have h0 := h.rIdle s hp
    refine rupd0 h s _ _ rfl rfl rfl rfl (by simp [c2]) ?_ ?_ ?_ ?_ ?_ ?_
    · intro hs; rw [h0] at hs; simp at hs
    · rw [c1]; simp [rInitSt]
    · rw [c1]; intro _; rw [h0]; simp [rInitSt]
    · rw [c1]; simp [rInitSt]
    · rw [c1]; simp [rInitSt]
    · rw [c1]; simp [rInitSt]
  · have hsg2 := derivable_sig h hd
    refine rupd0 h s _ _ rfl rfl rfl rfl (by simp [c2]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [c1]; intro hs; simp [rfSt, hs]
    · rw [c1]; simp [rfSt]
    · rw [c1]; simp [rfSt]
    · rw [c1]; simp [rfSt]
    · rw [c1]; intro _ _ hpe
      simp only [rfSt] at hpe ⊢
      rcases hsg2 _ false _ hsg with e | e
      · exact absurd e hpe
      · exact h.signedInit _ _ e
    · rw [c1]; simp [rfSt]
  · refine rupd0 h s _ _ rfl rfl rfl rfl (by simp [c2]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
  · exact rsame_inv h rfl (by show upd g.rst s _ = _; rw [c1, upd_self]) _ rfl rfl (by
      intro m' hm'; simp [c2] at hm'; subst hm'; exact Or.inl (NoSig_default _ rfl))
  · have h0 := h.rIdle s hp
    refine rupd0 h s _ _ rfl rfl rfl rfl (by
      intro m' hm'; simp [c2] at hm'; subst hm'; exact Or.inl (NoSig_rhReply _ _ _ _ _)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro hs; rw [h0] at hs; simp at hs
    · rw [c1]; simp [rhSt]
    · rw [c1]; simp [rhSt]
    · rw [c1]; intro _; show addNet g _ _; right; rw [c2]; simp [rhSt]
    · rw [c1]; simp [rhSt]
    · rw [c1]; simp [rhSt]
  · refine rupd0 h s _ _ rfl rfl rfl rfl (by simp [c2]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp

theorem rAnswer_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (kind : KRes) : Inv1 (stepRAnswer g s kind) := by
  rcases RKey_cases (g.rst s) s.1 s.2 (g.sto s.1) kind with ⟨c1, c2, c3, -⟩ | ⟨hp, c1, c2, c3, -⟩ | ⟨hp, hk, c1, c2, c3, -⟩
  · have hs' : (stepRAnswer g s kind).signed = g.signed := by
      funext id r th; apply propext; simp [stepRAnswer, addSig, c3]
    exact rsame_inv h rfl (by show upd g.rst s _ = _; rw [c1, upd_self]) _ rfl hs' (by simp [stepRAnswer, c2])
  · have hs' : (stepRAnswer g s kind).signed = g.signed := by
      funext id r th; apply propext; simp [stepRAnswer, addSig, c3]
    have h0 := h.rSign s hp
    refine rupd0 h s _ _ rfl rfl rfl hs' (by simp [c2]) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [c1]; intro hs; rw [h0.1] at hs; simp at hs
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
  · have h0 := h.rSign s hp
    refine rupd_inv h s _ _ _ rfl rfl rfl (by show addSig g _ = _; rw [c3]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro m' hm'; rw [c2] at hm'; simp at hm'; subst hm'
      refine Or.inr (fun id r th e => ?_)
      simp [rkReply, rkSig] at e; obtain ⟨e1, e2, e3⟩ := e; subst e1 e2 e3
      show addSig g _ _ _ _; right; rw [c3]; simp
    · intro hs; rw [h0.1] at hs; simp at hs
    · intro e he; simp at he; subst he
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> rw [c1] <;> simp [rkSt, h0.2]
    · rw [c1]; simp [rkSt]
    · rw [c1]; simp [rkSt]
    · rw [c1]; intro _; show addNet g _ _; right; rw [c2]; simp [rkSt]
    · rw [c1]; simp [rkSt]
    · rw [c1]; simp [rkSt]

theorem rRetrans_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (hp : (g.rst s).ph = .finish) :
    Inv1 (stepRRetrans g s) :=
  Inv1_same h rfl rfl _ rfl rfl (by
    intro m' hm'; simp [RRetransmit, hp, ROk] at hm'; subst hm'; exact Or.inr (h.rFinish s (Or.inl hp)))

theorem rShed_inv {g : G} (h : Inv1 g) (s : Nat × Nat) : Inv1 (stepRShed g s) := by
  by_cases hp : (g.rst s).ph = .resumed
  · have hrs := h.rRes s hp
    refine rupd0 (g := g) (g' := stepRShed g s) h s (RShed (g.rst s)) [] rfl rfl (by simp [stepRShed, addNet_nil]) rfl
      (by simp) ?_ ?_ ?_ ?_ ?_ ?_
    · intro hs; simp [RShed, hp, hs]
    · simp [RShed, hp]
    · simp [RShed, hp]
    · simp [RShed, hp]
    · intro _ hr; simp [RShed, hp, hrs] at hr
    · simp [RShed, hp]
  · exact rsame_inv h rfl (by show upd g.rst s _ = _; simp [RShed, hp, upd_self]) [] (by simp [stepRShed, addNet_nil]) rfl (by simp)

theorem Inv1_step {kn : Term → Prop} {g g' : G} (h : Inv1 g) (hs : StepK kn g g') : Inv1 g' := by
  cases hs with
  | iStart s peer al short take _ hn _ => exact startFull_inv h s peer al short take hn
  | iRecv s m _ hd => exact iRecv_inv h s m hd
  | iAnswer s kind _ _ => exact iAnswer_inv h s kind
  | iRetrans s _ _ => exact iRetrans_inv h s
  | iShed s _ _ => exact iShed_inv h s
  | iAccept s tids _ _ _ _ _ => exact iAccept_inv h s tids
  | rRecv s m cs _ hd => exact rRecv_inv h s m cs hd
  | rAnswer s kind _ _ => exact rAnswer_inv h s kind
  | rRetrans s _ hp => exact rRetrans_inv h s hp
  | rShed s _ => exact rShed_inv h s
  | expire n i sl _ _ _ _ => exact (Inv1_congr (g := g) (g' := stepExpire g n i) rfl rfl rfl rfl).2 h
  | expireC n i sl _ _ _ _ => exact (Inv1_congr (g := g) (g' := stepExpireC g n i) rfl rfl rfl rfl).2 h
  | «export» n mx _ => exact (Inv1_congr (g := g) (g' := stepExport g n mx) rfl rfl rfl rfl).2 h
  | restore n drop _ => exact (Inv1_congr (g := g) (g' := stepRestore g n drop) rfl rfl rfl rfl).2 h
  | restart n _ => exact (Inv1_congr (g := g) (g' := stepRestart g n) rfl rfl rfl rfl).2 h

/-- Every reachable state satisfies the invariant, whatever the attacker can deduce (`kn`): it rests on the
signatures alone. -/
theorem Inv1_reach {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) : Inv1 g := by
  induction h with
  | init => exact Inv1_init K C
  | step _ hs ih => exact Inv1_step ih hs

/-- Authentication of the responder, for any number of sessions: an initiator that finished a full handshake with an
honest peer X holds a transcript that a responder session of X signed. It holds against every attacker `kn`, a broken
half of the hybrid included (`HandshakeHybrid`): it rests on the signatures, which stay ideal. -/
theorem authI {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) (s : Nat × Nat) (hd : (g.ist s).ph = .done)
    (hr : (g.ist s).resumed = false) (hp : (g.ist s).peer ≠ att) :
    ∃ k, (g.rst ((g.ist s).peer, k)).sgn = true ∧ (g.rst ((g.ist s).peer, k)).ath = (g.ist s).ath :=
  (Inv1_reach h).iAuth s (Or.inr hd) hr hp

/-- Authentication of the initiator, for any number of sessions: a responder that finished a full handshake with an
honest peer Y holds a transcript that an initiator session of Y signed. It holds against every attacker `kn`, as
`authI`. -/
theorem authR {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) (s : Nat × Nat) (hd : (g.rst s).ph = .done)
    (hr : (g.rst s).resumed = false) (hp : (g.rst s).peer ≠ att) :
    ∃ k, (g.ist ((g.rst s).peer, k)).ph = .done ∧ (g.ist ((g.rst s).peer, k)).th4 = (g.rst s).th4
      ∧ (g.ist ((g.rst s).peer, k)).resumed = false :=
  (Inv1_reach h).rAuth s hd hr hp

#audit_axioms Pinc.Hs.Inv1_reach
#audit_axioms Pinc.Hs.authI
#audit_axioms Pinc.Hs.authR

end Pinc.Hs
