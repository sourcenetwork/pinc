import Vinc.HandshakeCases

/-!
# Authentication of the full handshake, for unboundedly many sessions

Inductive invariants of the system of `HandshakeSys` (any number of honest nodes, sessions and tickets, any store
capacity, the Dolev-Yao attacker `Derivable`), proved over every reachable state.
-/

namespace Vinc.Hs
open Term

/-- The invariant of the signature ledger and of the sessions that sign. -/
structure Inv1 (g : G) : Prop where
  netSigned : ∀ m, g.net m → ∀ id r th, m.sealed.sig = Term.sig id r th → g.signed id r th
  signedResp : ∀ id th, g.signed id true th →
    ∃ k, (g.rst (id, k)).sgn = true ∧ (g.rst (id, k)).th2 = th ∧ (g.rst (id, k)).ath = th
  signedInit : ∀ id th, g.signed id false th → ∃ k, (g.ist (id, k)).ph = .done ∧ (g.ist (id, k)).th4 = th
  decapGood : ∀ s, (g.ist s).ph = .decap → SigGood g (g.ist s).reply.sealed
  iAuth : ∀ s, ((g.ist s).ph = .sign ∨ (g.ist s).ph = .done) → (g.ist s).resumed = false → (g.ist s).peer ≠ att →
    ∃ k, (g.rst ((g.ist s).peer, k)).sgn = true ∧ (g.rst ((g.ist s).peer, k)).ath = (g.ist s).ath
  rAuth : ∀ s, (g.rst s).ph = .done → (g.rst s).resumed = false → (g.rst s).peer ≠ att →
    ∃ k, (g.ist ((g.rst s).peer, k)).ph = .done ∧ (g.ist ((g.rst s).peer, k)).th4 = (g.rst s).th4
  rIdle : ∀ s, (g.rst s).ph = .idle → g.rst s = {}
  rSign : ∀ s, (g.rst s).ph = .sign → (g.rst s).sgn = false ∧ (g.rst s).ath = (g.rst s).th2
  rFinish : ∀ s, (g.rst s).ph = .finish → g.net (g.rst s).reply

theorem Inv1_init (K : Nat) : Inv1 (G0 K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [G0]


/-- The message has no signature on its blob. -/
def NoSig (m : Msg) : Prop := ∀ id r th, m.sealed.sig ≠ Term.sig id r th

theorem NoSig_default (m : Msg) (h : m.sealed = BadBlob) : NoSig m := by
  intro id r th; simp [h, BadBlob]

theorem SigGood_mono {g g' : G} (h : ∀ id r th, g.signed id r th → g'.signed id r th) {b : Blob}
    (hb : SigGood g b) : SigGood g' b := fun id r th e => (hb id r th e).elim Or.inl (fun x => Or.inr (h id r th x))

theorem IBeginFull_props (n : Nat) (x : Atom) (peer : Nat) (short : Bool) :
    (IBeginFull n x peer short nil nil).st.ph = .reply ∧ (IBeginFull n x peer short nil nil).st.resumed = false
    ∧ ∀ m ∈ (IBeginFull n x peer short nil nil).out, NoSig m := by
  refine ⟨by simp [IBeginFull, Ok], by simp [IBeginFull, Ok], ?_⟩
  intro m hm; apply NoSig_default; cases short <;> simp [IBeginFull, Ok] at hm <;> simp [hm]

/-- An update of one initiator session that is not a finished one, whose new state satisfies the session clauses. -/
theorem upd_inv0 {g : G} (h : Inv1 g) (s : Nat × Nat) (st' : IState) (out : List Msg)
    (hold : (g.ist s).ph ≠ .done)
    (hdec : st'.ph = .decap → SigGood g st'.reply.sealed)
    (hauth : (st'.ph = .sign ∨ st'.ph = .done) → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.rst (st'.peer, k)).sgn = true ∧ (g.rst (st'.peer, k)).ath = st'.ath)
    (hout : ∀ m ∈ out, NoSig m) :
    Inv1 { g with ist := upd g.ist s st', net := addNet g out } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm id r th e
    rcases hm with hm | hm
    · exact h.netSigned m hm id r th e
    · exact absurd e (hout m hm id r th)
  · intro id th hs; exact h.signedResp id th hs
  · intro id th hs
    obtain ⟨k, hk1, hk2⟩ := h.signedInit id th hs
    have hk : (id, k) ≠ s := fun e => hold (e ▸ hk1)
    refine ⟨k, ?_, ?_⟩ <;> simp [upd, hk, hk1, hk2]
  · intro s' hs'
    by_cases hh : s' = s
    · subst hh; simp only [upd_same] at hs'; simp only [upd_same]; exact hdec hs'
    · simp only [upd_ne _ _ _ _ hh] at hs' ⊢; exact SigGood_mono (fun _ _ _ x => x) (h.decapGood s' hs')
  · intro s' hs' hr hp
    by_cases hh : s' = s
    · subst hh; simp only [upd_same] at *; exact hauth hs' hr hp
    · simp only [upd_ne _ _ _ _ hh] at *; exact h.iAuth s' hs' hr hp
  · intro s' hd hr hp
    obtain ⟨k, hk1, hk2⟩ := h.rAuth s' hd hr hp
    have hk : ((g.rst s').peer, k) ≠ s := fun e => hold (e ▸ hk1)
    refine ⟨k, ?_, ?_⟩ <;> simp [upd, hk, hk1, hk2]
  · exact h.rIdle
  · exact h.rSign
  · intro s' hf; exact Or.inl (h.rFinish s' hf)

theorem Inv1_congr {g g' : G} (hi : g'.ist = g.ist) (hr : g'.rst = g.rst) (hn : g'.net = g.net)
    (hs : g'.signed = g.signed) : Inv1 g' ↔ Inv1 g := by
  cases g; cases g'; simp only at hi hr hn hs; subst hi hr hn hs
  exact ⟨fun h => ⟨h.netSigned, h.signedResp, h.signedInit, h.decapGood, h.iAuth, h.rAuth, h.rIdle, h.rSign, h.rFinish⟩,
    fun h => ⟨h.netSigned, h.signedResp, h.signedInit, h.decapGood, h.iAuth, h.rAuth, h.rIdle, h.rSign, h.rFinish⟩⟩

theorem upd_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : IState) (out : List Msg)
    (hist : g'.ist = upd g.ist s st') (hnet : g'.net = addNet g out) (hrst : g'.rst = g.rst)
    (hsig : g'.signed = g.signed)
    (hold : (g.ist s).ph ≠ .done)
    (hdec : st'.ph = .decap → SigGood g st'.reply.sealed)
    (hauth : (st'.ph = .sign ∨ st'.ph = .done) → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.rst (st'.peer, k)).sgn = true ∧ (g.rst (st'.peer, k)).ath = st'.ath)
    (hout : ∀ m ∈ out, NoSig m) : Inv1 g' :=
  (Inv1_congr (g := { g with ist := upd g.ist s st', net := addNet g out }) hist hrst hnet hsig).2
    (upd_inv0 h s st' out hold hdec hauth hout)

theorem startFull_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (peer : Nat) (short : Bool) (hn : (g.ist s).ph = .none) :
    Inv1 { g with ist := upd g.ist s (IBeginFull s.1 (atom 0 s.1 s.2) peer short nil nil).st,
                  net := addNet g (IBeginFull s.1 (atom 0 s.1 s.2) peer short nil nil).out } := by
  obtain ⟨hph, hres, hout⟩ := IBeginFull_props s.1 (atom 0 s.1 s.2) peer short
  exact upd_inv0 h s _ _ (by simp [hn]) (by simp [hph]) (by simp [hph]) hout

theorem IBeginResume_props (n : Nat) (x : Atom) (tk : Tk) :
    (IBeginResume n x tk).st.ph = .resume ∧ ∀ m ∈ (IBeginResume n x tk).out, NoSig m := by
  refine ⟨by simp [IBeginResume, Ok], ?_⟩
  intro m hm; apply NoSig_default; simp [IBeginResume, Ok] at hm; simp [hm]

theorem startResume_inv {g : G} (h : Inv1 g) (s : Nat × Nat) (tk : Tk) (cl : Nat → List Tk)
    (hn : (g.ist s).ph = .none) :
    Inv1 { g with ist := upd g.ist s (IBeginResume s.1 (atom 0 s.1 s.2) tk).st, cli := cl,
                  net := addNet g (IBeginResume s.1 (atom 0 s.1 s.2) tk).out } := by
  obtain ⟨hph, hout⟩ := IBeginResume_props s.1 (atom 0 s.1 s.2) tk
  exact upd_inv h s (IBeginResume s.1 (atom 0 s.1 s.2) tk).st (IBeginResume s.1 (atom 0 s.1 s.2) tk).out
    rfl rfl rfl rfl (by simp [hn]) (by simp [hph]) (by simp [hph]) hout

theorem derivable_sig {g : G} (h : Inv1 g) {m : Msg} (hm : Derivable g m) : SigGood g m.sealed := by
  rcases hm with hm | ⟨hs, -⟩
  · exact fun id r th e => Or.inr (h.netSigned m hm id r th e)
  · exact hs

theorem addNet_nil (g : G) : addNet g [] = g.net := by
  funext m; simp [addNet]

theorem upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) : upd f a (f a) = f := by
  funext x; by_cases h : x = a <;> simp [upd, h]

theorem Inv1_same {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : IState) (hst : st' = g.ist s)
    (hist : g'.ist = upd g.ist s st') (hnet : g'.net = g.net) (hrst : g'.rst = g.rst)
    (hsig : g'.signed = g.signed) : Inv1 g' :=
  (Inv1_congr (g := g) (by rw [hist, hst, upd_self]) hrst hnet hsig).2 h

theorem NoSig_init (n : Nat) (st : IState) :
    ∀ m ∈ [({ ty := .init, form := .full, e := pub st.x, pk := ek n } : Msg)], NoSig m := by
  intro m hm; apply NoSig_default; simp at hm; simp [hm]

theorem iRecv_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (m : Msg) (hd : Derivable g m)
    (hist : g'.ist = upd g.ist s (IHandle (g.ist s) s.1 m).st) (hnet : g'.net = addNet g (IHandle (g.ist s) s.1 m).out)
    (hrst : g'.rst = g.rst) (hsig : g'.signed = g.signed) : Inv1 g' := by
  rcases IHandle_cases (g.ist s) s.1 m with ⟨c1, c2⟩ | ⟨hp, c1, c2⟩ | ⟨hp, hty, hr, c1, c2⟩ | ⟨hp, hsh, hty, he, c1, c2⟩
    | ⟨hp, hty, c1, c2, hc⟩ | ⟨hp, hty, he, c1, c2⟩
  · exact Inv1_same h s _ c1 hist (by rw [hnet, c2, addNet_nil]) hrst hsig
  · refine upd_inv h s _ _ hist hnet hrst hsig (by rcases hp with hp | hp <;> simp [hp]) ?_ ?_ (by simp [c2])
    · simp [c1]
    · simp [c1]
  · refine upd_inv h s _ _ hist hnet hrst hsig (by simp [hp]) ?_ ?_ (by simp [c2])
    · rw [c1]; intro _; simpa using derivable_sig h hd
    · rw [c1]; simp
  · refine upd_inv h s _ _ hist hnet hrst hsig (by simp [hp]) ?_ ?_ (by rw [c2]; exact NoSig_init _ _)
    · rw [c1]; simp [hp]
    · rw [c1]; simp [hp]
  · refine upd_inv h s _ _ hist hnet hrst hsig (by simp [hp]) ?_ ?_ (by simp [c2])
    · rw [c1]; simp [rrDone]
    · rw [c1]; simp [rrDone]
  · refine upd_inv h s _ _ hist hnet hrst hsig (by simp [hp]) ?_ ?_ (by rw [c2]; intro m hm; apply NoSig_default; simp [IBeginFull, Ok] at hm; simp [hm])
    · rw [c1]; simp [rrFall, IBeginFull, Ok]
    · rw [c1]; simp [rrFall, IBeginFull, Ok]

theorem iAnswerSign_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (hp : (g.ist s).ph = .sign)
    (hist : g'.ist = upd g.ist s (ikDoneSt (g.ist s) s.1))
    (hnet : g'.net = addNet g [{ ty := .fin, sealed := ⟨(g.ist s).hsi, (g.ist s).th3, s.1, ikSig (g.ist s) s.1⟩ }])
    (hrst : g'.rst = g.rst)
    (hsig : g'.signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ [(⟨s.1, false, (g.ist s).th4⟩ : SigE)]) :
    Inv1 g' := by
  have hmono : ∀ id r th, g.signed id r th → g'.signed id r th := by
    intro id r th hh; rw [hsig]; exact Or.inl hh
  have hnew : g'.signed s.1 false (g.ist s).th4 := by rw [hsig]; right; simp
  have hold : ∀ id r th, g'.signed id r th → g.signed id r th ∨ (id = s.1 ∧ r = false ∧ th = (g.ist s).th4) := by
    intro id r th hh; rw [hsig] at hh; rcases hh with hh | hh
    · exact Or.inl hh
    · right; simp at hh; exact ⟨hh.1, hh.2.1, hh.2.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm id r th e
    rw [hnet] at hm; rcases hm with hm | hm
    · exact hmono _ _ _ (h.netSigned m hm id r th e)
    · simp at hm; subst hm
      simp [ikSig] at e; obtain ⟨e1, e2, e3⟩ := e; subst e1 e2 e3; exact hnew
  · intro id th hs
    rcases hold _ _ _ hs with hs | ⟨-, hr, -⟩
    · rw [hrst]; exact h.signedResp id th hs
    · exact absurd hr (by simp)
  · intro id th hs
    rcases hold _ _ _ hs with hs | ⟨hid, -, hth⟩
    · obtain ⟨k, hk1, hk2⟩ := h.signedInit id th hs
      have hk : (id, k) ≠ s := fun e => by rw [e] at hk1; rw [hp] at hk1; cases hk1
      refine ⟨k, ?_, ?_⟩ <;> simp [hist, upd, hk, hk1, hk2]
    · subst hid hth; exact ⟨s.2, by simp [hist, upd, ikDoneSt], by simp [hist, upd, ikDoneSt]⟩
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
    obtain ⟨k, hk1, hk2⟩ := h.rAuth s' hd hr hpe
    have hk : ((g.rst s').peer, k) ≠ s := fun e => by rw [e] at hk1; rw [hp] at hk1; cases hk1
    refine ⟨k, ?_, ?_⟩ <;> simp [hist, upd, hk, hk1, hk2]
  · rw [hrst]; exact h.rIdle
  · rw [hrst]; exact h.rSign
  · intro s' hf; rw [hrst] at *; rw [hnet]; exact Or.inl (h.rFinish s' hf)

theorem iAnswer_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (kind : KRes)
    (hist : g'.ist = upd g.ist s (IKey (g.ist s) s.1 kind).st) (hnet : g'.net = addNet g (IKey (g.ist s) s.1 kind).out)
    (hrst : g'.rst = g.rst)
    (hsig : g'.signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ (IKey (g.ist s) s.1 kind).sg) : Inv1 g' := by
  rcases IKey_cases (g.ist s) s.1 kind with ⟨c1, c2, c3⟩ | ⟨hp, c1, c2, c3⟩ | ⟨hp, hk, k1, k2, k3, k4, c1, c2, c3⟩
    | ⟨hp, hk, c1, c2, c3⟩
  · refine Inv1_same h s _ c1 hist (by rw [hnet, c2, addNet_nil]) hrst ?_
    rw [hsig, c3]; funext id r th; apply propext; simp
  · have hsig' : g'.signed = g.signed := by rw [hsig, c3]; funext id r th; apply propext; simp
    refine upd_inv h s _ _ hist hnet hrst hsig' (by rcases hp with hp | hp <;> simp [hp]) ?_ ?_ (by simp [c2])
    · simp [c1]
    · simp [c1]
  · have hsig' : g'.signed = g.signed := by rw [hsig, c3]; funext id r th; apply propext; simp
    refine upd_inv h s _ _ hist hnet hrst hsig' (by simp [hp]) ?_ ?_ (by simp [c2])
    · rw [c1]; simp [ikSignSt]
    · rw [c1]; intro _ hr hpe
      simp only [ikSignSt] at hr hpe ⊢
      have hs := h.decapGood s hp
      have hsg := hs _ true (th2 (g.ist s).th1 (g.ist s).reply.sealed.id) k4
      rcases hsg with hsg | hsg
      · exact absurd (k3 ▸ hsg) hpe
      · obtain ⟨kk, hk1, hk2, hk3⟩ := h.signedResp _ _ hsg
        refine ⟨kk, ?_, ?_⟩
        · rw [k3] at hk1; exact hk1
        · rw [k3] at hk3 ⊢; exact hk3
  · exact iAnswerSign_inv h s hp (by rw [hist, c1]) (by rw [hnet, c2]) hrst (by rw [hsig, c3])
/-- An update of one responder session, with the ledger entries it adds. -/
theorem rupd_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : RState) (out : List Msg) (sg : List SigE)
    (hist : g'.ist = g.ist) (hrst : g'.rst = upd g.rst s st') (hnet : g'.net = addNet g out)
    (hsig : g'.signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ sg)
    (hout : ∀ m ∈ out, NoSig m ∨ ∀ id r th, m.sealed.sig = Term.sig id r th → g'.signed id r th)
    (hwit : (g.rst s).sgn = true → st'.sgn = true ∧ st'.th2 = (g.rst s).th2 ∧ st'.ath = (g.rst s).ath)
    (hsg : ∀ e ∈ sg, e.resp = true ∧ e.id = s.1 ∧ st'.sgn = true ∧ st'.th2 = e.th ∧ st'.ath = e.th)
    (hidle : st'.ph = .idle → st' = {})
    (hsign : st'.ph = .sign → st'.sgn = false ∧ st'.ath = st'.th2)
    (hfin : st'.ph = .finish → g'.net st'.reply)
    (hrauth : st'.ph = .done → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.ist (st'.peer, k)).ph = .done ∧ (g.ist (st'.peer, k)).th4 = st'.th4) :
    Inv1 g' := by
  have hmono : ∀ id r th, g.signed id r th → g'.signed id r th := by
    intro id r th hh; rw [hsig]; exact Or.inl hh
  have hnet' : ∀ m, g.net m → g'.net m := fun m hm => by rw [hnet]; exact Or.inl hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem rsame_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : RState) (out : List Msg)
    (hst : st' = g.rst s) (hist : g'.ist = g.ist) (hrst : g'.rst = upd g.rst s st') (hnet : g'.net = addNet g out)
    (hsig : g'.signed = g.signed)
    (hout : ∀ m ∈ out, NoSig m ∨ g.net m) : Inv1 g' := by
  have hsig' : g'.signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ ([] : List SigE) := by
    rw [hsig]; funext id r th; apply propext; simp
  refine rupd_inv h s st' out [] hist hrst hnet hsig' ?_ ?_ (by simp) ?_ ?_ ?_ ?_
  · intro m hm
    rcases hout m hm with ho | ho
    · exact Or.inl ho
    · refine Or.inr (fun id r th e => ?_)
      rw [hsig]; exact h.netSigned m ho id r th e
  · intro hs; subst hst; exact ⟨hs, rfl, rfl⟩
  · intro hi; subst hst; exact h.rIdle s hi
  · intro hi; subst hst; exact h.rSign s hi
  · intro hi; subst hst; rw [hnet]; exact Or.inl (h.rFinish s hi)
  · intro hd hr hpe; subst hst; exact h.rAuth s hd hr hpe

theorem rupd0 {g g' : G} (h : Inv1 g) (s : Nat × Nat) (st' : RState) (out : List Msg)
    (hist : g'.ist = g.ist) (hrst : g'.rst = upd g.rst s st') (hnet : g'.net = addNet g out)
    (hsig : g'.signed = g.signed)
    (hout : ∀ m ∈ out, NoSig m)
    (hwit : (g.rst s).sgn = true → st'.sgn = true ∧ st'.th2 = (g.rst s).th2 ∧ st'.ath = (g.rst s).ath)
    (hidle : st'.ph = .idle → st' = {})
    (hsign : st'.ph = .sign → st'.sgn = false ∧ st'.ath = st'.th2)
    (hfin : st'.ph = .finish → g'.net st'.reply)
    (hrauth : st'.ph = .done → st'.resumed = false → st'.peer ≠ att →
      ∃ k, (g.ist (st'.peer, k)).ph = .done ∧ (g.ist (st'.peer, k)).th4 = st'.th4) : Inv1 g' := by
  have hsig' : g'.signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ ([] : List SigE) := by
    rw [hsig]; funext id r th; apply propext; simp
  exact rupd_inv h s st' out [] hist hrst hnet hsig' (fun m hm => Or.inl (hout m hm)) hwit (by simp) hidle hsign hfin hrauth

theorem NoSig_msg (m : Msg) (h : m.sealed = BadBlob) : NoSig m := NoSig_default m h

theorem rRecv_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (m : Msg) (hd : Derivable g m)
    (hist : g'.ist = g.ist)
    (hrst : g'.rst = upd g.rst s (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st)
    (hnet : g'.net = addNet g (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).out)
    (hsig : g'.signed = g.signed) : Inv1 g' := by
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m with
      ⟨c1, c2, -⟩ | ⟨hp, c1, c2, -⟩ | ⟨hp, hty, c1, c2, -⟩ | ⟨hp, hty, c1, c2, -⟩ | ⟨hp, hty, hprm, c1, c2, -⟩
    | ⟨hp, hty, hk, had, hsg, c1, c2, -⟩ | ⟨hp, hty, hprm, c1, c2, -⟩ | ⟨hp, hty, hprm, i0, hf, he, hb, c1, c2, -⟩
  · exact rsame_inv h s _ _ c1 hist hrst (by rw [hnet, c2]) hsig (by simp [c2])
  · refine rupd0 h s _ _ hist hrst hnet hsig (by simp [c2]) ?_ ?_ ?_ ?_ ?_
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
  · exact rsame_inv h s _ _ c1 hist hrst (by rw [hnet]) hsig (by
      intro m' hm'; rw [c2] at hm'; simp at hm'; subst hm'; exact Or.inr (h.rFinish s hp))
  · exact rsame_inv h s _ _ c1 hist hrst hnet hsig (by
      intro m' hm'; rw [c2] at hm'; simp at hm'; subst hm'; exact Or.inl (NoSig_msg _ rfl))
  · have h0 := h.rIdle s hp
    refine rupd0 h s _ _ hist hrst hnet hsig (by simp [c2]) ?_ ?_ ?_ ?_ ?_
    · intro hs; rw [h0] at hs; simp at hs
    · rw [c1]; simp [rInitSt]
    · rw [c1]; intro _; rw [h0]; simp [rInitSt]
    · rw [c1]; simp [rInitSt]
    · rw [c1]; simp [rInitSt]
  · have hsg2 := derivable_sig h hd
    refine rupd0 h s _ _ hist hrst hnet hsig (by simp [c2]) ?_ ?_ ?_ ?_ ?_
    · rw [c1]; intro hs; simp [rfSt, hs]
    · rw [c1]; simp [rfSt]
    · rw [c1]; simp [rfSt]
    · rw [c1]; simp [rfSt]
    · rw [c1]; intro _ _ hpe
      simp only [rfSt] at hpe ⊢
      rcases hsg2 _ false _ hsg with e | e
      · exact absurd e hpe
      · exact h.signedInit _ _ e
  · exact rsame_inv h s _ _ c1 hist hrst hnet hsig (by
      intro m' hm'; rw [c2] at hm'; simp at hm'; subst hm'; exact Or.inl (NoSig_msg _ rfl))
  · have h0 := h.rIdle s hp
    refine rupd0 h s _ _ hist hrst hnet hsig (by
      intro m' hm'; rw [c2] at hm'; simp at hm'; subst hm'; exact NoSig_msg _ rfl) ?_ ?_ ?_ ?_ ?_
    · intro hs; rw [h0] at hs; simp at hs
    · rw [c1]; simp [rhSt]
    · rw [c1]; simp [rhSt]
    · rw [c1]; simp [rhSt]
    · rw [c1]; simp [rhSt]

theorem rAnswer_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (kind : KRes)
    (hist : g'.ist = g.ist)
    (hrst : g'.rst = upd g.rst s (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).st)
    (hnet : g'.net = addNet g (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).out)
    (hsig : g'.signed = fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).sg) :
    Inv1 g' := by
  rcases RKey_cases (g.rst s) s.1 s.2 (g.sto s.1) kind with ⟨c1, c2, c3, -⟩ | ⟨hp, c1, c2, c3, -⟩ | ⟨hp, hk, c1, c2, c3, -⟩
  · have hs' : g'.signed = g.signed := by rw [hsig, c3]; funext id r th; apply propext; simp
    exact rsame_inv h s _ _ c1 hist hrst (by rw [hnet, c2]) hs' (by simp [c2])
  · have hs' : g'.signed = g.signed := by rw [hsig, c3]; funext id r th; apply propext; simp
    have h0 := h.rSign s hp
    refine rupd0 h s _ _ hist hrst hnet hs' (by simp [c2]) ?_ ?_ ?_ ?_ ?_
    · rw [c1]; intro hs; rw [h0.1] at hs; simp at hs
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
    · rw [c1]; simp
  · have h0 := h.rSign s hp
    refine rupd_inv h s _ _ _ hist hrst hnet hsig ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro m' hm'; rw [c2] at hm'; simp at hm'; subst hm'
      refine Or.inr (fun id r th e => ?_)
      simp [rkReply, rkSig] at e; obtain ⟨e1, e2, e3⟩ := e; subst e1 e2 e3
      rw [hsig]; right; rw [c3]; simp
    · intro hs; rw [h0.1] at hs; simp at hs
    · intro e he; rw [c3] at he; simp at he; subst he
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> rw [c1] <;> simp [rkSt, h0.2]
    · rw [c1]; simp [rkSt]
    · rw [c1]; simp [rkSt]
    · rw [c1]; intro _; rw [hnet, c2]; right; simp [rkSt]
    · rw [c1]; simp [rkSt]

theorem retransmit_inv {g g' : G} (h : Inv1 g) (msg : Msg) (hm : NoSig msg) (hist : g'.ist = g.ist) (hrst : g'.rst = g.rst)
    (hnet : g'.net = addNet g [msg]) (hsig : g'.signed = g.signed) : Inv1 g' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m' hm' id r th e
    rw [hnet] at hm'; rcases hm' with hm' | hm'
    · rw [hsig]; exact h.netSigned m' hm' id r th e
    · simp at hm'; subst hm'; exact absurd e (hm id r th)
  · intro id th hs; rw [hsig] at hs; rw [hrst]; exact h.signedResp id th hs
  · intro id th hs; rw [hsig] at hs; rw [hist]; exact h.signedInit id th hs
  · intro s' hs'; rw [hist] at hs' ⊢
    exact SigGood_mono (fun id r th hh => by rw [hsig]; exact hh) (h.decapGood s' hs')
  · intro s' hs' hr hpe; rw [hist] at hs' hr hpe ⊢; rw [hrst]; exact h.iAuth s' hs' hr hpe
  · intro s' hd hr hpe; rw [hrst] at hd hr hpe ⊢; rw [hist]; exact h.rAuth s' hd hr hpe
  · intro s' hi; rw [hrst] at hi ⊢; exact h.rIdle s' hi
  · intro s' hi; rw [hrst] at hi ⊢; exact h.rSign s' hi
  · intro s' hi; rw [hrst] at hi ⊢; rw [hnet]; exact Or.inl (h.rFinish s' hi)

theorem acc_inv {g g' : G} (h : Inv1 g) (s : Nat × Nat) (hist : g'.ist = upd g.ist s { g.ist s with acc := true })
    (hrst : g'.rst = g.rst) (hnet : g'.net = g.net) (hsig : g'.signed = g.signed) : Inv1 g' := by
  have hI : ∀ s', (g'.ist s').ph = (g.ist s').ph ∧ (g'.ist s').th4 = (g.ist s').th4 ∧ (g'.ist s').resumed = (g.ist s').resumed
      ∧ (g'.ist s').peer = (g.ist s').peer ∧ (g'.ist s').ath = (g.ist s').ath ∧ (g'.ist s').reply = (g.ist s').reply := by
    intro s'; by_cases hh : s' = s
    · subst hh; simp [hist, upd_same]
    · simp [hist, upd_ne _ _ _ _ hh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m' hm' id r th e; rw [hnet] at hm'; rw [hsig]; exact h.netSigned m' hm' id r th e
  · intro id th hs; rw [hsig] at hs; rw [hrst]; exact h.signedResp id th hs
  · intro id th hs; rw [hsig] at hs
    obtain ⟨k, hk1, hk2⟩ := h.signedInit id th hs
    exact ⟨k, by rw [(hI _).1]; exact hk1, by rw [(hI _).2.1]; exact hk2⟩
  · intro s' hs'; rw [(hI s').1] at hs'; rw [(hI s').2.2.2.2.2]
    exact SigGood_mono (fun id r th hh => by rw [hsig]; exact hh) (h.decapGood s' hs')
  · intro s' hs' hr hpe
    rw [(hI s').1] at hs'; rw [(hI s').2.2.1] at hr; rw [(hI s').2.2.2.1] at hpe
    rw [(hI s').2.2.2.1, (hI s').2.2.2.2.1, hrst]; exact h.iAuth s' hs' hr hpe
  · intro s' hd hr hpe
    rw [hrst] at hd hr hpe ⊢
    obtain ⟨k, hk1, hk2⟩ := h.rAuth s' hd hr hpe
    exact ⟨k, by rw [(hI _).1]; exact hk1, by rw [(hI _).2.1]; exact hk2⟩
  · intro s' hi; rw [hrst] at hi ⊢; exact h.rIdle s' hi
  · intro s' hi; rw [hrst] at hi ⊢; exact h.rSign s' hi
  · intro s' hi; rw [hrst] at hi ⊢; rw [hnet]; exact h.rFinish s' hi

theorem Inv1_step {g g' : G} (h : Inv1 g) (hs : Step g g') : Inv1 g' := by
  cases hs with
  | startFull s peer short _ hn _ => exact startFull_inv h s peer short hn
  | startResume s tk _ hn _ => exact startResume_inv h s tk _ hn
  | iRecv s m _ hd => exact iRecv_inv h s m hd rfl rfl rfl rfl
  | iAnswer s kind _ => exact iAnswer_inv h s kind rfl rfl rfl rfl
  | iRetransmit s _ _ =>
    exact retransmit_inv h _ (NoSig_default _ rfl) rfl rfl rfl rfl
  | iAcceptFull s r _ _ _ _ _ _ _ => exact acc_inv h s rfl rfl rfl rfl
  | iAcceptResumed s t _ _ _ _ _ => exact acc_inv h s rfl rfl rfl rfl
  | rRecv s m _ hd => exact rRecv_inv h s m hd rfl rfl rfl rfl
  | rAnswer s kind _ => exact rAnswer_inv h s kind rfl rfl rfl rfl
  | expire n i => refine (Inv1_congr (g := g) ?_ ?_ ?_ ?_).2 h <;> rfl

/-- Every reachable state satisfies the invariant. -/
theorem Inv1_reach {K : Nat} {g : G} (h : Reach K g) : Inv1 g := by
  induction h with
  | init => exact Inv1_init K
  | step _ hs ih => exact Inv1_step ih hs

/-- Authentication of the responder, for any number of sessions: an initiator that finished a full handshake with an
honest peer X holds a transcript that a responder session of X signed. -/
theorem authI {K : Nat} {g : G} (h : Reach K g) (s : Nat × Nat) (hd : (g.ist s).ph = .done)
    (hr : (g.ist s).resumed = false) (hp : (g.ist s).peer ≠ att) :
    ∃ k, (g.rst ((g.ist s).peer, k)).sgn = true ∧ (g.rst ((g.ist s).peer, k)).ath = (g.ist s).ath :=
  (Inv1_reach h).iAuth s (Or.inr hd) hr hp

/-- Authentication of the initiator, for any number of sessions: a responder that finished a full handshake with an
honest peer Y holds a transcript that an initiator session of Y signed. -/
theorem authR {K : Nat} {g : G} (h : Reach K g) (s : Nat × Nat) (hd : (g.rst s).ph = .done)
    (hr : (g.rst s).resumed = false) (hp : (g.rst s).peer ≠ att) :
    ∃ k, (g.ist ((g.rst s).peer, k)).ph = .done ∧ (g.ist ((g.rst s).peer, k)).th4 = (g.rst s).th4 :=
  (Inv1_reach h).rAuth s hd hr hp

#audit_axioms Vinc.Hs.Inv1_reach
#audit_axioms Vinc.Hs.authI
#audit_axioms Vinc.Hs.authR

end Vinc.Hs