import Vinc.HandshakeTicket

/-!
# Resumption: the initiator side and the network

The step proofs of the initiator clauses of `Inv4` (`iloc`, `ick`, `ires2`) and of the two network clauses
(`netConf`, `netHello`). The point where the attacker could break a resumption is a forged Reply: its confirmation tag
is under a key derived from the pre-shared key of the ticket, which the attacker does not know, so a Reply that
verifies is one an established resumed responder sent (`netConf`), and it fixes the responder session, its transcript
and the ticket ids it handed out.
-/

namespace Vinc.Hs
open Term

theorem binder_inj {a b c d : Term} (h : binder a b = binder c d) : a = c ∧ b = d := by
  simp only [binder.injEq] at h; exact h

theorem conf_inj {a b c d : Term} (h : conf a b = conf c d) : a = c ∧ b = d := by
  simp only [conf.injEq] at h; exact h

/-! ## What an initiator step sends -/

theorem IHandle_out_nil (st : IState) (n : Nat) (m : Msg) :
    ∀ x ∈ (IHandle st n m).out, x.conf = nil ∧ x.binder = nil := by
  intro x hx
  rcases IHandle_cases st n m with ⟨c1, c2⟩ | ⟨hp, c1, c2⟩ | ⟨hp, hty, hio, c1, c2⟩ | ⟨hp, hsh, hty, he, c1, c2⟩
    | ⟨hp, hty, hc, c1, c2⟩ | ⟨hp, hl, hty, hc, c1, c2⟩ | ⟨hp, hty, he, c1, c2⟩ <;> rw [c2] at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx; subst hx; simp [IInitMsg]
  · simp at hx
  · simp at hx
  · simp [IBeginFull, Ok] at hx; subst hx; simp [IInitMsg]

theorem IKey_out_nil (st : IState) (n : Nat) (kind : KRes) :
    ∀ x ∈ (IKey st n kind).out, x.conf = nil ∧ x.binder = nil := by
  intro x hx
  rcases IKey_cases st n kind with ⟨c1, c2, -⟩ | ⟨hp, c1, c2, -⟩ | ⟨hp, hk, hb, hc, hcr, hid, hsg, c1, c2, -⟩
    | ⟨hp, hk, c1, c2, -⟩ <;> rw [c2] at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx; subst hx; simp [ikFin]

/-- What an initiator's loss timer sends: an Initial, a Hello, or a Finish already on the network. -/
theorem IRetransmit_out {g : G} (h1 : Inv1 g) (s : Nat × Nat) :
    ∀ x ∈ (IRetransmit s.1 (g.ist s)).out, (x.conf = nil ∧ x.binder = nil) ∨ g.net x ∨
      ((g.ist s).ph = .resume ∧ x = IHello (g.ist s)) := by
  intro x hx
  rcases IRetransmit_cases s.1 (g.ist s) with ⟨hp, hsh, c1, c2⟩ | ⟨hp, hl, c1, c2⟩ | ⟨hp, hl, c1, c2⟩
    | ⟨c1, c2 | c2 | ⟨hp, hf, c2⟩⟩ <;> rw [c2] at hx
  · simp at hx; subst hx; left; simp [IInitMsg]
  · simp at hx; subst hx; right; right; exact ⟨hp, rfl⟩
  · simp [lateFallB, IBeginFull, Ok] at hx; subst hx; left; simp [IInitMsg]
  · simp at hx
  · simp at hx; subst hx; left; simp [IInitMsg]
  · simp at hx; subst hx; right; left; exact h1.iFin s hf

/-! ## A forged Reply is a genuine one -/

/-- A Reply that verifies against the Hello of a ticket the attacker does not know was sent by an established resumed
responder session of the ticket's issuer: it fixes that session's transcript, resumption secret and ticket ids, the
credit record is the issuer's, and the session names the initiator as its peer. -/
theorem rreply_origin {K C : Nat} {g : G} (hr : Reach K C g) (h4 : Inv4 g) (m : Msg) (hd : Derivable g m)
    (x : Atom) (ckp thh b : Term) (t : Tk) (n peer : Nat) (hti : g.issued t) (hck : ckp = ckpsk t.psk)
    (hsec : ¬ Known t.psk) (hb : b = binder t.psk thh) (hsess : ∃ k, pskSess t.psk = some (peer, k))
    (hown : t.peer = n) (hc : RrConfOK x ckp thh b m) :
    ∃ r, Est (g.rst r).ph ∧ (g.rst r).resumed = true ∧ (g.rst r).thf = RrThr thh b m ∧
      m.tids = (g.rst r).mytids ∧ (g.rst r).res = res (RrCk2 x ckp (RrThr thh b m) m) (RrThr thh b m) ∧
      m.cr = RCr r.1 ∧ r.1 = peer ∧ (g.rst r).peer = n := by
  have h3 := Inv3_reach hr
  have hE := EInv_reach hr
  have hconf : m.conf = conf (cfk (RrCk2 x ckp (RrThr thh b m) m) (RrThr thh b m))
      (thT (RrThr thh b m) (tlist m.tids)) := hc
  have hm' : ∃ m', g.net m' ∧ m'.conf = m.conf := by
    rcases hd with hnet | ⟨-, -, -, hC⟩
    · exact ⟨m, hnet, rfl⟩
    · rcases hC _ _ hconf with hk | hm
      · exfalso
        apply hsec
        simp only [Known, RrCk2, hck] at hk
        exact hk.1
      · exact hm
  obtain ⟨m', hnet, hceq⟩ := hm'
  have hne : m'.conf ≠ nil := by rw [hceq, hconf]; intro h; cases h
  obtain ⟨r, hEr, hres, hconf', htids⟩ := h4.netConf m' hnet hne
  have hrd := (h3.rc r).res (by
    rcases (h3.rc r).resFlag hres with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hres⟩)
  obtain ⟨p, e, h1, h2, -, -, -, h6, -, h8, h9, -, -, -, -, -, -, -, -, h18⟩ := hrd
  rw [← hceq, hconf', h18] at hconf
  obtain ⟨hk1, hk2⟩ := conf_inj hconf
  simp only [cfk.injEq] at hk1
  simp only [thT.injEq] at hk2
  obtain ⟨hck2, hthr⟩ := hk1
  have htl := tlist_inj hk2.2
  have hthr' : RrThr thh b m = (g.rst r).thf := hthr.symm
  have h2' := h2
  rw [← hthr'] at h2'
  simp only [RrThr, thR.injEq] at h2'
  obtain ⟨hthh, hbb, hsc, hme, hmcr⟩ := h2'
  have hbp : t.psk = p := by
    have := hb.symm.trans hbb
    rw [hthh] at this
    exact (binder_inj this).1
  have hpsk : (g.rst r).tpsk = t.psk := by rw [h9, hbp]
  have hep := (hE.ep r (by rw [h8]; intro h; cases h)).2.2.2
  obtain ⟨k', hk'⟩ := hep
  obtain ⟨k0, hk0⟩ := hsess
  rw [hpsk, hk0] at hk'
  have hr1 : r.1 = peer := by
    have := Option.some.inj hk'
    exact (Prod.mk.inj this).1.symm
  obtain ⟨tr, htr, htr1, -, htr3, -⟩ := h4.rok r hres
  have htt : tr = t := h4.lfun tr t htr hti (by rw [htr1, hpsk])
  refine ⟨r, hEr, hres, hthr, (tlist_inj hk2.2).symm, by rw [h6, hck2, hthr], hmcr, hr1, by rw [← htr3, htt, hown]⟩


/-! ## The client store -/

theorem CDropExpired_mem {sl : List Slot} {a : Slot} (h : a ∈ CDropExpired sl) (ho : a.occ = true) : a ∈ sl := by
  simp only [CDropExpired, List.mem_map] at h
  obtain ⟨x, hx, hxa⟩ := h
  have := dropExp_occ hxa ho
  rw [this]; exact hx

theorem CTake_mem {sl : List Slot} {peer : Nat} {al : Term} {x : Slot} (h : x ∈ (CTake sl peer al).sl)
    (ho : x.occ = true) : x ∈ sl := by
  unfold CTake at h
  cases hc : CFind (CDropExpired sl) peer al with
  | none => simp only [hc] at h; exact CDropExpired_mem h ho
  | some i =>
    simp only [hc] at h
    rcases Put_mem h with h | h
    · exact CDropExpired_mem h ho
    · simp [h, NoSlot] at ho

theorem CTake_tk {sl : List Slot} {peer : Nat} {al : Term} {tk : Tk} (h : (CTake sl peer al).tk = some tk) :
    ∃ x ∈ sl, x.occ = true ∧ TicketOf x = tk ∧ x.peer = peer := by
  unfold CTake at h
  cases hc : CFind (CDropExpired sl) peer al with
  | none => simp only [hc] at h; cases h
  | some i =>
    simp only [hc, Option.some.injEq] at h
    unfold CFind at hc
    rw [List.findIdx?_eq_some_iff_getElem] at hc
    obtain ⟨hl, hp, -⟩ := hc
    have hget : (CDropExpired sl).getD i NoSlot = (CDropExpired sl)[i] := by
      simp [List.getD_eq_getElem?_getD, hl]
    rw [hget] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨ho, hpe⟩, -⟩ := hp
    exact ⟨_, CDropExpired_mem (List.getElem_mem hl) ho, ho, h, hpe⟩

theorem CInsert_mem {sl : List Slot} {tk : Tk} {x : Slot} (h : x ∈ CInsert sl tk) : x ∈ sl ∨ TicketOf x = tk := by
  unfold CInsert at h
  rcases Put_mem h with h | h
  · exact Or.inl h
  · right; subst h; rfl

theorem CInsertAll_mem (tks : List Tk) : ∀ {sl : List Slot} {x : Slot}, x ∈ CInsertAll sl tks →
    x ∈ sl ∨ ∃ tk ∈ tks, TicketOf x = tk := by
  induction tks with
  | nil => intro sl x h; exact Or.inl h
  | cons t r ih =>
    intro sl x h
    rcases ih h with h | ⟨tk, htk, e⟩
    · rcases CInsert_mem h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨t, by simp, h⟩
    · exact Or.inr ⟨tk, by simp [htk], e⟩

theorem KeepSeq_mem : ∀ (l : List Tk) (drop : List Nat) (j : Nat) {tk : Tk}, tk ∈ KeepSeq l drop j → tk ∈ l := by
  intro l
  induction l with
  | nil => intro drop j tk h; simp [KeepSeq] at h
  | cons t r ih =>
    intro drop j tk h
    simp only [KeepSeq, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h
      · simp at h; subst h; simp
    · exact List.mem_cons_of_mem _ (ih _ _ h)

theorem CExport_mem {sl : List Slot} {mx : Nat} {tk : Tk} (h : tk ∈ CExport sl mx) :
    ∃ y ∈ sl, y.occ = true ∧ TicketOf y = tk := by
  unfold CExport at h
  simp only [] at h
  have h1 := List.mem_of_mem_drop h
  simp only [List.mem_map, List.mem_mergeSort, Live, List.mem_filter] at h1
  obtain ⟨y, ⟨hy, hy2⟩, rfl⟩ := h1
  simp only [Bool.and_eq_true] at hy2
  exact ⟨y, hy, hy2.1, rfl⟩

theorem IRes2Of_mono {g g' : G} (hs : Step g g') {s : Nat × Nat} {st : IState} (h : IRes2Of g s st) :
    IRes2Of g' s st := by
  obtain ⟨r, hE, hres, hthf, htids, hres2, hpcr, hr1, hpeer⟩ := h
  obtain ⟨sp, nr, ph, hph, hb⟩ := rst_est_stab hs r hE
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, hpcr, hr1, ?_⟩ <;> rw [hb]
  · exact hph
  · exact hres
  · exact hthf
  · exact htids
  · exact hres2
  · exact hpeer

/-! ## Initiator states: the ticket facts a step keeps -/

theorem CkS_of_near {n : Nat} {t : Tk} {st st' : IState} (h : CkS n t st) (hn : Near st st')
    (hr : (st'.ph = .done → st'.resumed = true) → t.cr = st'.rcr) : CkS n t st' :=
  ⟨hn.2.1.trans h.ck, by rw [hn.2.2.1]; exact h.peer, hn.2.2.2.1.trans h.tid, h.own,
    by rw [hn.2.2.1]; exact h.sess, h.sec, by rw [hn.2.2.2.2, hn.1]; exact h.binder, hr⟩

theorem CkS_ihandle {s : Nat × Nat} {t : Tk} {st : IState} (m : Msg) (hI : ICl s st) (hL : ILoc st)
    (h : CkS s.1 t st) : CkS s.1 t (IHandle st s.1 m).st := by
  refine CkS_of_near h (IHandle_near st s.1 m) ?_
  rcases IHandle_cases st s.1 m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hio, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, hc, c1, -⟩ | ⟨hp, hl, hty, hc, c1, -⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact h.rcr
  · rw [c1]; intro _; exact h.rcr (fun e => by rcases hp with hp | hp <;> simp [hp] at e)
  · rw [c1]; intro _; exact h.rcr (fun e => by simp [hp] at e)
  · rw [c1]; intro _; exact h.rcr (fun e => by simp [hp] at e)
  · rw [c1]; intro _; exact h.rcr (fun e => by simp [hp] at e)
  · rw [c1]; intro _
    have hl' := hL.late hp hl
    exact (h.rcr (fun e => by rcases hp with hp | hp | hp <;> simp [hp] at e)).trans hl'.2.1.symm
  · rw [c1]; intro _; exact h.rcr (fun e => by simp [hp] at e)

theorem CkS_ikey {s : Nat × Nat} {t : Tk} {st : IState} (kind : KRes) (hI : ICl s st)
    (h : CkS s.1 t st) : CkS s.1 t (IKey st s.1 kind).st := by
  refine CkS_of_near h (IKey_near st s.1 kind) ?_
  rcases IKey_cases st s.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, -, -, -, -, -, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · rw [c1]; exact h.rcr
  · rw [c1]; intro _; exact h.rcr (fun e => by rcases hp with hp | hp <;> simp [hp] at e)
  · rw [c1]; intro _; exact h.rcr (fun e => by simp [hp] at e)
  · rw [c1]; intro hh
    exfalso
    have := hh (by simp [ikDoneSt])
    have h2 := hI.resFlag (by simpa [ikDoneSt] using this)
    rw [hp] at h2; cases h2

theorem CkS_iretransmit {s : Nat × Nat} {t : Tk} {st : IState} (h : CkS s.1 t st) :
    CkS s.1 t (IRetransmit s.1 st).st := by
  refine CkS_of_near h (IRetransmit_near s.1 st) ?_
  rcases IRetransmit_cases s.1 st with ⟨hp, hsh, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨c1, -⟩
  · rw [c1]; exact h.rcr
  · rw [c1]; exact h.rcr
  · rw [c1]; intro _; exact h.rcr (fun e => by simp [hp] at e)
  · rw [c1]; exact h.rcr

theorem CkS_ished {n : Nat} {t : Tk} {st : IState} (h : CkS n t st) : CkS n t (IShed st) :=
  ⟨h.ck, h.peer, h.tid, h.own, h.sess, h.sec, h.binder, h.rcr⟩

theorem CkS_acc {n : Nat} {t : Tk} {st : IState} (h : CkS n t st) : CkS n t { st with acc := true } :=
  ⟨h.ck, h.peer, h.tid, h.own, h.sess, h.sec, h.binder, h.rcr⟩

theorem CkS_new {g : G} {n k peer : Nat} {al : Term} {short : Bool} {tk : Tk} (h : CliTk g n tk) (hp : tk.peer = peer) :
    ∃ t, g.issued t ∧ CkS n t (INew n k peer al short (some tk)).st := by
  obtain ⟨hpe, ⟨k0, hk0⟩, hsec, t, ht, e1, e2, e3, e4⟩ := h
  refine ⟨t, ht, ?_, ?_, ?_, e3, ?_, ?_, ?_, ?_⟩ <;> simp [INew, IBeginResume, Ok, e2, e1, e4, ← hp]
  · exact hpe
  · exact ⟨k0, hk0⟩
  · exact hsec


/-! ## The initiator clauses -/

theorem stepIStart_tk (sl : List Slot) (peer : Nat) (al : Term) (take : Bool) (tk : Tk)
    (h : (if take = true then CTake sl peer al else (⟨sl, none⟩ : CTakeRes)).tk = some tk) :
    ∃ x ∈ sl, x.occ = true ∧ TicketOf x = tk ∧ x.peer = peer := by
  by_cases ht : take = true
  · simp only [ht, if_true] at h; exact CTake_tk h
  · simp only [ht, if_false] at h; cases h

theorem iloc_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ s, ILoc (g'.ist s) := by
  have h3 := Inv3_reach hr
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    intro s
    show ILoc (upd g.ist s0 _ s)
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact ILoc_new _ _ _ _ _ _
    · rw [upd_ne _ _ _ _ e]; exact h4.iloc s
  | iRecv s0 m hn hd =>
    intro s
    show ILoc (upd g.ist s0 _ s)
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact ILoc_ihandle _ _ m (h3.ic s) (h4.iloc s)
    · rw [upd_ne _ _ _ _ e]; exact h4.iloc s
  | iAnswer s0 kind hn hph =>
    intro s
    show ILoc (upd g.ist s0 _ s)
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact ILoc_ikey _ _ kind (h3.ic s) (h4.iloc s)
    · rw [upd_ne _ _ _ _ e]; exact h4.iloc s
  | iRetrans s0 hn hph =>
    intro s
    show ILoc (upd g.ist s0 _ s)
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact ILoc_iretransmit _ _ (h4.iloc s)
    · rw [upd_ne _ _ _ _ e]; exact h4.iloc s
  | iShed s0 hn hph =>
    intro s
    show ILoc (upd g.ist s0 _ s)
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact ILoc_ished _ (h4.iloc s)
    · rw [upd_ne _ _ _ _ e]; exact h4.iloc s
  | iAccept s0 tids hn hph hacc hpe hat =>
    intro s
    show ILoc (upd g.ist s0 _ s)
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact ILoc_acc _ (h4.iloc s)
    · rw [upd_ne _ _ _ _ e]; exact h4.iloc s
  | _ => exact h4.iloc

theorem ick_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ s, (g'.ist s).ckpsk ≠ nil → ∃ t, g'.issued t ∧ CkS s.1 t (g'.ist s) := by
  have h3 := Inv3_reach hr
  have mono := issued_mono hs
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    intro s hne
    by_cases e : s = s0
    · subst e
      have hist : (stepIStart g s peer al short take).ist s = (INew s.1 s.2 peer al short
          (if take = true then CTake (g.cli s.1) peer al else (⟨g.cli s.1, none⟩ : CTakeRes)).tk).st := by
        show upd g.ist s _ s = _; rw [upd_same]
      rw [hist] at hne ⊢
      cases htk : (if take = true then CTake (g.cli s.1) peer al else (⟨g.cli s.1, none⟩ : CTakeRes)).tk with
      | none => rw [htk] at hne; simp [INew, IBeginFull, Ok] at hne
      | some tk =>
        rw [htk] at hne
        obtain ⟨x, hx, hxo, hxt, hxp⟩ := stepIStart_tk _ _ _ _ _ htk
        have hc := h4.cli s.1 x hx hxo
        rw [hxt] at hc
        obtain ⟨t, ht, hck⟩ := CkS_new (k := s.2) (peer := peer) (al := al) (short := short) hc (by rw [← hxt]; exact hxp)
        exact ⟨t, mono t ht, hck⟩
    · have : (stepIStart g s0 peer al short take).ist s = g.ist s := upd_ne _ _ _ _ e
      rw [this] at hne ⊢
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, hC⟩
  | iRecv s0 m hn hd =>
    intro s hne
    by_cases e : s = s0
    · subst e
      have hist : (stepIRecv g s m).ist s = (IHandle (g.ist s) s.1 m).st := by
        show upd g.ist s _ s = _; rw [upd_same]
      rw [hist] at hne ⊢
      obtain ⟨t, ht, hC⟩ := h4.ick s (by rw [← (IHandle_near _ _ m).2.1]; exact hne)
      exact ⟨t, mono t ht, CkS_ihandle m (h3.ic s) (h4.iloc s) hC⟩
    · have : (stepIRecv g s0 m).ist s = g.ist s := upd_ne _ _ _ _ e
      rw [this]; rw [this] at hne
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, hC⟩
  | iAnswer s0 kind hn hph =>
    intro s hne
    by_cases e : s = s0
    · subst e
      have hist : (stepIAnswer g s kind).ist s = (IKey (g.ist s) s.1 kind).st := by
        show upd g.ist s _ s = _; rw [upd_same]
      rw [hist] at hne ⊢
      obtain ⟨t, ht, hC⟩ := h4.ick s (by rw [← (IKey_near _ _ kind).2.1]; exact hne)
      exact ⟨t, mono t ht, CkS_ikey kind (h3.ic s) hC⟩
    · have : (stepIAnswer g s0 kind).ist s = g.ist s := upd_ne _ _ _ _ e
      rw [this]; rw [this] at hne
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, hC⟩
  | iRetrans s0 hn hph =>
    intro s hne
    by_cases e : s = s0
    · subst e
      have hist : (stepIRetrans g s).ist s = (IRetransmit s.1 (g.ist s)).st := by
        show upd g.ist s _ s = _; rw [upd_same]
      rw [hist] at hne ⊢
      obtain ⟨t, ht, hC⟩ := h4.ick s (by rw [← (IRetransmit_near s.1 _).2.1]; exact hne)
      exact ⟨t, mono t ht, CkS_iretransmit hC⟩
    · have : (stepIRetrans g s0).ist s = g.ist s := upd_ne _ _ _ _ e
      rw [this]; rw [this] at hne
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, hC⟩
  | iShed s0 hn hph =>
    intro s hne
    by_cases e : s = s0
    · subst e
      have hist : (stepIShed g s).ist s = IShed (g.ist s) := by
        show upd g.ist s _ s = _; rw [upd_same]
      rw [hist] at hne ⊢
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, CkS_ished hC⟩
    · have : (stepIShed g s0).ist s = g.ist s := upd_ne _ _ _ _ e
      rw [this]; rw [this] at hne
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, hC⟩
  | iAccept s0 tids hn hph hacc hpe hat =>
    intro s hne
    by_cases e : s = s0
    · subst e
      have hist : (stepIAccept g s tids).ist s = { g.ist s with acc := true } := by
        show upd g.ist s _ s = _; rw [upd_same]
      rw [hist] at hne ⊢
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, CkS_acc hC⟩
    · have : (stepIAccept g s0 tids).ist s = g.ist s := upd_ne _ _ _ _ e
      rw [this]; rw [this] at hne
      obtain ⟨t, ht, hC⟩ := h4.ick s hne
      exact ⟨t, mono t ht, hC⟩
  | _ =>
    intro s hne
    obtain ⟨t, ht, hC⟩ := h4.ick s hne
    exact ⟨t, mono t ht, hC⟩


/-- A finished resumption by Reply: the responder session that sent it. -/
theorem complete_ires2 {K C : Nat} {g : G} (hr : Reach K C g) (h4 : Inv4 g) (s0 : Nat × Nat) (m : Msg)
    (hd : Derivable g m) (x : Atom) (ckp thh b rcr ad : Term) (hne : (g.ist s0).ckpsk ≠ nil)
    (hck : ckp = (g.ist s0).ckpsk) (hthh : thh = (g.ist s0).thh) (hb : b = (g.ist s0).binder)
    (hc : RrConfOK x ckp thh b m) : IRes2Of g s0 (IResumed (g.ist s0) x ckp thh b rcr ad m) := by
  obtain ⟨t, ht, hC⟩ := h4.ick s0 hne
  obtain ⟨r, hE, hres, hthf, htids, hres2, hmcr, hr1, hpeer⟩ :=
    rreply_origin hr h4 m hd x ckp thh b t s0.1 (g.ist s0).peer ht (hck.trans hC.ck) hC.sec
      (by rw [hb, hthh]; exact hC.binder) hC.sess hC.own hc
  exact ⟨r, hE, hres, hthf, htids, hres2.symm, hmcr, hr1, hpeer⟩

theorem ires2_upd {g g' : G} (hs : Step g g') (h4 : Inv4 g) {s0 : Nat × Nat} {st' : IState}
    (hist : g'.ist = upd g.ist s0 st') (hnew : st'.ph = .done → st'.resumed = true → IRes2Of g' s0 st') :
    ∀ s, (g'.ist s).ph = .done → (g'.ist s).resumed = true → IRes2Of g' s (g'.ist s) := by
  intro s hph hres
  rw [hist] at hph hres ⊢
  by_cases e : s = s0
  · subst e; rw [upd_same] at *; exact hnew hph hres
  · rw [upd_ne _ _ _ _ e] at *; exact IRes2Of_mono hs (h4.ires2 s hph hres)

theorem ires2_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ s, (g'.ist s).ph = .done → (g'.ist s).resumed = true → IRes2Of g' s (g'.ist s) := by
  have h3 := Inv3_reach hr
  have hs0 := hs
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    refine ires2_upd hs0 h4 rfl ?_
    intro hp _
    have h := (INew_props s0.1 s0.2 peer al short
      (if take = true then CTake (g.cli s0.1) peer al else (⟨g.cli s0.1, none⟩ : CTakeRes)).tk).1
    rcases h with h | h <;> rw [h] at hp <;> cases hp
  | iRecv s0 m hn hd =>
    refine ires2_upd hs0 h4 rfl ?_
    have hI := h3.ic s0
    rcases IHandle_cases (g.ist s0) s0.1 m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hio, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
      | ⟨hp, hty, hc, c1, -⟩ | ⟨hp, hl, hty, hc, c1, -⟩ | ⟨hp, hty, he, c1, -⟩
    · rw [c1]; intro hph hres; exact IRes2Of_mono hs0 (h4.ires2 s0 hph hres)
    · rw [c1]; intro hph; rcases hp with hp | hp <;> simp [hp] at hph
    · rw [c1]; intro hph; simp [hp] at hph
    · rw [c1]; intro hph; simp [hp] at hph
    · rw [c1]; intro _ _
      obtain ⟨⟨p, hp1, -⟩, -, -⟩ := hI.resume hp
      exact complete_ires2 hr h4 s0 m hd _ _ _ _ _ _ (by rw [hp1]; intro h; cases h) rfl rfl rfl hc
    · rw [c1]; intro _ _
      have hl' := (h4.iloc s0).late hp hl
      obtain ⟨p, hp1, -⟩ := hI.late hl
      exact complete_ires2 hr h4 s0 m hd _ _ _ _ _ _ (by rw [← hl'.1, hp1]; intro h; cases h) hl'.1 hl'.2.2.1 hl'.2.2.2 hc
    · rw [c1]; intro hph; simp [rrFall, IBeginFull, Ok] at hph
  | iAnswer s0 kind hn hph =>
    refine ires2_upd hs0 h4 rfl ?_
    have hI := h3.ic s0
    rcases IKey_cases (g.ist s0) s0.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, -, -, -, -, -, c1, -⟩ | ⟨hp, hk, c1, -⟩
    · rw [c1]; intro hph hres; exact IRes2Of_mono hs0 (h4.ires2 s0 hph hres)
    · rw [c1]; intro hph; rcases hp with hp | hp <;> simp [hp] at hph
    · rw [c1]; intro hph; simp [ikSignSt] at hph
    · rw [c1]; intro _ hres
      have h2 := hI.resFlag (by simpa [ikDoneSt] using hres)
      rw [hp] at h2; cases h2
  | iRetrans s0 hn hph =>
    refine ires2_upd hs0 h4 rfl ?_
    rcases IRetransmit_cases s0.1 (g.ist s0) with ⟨hp, hsh, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨c1, -⟩
    · rw [c1]; intro hph; simp [hp] at hph
    · rw [c1]; intro hph; simp [hp] at hph
    · rw [c1]; intro hph; simp [lateFall, lateFallB, IBeginFull, Ok] at hph
    · rw [c1]; intro hph hres; exact IRes2Of_mono hs0 (h4.ires2 s0 hph hres)
  | iShed s0 hn hph =>
    refine ires2_upd hs0 h4 rfl ?_
    intro hph hres; exact IRes2Of_mono hs0 (h4.ires2 s0 hph hres)
  | iAccept s0 tids hn hph hacc hpe hat =>
    refine ires2_upd hs0 h4 rfl ?_
    intro hph hres; exact IRes2Of_mono hs0 (h4.ires2 s0 hph hres)
  | _ => intro s hph hres; exact IRes2Of_mono hs0 (h4.ires2 s hph hres)


/-! ## The network -/

theorem INew_out (n k peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) :
    ∀ x ∈ (INew n k peer al short tk).out, x.conf = nil ∧
      (x.binder = nil ∨ ∃ t, tk = some t ∧ x.binder = binder t.psk (INew n k peer al short tk).st.thh) := by
  intro x hx
  cases tk with
  | none =>
    simp [INew, IBeginFull, Ok] at hx; subst hx; simp [IInitMsg]
  | some t =>
    simp [INew, IBeginResume, Ok] at hx; subst hx
    exact ⟨rfl, Or.inr ⟨t, rfl, rfl⟩⟩

theorem RKey_out (st : RState) (n k : Nat) (sto : Store) (kind : KRes) :
    ∀ x ∈ (RKey st n k sto kind).out, x.conf = nil ∧ x.binder = nil := by
  intro x hx
  rcases RKey_cases st n k sto kind with ⟨c1, c2, -⟩ | ⟨hp, c1, c2, -⟩ | ⟨hp, hk, c1, c2, -⟩ <;> rw [c2] at hx
  · simp at hx
  · simp at hx
  · simp at hx; subst hx; simp [rkReply]

/-- What a responder step sends: a message already on the network, one without a tag or binder, or the Reply of a
Hello it accepted. -/
theorem RHandle_out {g : G} (h1 : Inv1 g) (s : Nat × Nat) (m : Msg) (cs : List (List Nat)) :
    ∀ x ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).out, g.net x ∨ (x.conf = nil ∧ x.binder = nil) ∨
      (x = rhReply s.1 s.2 (g.sto s.1) m cs ∧ (g.rst s).ph = .idle ∧ m.ty = .hello ∧ rhUsable (g.sto s.1) m ∧
        (rhIs s.1 s.2 (g.sto s.1) m cs).ok = true ∧
        (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).st = rhSt (g.rst s) s.1 s.2 (g.sto s.1) m cs) := by
  intro x hx
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m cs with ⟨c1, c2, c3, c4, -⟩ | ⟨hp, c1, c2, c3, c4, -⟩
    | ⟨hp, ⟨sp, nr, c1⟩, c2, c3, c4, -⟩
    | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, had, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
  · rw [c2] at hx; simp at hx
  · rw [c2] at hx; simp at hx
  · rcases c2 with c2 | c2 <;> rw [c2] at hx
    · simp at hx
    · simp at hx; subst hx; exact Or.inl (h1.rFinish s (Or.inr hp))
  · rw [c2] at hx; simp at hx; subst hx; exact Or.inl (h1.rFinish s (Or.inl hp))
  · rw [c2] at hx; simp at hx; subst hx; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [c2] at hx; simp at hx
  · rw [c2] at hx; simp at hx
  · rw [c2] at hx; simp at hx
  · rw [c2] at hx; simp at hx; subst hx; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [c2] at hx; simp at hx; subst hx; exact Or.inr (Or.inr ⟨rfl, hp, hty, hu, hok, c1⟩)
  · rw [c2] at hx; simp at hx


theorem netConf_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ m, g'.net m → m.conf ≠ nil → ∃ r, Est (g'.rst r).ph ∧ (g'.rst r).resumed = true ∧
      m.conf = (g'.rst r).reply.conf ∧ m.tids = (g'.rst r).mytids := by
  have h1 := Inv1_reach hr
  have hs0 := hs
  have old : ∀ m, g.net m → m.conf ≠ nil → ∃ r, Est (g'.rst r).ph ∧ (g'.rst r).resumed = true ∧
      m.conf = (g'.rst r).reply.conf ∧ m.tids = (g'.rst r).mytids := by
    intro m hm hne
    obtain ⟨r, hE, hres, hc, ht⟩ := h4.netConf m hm hne
    obtain ⟨sp, nr, ph, hph, hb⟩ := rst_est_stab hs0 r hE
    exact ⟨r, by rw [hb]; exact hph, by rw [hb]; exact hres, by rw [hb]; exact hc, by rw [hb]; exact ht⟩
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (INew_out _ _ _ _ _ _ m hm).1 hne
  | iRecv s0 m0 hn hd =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (IHandle_out_nil _ _ _ m hm).1 hne
  | iAnswer s0 kind hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (IKey_out_nil _ _ _ m hm).1 hne
  | iRetrans s0 hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · rcases IRetransmit_out h1 s0 m hm with ⟨hc, -⟩ | hn' | ⟨-, rfl⟩
      · exact absurd hc hne
      · exact old m hn' hne
      · exact absurd rfl hne
  | rRecv s m0 cs hn hd =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · rcases RHandle_out h1 s m0 cs m hm with hn' | ⟨hc, -⟩ | ⟨rfl, hp, hty, hu, hok, c1⟩
      · exact old m hn' hne
      · exact absurd hc hne
      · have hst : (stepRRecv g s m0 cs).rst s = rhSt (g.rst s) s.1 s.2 (g.sto s.1) m0 cs := by
          rw [stepRRecv_rst_same, c1]
        exact ⟨s, by rw [hst]; exact Or.inr rfl, by rw [hst]; rfl, by rw [hst]; rfl, by rw [hst]; rfl⟩
  | rAnswer s kind hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (RKey_out _ _ _ _ _ m hm).1 hne
  | rRetrans s hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · simp [RRetransmit, hph, ROk] at hm; subst hm
      exact old _ (h1.rFinish s (Or.inl hph)) hne
  | _ => intro m hm hne; exact old m hm hne

theorem netHello_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ m, g'.net m → m.binder ≠ nil →
      ∃ s t, s.1 ≠ att ∧ (g'.ist s).thh ≠ nil ∧ g'.issued t ∧ t.peer = s.1 ∧ m.binder = binder t.psk (g'.ist s).thh := by
  have h1 := Inv1_reach hr
  have h3 := Inv3_reach hr
  have hs0 := hs
  have old : ∀ m, g.net m → m.binder ≠ nil →
      ∃ s t, s.1 ≠ att ∧ (g'.ist s).thh ≠ nil ∧ g'.issued t ∧ t.peer = s.1 ∧ m.binder = binder t.psk (g'.ist s).thh := by
    intro m hm hne
    obtain ⟨s, t, hn, hth, ht, htp, hb⟩ := h4.netHello m hm hne
    have := thh_keep h4.iloc hs0 s hth
    exact ⟨s, t, hn, by rw [this]; exact hth, issued_mono hs0 t ht, htp, by rw [this]; exact hb⟩
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · have hist : (stepIStart g s0 peer al short take).ist s0 = (INew s0.1 s0.2 peer al short
          (if take = true then CTake (g.cli s0.1) peer al else (⟨g.cli s0.1, none⟩ : CTakeRes)).tk).st := by
        show upd g.ist s0 _ s0 = _; rw [upd_same]
      rcases (INew_out _ _ _ _ _ _ m hm).2 with hb | ⟨tk, htk, hb⟩
      · exact absurd hb hne
      · obtain ⟨x, hx, hxo, hxt, hxp⟩ := stepIStart_tk _ _ _ _ _ htk
        have hc := h4.cli s0.1 x hx hxo
        rw [hxt] at hc
        obtain ⟨-, -, -, t', ht', e1, e2, e3, e4⟩ := hc
        refine ⟨s0, t', hn, ?_, issued_mono hs0 t' ht', e3, ?_⟩
        · rw [hist, htk]; simp [INew, IBeginResume, Ok]
        · rw [hist, hb, e2]
  | iRecv s0 m0 hn hd =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (IHandle_out_nil _ _ _ m hm).2 hne
  | iAnswer s0 kind hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (IKey_out_nil _ _ _ m hm).2 hne
  | iRetrans s0 hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · rcases IRetransmit_out h1 s0 m hm with ⟨-, hc⟩ | hn' | ⟨hp, rfl⟩
      · exact absurd hc hne
      · exact old m hn' hne
      · have hist : (stepIRetrans g s0).ist s0 = (IRetransmit s0.1 (g.ist s0)).st := by
          show upd g.ist s0 _ s0 = _; rw [upd_same]
        obtain ⟨⟨p, hp1, hp2, hp3, hp4⟩, -, -⟩ := (h3.ic s0).resume hp
        obtain ⟨t, ht, hC⟩ := h4.ick s0 (by rw [hp1]; intro h; cases h)
        have hnr := IRetransmit_near s0.1 (g.ist s0)
        have hth : (g.ist s0).thh ≠ nil := by rw [hp2]; intro h; cases h
        refine ⟨s0, t, hn, ?_, issued_mono hs0 t ht, hC.own, ?_⟩
        · rw [hist, hnr.1]; exact hth
        · rw [hist, hnr.1]; exact hC.binder
  | rRecv s m0 cs hn hd =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · rcases RHandle_out h1 s m0 cs m hm with hn' | ⟨-, hc⟩ | ⟨rfl, hp, hty, hu, hok, c1⟩
      · exact old m hn' hne
      · exact absurd hc hne
      · exact absurd rfl hne
  | rAnswer s kind hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · exact absurd (RKey_out _ _ _ _ _ m hm).2 hne
  | rRetrans s hn hph =>
    intro m hm hne
    rcases hm with hm | hm
    · exact old m hm hne
    · simp [RRetransmit, hph, ROk] at hm; subst hm
      exact old _ (h1.rFinish s (Or.inl hph)) hne
  | _ => intro m hm hne; exact old m hm hne

end Vinc.Hs
