import Vinc.HandshakeSecrecy
import Vinc.HandshakeStore

/-!
# Resumption: where tickets come from, for unboundedly many sessions

The origin of every ticket: an issued ticket, a ticket in a client store and the ticket a resuming initiator or
responder holds each trace back to one finished responder session (the one whose id is the ticket id), whose
resumption secret the pre-shared key is derived from. A finished responder session never changes, so these facts stay
true. They are the bridge from the keys of a resumed session to the keys of the session it resumes, for agreement,
secrecy and authentication of resumptions.
-/

namespace Vinc.Hs
open Term

/-- A finished responder session never changes. -/
theorem rst_done_stable {g g' : G} (hs : Step g g') (r : Nat × Nat) (hd : (g.rst r).ph = .done) :
    g'.rst r = g.rst r := by
  cases hs with
  | rRecv s m hn hdv =>
    show upd g.rst s _ r = g.rst r
    by_cases hh : r = s
    · subst hh
      rcases RHandle_cases (g.rst r) r.1 r.2 (g.sto r.1) m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, c1, -⟩ | ⟨hp, hty, c1, -⟩
        | ⟨hp, hty, hprm, c1, -⟩ | ⟨hp, hty, hk, had, hsg, c1, -⟩ | ⟨hp, hty, hprm, c1, -⟩
        | ⟨hp, hty, hprm, i0, hf, he, hb, c1, -⟩
      · rw [upd_same, c1]
      all_goals (exfalso; first | (rcases hp with hp | hp <;> simp [hd] at hp) | simp [hd] at hp)
    · exact upd_ne _ _ _ _ hh
  | rAnswer s kind hn =>
    show upd g.rst s _ r = g.rst r
    by_cases hh : r = s
    · subst hh
      rcases RKey_cases (g.rst r) r.1 r.2 (g.sto r.1) kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
      · rw [upd_same, c1]
      all_goals (exfalso; simp [hd] at hp)
    · exact upd_ne _ _ _ _ hh
  | _ => rfl

/-- The issuing session of a ticket id. -/
def Issuer (g : G) (rn rk : Nat) : Prop := (g.rst (rn, rk)).ph = .done ∧ (g.rst (rn, rk)).mytid = tid rn rk

def IssOK (g : G) (t : Tk) : Prop := ∃ rn rk, t.tid = tid rn rk ∧ Issuer g rn rk ∧
  t.psk = psk (g.rst (rn, rk)).res t.tid ∧ t.peer = (g.rst (rn, rk)).peer

def CliOK (g : G) (n : Nat) (tk : Tk) : Prop := ∃ rn rk, tk.tid = tid rn rk ∧ tk.peer = rn ∧ rn ≠ att ∧ Issuer g rn rk ∧
  tk.psk = psk (g.rst (rn, rk)).res tk.tid ∧ (g.rst (rn, rk)).peer = n

def IresOK (g : G) (n : Nat) (st : IState) : Prop := ∃ rn rk, st.tid = tid rn rk ∧ st.peer = rn ∧ rn ≠ att ∧
  Issuer g rn rk ∧ st.ckpsk = ckpsk (psk (g.rst (rn, rk)).res st.tid) ∧ (g.rst (rn, rk)).peer = n

def RresOK (g : G) (r : Nat × Nat) (st : RState) : Prop := ∃ rk0, st.tid = tid r.1 rk0 ∧ Issuer g r.1 rk0 ∧
  st.peer = (g.rst (r.1, rk0)).peer ∧ st.early = early (ckpsk (psk (g.rst (r.1, rk0)).res st.tid)) st.thh

/-- The ticket ledger, the client stores, the resumers and the network point at finished responder sessions. -/
structure Inv4 (g : G) : Prop where
  iss : ∀ t, g.issued t → IssOK g t
  cli : ∀ n tk, tk ∈ g.cli n → CliOK g n tk
  ires : ∀ s, ((g.ist s).ph = .resume ∨ ((g.ist s).ph = .done ∧ (g.ist s).resumed = true)) → IresOK g s.1 (g.ist s)
  ires2 : ∀ s, (g.ist s).ph = .done → (g.ist s).resumed = true →
    ∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧ (g.rst r).thf = (g.ist s).thf ∧
      (g.ist s).tids = one (tid r.1 r.2)
  rres : ∀ r, (g.rst r).ph = .done → (g.rst r).resumed = true → RresOK g r (g.rst r)
  secrres : ∀ r, (g.rst r).ph = .done → (g.rst r).resumed = true → (g.rst r).peer ≠ att → ¬ Known (g.rst r).res
  netConf : ∀ m, g.net m → m.conf ≠ nil →
    ∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧ m.tids = one (tid r.1 r.2) ∧
      ∃ ck', (g.rst r).res = res ck' (g.rst r).thf ∧
        m.conf = conf (cfk ck' (g.rst r).thf) (thT (g.rst r).thf (one (tid r.1 r.2)))
  netHello : ∀ m, g.net m → m.binder ≠ nil →
    ∃ s rn rk, m.tid = tid rn rk ∧ (g.ist s).thh = thH ok m.tid m.e ∧ Issuer g rn rk ∧ (g.rst (rn, rk)).peer = s.1 ∧
      s.1 ≠ att ∧ m.binder = binder (psk (g.rst (rn, rk)).res m.tid) (thH ok m.tid m.e)
  rres2 : ∀ r, (g.rst r).ph = .done → (g.rst r).resumed = true → (g.rst r).peer ≠ att →
    ∃ k, (g.ist ((g.rst r).peer, k)).thh = (g.rst r).thh
  nonethh : ∀ s, (g.ist s).ph = .none → (g.ist s).thh = nil

/-! ### Stability of what refers to finished responder sessions -/

theorem Issuer_stab {g g' : G} (hs : Step g g') {rn rk : Nat} (h : Issuer g rn rk) : Issuer g' rn rk := by
  have := rst_done_stable hs (rn, rk) h.1
  unfold Issuer; rw [this]; exact h

theorem IssOK_stab {g g' : G} (hs : Step g g') {t : Tk} (h : IssOK g t) : IssOK g' t := by
  obtain ⟨rn, rk, a, b, c, d⟩ := h
  have := rst_done_stable hs (rn, rk) b.1
  exact ⟨rn, rk, a, Issuer_stab hs b, by rw [this]; exact c, by rw [this]; exact d⟩

theorem CliOK_stab {g g' : G} (hs : Step g g') {n : Nat} {t : Tk} (h : CliOK g n t) : CliOK g' n t := by
  obtain ⟨rn, rk, a, a', a'', b, c, d⟩ := h
  have := rst_done_stable hs (rn, rk) b.1
  exact ⟨rn, rk, a, a', a'', Issuer_stab hs b, by rw [this]; exact c, by rw [this]; exact d⟩

theorem IresOK_stab {g g' : G} (hs : Step g g') {n : Nat} {st : IState} (h : IresOK g n st) : IresOK g' n st := by
  obtain ⟨rn, rk, a, a', a'', b, c, d⟩ := h
  have := rst_done_stable hs (rn, rk) b.1
  exact ⟨rn, rk, a, a', a'', Issuer_stab hs b, by rw [this]; exact c, by rw [this]; exact d⟩

theorem RresOK_stab {g g' : G} (hs : Step g g') {r : Nat × Nat} {st : RState} (h : RresOK g r st) : RresOK g' r st := by
  obtain ⟨rk0, a, b, c, d⟩ := h
  have := rst_done_stable hs (r.1, rk0) b.1
  exact ⟨rk0, a, Issuer_stab hs b, by rw [this]; exact c, by rw [this]; exact d⟩

/-- A ticket issued by a step of a responder session: it is the session's own, under its new finished state. -/
theorem RHandle_iss (st : RState) (n k : Nat) (sto : Store) (m : Msg) (t : Tk) (ht : t ∈ (RHandle st n k sto m).iss) :
    (RHandle st n k sto m).st.ph = .done ∧ (RHandle st n k sto m).st.mytid = tid n k ∧ t.tid = tid n k ∧
    t.psk = psk (RHandle st n k sto m).st.res t.tid ∧ t.peer = (RHandle st n k sto m).st.peer := by
  rcases RHandle_cases st n k sto m with ⟨-, -, -, c4, -⟩ | ⟨-, -, -, -, c4, -⟩ | ⟨-, -, -, -, -, c4, -⟩
    | ⟨-, -, -, -, -, c4, -⟩ | ⟨-, -, -, -, -, -, c4, -⟩ | ⟨-, -, -, -, -, c1, -, -, c4, -⟩
    | ⟨-, -, -, -, -, c4, -⟩ | ⟨_, _, _, _, _, _, _, c1, _, _, c4, _⟩
  · simp [c4] at ht
  · simp [c4] at ht
  · simp [c4] at ht
  · simp [c4] at ht
  · simp [c4] at ht
  · rw [c4] at ht; simp at ht; subst ht; rw [c1]; simp [rfSt, rfRes]
  · simp [c4] at ht
  · rw [c4] at ht; simp at ht; subst ht; rw [c1]; simp [rhSt, rhCk2]

theorem Inv4_iss_step {g g' : G} (hs : Step g g') (h4 : ∀ t, g.issued t → IssOK g t) :
    ∀ t, g'.issued t → IssOK g' t := by
  have old : ∀ t, g.issued t → IssOK g' t := fun t ht => IssOK_stab hs (h4 t ht)
  cases hs with
  | rRecv s m hn hdv =>
    intro t ht
    rcases ht with ht | ht
    · exact old t ht
    · obtain ⟨a, b, c, d, e⟩ := RHandle_iss _ _ _ _ _ _ ht
      refine ⟨s.1, s.2, c, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [upd_same, *]
  | startFull => exact old
  | startResume => exact old
  | iRecv => exact old
  | iAnswer => exact old
  | iRetransmit => exact old
  | iAcceptFull => exact old
  | iAcceptResumed => exact old
  | rAnswer => exact old
  | expire => exact old

/-! ### Agreement of resumptions -/

theorem tid_inj {a b c d : Nat} (h : tid a b = tid c d) : a = c ∧ b = d := by
  simp only [tid.injEq] at h; exact h

/-- Two finished resumptions with the same final transcript hash hold the same keys and name each other. -/
theorem agree_res {g : G} (h3 : Inv3 g) (h4 : Inv4 g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hri : (g.ist i).resumed = true) (hr : (g.rst r).ph = .done) (hrr : (g.rst r).resumed = true)
    (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).send = (g.rst r).recv ∧ (g.ist i).recv = (g.rst r).send ∧ (g.ist i).res = (g.rst r).res ∧
    (g.ist i).peer = r.1 ∧ (g.rst r).peer = i.1 := by
  obtain ⟨rp, e, hf, -, hs, hrv, hrs⟩ := (h3.ic i).2.2.2.2.2.2 hi hri
  obtain ⟨p, hck, hthh, hbind, hx, -, -⟩ := (h3.ic i).2.2.2.2.2.1 (Or.inr ⟨hi, hri⟩)
  obtain ⟨p', e', b', hthh', hf', -, hb', hs', hr', hrs', -, -, -, -⟩ := (h3.rc r).2.2.2.2.2.2.2.1 hr hrr
  have hthf := hth
  rw [hf, hf'] at hth
  simp only [thR.injEq] at hth
  obtain ⟨h1, h2, h3', h4'⟩ := hth
  rw [hthh] at h1
  rw [hthh'] at h1
  simp only [thH.injEq] at h1
  obtain ⟨-, htid, hee⟩ := h1
  have hpp : p = p' := by
    have : binder p (g.ist i).thh = binder p' (g.rst r).thh := by rw [← hbind, ← hb', h2]
    have h' : (g.ist i).thh = (g.rst r).thh := by
      rw [hthh, hthh', htid, hee]
    rw [h'] at this
    simp only [binder.injEq] at this; exact this.1
  have hxe : atomOf e' = (g.ist i).x := by rw [← hee]; simp [atomOf]
  have hrye : atomOf e = ry r.1 r.2 := by rw [h4']; simp [atomOf]
  have hD : Dh (g.ist i).x (atomOf e) = Dh (ry r.1 r.2) (atomOf e') := by rw [hrye, hxe, Dh_comm]
  have hk : ck2 (ck1r (g.ist i).ckpsk (Dh (g.ist i).x (atomOf e))) (g.ist i).thf =
      ck2 (ck1r (ckpsk p') (Dh (ry r.1 r.2) (atomOf e'))) (g.rst r).thf := by
    rw [hck, hpp, hD, hthf]
  obtain ⟨rn, rk, hit, hip, -, -, -, hrp⟩ := h4.ires i (Or.inr ⟨hi, hri⟩)
  obtain ⟨rk0, hrt, -, hrpeer, -⟩ := h4.rres r hr hrr
  have hti : tid rn rk = tid r.1 rk0 := by rw [← hit, ← hrt]; exact htid
  obtain ⟨hrn, hrk⟩ := tid_inj hti
  subst hrn hrk
  refine ⟨?_, ?_, ?_, hip, ?_⟩
  · rw [hs, hr', hk, hthf]
  · rw [hrv, hs', hk, hthf]
  · rw [hrs, hrs', hk, hthf]
  · rw [hrpeer]; exact hrp

/-- The resumption secret of a finished responder session with an honest peer is secret. -/
theorem issuer_res_secret {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) {rn rk : Nat} (hI : Issuer g rn rk)
    (hp : (g.rst (rn, rk)).peer ≠ att) : ¬ Known (g.rst (rn, rk)).res := by
  cases hres : (g.rst (rn, rk)).resumed
  · exact (secrecy_resp_full hr (rn, rk) hI.1 hres hp).2.2
  · exact h4.secrres (rn, rk) hI.1 hres hp

/-! ### The client stores -/

theorem cli_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ n tk, tk ∈ g'.cli n → CliOK g' n tk := by
  have h3 := Inv3_reach hr
  have hst := hs
  have old : ∀ n tk, tk ∈ g.cli n → CliOK g' n tk := fun n tk ht => CliOK_stab hst (h4.cli n tk ht)
  cases hs with
  | startFull => exact old
  | iRecv => exact old
  | iAnswer => exact old
  | iRetransmit => exact old
  | rRecv => exact old
  | rAnswer => exact old
  | expire => exact old
  | startResume s tk0 hn hph hc =>
    intro n tk ht
    by_cases hh : n = s.1
    · subst hh
      simp only [upd_same, List.mem_filter] at ht
      exact old _ tk ht.1
    · simp only [upd_ne _ _ _ _ hh] at ht
      exact old _ tk ht
  | iAcceptFull s r hd hacc hpe hrsm hr1 hrd hth =>
    intro n tk ht
    by_cases hh : n = s.1
    · subst hh
      simp only [upd_same, List.mem_cons] at ht
      rcases ht with ht | ht
      · have hrr : (g.rst r).resumed = false := by
          have := agreement_resumed_flag hr s r hd hrd hth.symm
          rw [hrsm] at this; exact this.symm
        obtain ⟨k1, k2, k3, k4, k5⟩ := agreement_full hr s r hd hrd hrsm hrr hth.symm
        have hmy : (g.rst r).mytid = tid r.1 r.2 := (h3.rc r).2.2.2.2.2.2.2.2.2.1 hrd
        subst ht
        refine ⟨r.1, r.2, hmy, hr1.symm, ?_, ⟨hrd, hmy⟩, ?_, k5⟩
        · rw [hr1]; exact hpe
        · simp only [k3]
      · exact old _ tk ht
    · simp only [upd_ne _ _ _ _ hh] at ht
      exact old _ tk ht
  | iAcceptResumed s t hd hacc hpe hrsm ht0 =>
    intro n tk ht
    by_cases hh : n = s.1
    · subst hh
      simp only [upd_same, List.mem_cons] at ht
      rcases ht with ht | ht
      · obtain ⟨r, hrd, hrr, hthf, htids⟩ := h4.ires2 s hd hrsm
        obtain ⟨k1, k2, k3, k4, k5⟩ := agree_res h3 h4 s r hd hrsm hrd hrr hthf.symm
        have hmy : (g.rst r).mytid = tid r.1 r.2 := (h3.rc r).2.2.2.2.2.2.2.2.2.1 hrd
        rw [htids] at ht0
        simp [tidsList] at ht0
        subst ht ht0
        refine ⟨r.1, r.2, rfl, k4.symm ▸ rfl, ?_, ⟨hrd, hmy⟩, ?_, k5⟩
        · rw [← k4]; exact hpe
        · simp only [k3]
      · exact old _ tk ht
    · simp only [upd_ne _ _ _ _ hh] at ht
      exact old _ tk ht

/-! ### The resuming initiators -/

def ResP (st : IState) : Prop := st.ph = .resume ∨ (st.ph = .done ∧ st.resumed = true)

theorem ires_ihandle (g : G) (s : Nat × Nat) (m : Msg) (hold : ResP (g.ist s) → IresOK g s.1 (g.ist s)) :
    ResP (IHandle (g.ist s) s.1 m).st → IresOK g s.1 (IHandle (g.ist s) s.1 m).st := by
  rcases IHandle_cases (g.ist s) s.1 m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hr, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, c1, -, hc⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact hold
  · rw [c1]; intro hh; simp [ResP] at hh
  · rw [c1]; intro hh; simp [ResP] at hh
  · rw [c1]; intro hh; simp [ResP, hp] at hh
  · rw [c1]; intro _
    have := hold (Or.inl hp)
    simpa [IresOK, rrDone] using this
  · rw [c1]; intro hh; simp [ResP, rrFall, IBeginFull, Ok] at hh

theorem ires_ikey (g : G) (s : Nat × Nat) (kind : KRes) (hI : ICl s (g.ist s))
    (hold : ResP (g.ist s) → IresOK g s.1 (g.ist s)) :
    ResP (IKey (g.ist s) s.1 kind).st → IresOK g s.1 (IKey (g.ist s) s.1 kind).st := by
  rcases IKey_cases (g.ist s) s.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, k1, k2, k3, k4, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · rw [c1]; exact hold
  · rw [c1]; intro hh; simp [ResP] at hh
  · rw [c1]; intro hh; simp [ResP, ikSignSt] at hh
  · rw [c1]; intro hh
    have hres : (g.ist s).resumed = false := (hI.2.2.2.1 hp).1.1.2.2
    simp [ResP, ikDoneSt, hres] at hh

theorem ires_gen {g g' : G} (hst : Step g g') (h4 : Inv4 g) (s0 : Nat × Nat) (st0 : IState)
    (hist : g'.ist = upd g.ist s0 st0) (hnew : ResP st0 → IresOK g' s0.1 st0) :
    ∀ s, ResP (g'.ist s) → IresOK g' s.1 (g'.ist s) := by
  intro s hp
  by_cases hh : s = s0
  · subst hh; rw [hist, upd_same] at hp ⊢; exact hnew hp
  · rw [hist, upd_ne _ _ _ _ hh] at hp ⊢; exact IresOK_stab hst (h4.ires s hp)

theorem ires_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ s, ResP (g'.ist s) → IresOK g' s.1 (g'.ist s) := by
  have h3 := Inv3_reach hr
  have hst := hs
  have same : ∀ (hi : g'.ist = g.ist), ∀ s, ResP (g'.ist s) → IresOK g' s.1 (g'.ist s) := by
    intro hi s hp; rw [hi] at hp ⊢; exact IresOK_stab hst (h4.ires s hp)
  cases hs with
  | startFull s peer short hn hph hpe =>
    exact ires_gen hst h4 s _ rfl (by intro hp; simp [ResP, IBeginFull, Ok] at hp)
  | startResume s tk hn hph hc =>
    refine ires_gen hst h4 s _ rfl ?_
    intro _
    obtain ⟨rn, rk, a, b, c, d, e, f⟩ := h4.cli s.1 tk hc
    have hs' := rst_done_stable hst (rn, rk) d.1
    refine ⟨rn, rk, ?_, ?_, c, Issuer_stab hst d, ?_, ?_⟩
    · simpa [IBeginResume, Ok] using a
    · simpa [IBeginResume, Ok] using b
    · show ckpsk tk.psk = ckpsk (psk (g.rst (rn, rk)).res tk.tid)
      rw [e]
    · show (g.rst (rn, rk)).peer = s.1; exact f
  | iRecv s m hn hd =>
    exact ires_gen hst h4 s _ rfl (fun hp => IresOK_stab hst (ires_ihandle g s m (h4.ires s) hp))
  | iAnswer s kind hn =>
    exact ires_gen hst h4 s _ rfl (fun hp => IresOK_stab hst (ires_ikey g s kind (h3.ic s) (h4.ires s) hp))
  | iRetransmit => exact same rfl
  | rRecv => exact same rfl
  | rAnswer => exact same rfl
  | expire => exact same rfl
  | iAcceptFull s r hd hacc hpe hrsm hr1 hrd hth =>
    exact ires_gen hst h4 s _ rfl (fun hp => IresOK_stab hst (by simpa [IresOK, ResP] using h4.ires s (by simpa [ResP] using hp)))
  | iAcceptResumed s t hd hacc hpe hrsm ht0 =>
    exact ires_gen hst h4 s _ rfl (fun hp => IresOK_stab hst (by simpa [IresOK, ResP] using h4.ires s (by simpa [ResP] using hp)))

/-! ### The resuming responders -/

/-- The slot a Hello finds is a ticket of a finished session of the same node. -/
theorem slot_origin {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) (n i0 : Nat) (t : Term)
    (hf : (g.sto n).tks.findIdx? (fun s => s.occ && s.tid == t) = some i0) :
    ∃ k0, t = tid n k0 ∧ Issuer g n k0 ∧ (rhSlot (g.sto n) i0).psk = psk (g.rst (n, k0)).res t ∧
      (rhSlot (g.sto n) i0).peer = (g.rst (n, k0)).peer := by
  obtain ⟨sl0, hsl, hocc, htid⟩ := find_facts _ _ _ hf
  have hrs : rhSlot (g.sto n) i0 = sl0 := by simp [rhSlot, hsl]
  have hrt := InvRT_reach hr
  obtain ⟨k, hk1, hk2⟩ := hrt.sO n i0 sl0 hsl hocc
  have hi := hrt.sI n i0 sl0 hsl hocc
  obtain ⟨rn, rk, a, b, c, d⟩ := h4.iss _ hi
  simp only at a c d
  rw [hk1] at a
  obtain ⟨hn, hk⟩ := tid_inj a
  subst hn hk
  refine ⟨k, htid.symm.trans hk1, b, ?_, ?_⟩
  · rw [hrs, c, htid]
  · rw [hrs]; exact d

theorem rres_rhandle {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) (s : Nat × Nat) (m : Msg) :
    (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.ph = .done → (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.resumed = true →
      RresOK g s (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st := by
  have h3 := Inv3_reach hr
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, c1, -⟩ | ⟨hp, hty, c1, -⟩
    | ⟨hp, hty, hprm, c1, -⟩ | ⟨hp, hty, hk, had, hsg, c1, -⟩ | ⟨hp, hty, hprm, c1, -⟩
    | ⟨hp, hty, hprm, i0, hf, he, hb, c1, -⟩
  · rw [c1]; exact h4.rres s
  · rw [c1]; intro hh; simp at hh
  · rw [c1]; exact h4.rres s
  · rw [c1]; exact h4.rres s
  · rw [c1]; intro hh; simp [rInitSt] at hh
  · rw [c1]; intro _ hh
    obtain ⟨-, ⟨m', hm⟩, -⟩ := (h3.rc s).2.2.2.2.1 hp
    have : (g.rst s).resumed = false := hm.2.2.2.2.2.2.2.2.2.2.2.2
    simp [rfSt, this] at hh
  · rw [c1]; exact h4.rres s
  · rw [c1]; intro _ _
    obtain ⟨k0, ht, hI, hpsk, hpeer⟩ := slot_origin hr h4 s.1 i0 m.tid hf
    refine ⟨k0, ?_, hI, ?_, ?_⟩
    · simp [rhSt, ht]
    · simp [rhSt, hpeer]
    · simp [rhSt, hpsk, ht]

theorem rres_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → RresOK g' r (g'.rst r) := by
  have hst := hs
  have same : ∀ (hi : g'.rst = g.rst), ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true →
      RresOK g' r (g'.rst r) := by
    intro hi r hp hq; rw [hi] at hp hq ⊢; exact RresOK_stab hst (h4.rres r hp hq)
  have gen : ∀ (s0 : Nat × Nat) (st0 : RState) (hrst : g'.rst = upd g.rst s0 st0)
      (hnew : st0.ph = .done → st0.resumed = true → RresOK g s0 st0),
      ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → RresOK g' r (g'.rst r) := by
    intro s0 st0 hrst hnew r hp hq
    by_cases hh : r = s0
    · subst hh; rw [hrst, upd_same] at hp hq ⊢; exact RresOK_stab hst (hnew hp hq)
    · rw [hrst, upd_ne _ _ _ _ hh] at hp hq ⊢; exact RresOK_stab hst (h4.rres r hp hq)
  cases hs with
  | startFull => exact same rfl
  | startResume => exact same rfl
  | iRecv => exact same rfl
  | iAnswer => exact same rfl
  | iRetransmit => exact same rfl
  | iAcceptFull => exact same rfl
  | iAcceptResumed => exact same rfl
  | expire => exact same rfl
  | rRecv s m hn hd => exact gen s _ rfl (rres_rhandle hr h4 s m)
  | rAnswer s kind hn =>
    refine gen s _ rfl ?_
    rcases RKey_cases (g.rst s) s.1 s.2 (g.sto s.1) kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
    · rw [c1]; exact h4.rres s
    · rw [c1]; intro hh; simp at hh
    · rw [c1]; intro hh; simp [rkSt] at hh

/-! ### Secrecy of the resumed responders -/

theorem secrres_rhandle {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) (s : Nat × Nat) (m : Msg) :
    (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.ph = .done → (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.resumed = true →
      (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.peer ≠ att → ¬ Known (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.res := by
  have h3 := Inv3_reach hr
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, c1, -⟩ | ⟨hp, hty, c1, -⟩
    | ⟨hp, hty, hprm, c1, -⟩ | ⟨hp, hty, hk, had, hsg, c1, -⟩ | ⟨hp, hty, hprm, c1, -⟩
    | ⟨hp, hty, hprm, i0, hf, he, hb, c1, -⟩
  · rw [c1]; exact h4.secrres s
  · rw [c1]; intro hh; simp at hh
  · rw [c1]; exact h4.secrres s
  · rw [c1]; exact h4.secrres s
  · rw [c1]; intro hh; simp [rInitSt] at hh
  · rw [c1]; intro _ hh
    obtain ⟨-, ⟨m', hm⟩, -⟩ := (h3.rc s).2.2.2.2.1 hp
    have : (g.rst s).resumed = false := hm.2.2.2.2.2.2.2.2.2.2.2.2
    simp [rfSt, this] at hh
  · rw [c1]; exact h4.secrres s
  · rw [c1]; intro _ _ hpe
    obtain ⟨k0, ht, hI, hpsk, hpeer⟩ := slot_origin hr h4 s.1 i0 m.tid hf
    have hpe' : (g.rst (s.1, k0)).peer ≠ att := by rw [← hpeer]; simpa [rhSt] using hpe
    have hsec := issuer_res_secret hr h4 hI hpe'
    simp only [rhSt, rhCk2, Known]
    intro hk
    apply hsec
    have : Known (psk (g.rst (s.1, k0)).res m.tid) := by rw [← hpsk]; exact hk.1
    simpa [Known] using this

theorem secrres_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → (g'.rst r).peer ≠ att → ¬ Known (g'.rst r).res := by
  have same : ∀ (hi : g'.rst = g.rst), ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true →
      (g'.rst r).peer ≠ att → ¬ Known (g'.rst r).res := by
    intro hi r hp hq hz; rw [hi] at hp hq hz ⊢; exact h4.secrres r hp hq hz
  have gen : ∀ (s0 : Nat × Nat) (st0 : RState) (hrst : g'.rst = upd g.rst s0 st0)
      (hnew : st0.ph = .done → st0.resumed = true → st0.peer ≠ att → ¬ Known st0.res),
      ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → (g'.rst r).peer ≠ att → ¬ Known (g'.rst r).res := by
    intro s0 st0 hrst hnew r hp hq hz
    by_cases hh : r = s0
    · subst hh; rw [hrst, upd_same] at hp hq hz ⊢; exact hnew hp hq hz
    · rw [hrst, upd_ne _ _ _ _ hh] at hp hq hz ⊢; exact h4.secrres r hp hq hz
  cases hs with
  | startFull => exact same rfl
  | startResume => exact same rfl
  | iRecv => exact same rfl
  | iAnswer => exact same rfl
  | iRetransmit => exact same rfl
  | iAcceptFull => exact same rfl
  | iAcceptResumed => exact same rfl
  | expire => exact same rfl
  | rRecv s m hn hd => exact gen s _ rfl (secrres_rhandle hr h4 s m)
  | rAnswer s kind hn =>
    refine gen s _ rfl ?_
    rcases RKey_cases (g.rst s) s.1 s.2 (g.sto s.1) kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
    · rw [c1]; exact h4.secrres s
    · rw [c1]; intro hh; simp at hh
    · rw [c1]; intro hh; simp [rkSt] at hh

/-! ### The responder behind an accepted resumption reply -/

theorem conf_inj {a b c d : Term} (h : conf a b = conf c d) : a = c ∧ b = d := by
  simp only [conf.injEq] at h; exact h

theorem rreply_origin {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) (s : Nat × Nat) (m : Msg)
    (hn : s.1 ≠ att) (hd : Derivable g m) (hph : (g.ist s).ph = .resume)
    (hc : m.conf = conf (cfk (rrCk2 (g.ist s) m) (rrThr (g.ist s) m)) (thT (rrThr (g.ist s) m) m.tids)) :
    ∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧ (g.rst r).thf = rrThr (g.ist s) m ∧
      m.tids = one (tid r.1 r.2) ∧ (g.rst r).res = res (rrCk2 (g.ist s) m) (rrThr (g.ist s) m) := by
  obtain ⟨rn, rk, a, b, c, d, e, f⟩ := h4.ires s (Or.inl hph)
  have hsec : ¬ Known (g.ist s).ckpsk := by
    rw [e]
    have := issuer_res_secret hr h4 d (by rw [f]; exact hn)
    simpa [Known] using this
  have hmn : ∃ m', g.net m' ∧ m'.conf = m.conf := by
    rcases hd with hnet | ⟨-, -, -, hcf⟩
    · exact ⟨m, hnet, rfl⟩
    · rcases hcf _ _ hc with hk | hk
      · exfalso
        simp only [Known, rrCk2] at hk
        exact hsec hk.1
      · exact hk
  obtain ⟨m', hnm', hcm'⟩ := hmn
  have hne : m'.conf ≠ nil := by rw [hcm', hc]; simp
  obtain ⟨r, hrd, hrr, htids, ck', hres, hconf⟩ := h4.netConf m' hnm' hne
  rw [hcm', hc] at hconf
  obtain ⟨h1, h2⟩ := conf_inj hconf
  simp only [cfk.injEq] at h1
  obtain ⟨hck2, hthr⟩ := h1
  simp only [thT.injEq] at h2
  refine ⟨r, hrd, hrr, hthr.symm, ?_, ?_⟩
  · exact h2.2
  · rw [hres, hck2, hthr]

theorem ires2_ihandle {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) (s : Nat × Nat) (m : Msg) (hn : s.1 ≠ att)
    (hd : Derivable g m) :
    (IHandle (g.ist s) s.1 m).st.ph = .done → (IHandle (g.ist s) s.1 m).st.resumed = true →
      ∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧ (g.rst r).thf = (IHandle (g.ist s) s.1 m).st.thf ∧
        (IHandle (g.ist s) s.1 m).st.tids = one (tid r.1 r.2) := by
  rcases IHandle_cases (g.ist s) s.1 m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hr', c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, c1, -, hc⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact h4.ires2 s
  · rw [c1]; intro hh; simp at hh
  · rw [c1]; intro hh; simp at hh
  · rw [c1]; intro hh; simp [hp] at hh
  · rw [c1]; intro _ _
    obtain ⟨r, a, b, c, d, e⟩ := rreply_origin hr h4 s m hn hd hp hc
    exact ⟨r, a, b, by simpa [rrDone] using c, by simpa [rrDone] using d⟩
  · rw [c1]; intro hh; simp [rrFall, IBeginFull, Ok] at hh

theorem ires2_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ s, (g'.ist s).ph = .done → (g'.ist s).resumed = true →
      ∃ r, (g'.rst r).ph = .done ∧ (g'.rst r).resumed = true ∧ (g'.rst r).thf = (g'.ist s).thf ∧
        (g'.ist s).tids = one (tid r.1 r.2) := by
  have h3 := Inv3_reach hr
  have hst := hs
  have tr : ∀ (s : Nat × Nat) (st0 : IState), (∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧
      (g.rst r).thf = st0.thf ∧ st0.tids = one (tid r.1 r.2)) →
      ∃ r, (g'.rst r).ph = .done ∧ (g'.rst r).resumed = true ∧ (g'.rst r).thf = st0.thf ∧
        st0.tids = one (tid r.1 r.2) := by
    intro s st0 ⟨r, a, b, c, d⟩
    have := rst_done_stable hst r a
    exact ⟨r, by rw [this]; exact a, by rw [this]; exact b, by rw [this]; exact c, d⟩
  have gen : ∀ (s0 : Nat × Nat) (st0 : IState) (hist : g'.ist = upd g.ist s0 st0)
      (hnew : st0.ph = .done → st0.resumed = true → ∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧
        (g.rst r).thf = st0.thf ∧ st0.tids = one (tid r.1 r.2)),
      ∀ s, (g'.ist s).ph = .done → (g'.ist s).resumed = true →
        ∃ r, (g'.rst r).ph = .done ∧ (g'.rst r).resumed = true ∧ (g'.rst r).thf = (g'.ist s).thf ∧
          (g'.ist s).tids = one (tid r.1 r.2) := by
    intro s0 st0 hist hnew s hp hq
    by_cases hh : s = s0
    · subst hh; rw [hist, upd_same] at hp hq ⊢; exact tr s _ (hnew hp hq)
    · rw [hist, upd_ne _ _ _ _ hh] at hp hq ⊢; exact tr s _ (h4.ires2 s hp hq)
  have same : ∀ (hi : g'.ist = g.ist), ∀ s, (g'.ist s).ph = .done → (g'.ist s).resumed = true →
      ∃ r, (g'.rst r).ph = .done ∧ (g'.rst r).resumed = true ∧ (g'.rst r).thf = (g'.ist s).thf ∧
        (g'.ist s).tids = one (tid r.1 r.2) := by
    intro hi s hp hq; rw [hi] at hp hq ⊢; exact tr s _ (h4.ires2 s hp hq)
  cases hs with
  | startFull s peer short hn hph hpe =>
    exact gen s _ rfl (by intro hp; simp [IBeginFull, Ok] at hp)
  | startResume s tk hn hph hc =>
    exact gen s _ rfl (by intro hp; simp [IBeginResume, Ok] at hp)
  | iRecv s m hn hd => exact gen s _ rfl (ires2_ihandle hr h4 s m hn hd)
  | iAnswer s kind hn =>
    refine gen s _ rfl ?_
    rcases IKey_cases (g.ist s) s.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, k1, k2, k3, k4, c1, -⟩ | ⟨hp, hk, c1, -⟩
    · rw [c1]; exact h4.ires2 s
    · rw [c1]; intro hh; simp at hh
    · rw [c1]; intro hh; simp [ikSignSt] at hh
    · rw [c1]; intro _ hh
      have hres : (g.ist s).resumed = false := ((h3.ic s).2.2.2.1 hp).1.1.2.2
      simp [ikDoneSt, hres] at hh
  | iRetransmit => exact same rfl
  | rRecv => exact same rfl
  | rAnswer => exact same rfl
  | expire => exact same rfl
  | iAcceptFull s r hd hacc hpe hrsm hr1 hrd hth =>
    exact gen s _ rfl (fun hp hq => by simpa using h4.ires2 s hp hq)
  | iAcceptResumed s t hd hacc hpe hrsm ht0 =>
    exact gen s _ rfl (fun hp hq => by simpa using h4.ires2 s hp hq)

/-! ### The network -/

theorem IHandle_out_nil (st : IState) (n : Nat) (m : Msg) : ∀ x ∈ (IHandle st n m).out, x.conf = nil ∧ x.binder = nil := by
  rcases IHandle_cases st n m with ⟨-, c2⟩ | ⟨-, -, c2⟩ | ⟨-, -, -, -, c2⟩ | ⟨-, -, -, -, -, c2⟩
    | ⟨-, -, -, c2, -⟩ | ⟨-, -, -, -, c2⟩
  all_goals (intro x hx; rw [c2] at hx; simp [IBeginFull, Ok] at hx; try (subst hx; simp); try (rcases hx with hx | hx <;> subst hx <;> simp))

theorem IKey_out_nil (st : IState) (n : Nat) (kind : KRes) : ∀ x ∈ (IKey st n kind).out, x.conf = nil ∧ x.binder = nil := by
  rcases IKey_cases st n kind with ⟨-, c2, -⟩ | ⟨-, -, c2, -⟩ | ⟨-, -, -, -, -, -, -, c2, -⟩ | ⟨-, -, -, c2, -⟩
  all_goals (intro x hx; rw [c2] at hx; simp at hx; try (subst hx; simp))

theorem RKey_out_nil (st : RState) (n k : Nat) (sto : Store) (kind : KRes) :
    ∀ x ∈ (RKey st n k sto kind).out, x.conf = nil ∧ x.binder = nil := by
  rcases RKey_cases st n k sto kind with ⟨-, c2, -⟩ | ⟨-, -, c2, -⟩ | ⟨-, -, -, c2, -⟩
  all_goals (intro x hx; rw [c2] at hx; simp [rkReply] at hx; try (subst hx; simp))

/-- What a responder step can put on the network. -/
theorem RHandle_out {K : Nat} {g : G} (hr : Reach K g) (s : Nat × Nat) (m : Msg) :
    ∀ x ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).out, x.binder = nil ∧
      (x.conf ≠ nil → (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.ph = .done ∧
        (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.resumed = true ∧ x.tids = one (tid s.1 s.2) ∧
        ∃ ck', (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.res = res ck' (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.thf ∧
          x.conf = conf (cfk ck' (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.thf)
            (thT (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.thf (one (tid s.1 s.2)))) := by
  have h3 := Inv3_reach hr
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m with ⟨-, c2, -⟩ | ⟨-, -, c2, -⟩ | ⟨hp, hty, c1, c2, -⟩
    | ⟨-, -, c1, c2, -⟩ | ⟨-, -, -, c1, c2, -⟩ | ⟨-, -, -, -, -, c1, c2, -⟩ | ⟨-, -, -, c1, c2, -⟩
    | ⟨hp, hty, hprm, i0, hf, he, hb, c1, c2, -⟩
  · intro x hx; rw [c2] at hx; simp at hx
  · intro x hx; rw [c2] at hx; simp at hx
  · intro x hx; rw [c2] at hx; simp at hx; subst hx
    have := (h3.rc s).2.2.2.2.2.2.2.2.2.2 hp
    exact ⟨this.2, fun h => absurd this.1 h⟩
  · intro x hx; rw [c2] at hx; simp at hx; subst hx; simp
  · intro x hx; rw [c2] at hx; simp at hx
  · intro x hx; rw [c2] at hx; simp at hx
  · intro x hx; rw [c2] at hx; simp at hx; subst hx; simp
  · intro x hx; rw [c2] at hx; simp at hx; subst hx
    refine ⟨by simp [rhMsg], fun _ => ?_⟩
    rw [c1]
    refine ⟨rfl, rfl, by simp [rhMsg], rhCk2 s.1 s.2 (g.sto s.1) i0 m, by simp [rhSt], by simp [rhMsg, rhSt]⟩

/-! ### The Hello transcripts of the initiators -/

theorem IHandle_thh (st : IState) (n : Nat) (m : Msg) : (IHandle st n m).st.thh = st.thh ∧
    ((IHandle st n m).st.ph = .none → st.ph = .none) := by
  rcases IHandle_cases st n m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hr, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, c1, -, hc⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact ⟨rfl, id⟩
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp at hh
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp at hh
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp [hp] at hh
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp [rrDone] at hh
  · rw [c1]; refine ⟨by simp [rrFall, IBeginFull, Ok], ?_⟩; intro hh; simp [rrFall, IBeginFull, Ok] at hh

theorem IKey_thh (st : IState) (n : Nat) (kind : KRes) : (IKey st n kind).st.thh = st.thh ∧
    ((IKey st n kind).st.ph = .none → st.ph = .none) := by
  rcases IKey_cases st n kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, k1, k2, k3, k4, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · rw [c1]; exact ⟨rfl, id⟩
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp at hh
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp [ikSignSt] at hh
  · rw [c1]; refine ⟨rfl, ?_⟩; intro hh; simp [ikDoneSt] at hh

/-- The transcript of a session that was started never changes. -/
theorem thh_step {g g' : G} (h4 : Inv4 g) (hs : Step g g') (s : Nat × Nat) (hne : (g.ist s).thh ≠ nil) :
    (g'.ist s).thh = (g.ist s).thh := by
  have hnn : (g.ist s).ph ≠ .none := fun h => hne (h4.nonethh s h)
  cases hs with
  | startFull s0 peer short hn hph hpe =>
    by_cases hh : s = s0
    · subst hh; exact absurd hph hnn
    · show (upd g.ist s0 _ s).thh = _; rw [upd_ne _ _ _ _ hh]
  | startResume s0 tk hn hph hc =>
    by_cases hh : s = s0
    · subst hh; exact absurd hph hnn
    · show (upd g.ist s0 _ s).thh = _; rw [upd_ne _ _ _ _ hh]
  | iRecv s0 m hn hd =>
    by_cases hh : s = s0
    · subst hh; show (upd g.ist s _ s).thh = _; rw [upd_same]; exact (IHandle_thh _ _ _).1
    · show (upd g.ist s0 _ s).thh = _; rw [upd_ne _ _ _ _ hh]
  | iAnswer s0 kind hn =>
    by_cases hh : s = s0
    · subst hh; show (upd g.ist s _ s).thh = _; rw [upd_same]; exact (IKey_thh _ _ _).1
    · show (upd g.ist s0 _ s).thh = _; rw [upd_ne _ _ _ _ hh]
  | iRetransmit => rfl
  | rRecv => rfl
  | rAnswer => rfl
  | expire => rfl
  | iAcceptFull s0 r hd hacc hpe hrsm hr1 hrd hth =>
    by_cases hh : s = s0
    · subst hh; show (upd g.ist s _ s).thh = _; rw [upd_same]
    · show (upd g.ist s0 _ s).thh = _; rw [upd_ne _ _ _ _ hh]
  | iAcceptResumed s0 t hd hacc hpe hrsm ht0 =>
    by_cases hh : s = s0
    · subst hh; show (upd g.ist s _ s).thh = _; rw [upd_same]
    · show (upd g.ist s0 _ s).thh = _; rw [upd_ne _ _ _ _ hh]

theorem nonethh_step {g g' : G} (h4 : Inv4 g) (hs : Step g g') :
    ∀ s, (g'.ist s).ph = .none → (g'.ist s).thh = nil := by
  have gen : ∀ (s0 : Nat × Nat) (st0 : IState) (hist : g'.ist = upd g.ist s0 st0)
      (hnew : st0.ph = .none → st0.thh = nil), ∀ s, (g'.ist s).ph = .none → (g'.ist s).thh = nil := by
    intro s0 st0 hist hnew s hp
    by_cases hh : s = s0
    · subst hh; rw [hist, upd_same] at hp ⊢; exact hnew hp
    · rw [hist, upd_ne _ _ _ _ hh] at hp ⊢; exact h4.nonethh s hp
  cases hs with
  | startFull s peer short hn hph hpe => exact gen s _ rfl (by intro hp; simp [IBeginFull, Ok] at hp)
  | startResume s tk hn hph hc => exact gen s _ rfl (by intro hp; simp [IBeginResume, Ok] at hp)
  | iRecv s m hn hd =>
    exact gen s _ rfl (fun hp => by rw [(IHandle_thh _ _ _).1]; exact h4.nonethh s ((IHandle_thh _ _ _).2 hp))
  | iAnswer s kind hn =>
    exact gen s _ rfl (fun hp => by rw [(IKey_thh _ _ _).1]; exact h4.nonethh s ((IKey_thh _ _ _).2 hp))
  | iRetransmit => exact h4.nonethh
  | rRecv => exact h4.nonethh
  | rAnswer => exact h4.nonethh
  | expire => exact h4.nonethh
  | iAcceptFull s r hd hacc hpe hrsm hr1 hrd hth =>
    exact gen s _ rfl (fun hp => absurd hp (by simp [hd]))
  | iAcceptResumed s t hd hacc hpe hrsm ht0 =>
    exact gen s _ rfl (fun hp => absurd hp (by simp [hd]))

/-! ### Confirmation tags and binders on the network -/

def NC (g : G) (x : Msg) : Prop :=
  ∃ r, (g.rst r).ph = .done ∧ (g.rst r).resumed = true ∧ x.tids = one (tid r.1 r.2) ∧
    ∃ ck', (g.rst r).res = res ck' (g.rst r).thf ∧
      x.conf = conf (cfk ck' (g.rst r).thf) (thT (g.rst r).thf (one (tid r.1 r.2)))

theorem NC_stab {g g' : G} (hs : Step g g') {x : Msg} (h : NC g x) : NC g' x := by
  obtain ⟨r, a, b, c, ck', d, e⟩ := h
  have := rst_done_stable hs r a
  exact ⟨r, by rw [this]; exact a, by rw [this]; exact b, c, ck', by rw [this]; exact d, by rw [this]; exact e⟩

theorem netConf_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ m, g'.net m → m.conf ≠ nil → NC g' m := by
  have hst := hs
  have gen : ∀ (out : List Msg) (hnet : g'.net = addNet g out) (hnew : ∀ x ∈ out, x.conf ≠ nil → NC g' x),
      ∀ m, g'.net m → m.conf ≠ nil → NC g' m := by
    intro out hnet hnew m hm hc
    rw [hnet] at hm
    rcases hm with hm | hm
    · exact NC_stab hst (h4.netConf m hm hc)
    · exact hnew m hm hc
  cases hs with
  | startFull s peer short hn hph hpe =>
    exact gen _ rfl (by intro x hx hc; cases short <;> (simp [IBeginFull, Ok] at hx; subst hx; simp at hc))
  | startResume s tk hn hph hc' =>
    exact gen _ rfl (by intro x hx hc; simp [IBeginResume, Ok] at hx; subst hx; simp at hc)
  | iRecv s m hn hd =>
    exact gen _ rfl (fun x hx hc => absurd (IHandle_out_nil _ _ _ x hx).1 hc)
  | iAnswer s kind hn =>
    exact gen _ rfl (fun x hx hc => absurd (IKey_out_nil _ _ _ x hx).1 hc)
  | iRetransmit s hp hsh =>
    exact gen _ rfl (by intro x hx hc; simp at hx; subst hx; simp at hc)
  | iAcceptFull => exact gen [] (addNet_nil g).symm (by simp)
  | iAcceptResumed => exact gen [] (addNet_nil g).symm (by simp)
  | expire => exact gen [] (addNet_nil g).symm (by simp)
  | rAnswer s kind hn =>
    exact gen _ rfl (fun x hx hc => absurd (RKey_out_nil _ _ _ _ _ x hx).1 hc)
  | rRecv s m hn hd =>
    refine gen _ rfl ?_
    intro x hx hc
    obtain ⟨-, h⟩ := RHandle_out hr s m x hx
    obtain ⟨a, b, c, ck', d, e⟩ := h hc
    exact ⟨s, by simp only [upd_same]; exact a, by simp only [upd_same]; exact b, c, ck',
      by simp only [upd_same]; exact d, by simp only [upd_same]; exact e⟩

def NH (g : G) (x : Msg) : Prop :=
  ∃ s rn rk, x.tid = tid rn rk ∧ (g.ist s).thh = thH ok x.tid x.e ∧ Issuer g rn rk ∧ (g.rst (rn, rk)).peer = s.1 ∧
    s.1 ≠ att ∧ x.binder = binder (psk (g.rst (rn, rk)).res x.tid) (thH ok x.tid x.e)

theorem NH_stab {g g' : G} (h4 : Inv4 g) (hs : Step g g') {x : Msg} (h : NH g x) : NH g' x := by
  obtain ⟨s, rn, rk, a, b, c, d, e, f⟩ := h
  have hne : (g.ist s).thh ≠ nil := by rw [b]; simp
  have := rst_done_stable hs (rn, rk) c.1
  exact ⟨s, rn, rk, a, by rw [thh_step h4 hs s hne]; exact b, Issuer_stab hs c, by rw [this]; exact d, e,
    by rw [this]; exact f⟩

theorem netHello_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ m, g'.net m → m.binder ≠ nil → NH g' m := by
  have hst := hs
  have gen : ∀ (out : List Msg) (hnet : g'.net = addNet g out) (hnew : ∀ x ∈ out, x.binder ≠ nil → NH g' x),
      ∀ m, g'.net m → m.binder ≠ nil → NH g' m := by
    intro out hnet hnew m hm hc
    rw [hnet] at hm
    rcases hm with hm | hm
    · exact NH_stab h4 hst (h4.netHello m hm hc)
    · exact hnew m hm hc
  cases hs with
  | startFull s peer short hn hph hpe =>
    exact gen _ rfl (by intro x hx hc; cases short <;> (simp [IBeginFull, Ok] at hx; subst hx; simp at hc))
  | startResume s tk hn hph hc' =>
    refine gen _ rfl ?_
    intro x hx hc
    simp [IBeginResume, Ok] at hx; subst hx
    obtain ⟨rn, rk, a, b, c, d, e, f⟩ := h4.cli s.1 tk hc'
    have hs' := rst_done_stable hst (rn, rk) d.1
    refine ⟨s, rn, rk, a, ?_, Issuer_stab hst d, ?_, hn, ?_⟩
    · show (upd g.ist s _ s).thh = _
      rw [upd_same]; simp [IBeginResume, Ok]
    · rw [hs']; exact f
    · simp [IBeginResume, Ok]
      rw [hs']; exact e
  | iRecv s m hn hd =>
    exact gen _ rfl (fun x hx hc => absurd (IHandle_out_nil _ _ _ x hx).2 hc)
  | iAnswer s kind hn =>
    exact gen _ rfl (fun x hx hc => absurd (IKey_out_nil _ _ _ x hx).2 hc)
  | iRetransmit s hp hsh =>
    exact gen _ rfl (by intro x hx hc; simp at hx; subst hx; simp at hc)
  | iAcceptFull => exact gen [] (addNet_nil g).symm (by simp)
  | iAcceptResumed => exact gen [] (addNet_nil g).symm (by simp)
  | expire => exact gen [] (addNet_nil g).symm (by simp)
  | rAnswer s kind hn =>
    exact gen _ rfl (fun x hx hc => absurd (RKey_out_nil _ _ _ _ _ x hx).2 hc)
  | rRecv s m hn hd =>
    exact gen _ rfl (fun x hx hc => absurd (RHandle_out hr s m x hx).1 hc)

/-! ### Authentication of the initiator in a resumption -/

theorem binder_inj {a b c d : Term} (h : binder a b = binder c d) : a = c ∧ b = d := by
  simp only [binder.injEq] at h; exact h

theorem rres2_rhandle {K : Nat} {g : G} (hr : Reach K g) (h4 : Inv4 g) (s : Nat × Nat) (m : Msg)
    (hd : Derivable g m) :
    (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.ph = .done → (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.resumed = true →
      (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.peer ≠ att →
      ∃ k, (g.ist ((RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.peer, k)).thh =
        (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st.thh := by
  have h3 := Inv3_reach hr
  rcases RHandle_cases (g.rst s) s.1 s.2 (g.sto s.1) m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, c1, -⟩ | ⟨hp, hty, c1, -⟩
    | ⟨hp, hty, hprm, c1, -⟩ | ⟨hp, hty, hk, had, hsg, c1, -⟩ | ⟨hp, hty, hprm, c1, -⟩
    | ⟨hp, hty, hprm, i0, hf, he, hb, c1, -⟩
  · rw [c1]; exact h4.rres2 s
  · rw [c1]; intro hh; simp at hh
  · rw [c1]; exact h4.rres2 s
  · rw [c1]; exact h4.rres2 s
  · rw [c1]; intro hh; simp [rInitSt] at hh
  · rw [c1]; intro _ hh
    obtain ⟨-, ⟨m', hm⟩, -⟩ := (h3.rc s).2.2.2.2.1 hp
    have : (g.rst s).resumed = false := hm.2.2.2.2.2.2.2.2.2.2.2.2
    simp [rfSt, this] at hh
  · rw [c1]; exact h4.rres2 s
  · rw [c1]; intro _ _ hpe
    obtain ⟨k0, ht, hI, hpsk, hpeer⟩ := slot_origin hr h4 s.1 i0 m.tid hf
    have hpe' : (g.rst (s.1, k0)).peer ≠ att := by rw [← hpeer]; simpa [rhSt] using hpe
    have hsec := issuer_res_secret hr h4 hI hpe'
    have hmn : ∃ m', g.net m' ∧ m'.binder = m.binder := by
      rcases hd with hnet | ⟨-, -, hbo, -⟩
      · exact ⟨m, hnet, rfl⟩
      · rcases hbo _ _ hb.symm with hk | hk
        · exfalso; apply hsec; rw [hpsk] at hk; simpa [Known] using hk
        · exact hk
    obtain ⟨m', hnm', hbm'⟩ := hmn
    have hne : m'.binder ≠ nil := by rw [hbm', ← hb]; simp
    obtain ⟨s', rn, rk, a1, a2, a3, a4, a5, a6⟩ := h4.netHello m' hnm' hne
    rw [hbm', ← hb] at a6
    obtain ⟨-, a7⟩ := binder_inj a6
    simp only [rhThh, hprm, thH.injEq] at a7
    obtain ⟨-, a8, a9⟩ := a7
    have a1' : tid rn rk = tid s.1 k0 := by rw [← a1, ← a8, ht]
    obtain ⟨hn1, hk1⟩ := tid_inj a1'
    subst hn1 hk1
    have hs1 : s'.1 = (rhSt (g.rst s) s.1 s.2 (g.sto s.1) i0 m).peer := by
      rw [← a4]; simp [rhSt, hpeer]
    refine ⟨s'.2, ?_⟩
    have : ((rhSt (g.rst s) s.1 s.2 (g.sto s.1) i0 m).peer, s'.2) = s' := Prod.ext hs1.symm rfl
    rw [this, a2, ← a8, ← a9]
    simp [rhSt, rhThh, hprm]

theorem rres2_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → (g'.rst r).peer ≠ att →
      ∃ k, (g'.ist ((g'.rst r).peer, k)).thh = (g'.rst r).thh := by
  have h3 := Inv3_reach hr
  have hst := hs
  -- the old witness keeps its transcript: it is not nil, because a finished resumption's transcript is a Hello's
  have keep : ∀ r, (g.rst r).ph = .done → (g.rst r).resumed = true → (g.rst r).peer ≠ att →
      ∃ k, (g'.ist ((g.rst r).peer, k)).thh = (g.rst r).thh := by
    intro r hp hq hz
    obtain ⟨k, hk⟩ := h4.rres2 r hp hq hz
    obtain ⟨p, e, b, hh1, -⟩ := (h3.rc r).2.2.2.2.2.2.2.1 hp hq
    have hne : (g.ist ((g.rst r).peer, k)).thh ≠ nil := by rw [hk, hh1]; simp
    exact ⟨k, by rw [thh_step h4 hst _ hne]; exact hk⟩
  have gen : ∀ (s0 : Nat × Nat) (st0 : RState) (hrst : g'.rst = upd g.rst s0 st0) (hist : g'.ist = g.ist)
      (hnew : st0.ph = .done → st0.resumed = true → st0.peer ≠ att → ∃ k, (g.ist (st0.peer, k)).thh = st0.thh),
      ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → (g'.rst r).peer ≠ att →
        ∃ k, (g'.ist ((g'.rst r).peer, k)).thh = (g'.rst r).thh := by
    intro s0 st0 hrst hist hnew r hp hq hz
    by_cases hh : r = s0
    · subst hh; rw [hrst, upd_same] at hp hq hz ⊢; rw [hist]; exact hnew hp hq hz
    · rw [hrst, upd_ne _ _ _ _ hh] at hp hq hz ⊢; exact keep r hp hq hz
  have same : ∀ (hi : g'.rst = g.rst), ∀ r, (g'.rst r).ph = .done → (g'.rst r).resumed = true → (g'.rst r).peer ≠ att →
      ∃ k, (g'.ist ((g'.rst r).peer, k)).thh = (g'.rst r).thh := by
    intro hi r hp hq hz; rw [hi] at hp hq hz ⊢; exact keep r hp hq hz
  cases hs with
  | startFull => exact same rfl
  | startResume => exact same rfl
  | iRecv => exact same rfl
  | iAnswer => exact same rfl
  | iRetransmit => exact same rfl
  | iAcceptFull => exact same rfl
  | iAcceptResumed => exact same rfl
  | expire => exact same rfl
  | rRecv s m hn hd => exact gen s _ rfl rfl (rres2_rhandle hr h4 s m hd)
  | rAnswer s kind hn =>
    refine gen s _ rfl rfl ?_
    rcases RKey_cases (g.rst s) s.1 s.2 (g.sto s.1) kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
    · rw [c1]; exact h4.rres2 s
    · rw [c1]; intro hh; simp at hh
    · rw [c1]; intro hh; simp [rkSt] at hh

end Vinc.Hs
