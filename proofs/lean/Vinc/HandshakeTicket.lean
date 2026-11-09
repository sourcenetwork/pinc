import Vinc.HandshakeSecrecy
import Vinc.HandshakeEarly
import Vinc.HandshakeRej

/-!
# Resumption: where tickets come from, for unboundedly many sessions

Definitions of the invariant `Inv4` and the facts the step proofs share. The tickets that responders issue are
recorded in the ledger `issued`; the invariant ties every ticket a client store, a snapshot, a resuming initiator or
a resumed responder holds to a ledger entry, and an entry to the session that issued it through the pre-shared key
(`pskSess`: the pre-shared key names the responder session whose resumption secret it derives from, so two sessions
never issue the same key although the generator may repeat a ticket id). A ticket whose peer is honest has a
pre-shared key the attacker does not know: the secrecy of the issuing session carries over to it.

* `Led`: ledger entries of an honest peer are secret and a pre-shared key names one entry.
* the responder side: the tickets of an established session, the ticket a resumed session accepted, and the initiator
  that sent the Hello it accepted.
* the initiator side: a resuming session holds a ticket of its peer, and a finished resumption has its keys from the
  responder session whose confirmation the reply carried.
* the client stores and snapshots hold only tickets of the ledger.
* the network: a confirmation tag on the network comes from an established resumed responder, a binder from a
  resuming initiator.
-/

namespace Vinc.Hs
open Term

/-- Established responder phases. -/
def Est (p : RPh) : Prop := p = .done ∨ p = .resumed

theorem Known_ckpsk (p : Term) : Known (ckpsk p) ↔ Known p := Iff.rfl

theorem RInit_resumed {n k : Nat} {st : RState} (h : RInit n k st) : st.resumed = false := by
  obtain ⟨m, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := h
  exact h15

/-- The secret of the resumption secret a Finish with an honest identity derives: the same as for the session that
would finish with no tickets to issue. -/
theorem fin_secret {K C : Nat} {g : G} (hr : Reach K C g) (s : Nat × Nat) (m : Msg) (hn : s.1 ≠ att)
    (hd : Derivable g m) (hty : m.ty = .fin) (hp : (g.rst s).ph = .finish) (hk : (g.rst s).hsi = m.sealed.k)
    (ha : (g.rst s).th3 = m.sealed.ad) (hsg : m.sealed.sig = sig m.sealed.id false (rfT4 (g.rst s) m))
    (hid : m.sealed.id ≠ att) : ¬ Known (rfRes (g.rst s) m) := by
  have hs := Step.rRecv g s m [] hn hd
  have hr' := Reach.step hr hs
  have h3 := Inv3_reach hr
  have hc : (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m []).st = rfSt (g.rst s) s.1 (g.sto s.1) m [] := by
    simp [RHandle, hty, RFinish, hp, ← hk, ← ha, hsg, rfIs, Issue, IssueAll]
  have hres : (g.rst s).resumed = false := RInit_resumed ((h3.rc s).finish hp).2.1
  have e1 : ((stepRRecv g s m []).rst s) = rfSt (g.rst s) s.1 (g.sto s.1) m [] := by
    show upd g.rst s _ s = _
    rw [upd_same, hc]
  have := secrecy_resp_full hr' s (by rw [e1]; rfl) (by rw [e1]; simpa [rfSt] using hres)
    (by rw [e1]; simpa [rfSt] using hid)
  rw [e1] at this
  exact this.2.2.1


/-! ## The invariant -/

/-- Facts about one initiator state that need no ticket: the early keys are none or derived from the state's
pre-shared key and Hello, a finished resumption has its keys derived from the state's key, the dial parameters of a
fallen-back Hello are kept in `late`. -/
structure ILoc (st : IState) : Prop where
  early : st.early = nil ∨ st.early = early st.ckpsk st.thh
  done : st.ph = .done → st.resumed = true → ∃ D b rsc e, st.res = res (ck2 (ck1r st.ckpsk D) st.thf) st.thf ∧
    st.thf = thR st.thh b rsc e st.pcr
  none : st.ph = .none → st.thh = nil
  late : (st.ph = .reply ∨ st.ph = .decap ∨ st.ph = .sign) → st.late.on = true →
    st.late.ckpsk = st.ckpsk ∧ st.late.rcr = st.rcr ∧ st.late.thh = st.thh ∧ st.late.binder = st.binder

/-- The ticket `t` an initiator session of node `n` resumes with: its pre-shared key is the state's key, it names the
peer's session, the attacker does not know it, and the state's remembered credit record is the ticket's. -/
structure CkS (n : Nat) (t : Tk) (st : IState) : Prop where
  ck : st.ckpsk = ckpsk t.psk
  peer : st.peer ≠ att
  tid : st.tid = t.tid
  own : t.peer = n
  sess : ∃ k, pskSess t.psk = some (st.peer, k)
  sec : ¬ Known t.psk
  binder : st.binder = binder t.psk st.thh
  rcr : (st.ph = .done → st.resumed = true) → t.cr = st.rcr

/-- A finished resumption of the session `s`: the responder session whose Reply it accepted. -/
def IRes2Of (g : G) (s : Nat × Nat) (st : IState) : Prop :=
  ∃ r, Est (g.rst r).ph ∧ (g.rst r).resumed = true ∧ (g.rst r).thf = st.thf ∧ st.tids = (g.rst r).mytids ∧
    st.res = (g.rst r).res ∧ st.pcr = RCr r.1 ∧ r.1 = st.peer ∧ (g.rst r).peer = s.1

/-- A ticket in a client store of node `n`: an honest peer's, secret, of the ledger. -/
def CliTk (g : G) (n : Nat) (tk : Tk) : Prop :=
  tk.peer ≠ att ∧ (∃ k, pskSess tk.psk = some (tk.peer, k)) ∧ ¬ Known tk.psk ∧
    ∃ t, g.issued t ∧ t.tid = tk.tid ∧ t.psk = tk.psk ∧ t.peer = n ∧ t.cr = tk.cr

structure Inv4 (g : G) : Prop where
  lsec : ∀ t, g.issued t → t.peer ≠ att → ¬ Known t.psk
  lfun : ∀ t t', g.issued t → g.issued t' → t.psk = t'.psk → t = t'
  myt : ∀ r, Est (g.rst r).ph → ∀ t ∈ (g.rst r).mytids, ∃ e, g.issued e ∧ e.tid = t ∧
    e.psk = psk (g.rst r).res t (RCr r.1) ∧ e.peer = (g.rst r).peer ∧ pskSess e.psk = some r ∧ e.cr = RCr r.1
  rok : ∀ r, (g.rst r).resumed = true → ∃ t, g.issued t ∧ t.psk = (g.rst r).tpsk ∧ t.tid = (g.rst r).tid ∧
    t.peer = (g.rst r).peer ∧ t.cr = (g.rst r).rcr
  hauth : ∀ r, (g.rst r).resumed = true → (g.rst r).peer ≠ att →
    ∃ k, (g.ist ((g.rst r).peer, k)).thh = (g.rst r).thh
  iloc : ∀ s, ILoc (g.ist s)
  ick : ∀ s, (g.ist s).ckpsk ≠ nil → ∃ t, g.issued t ∧ CkS s.1 t (g.ist s)
  ires2 : ∀ s, (g.ist s).ph = .done → (g.ist s).resumed = true → IRes2Of g s (g.ist s)
  cli : ∀ n x, x ∈ g.cli n → x.occ = true → CliTk g n (TicketOf x)
  snap : ∀ n tk, tk ∈ g.snap n → CliTk g n tk
  netConf : ∀ m, g.net m → m.conf ≠ nil → ∃ r, Est (g.rst r).ph ∧ (g.rst r).resumed = true ∧
    m.conf = (g.rst r).reply.conf ∧ m.tids = (g.rst r).mytids
  netHello : ∀ m, g.net m → m.binder ≠ nil →
    ∃ s t, s.1 ≠ att ∧ (g.ist s).thh ≠ nil ∧ g.issued t ∧ t.peer = s.1 ∧ m.binder = binder t.psk (g.ist s).thh

theorem ILoc_none : ILoc ({} : IState) :=
  ⟨Or.inl rfl, by simp, fun _ => rfl, by simp⟩

theorem Inv4_init (K C : Nat) : Inv4 (G0 K C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact absurd ht (by simp [G0])
  · intro t t' ht; exact absurd ht (by simp [G0])
  · intro r hr; simp [G0, Est] at hr
  · intro r hr; simp [G0] at hr
  · intro r hr; simp [G0] at hr
  · intro s; exact ILoc_none
  · intro s hs; simp [G0] at hs
  · intro s hs; simp [G0] at hs
  · intro n x hx ho; simp [G0, List.mem_replicate] at hx; rw [hx.2] at ho; simp [NoSlot] at ho
  · intro n tk htk; simp [G0] at htk
  · intro m hm; exact absurd hm (by simp [G0])
  · intro m hm; exact absurd hm (by simp [G0])


/-! ## Initiator states: what a step keeps -/

/-- The fields a step of the initiator never changes once a Hello was built. -/
def Near (st st' : IState) : Prop :=
  st'.thh = st.thh ∧ st'.ckpsk = st.ckpsk ∧ st'.peer = st.peer ∧ st'.tid = st.tid ∧ st'.binder = st.binder

theorem IHandle_near (st : IState) (n : Nat) (m : Msg) : Near st (IHandle st n m).st := by
  rcases IHandle_cases st n m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hio, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, hc, c1, -⟩ | ⟨hp, hl, hty, hc, c1, -⟩ | ⟨hp, hty, he, c1, -⟩ <;>
  rw [c1] <;> simp [Near, IResumed, rrFall, IBeginFull, Ok]

theorem IKey_near (st : IState) (n : Nat) (kind : KRes) : Near st (IKey st n kind).st := by
  rcases IKey_cases st n kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, -, -, -, -, -, c1, -⟩ | ⟨hp, hk, c1, -⟩ |
    ⟨-, -, -, c1, -⟩ <;>
  rw [c1] <;> simp [Near, ikSignSt, ikDoneSt, ikBackSt]

theorem IRetransmit_near (n : Nat) (st : IState) : Near st (IRetransmit n st).st := by
  rcases IRetransmit_cases n st with ⟨hp, hsh, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨c1, -⟩ <;>
  rw [c1] <;> simp [Near, lateFall, lateFallB, IBeginFull, Ok]

theorem ILoc_ihandle (s : Nat × Nat) (st : IState) (m : Msg) (hI : ICl s st) (h : ILoc st) :
    ILoc (IHandle st s.1 m).st := by
  rcases IHandle_cases st s.1 m with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hty, hio, c1, -⟩ | ⟨hp, hsh, hty, he, c1, -⟩
    | ⟨hp, hty, hc, c1, -⟩ | ⟨hp, hl, hty, hc, c1, -⟩ | ⟨hp, hty, he, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]; exact ⟨h.early, fun hh => by simp at hh, fun hh => by simp at hh, fun hh => by simp at hh⟩
  · rw [c1]; exact ⟨h.early, fun hh => by simp at hh, fun hh => by simp at hh, fun _ hl => h.late (Or.inl hp) hl⟩
  · rw [c1]; exact ⟨h.early, h.done, h.none, h.late⟩
  · rw [c1]
    exact ⟨h.early, fun _ _ => ⟨Dh st.x (atomOf m.e), st.binder, m.sc, m.e, rfl, rfl⟩,
      fun hh => by simp [IResumed] at hh, fun hh => by simp [IResumed] at hh⟩
  · rw [c1]
    have hl' := h.late (by rcases hp with hp | hp | hp <;> simp [hp]) hl
    refine ⟨h.early, fun _ _ => ⟨Dh st.late.x (atomOf m.e), st.late.binder, m.sc, m.e, ?_, ?_⟩,
      fun hh => by simp [IResumed] at hh, fun hh => by simp [IResumed] at hh⟩
    · simp only [IResumed, RrCk2, RrThr, hl'.1]
    · simp only [IResumed, RrThr, hl'.2.2.1]
  · rw [c1]
    exact ⟨Or.inl (by simp [rrFall, IBeginFull, Ok]), fun hh => by simp [rrFall, IBeginFull, Ok] at hh,
      fun hh => by simp [rrFall, IBeginFull, Ok] at hh, fun _ hl => by simp [rrFall, IBeginFull, Ok, NoLate] at hl⟩

theorem ILoc_ikey (s : Nat × Nat) (st : IState) (kind : KRes) (hI : ICl s st) (h : ILoc st) :
    ILoc (IKey st s.1 kind).st := by
  rcases IKey_cases st s.1 kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, -, -, -, -, -, c1, -⟩ | ⟨hp, hk, c1, -⟩ |
    ⟨hp, -, -, c1, -⟩
  · rw [c1]; exact h
  · rw [c1]; exact ⟨h.early, fun hh => by simp at hh, fun hh => by simp at hh, fun hh => by simp at hh⟩
  · rw [c1]
    exact ⟨h.early, fun hh => by simp [ikSignSt] at hh, fun hh => by simp [ikSignSt] at hh,
      fun _ hl => h.late (by simp [hp]) hl⟩
  · rw [c1]
    have hr : st.resumed = false := by
      cases hv : st.resumed
      · rfl
      · have := hI.resFlag hv; rw [hp] at this; cases this
    exact ⟨h.early, fun _ hh => by simp [ikDoneSt, hr] at hh, fun hh => by simp [ikDoneSt] at hh,
      fun hh => by simp [ikDoneSt] at hh⟩
  · rw [c1]
    exact ⟨h.early, fun hh => by simp [ikBackSt] at hh, fun hh => by simp [ikBackSt] at hh,
      fun _ hl => h.late (by simp [hp]) hl⟩

theorem ILoc_iretransmit (s : Nat × Nat) (st : IState) (h : ILoc st) : ILoc (IRetransmit s.1 st).st := by
  rcases IRetransmit_cases s.1 st with ⟨hp, hsh, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨hp, hl, c1, -⟩ | ⟨c1, -⟩
  · rw [c1]; exact ⟨h.early, h.done, h.none, h.late⟩
  · rw [c1]; exact ⟨h.early, h.done, h.none, h.late⟩
  · rw [c1]
    exact ⟨Or.inl (by simp [lateFall, lateFallB, IBeginFull, Ok]), fun hh => by simp [lateFall, lateFallB, IBeginFull, Ok] at hh,
      fun hh => by simp [lateFall, lateFallB, IBeginFull, Ok] at hh, fun _ _ => by simp [lateFall, lateFallB, IBeginFull, Ok]⟩
  · rw [c1]; exact h

theorem ILoc_ished (st : IState) (h : ILoc st) : ILoc (IShed st) :=
  ⟨h.early, h.done, h.none, fun hh hl => by simp [IShed, NoLate] at hl⟩

theorem ILoc_acc (st : IState) (h : ILoc st) : ILoc { st with acc := true } := ⟨h.early, h.done, h.none, h.late⟩

theorem ILoc_new (n k peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) :
    ILoc (INew n k peer al short tk).st := by
  cases tk with
  | none =>
    exact ⟨Or.inl (by simp [INew, IBeginFull, Ok]), fun hh => by simp [INew, IBeginFull, Ok] at hh,
      fun hh => by simp [INew, IBeginFull, Ok] at hh, fun _ hl => by simp [INew, IBeginFull, Ok] at hl⟩
  | some t =>
    exact ⟨Or.inr (by simp [INew, IBeginResume, Ok]), fun hh => by simp [INew, IBeginResume, Ok] at hh,
      fun hh => by simp [INew, IBeginResume, Ok] at hh, fun hh => by simp [INew, IBeginResume, Ok] at hh⟩


/-! ## Steps that keep the facts of a session -/

theorem issued_mono {g g' : G} (hs : Step g g') : ∀ t, g.issued t → g'.issued t := by
  intro t ht
  cases hs with
  | rRecv s m cs _ _ => exact Or.inl ht
  | _ => exact ht

/-- The Hello of an initiator session is never changed once built. -/
theorem thh_keep {g g' : G} (hl : ∀ s, ILoc (g.ist s)) (hs : Step g g') (s : Nat × Nat)
    (hne : (g.ist s).thh ≠ nil) : (g'.ist s).thh = (g.ist s).thh := by
  cases hs with
  | iStart s0 peer al short take hn hph hpe =>
    show (upd g.ist s0 _ s).thh = _
    by_cases e : s = s0
    · subst e; exact absurd ((hl s).none hph) hne
    · rw [upd_ne _ _ _ _ e]
  | iRecv s0 m hn hd =>
    show (upd g.ist s0 _ s).thh = _
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact (IHandle_near _ _ _).1
    · rw [upd_ne _ _ _ _ e]
  | iAnswer s0 kind hn hph =>
    show (upd g.ist s0 _ s).thh = _
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact (IKey_near _ _ _).1
    · rw [upd_ne _ _ _ _ e]
  | iRetrans s0 hn hph =>
    show (upd g.ist s0 _ s).thh = _
    by_cases e : s = s0
    · subst e; rw [upd_same]; exact (IRetransmit_near _ _).1
    · rw [upd_ne _ _ _ _ e]
  | iShed s0 hn hph =>
    show (upd g.ist s0 _ s).thh = _
    by_cases e : s = s0
    · subst e; rw [upd_same]; rfl
    · rw [upd_ne _ _ _ _ e]
  | iAccept s0 tids hn hph hacc hpe hat =>
    show (upd g.ist s0 _ s).thh = _
    by_cases e : s = s0
    · subst e; rw [upd_same]
    · rw [upd_ne _ _ _ _ e]
  | _ => rfl

theorem RHandle_est (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) (h : Est st.ph) :
    ∃ sp nr, (RHandle st n k sto m cs).st = { st with spent := sp, nre := nr } ∧
      (RHandle st n k sto m cs).iss = [] ∧ (RHandle st n k sto m cs).sto = sto ∧
      ((RHandle st n k sto m cs).out = [] ∨ (RHandle st n k sto m cs).out = [st.reply]) := by
  have hne : st.ph ≠ .idle ∧ st.ph ≠ .finish := by rcases h with h | h <;> simp [h]
  rcases RHandle_cases st n k sto m cs with ⟨c1, c2, c3, c4, -⟩ | ⟨hp, c1, c2, c3, c4, -⟩ | ⟨hp, ⟨sp, nr, c1⟩, c2, c3, c4, -⟩
    | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, had, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
  · exact ⟨st.spent, st.nre, by rw [c1], c4, c3, Or.inl c2⟩
  · rcases hp with hp | hp
    · exact absurd hp hne.1
    · exact absurd hp hne.2
  · exact ⟨sp, nr, c1, c4, c3, c2⟩
  all_goals first | exact absurd hp hne.2 | exact absurd hp hne.1

theorem RKey_est (st : RState) (n k : Nat) (sto : Store) (kind : KRes) (h : Est st.ph) :
    (RKey st n k sto kind).st = st := by
  have hne : st.ph ≠ .sign := by rcases h with h | h <;> simp [h]
  rcases RKey_cases st n k sto kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩
  · exact c1
  · exact absurd hp hne
  · exact absurd hp hne

/-- An established responder session only changes its phase (resumed to done), its byte count and its repeat count. -/
theorem rst_est_stab {g g' : G} (hs : Step g g') (r : Nat × Nat) (h : Est (g.rst r).ph) :
    ∃ sp nr ph, Est ph ∧ g'.rst r = { g.rst r with spent := sp, nre := nr, ph := ph } := by
  cases hs with
  | rRecv s m cs hn hd =>
    show ∃ sp nr ph, Est ph ∧ upd g.rst s _ r = _
    by_cases e : r = s
    · subst e
      obtain ⟨sp, nr, c1, -⟩ := RHandle_est (g.rst r) r.1 r.2 (g.sto r.1) m cs h
      exact ⟨sp, nr, (g.rst r).ph, h, by rw [upd_same, c1]⟩
    · exact ⟨_, _, _, h, by rw [upd_ne _ _ _ _ e]⟩
  | rAnswer s kind hn hph =>
    show ∃ sp nr ph, Est ph ∧ upd g.rst s _ r = _
    by_cases e : r = s
    · subst e; exact ⟨_, _, _, h, by rw [upd_same, RKey_est _ _ _ _ _ h]⟩
    · exact ⟨_, _, _, h, by rw [upd_ne _ _ _ _ e]⟩
  | rShed s hn =>
    show ∃ sp nr ph, Est ph ∧ upd g.rst s _ r = _
    by_cases e : r = s
    · subst e
      by_cases hp : (g.rst r).ph = .resumed
      · exact ⟨(g.rst r).spent, (g.rst r).nre, .done, Or.inl rfl, by rw [upd_same]; simp [RShed, hp]⟩
      · exact ⟨(g.rst r).spent, (g.rst r).nre, (g.rst r).ph, h, by rw [upd_same]; simp [RShed, hp]⟩
    · exact ⟨_, _, _, h, by rw [upd_ne _ _ _ _ e]⟩
  | _ => exact ⟨_, _, _, h, rfl⟩

/-! ## The ledger -/

/-- What every ticket a responder step issues has in common. -/
def IssConst (iss : List Tk) : Prop :=
  ∃ rs cr peer al ad, ∀ t ∈ iss, ∃ tid, t = ⟨tid, psk rs tid cr, peer, al, ad, cr⟩

theorem IssConst_IssuedOf (tids : List Term) (rs cr : Term) (peer : Nat) (al ad : Term) :
    IssConst (IssuedOf tids rs cr peer al ad) :=
  ⟨rs, cr, peer, al, ad, fun t ht => by
    simp only [IssuedOf, List.mem_map] at ht
    obtain ⟨x, -, rfl⟩ := ht
    exact ⟨x, rfl⟩⟩

theorem IssConst_nil : IssConst [] := ⟨nil, nil, 0, nil, nil, fun t ht => by simp at ht⟩

/-- A responder step issues tickets only when it completes a full handshake or accepts a Hello. -/
theorem RHandle_iss_cases (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    (RHandle st n k sto m cs).iss = [] ∨
    (st.ph = .finish ∧ m.ty = .fin ∧ st.hsi = m.sealed.k ∧ st.th3 = m.sealed.ad ∧
      m.sealed.sig = sig m.sealed.id false (rfT4 st m) ∧ (RHandle st n k sto m cs).iss = rfIss st n sto m cs) ∨
    (st.ph = .idle ∧ m.ty = .hello ∧ rhUsable sto m ∧ (RHandle st n k sto m cs).iss = rhIss n k sto m cs) := by
  rcases RHandle_cases st n k sto m cs with ⟨c1, c2, c3, c4, -⟩ | ⟨hp, c1, c2, c3, c4, -⟩ | ⟨hp, ⟨sp, nr, c1⟩, c2, c3, c4, -⟩
    | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, had, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
  · exact Or.inl c4
  · exact Or.inl c4
  · exact Or.inl c4
  · exact Or.inl c4
  · exact Or.inl c4
  · exact Or.inl c4
  · exact Or.inr (Or.inl ⟨hp, hty, hk, had, hsg, c4⟩)
  · exact Or.inr (Or.inl ⟨hp, hty, hk, had, hsg, c4⟩)
  · exact Or.inl c4
  · exact Or.inr (Or.inr ⟨hp, hty, hu, c4⟩)
  · exact Or.inr (Or.inr ⟨hp, hty, hu, c4⟩)

theorem RHandle_iss_const (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) :
    IssConst (RHandle st n k sto m cs).iss := by
  rcases RHandle_iss_cases st n k sto m cs with c | ⟨-, -, -, -, -, c⟩ | ⟨-, -, -, c⟩ <;> rw [c]
  · exact IssConst_nil
  · exact IssConst_IssuedOf _ _ _ _ _ _
  · exact IssConst_IssuedOf _ _ _ _ _ _

/-- The pre-shared keys of tickets an honest peer received are secret. -/
theorem iss_sec {K C : Nat} {g : G} (hr : Reach K C g) (h4 : Inv4 g) (s : Nat × Nat) (m : Msg)
    (cs : List (List Nat)) (hn : s.1 ≠ att) (hd : Derivable g m) :
    ∀ t ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).iss, t.peer ≠ att → ¬ Known t.psk := by
  intro t ht hpe
  rcases RHandle_iss_cases (g.rst s) s.1 s.2 (g.sto s.1) m cs with c | ⟨hp, hty, hk, ha, hsg, c⟩ | ⟨hp, hty, hu, c⟩
  · rw [c] at ht; simp at ht
  · rw [c] at ht
    simp only [rfIss, IssuedOf, List.mem_map] at ht
    obtain ⟨x, -, rfl⟩ := ht
    have hid : m.sealed.id ≠ att := hpe
    have := fin_secret hr s m hn hd hty hp hk ha hsg hid
    simpa [Known] using this
  · rw [c] at ht
    simp only [rhIss, IssuedOf, List.mem_map] at ht
    obtain ⟨x, -, rfl⟩ := ht
    obtain ⟨i0, sl, hi0, hsl, hocc, htid, hslot⟩ := rhI0_spec hu.1
    have hS := StoreInv_reach hr
    have hmem : sl ∈ (g.sto s.1).tks := List.mem_of_getElem? hsl
    have hl := h4.lsec _ (hS.sI s.1 sl hmem hocc)
    have hpe' : sl.peer ≠ att := by rw [← hslot]; exact hpe
    have hk0 : ¬ Known sl.psk := hl hpe'
    rw [← hslot] at hk0
    intro hk
    simp [Known, rhCk2] at hk
    exact hk0 hk.1


theorem led_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    (∀ t, g'.issued t → t.peer ≠ att → ¬ Known t.psk) ∧
    (∀ t t', g'.issued t → g'.issued t' → t.psk = t'.psk → t = t') := by
  cases hs with
  | rRecv s m cs hn hd =>
    have hE := EInv_reach hr
    have hnew : ∀ t ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).iss, pskSess t.psk = some s ∧ ¬ PhI (g.rst s).ph :=
      fun t ht => by
        have h := RHandle_iss (g.rst s) s.1 s.2 (g.sto s.1) m cs (hE.li3 s) t ht
        exact ⟨by simpa using h.1, h.2.2.1⟩
    obtain ⟨rs, cr, peer, al, ad, hc⟩ := RHandle_iss_const (g.rst s) s.1 s.2 (g.sto s.1) m cs
    refine ⟨?_, ?_⟩
    · intro t ht hpe
      rcases ht with ht | ht
      · exact h4.lsec t ht hpe
      · exact iss_sec hr h4 s m cs hn hd t ht hpe
    · have old_new : ∀ t t', g.issued t → t' ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).iss →
          t.psk = t'.psk → False := by
        intro t t' ht ht' hp
        obtain ⟨e1, e2⟩ := hnew t' ht'
        obtain ⟨s', e3, e4⟩ := hE.led t ht
        rw [hp, e1] at e3
        cases e3
        exact e2 e4
      intro t t' ht ht' hp
      rcases ht with ht | ht <;> rcases ht' with ht' | ht'
      · exact h4.lfun t t' ht ht' hp
      · exact (old_new t t' ht ht' hp).elim
      · exact (old_new t' t ht' ht hp.symm).elim
      · obtain ⟨a, ha⟩ := hc t ht
        obtain ⟨b, hb⟩ := hc t' ht'
        rw [ha, hb] at hp ⊢
        simp only [psk.injEq] at hp
        rw [hp.2.1]
  | _ => exact ⟨h4.lsec, h4.lfun⟩

/-- A responder step that makes a session established: a full handshake that completed, or a Hello accepted. -/
theorem RHandle_new (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) (h0 : ¬ Est st.ph)
    (h1 : Est (RHandle st n k sto m cs).st.ph) :
    (st.ph = .finish ∧ m.ty = .fin ∧ st.hsi = m.sealed.k ∧ st.th3 = m.sealed.ad ∧
      m.sealed.sig = sig m.sealed.id false (rfT4 st m) ∧ (rfIs st n sto m cs).ok = true ∧
      (RHandle st n k sto m cs).st = rfSt st n sto m cs ∧ (RHandle st n k sto m cs).iss = rfIss st n sto m cs) ∨
    (st.ph = .idle ∧ m.ty = .hello ∧ rhUsable sto m ∧ (rhIs n k sto m cs).ok = true ∧
      (RHandle st n k sto m cs).st = rhSt st n k sto m cs ∧ (RHandle st n k sto m cs).iss = rhIss n k sto m cs) := by
  rcases RHandle_cases st n k sto m cs with ⟨c1, c2, c3, c4, -⟩ | ⟨hp, c1, c2, c3, c4, -⟩ | ⟨hp, ⟨sp, nr, c1⟩, c2, c3, c4, -⟩
    | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, had, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hk, had, hsg, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, c1, c2, c3, c4, -⟩ | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
    | ⟨hp, hty, hv, hsv, hu, hok, c1, c2, c3, c4, -⟩
  · rw [c1] at h1; exact absurd h1 h0
  · rw [c1] at h1; simp [Est] at h1
  · rw [c1] at h1; exact absurd h1 h0
  · rw [c1] at h1; exact absurd h1 h0
  · rw [c1] at h1; exact absurd h1 h0
  · rw [c1] at h1; simp [rInitSt, Est] at h1
  · exact Or.inl ⟨hp, hty, hk, had, hsg, hok, c1, c4⟩
  · rw [c1] at h1; simp [Est] at h1
  · rw [c1] at h1; exact absurd h1 h0
  · exact Or.inr ⟨hp, hty, hu, hok, c1, c4⟩
  · rw [c1] at h1; simp [Est] at h1

/-- How the state of a responder session changes in one step. -/
theorem rchg {g g' : G} (hs : Step g g') (r : Nat × Nat) :
    g'.rst r = g.rst r ∨
    (Est (g.rst r).ph ∧ ∃ sp nr ph, Est ph ∧ g'.rst r = { g.rst r with spent := sp, nre := nr, ph := ph }) ∨
    ¬ Est (g'.rst r).ph ∨
    (∃ s m cs, s.1 ≠ att ∧ Derivable g m ∧ r = s ∧ g' = stepRRecv g s m cs ∧ ¬ Est (g.rst r).ph ∧
      Est (g'.rst r).ph) := by
  by_cases hE : Est (g.rst r).ph
  · exact Or.inr (Or.inl ⟨hE, rst_est_stab hs r hE⟩)
  by_cases hE' : Est (g'.rst r).ph
  · cases hs with
    | rRecv s m cs hn hd =>
      by_cases e : r = s
      · exact Or.inr (Or.inr (Or.inr ⟨s, m, cs, hn, hd, e, rfl, hE, hE'⟩))
      · exact Or.inl (upd_ne _ _ _ _ e)
    | rAnswer s kind hn hph =>
      by_cases e : r = s
      · subst e
        exfalso
        change Est (upd g.rst r _ r).ph at hE'
        rw [upd_same] at hE'
        rcases RKey_cases (g.rst r) r.1 r.2 (g.sto r.1) kind with ⟨c1, -⟩ | ⟨hp, c1, -⟩ | ⟨hp, hk, c1, -⟩ <;>
          rw [c1] at hE'
        · exact hE hE'
        · simp [Est] at hE'
        · simp [rkSt, Est] at hE'
      · exact Or.inl (upd_ne _ _ _ _ e)
    | rShed s hn =>
      by_cases e : r = s
      · subst e
        left
        have : (g.rst r).ph ≠ .resumed := fun h => hE (Or.inr h)
        show upd g.rst r _ r = _
        rw [upd_same]; simp [RShed, this]
      · exact Or.inl (upd_ne _ _ _ _ e)
    | _ => exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl hE'))


/-! ## The responder side -/

theorem stepRRecv_rst_same (g : G) (s : Nat × Nat) (m : Msg) (cs : List (List Nat)) :
    (stepRRecv g s m cs).rst s = (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).st := by
  show upd g.rst s _ s = _; rw [upd_same]

theorem myt_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ r, Est (g'.rst r).ph → ∀ t ∈ (g'.rst r).mytids, ∃ e, g'.issued e ∧ e.tid = t ∧
      e.psk = psk (g'.rst r).res t (RCr r.1) ∧ e.peer = (g'.rst r).peer ∧ pskSess e.psk = some r ∧
      e.cr = RCr r.1 := by
  intro r hEr t ht
  rcases rchg hs r with ha | ⟨hEo, sp, nr, ph, hph, hb⟩ | hc | ⟨s, m, cs, hn, hd, rfl, hg', hne, hEn⟩
  · rw [ha] at ht ⊢
    obtain ⟨e, he⟩ := h4.myt r (by rw [← ha]; exact hEr) t ht
    exact ⟨e, issued_mono hs e he.1, he.2⟩
  · rw [hb] at ht ⊢
    obtain ⟨e, he⟩ := h4.myt r hEo t ht
    exact ⟨e, issued_mono hs e he.1, he.2⟩
  · exact absurd hEr hc
  · subst hg'
    have hE := EInv_reach hr
    rcases RHandle_new (g.rst r) r.1 r.2 (g.sto r.1) m cs hne (by rw [← stepRRecv_rst_same]; exact hEn) with
      ⟨hp, hty, hk, ha, hsg, hok, c1, c4⟩ | ⟨hp, hty, hu, hok, c1, c4⟩
    · have hst : (stepRRecv g r m cs).rst r = rfSt (g.rst r) r.1 (g.sto r.1) m cs := by
        show upd g.rst r _ r = _; rw [upd_same, c1]
      rw [hst] at ht ⊢
      refine ⟨⟨t, psk (rfRes (g.rst r) m) t (RCr r.1), m.sealed.id, (g.rst r).al, (g.rst r).ad, RCr r.1⟩, ?_, rfl, rfl, rfl,
        ?_, rfl⟩
      · right; show _ ∈ (RHandle (g.rst r) r.1 r.2 (g.sto r.1) m cs).iss
        rw [c4]; simp only [rfIss, IssuedOf, List.mem_map]
        exact ⟨t, ht, rfl⟩
      · show pskSess (psk (rfRes (g.rst r) m) t (RCr r.1)) = some r
        rw [pskSess_psk, resSess_rfRes, hE.li3 r hp]
    · have hst : (stepRRecv g r m cs).rst r = rhSt (g.rst r) r.1 r.2 (g.sto r.1) m cs := by
        show upd g.rst r _ r = _; rw [upd_same, c1]
      rw [hst] at ht ⊢
      refine ⟨⟨t, psk (res (rhCk2 r.1 r.2 (g.sto r.1) m) (rhThr r.1 r.2 m)) t (RCr r.1), (rhSlot (g.sto r.1) m).peer, m.al,
        (rhSlot (g.sto r.1) m).ad, RCr r.1⟩, ?_, rfl, rfl, rfl, ?_, rfl⟩
      · right; show _ ∈ (RHandle (g.rst r) r.1 r.2 (g.sto r.1) m cs).iss
        rw [c4]; simp only [rhIss, IssuedOf, List.mem_map]
        exact ⟨t, ht, rfl⟩
      · show pskSess (psk (res (rhCk2 r.1 r.2 (g.sto r.1) m) (rhThr r.1 r.2 m)) t (RCr r.1)) = some r
        rw [pskSess_psk, resSess_rhRes]

theorem rok_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ r, (g'.rst r).resumed = true → ∃ t, g'.issued t ∧ t.psk = (g'.rst r).tpsk ∧ t.tid = (g'.rst r).tid ∧
      t.peer = (g'.rst r).peer ∧ t.cr = (g'.rst r).rcr := by
  intro r hres
  have h3' := Inv3_reach (Reach.step hr hs)
  have hEr : Est (g'.rst r).ph := by
    rcases (h3'.rc r).resFlag hres with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases rchg hs r with ha | ⟨hEo, sp, nr, ph, hph, hb⟩ | hc | ⟨s, m, cs, hn, hd, rfl, hg', hne, hEn⟩
  · rw [ha] at hres ⊢
    obtain ⟨e, he⟩ := h4.rok r hres
    exact ⟨e, issued_mono hs e he.1, he.2⟩
  · rw [hb] at hres ⊢
    obtain ⟨e, he⟩ := h4.rok r hres
    exact ⟨e, issued_mono hs e he.1, he.2⟩
  · exact absurd hEr hc
  · subst hg'
    have hS := StoreInv_reach hr
    have h3 := Inv3_reach hr
    rcases RHandle_new (g.rst r) r.1 r.2 (g.sto r.1) m cs hne (by rw [← stepRRecv_rst_same]; exact hEn) with
      ⟨hp, hty, hk, ha, hsg, hok, c1, c4⟩ | ⟨hp, hty, hu, hok, c1, c4⟩
    · have hst : (stepRRecv g r m cs).rst r = rfSt (g.rst r) r.1 (g.sto r.1) m cs := by
        show upd g.rst r _ r = _; rw [upd_same, c1]
      rw [hst] at hres
      have : (g.rst r).resumed = false := RInit_resumed ((h3.rc r).finish hp).2.1
      simp [rfSt, this] at hres
    · have hst : (stepRRecv g r m cs).rst r = rhSt (g.rst r) r.1 r.2 (g.sto r.1) m cs := by
        show upd g.rst r _ r = _; rw [upd_same, c1]
      rw [hst]
      obtain ⟨i0, sl, hi0, hsl, hocc, htid, hslot⟩ := rhI0_spec hu.1
      have hmem : sl ∈ (g.sto r.1).tks := List.mem_of_getElem? hsl
      refine ⟨TicketOf sl, Or.inl (hS.sI r.1 sl hmem hocc), ?_, ?_, ?_, ?_⟩ <;>
        simp [rhSt, TicketOf, hslot, htid]


theorem rthh_ne {g : G} (h3 : Inv3 g) (r : Nat × Nat) (hres : (g.rst r).resumed = true) : (g.rst r).thh ≠ nil := by
  have hr := (h3.rc r).res (by
    rcases (h3.rc r).resFlag hres with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hres⟩)
  obtain ⟨p, e, hth, -⟩ := hr
  rw [hth]; intro h; cases h

theorem hauth_step {K C : Nat} {g g' : G} (hr : Reach K C g) (h4 : Inv4 g) (hs : Step g g') :
    ∀ r, (g'.rst r).resumed = true → (g'.rst r).peer ≠ att →
      ∃ k, (g'.ist ((g'.rst r).peer, k)).thh = (g'.rst r).thh := by
  intro r hres hpe
  have h3 := Inv3_reach hr
  have h3' := Inv3_reach (Reach.step hr hs)
  have hEr : Est (g'.rst r).ph := by
    rcases (h3'.rc r).resFlag hres with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases rchg hs r with ha | ⟨hEo, sp, nr, ph, hph, hb⟩ | hc | ⟨s, m, cs, hn, hd, rfl, hg', hne, hEn⟩
  · rw [ha] at hres hpe ⊢
    obtain ⟨k, hk⟩ := h4.hauth r hres hpe
    refine ⟨k, ?_⟩
    rw [thh_keep h4.iloc hs _ (by rw [hk]; exact rthh_ne h3 r hres), hk]
  · rw [hb] at hres hpe ⊢
    obtain ⟨k, hk⟩ := h4.hauth r hres hpe
    refine ⟨k, ?_⟩
    have := thh_keep h4.iloc hs ((g.rst r).peer, k) (by rw [hk]; exact rthh_ne h3 r hres)
    exact this.trans hk
  · exact absurd hEr hc
  · subst hg'
    have hS := StoreInv_reach hr
    rcases RHandle_new (g.rst r) r.1 r.2 (g.sto r.1) m cs hne (by rw [← stepRRecv_rst_same]; exact hEn) with
      ⟨hp, hty, hk, ha, hsg, hok, c1, c4⟩ | ⟨hp, hty, hu, hok, c1, c4⟩
    · have hst : (stepRRecv g r m cs).rst r = rfSt (g.rst r) r.1 (g.sto r.1) m cs := by
        show upd g.rst r _ r = _; rw [upd_same, c1]
      rw [hst] at hres
      have : (g.rst r).resumed = false := RInit_resumed ((h3.rc r).finish hp).2.1
      simp [rfSt, this] at hres
    · have hst : (stepRRecv g r m cs).rst r = rhSt (g.rst r) r.1 r.2 (g.sto r.1) m cs := by
        show upd g.rst r _ r = _; rw [upd_same, c1]
      rw [hst] at hpe ⊢
      obtain ⟨i0, sl, hi0, hsl, hocc, htid, hslot⟩ := rhI0_spec hu.1
      have hmem : sl ∈ (g.sto r.1).tks := List.mem_of_getElem? hsl
      have hI := hS.sI r.1 sl hmem hocc
      have hpe' : sl.peer ≠ att := by simpa [rhSt, hslot] using hpe
      have hsec : ¬ Known sl.psk := h4.lsec _ hI hpe'
      have hb := hu.2.2.2.2
      have hm' : ∃ m', g.net m' ∧ m'.binder = m.binder := by
        rcases hd with hnet | ⟨-, -, hB, -⟩
        · exact ⟨m, hnet, rfl⟩
        · rcases hB (rhSlot (g.sto r.1) m).psk (rhThh m) hb.symm with hk | hm
          · rw [hslot] at hk; exact absurd hk hsec
          · exact hm
      obtain ⟨m', hnet', hbind⟩ := hm'
      have hbne : m'.binder ≠ nil := by rw [hbind, ← hb]; intro h; cases h
      obtain ⟨s', t, hn', -, ht, htp, hbt⟩ := h4.netHello m' hnet' hbne
      rw [hbind, ← hb, hslot] at hbt
      simp only [binder.injEq] at hbt
      obtain ⟨hpsk, hthh⟩ := hbt
      have hteq : t = TicketOf sl := h4.lfun t _ ht hI hpsk.symm
      have hpeq : sl.peer = s'.1 := by rw [← htp, hteq]; rfl
      refine ⟨s'.2, ?_⟩
      show (g.ist ((rhSlot (g.sto r.1) m).peer, s'.2)).thh = rhThh m
      rw [hslot, hpeq]
      exact hthh.symm

end Vinc.Hs
