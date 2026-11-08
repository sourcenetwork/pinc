import Vinc.HandshakeInv
import Vinc.HandshakeLocal

/-!
# Agreement of the full handshake, for unboundedly many sessions

`Inv3` (every session is locally consistent, `HandshakeLocal`) holds in every reachable state. Two finished sessions
that hold the same final transcript hash then hold the same fields: the transcript terms are a free algebra, so equal
hashes have equal arguments, down to the two ephemeral publics, the ciphertext and the prekey, and the keys are the
same function of them.
-/

namespace Vinc.Hs
open Term

structure Inv3 (g : G) : Prop where
  ic : ∀ s, ICl s (g.ist s)
  rc : ∀ s, RCl s (g.rst s)

theorem Inv3_init (K : Nat) : Inv3 (G0 K) := ⟨fun s => ICl_none s, fun s => RCl_none s⟩

theorem ICl_upd {g : G} (h : ∀ s, ICl s (g.ist s)) (s0 : Nat × Nat) (st : IState) (hs : ICl s0 st) :
    ∀ s, ICl s (upd g.ist s0 st s) := by
  intro s; by_cases e : s = s0
  · subst e; simpa [upd_same] using hs
  · rw [upd_ne _ _ _ _ e]; exact h s

theorem RCl_upd {g : G} (h : ∀ s, RCl s (g.rst s)) (s0 : Nat × Nat) (st : RState) (hs : RCl s0 st) :
    ∀ s, RCl s (upd g.rst s0 st s) := by
  intro s; by_cases e : s = s0
  · subst e; simpa [upd_same] using hs
  · rw [upd_ne _ _ _ _ e]; exact h s

theorem Inv3_step {g g' : G} (h : Inv3 g) (hs : Step g g') : Inv3 g' := by
  cases hs with
  | startFull s peer short hn hph hpe =>
    exact ⟨ICl_upd h.ic s _ (ICl_begin_full s _ peer short nil nil rfl hn), h.rc⟩
  | startResume s tk hn hph hc =>
    exact ⟨ICl_upd h.ic s _ (ICl_begin_resume s _ tk rfl hn), h.rc⟩
  | iRecv s m hn hd => exact ⟨ICl_upd h.ic s _ (ICl_ihandle s _ m (h.ic s)), h.rc⟩
  | iAnswer s kind hn => exact ⟨ICl_upd h.ic s _ (ICl_ikey s _ kind (h.ic s)), h.rc⟩
  | iRetransmit s _ _ => exact ⟨h.ic, h.rc⟩
  | iAcceptFull s r _ _ _ _ _ _ _ => exact ⟨ICl_upd h.ic s _ (ICl_acc s _ (h.ic s)), h.rc⟩
  | iAcceptResumed s t _ _ _ _ _ => exact ⟨ICl_upd h.ic s _ (ICl_acc s _ (h.ic s)), h.rc⟩
  | rRecv s m hn hd => exact ⟨h.ic, RCl_upd h.rc s _ (RCl_rhandle s _ _ m hn (h.rc s))⟩
  | rAnswer s kind hn => exact ⟨h.ic, RCl_upd h.rc s _ (RCl_rkey s _ _ kind hn (h.rc s))⟩
  | expire n i => exact ⟨h.ic, h.rc⟩

theorem Inv3_reach {K : Nat} {g : G} (h : Reach K g) : Inv3 g := by
  induction h with
  | init => exact Inv3_init K
  | step _ hs ih => exact Inv3_step ih hs

theorem ekNode_rEk (m : Msg) (n : Nat) (h : rHpk m = hash (ek n)) : ekNode (rEk m) = n := by
  by_cases hf : m.form = .full
  · have h' : hash m.pk = hash (ek n) := by simpa [rHpk, hf] using h
    have h'' : m.pk = ek n := by injection h'
    simp [rEk, hf, h'', ekNode]
  · have h' : m.pk = hash (ek n) := by simpa [rHpk, hf] using h
    simp [rEk, hf, h, ekNode]

/-- The transcript chain of a finished full handshake, read off both sides from equal final hashes: the two
sessions agree on the ephemerals, the ciphertext, the prekey and both identities. -/
theorem full_chain (i r : Nat × Nat) (sti : IState) (str : RState) (m : Msg) (hi : IDone i.1 sti) (hr : RDone str)
    (hri : RInitM r.1 r.2 str m) (hrf : RFin r.1 str) (hth : sti.thf = str.thf) :
    sti.peer = r.1 ∧ str.peer = i.1 ∧ sti.th0 = rT0 m ∧
      sti.reply.e = pub (ry r.1 r.2) ∧ sti.reply.ct = rC r.1 r.2 m ∧ m.e = pub sti.x ∧ rHpk m = hash (ek i.1) := by
  obtain ⟨⟨⟨⟨hb0, hbx, hbr⟩, hrp, ht1, hssx⟩, hck, hid, ht2, ht3, ht4, hath, hsig, hhsi⟩, hf5, -, -, -⟩ := hi
  obtain ⟨hprm, h0, hhp, hek, hct, hr1, hr2, hra, hrck, -, -, -, -⟩ := hri
  obtain ⟨hd4, hd5, -, -, -⟩ := hr
  rw [hf5, hd5] at hth
  simp only [th5.injEq, sig.injEq] at hth
  obtain ⟨h4, hnode, -, -⟩ := hth
  rw [ht4, hd4] at h4
  simp only [th4.injEq] at h4
  obtain ⟨h3, hp4⟩ := h4
  rw [ht3, hrf] at h3
  simp only [th3.injEq, sig.injEq] at h3
  obtain ⟨h2, hs3⟩ := h3
  rw [ht2, hr2] at h2
  simp only [th2.injEq] at h2
  obtain ⟨h1, hp2⟩ := h2
  rw [ht1, hr1] at h1
  unfold rT1 at h1
  simp only [th1.injEq] at h1
  obtain ⟨h0', -, he, hc⟩ := h1
  have h0m : th0 ok (pub sti.x) (hash (ek i.1)) = th0 m.prm m.e (rHpk m) := by
    rw [← hb0, h0']; rfl
  simp only [th0.injEq] at h0m
  obtain ⟨-, hex, hhk⟩ := h0m
  have hs3' : sti.peer = r.1 := by
    rw [hsig] at hs3; simp only [sig.injEq] at hs3; exact hs3.1
  exact ⟨hs3', hnode.symm, h0', he, hc, hex.symm, hhk.symm⟩

/-- Agreement of two finished full handshakes with the same final transcript hash. -/
theorem agree_full_core (i r : Nat × Nat) (sti : IState) (str : RState) (m : Msg) (hi : IDone i.1 sti)
    (hr : RDone str) (hri : RInitM r.1 r.2 str m) (hrf : RFin r.1 str) (hth : sti.thf = str.thf) :
    sti.send = str.recv ∧ sti.recv = str.send ∧ sti.res = str.res ∧ sti.peer = r.1 ∧ str.peer = i.1 := by
  obtain ⟨hp1, hp2, h0, he, hc, hex, hhk⟩ := full_chain i r sti str m hi hr hri hrf hth
  obtain ⟨⟨⟨⟨hb0, hbx, hbr⟩, hrp, ht1, hssx⟩, hck, hid, ht2, ht3, ht4, hath, hsig, hhsi⟩, hf5, hs, hrv, hrs⟩ := hi
  obtain ⟨hprm, h0', hhp, hek, hct, hr1, hr2, hra, hrck, -, -, -, -⟩ := hri
  obtain ⟨hd4, hd5, hds, hdr, hdres⟩ := hr
  have hn : ekNode (rEk m) = i.1 := ekNode_rEk m i.1 hhk
  have hck1 : sti.ck1 = str.ck1 := by
    rw [hck, hrck]
    unfold ikCk1 ikSsk rCk1
    rw [hssx, hc, he, hex]
    simp only [rC, hn, Decap, ite_true, atomOf]
    rw [Dh_comm]
  have hk : ck2 sti.ck1 sti.thf = ck2 str.ck1 str.thf := by rw [hck1, hth]
  refine ⟨?_, ?_, ?_, hp1, hp2⟩
  · rw [hs, hdr, hk, hth]
  · rw [hrv, hds, hk, hth]
  · rw [hrs, hdres, hk, hth]

/-- Agreement of full handshakes, for any number of sessions, nodes and tickets: an initiator session and a responder
session that both finished a full handshake and hold the same final transcript hash hold the same application keys
(each one's send key is the other's receive key), the same resumption secret, and name each other as peer. -/
theorem agreement_full {K : Nat} {g : G} (h : Reach K g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done) (hri : (g.ist i).resumed = false) (hrr : (g.rst r).resumed = false)
    (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).send = (g.rst r).recv ∧ (g.ist i).recv = (g.rst r).send ∧ (g.ist i).res = (g.rst r).res ∧
    (g.ist i).peer = r.1 ∧ (g.rst r).peer = i.1 := by
  have h3 := Inv3_reach h
  have hI := (h3.ic i).2.2.2.2.1 hi hri
  obtain ⟨-, -, -, hrf, -, hsg, hrd, -, -, -, -⟩ := h3.rc r
  obtain ⟨⟨m, hm⟩, hfin⟩ := hrf (hsg hr) hrr
  exact agree_full_core i r _ _ m hI (hrd hr hrr) hm hfin hth

/-- A full handshake and a resumed one never share a final transcript hash. -/
theorem agreement_resumed_flag {K : Nat} {g : G} (h : Reach K g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done) (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).resumed = (g.rst r).resumed := by
  have h3 := Inv3_reach h
  by_cases a : (g.ist i).resumed = true <;> by_cases b : (g.rst r).resumed = true
  · simp [a, b]
  · exfalso
    have hb : (g.rst r).resumed = false := by simpa using b
    obtain ⟨rp, e1, hf1, -⟩ := (h3.ic i).2.2.2.2.2.2 hi a
    obtain ⟨-, -, -, hrf, -, hsg, hrd, -, -, -, -⟩ := h3.rc r
    obtain ⟨hd4, hd5, -⟩ := hrd hr hb
    rw [hf1, hd5] at hth
    cases hth
  · exfalso
    have ha : (g.ist i).resumed = false := by simpa using a
    have hb : (g.rst r).resumed = true := by simpa using b
    obtain ⟨hI, hf5, -⟩ := (h3.ic i).2.2.2.2.1 hi ha
    obtain ⟨-, -, -, -, -, -, -, hR, -, -, -⟩ := h3.rc r
    obtain ⟨p, e, bb, h1, h2, -⟩ := hR hr hb
    rw [hf5, h2] at hth
    cases hth
  · have a' : (g.ist i).resumed = false := by simpa using a
    have b' : (g.rst r).resumed = false := by simpa using b
    simp [a', b']

#audit_axioms Vinc.Hs.agreement_full
#audit_axioms Vinc.Hs.agreement_resumed_flag

#audit_axioms Vinc.Hs.Inv3_reach

end Vinc.Hs
