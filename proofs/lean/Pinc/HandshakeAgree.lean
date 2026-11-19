import Pinc.HandshakeInv
import Pinc.HandshakeLocal

/-!
# Agreement of the full handshake, for unboundedly many sessions

`Inv3` (every session is locally consistent, `HandshakeLocal`) holds in every reachable state. Two finished sessions
that hold the same final transcript hash then hold the same fields: the transcript terms are a free algebra, so equal
hashes have equal arguments, down to the two ephemeral publics, the ciphertext, the prekey, the ALPN, the AEAD and
the credit records, and the keys are the same function of them.
-/

namespace Pinc.Hs
open Term

structure Inv3 (g : G) : Prop where
  ic : ∀ s, ICl s (g.ist s)
  rc : ∀ s, RCl s (g.rst s)

theorem Inv3_init (K C : Nat) : Inv3 (G0 K C) := ⟨fun s => ICl_none s, fun s => RCl_none s⟩

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

theorem Inv3_step {kn : Term → Prop} {g g' : G} (h : Inv3 g) (hs : StepK kn g g') : Inv3 g' := by
  cases hs with
  | iStart s peer al short take hn _ _ =>
    refine ⟨?_, h.rc⟩
    show ∀ s', ICl s' (upd g.ist s _ s')
    exact ICl_upd h.ic s _ (ICl_new s peer al short _ hn)
  | iRecv s m hn hd => exact ⟨ICl_upd h.ic s _ (ICl_ihandle s _ m (h.ic s)), h.rc⟩
  | iAnswer s kind hn _ => exact ⟨ICl_upd h.ic s _ (ICl_ikey s _ kind (h.ic s)), h.rc⟩
  | iRetrans s hn _ => exact ⟨ICl_upd h.ic s _ (ICl_iretransmit s _ (h.ic s)), h.rc⟩
  | iShed s hn _ => exact ⟨ICl_upd h.ic s _ (ICl_ished s _ (h.ic s)), h.rc⟩
  | iAccept s tids _ _ _ _ _ => exact ⟨ICl_upd h.ic s _ (ICl_acc s _ (h.ic s)), h.rc⟩
  | rRecv s m cs hn hd => exact ⟨h.ic, RCl_upd h.rc s _ (RCl_rhandle s _ _ m cs hn (h.rc s))⟩
  | rAnswer s kind hn _ => exact ⟨h.ic, RCl_upd h.rc s _ (RCl_rkey s _ _ kind hn (h.rc s))⟩
  | rRetrans s _ _ => exact ⟨h.ic, h.rc⟩
  | rShed s hn => exact ⟨h.ic, RCl_upd h.rc s _ (RCl_rshed s _ (h.rc s))⟩
  | expire n i sl _ _ _ _ => exact ⟨h.ic, h.rc⟩
  | expireC n i sl _ _ _ _ => exact ⟨h.ic, h.rc⟩
  | «export» n mx _ => exact ⟨h.ic, h.rc⟩
  | restore n drop _ => exact ⟨h.ic, h.rc⟩
  | restart n _ => exact ⟨h.ic, h.rc⟩

theorem Inv3_reach {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) : Inv3 g := by
  induction h with
  | init => exact Inv3_init K C
  | step _ hs ih => exact Inv3_step ih hs

theorem rEk_of_rHpk (m : Msg) (n : Nat) (h : rHpk m = hash (ek n)) : rEk m = ek n := by
  by_cases hf : m.form = .full
  · have h' : hash m.pk = hash (ek n) := by simpa [rHpk, hf] using h
    have h'' : m.pk = ek n := by injection h'
    simp [rEk, hf, h'']
  · have h' : m.pk = hash (ek n) := by simpa [rHpk, hf] using h
    simp only [rEk, hf, if_false]; rw [h]

/-- The transcript chain of a finished full handshake, read off both sides from equal final hashes: the two sessions
agree on the ephemerals, the ciphertext, the prekey, the ALPN, the AEAD, both identities and the credit record. -/
theorem full_chain (i r : Nat × Nat) (sti : IState) (str : RState) (m : Msg) (hi : IDone i.1 sti) (hr : RDone str)
    (hri : RInitM r.1 r.2 str m) (hrf : RFin r.1 r.2 str) (hth : sti.thf = str.thf) :
    sti.peer = r.1 ∧ str.peer = i.1 ∧ sti.pcr = RCr r.1 ∧ sti.th0 = rT0 m ∧
      sti.reply.e = pub (ry r.1 r.2) ∧ sti.reply.ct = rC r.1 r.2 m ∧ sti.reply.ad = rAd r.1 m ∧ m.e = pub sti.x ∧
      rHpk m = hash (ek i.1) ∧ m.al = sti.al ∧ m.cr = sti.cr := by
  obtain ⟨⟨⟨⟨hb0, hbx, hbr⟩, hio, had, ht1, hssx⟩, hck, hid, hcrn, hpcr, ht2, ht3, ht4, hath, hsig, hhsi⟩, hf5, -, -, -, -, -⟩ := hi
  obtain ⟨hver, hsv, hadn, h0, hhp, hek, hct, hr1, hr2, hra, hrck, -, -, -, -, hal, hadr, -, -, hpr, -⟩ := hri
  obtain ⟨hd4, hd5, -, -, -, -⟩ := hr
  obtain ⟨hf3, hfr⟩ := hrf
  rw [hf5, hd5] at hth
  simp only [th5.injEq, sig.injEq] at hth
  obtain ⟨h4, hnode, -, -⟩ := hth
  rw [ht4, hd4] at h4
  simp only [th4.injEq] at h4
  obtain ⟨h3, hp4⟩ := h4
  rw [ht3, hf3] at h3
  simp only [th3.injEq, sig.injEq] at h3
  obtain ⟨h2, hs3⟩ := h3
  rw [ht2, hr2] at h2
  unfold rT2 at h2
  simp only [th2.injEq] at h2
  obtain ⟨h1, hp2, hcr⟩ := h2
  rw [ht1] at h1
  unfold rT1 at h1
  simp only [th1.injEq] at h1
  obtain ⟨h0', -, had', he, hc⟩ := h1
  have h0m : th0 ok sti.al sti.dc sti.sc sti.cr sti.of (pub sti.x) (hash (ek i.1)) = th0 m.ver m.al m.dc m.sc m.cr m.of m.e (rHpk m) := by
    rw [← hb0, h0']; rfl
  simp only [th0.injEq] at h0m
  obtain ⟨-, hal', -, -, hcr', -, hex, hhk⟩ := h0m
  exact ⟨hp2, hnode.symm, hcr, h0', he, hc, had', hex.symm, hhk.symm, hal'.symm, hcr'.symm⟩

/-- Agreement of two finished full handshakes with the same final transcript hash. -/
theorem agree_full_core (i r : Nat × Nat) (sti : IState) (str : RState) (m : Msg) (hi : IDone i.1 sti)
    (hr : RDone str) (hri : RInitM r.1 r.2 str m) (hrf : RFin r.1 r.2 str) (hth : sti.thf = str.thf) :
    sti.send = str.recv ∧ sti.recv = str.send ∧ sti.res = str.res ∧ sti.cid = str.cid ∧ sti.peer = r.1 ∧
      str.peer = i.1 ∧ sti.al = str.al ∧ sti.ad = str.ad ∧ sti.pcr = RCr r.1 ∧ str.pcr = sti.cr ∧ sti.rcr = str.rcr := by
  obtain ⟨hp1, hp2, hpc, h0, he, hc, hadd, hex, hhk, hal, hcr⟩ := full_chain i r sti str m hi hr hri hrf hth
  obtain ⟨⟨⟨⟨hb0, hbx, hbr⟩, hio, had, ht1, hssx⟩, hck, hid, hcrn, hpcr, ht2, ht3, ht4, hath, hsig, hhsi⟩, hf5, hs, hrv, hrs, hcidi, hrcri⟩ := hi
  obtain ⟨hver, hsv, hadn, h0', hhp, hek, hct, hr1, hr2, hra, hrck, -, -, -, -, hal2, hadr, -, -, hpr, hrcr⟩ := hri
  obtain ⟨hd4, hd5, hds, hdr, hdres, hdcid⟩ := hr
  have hn : rEk m = ek i.1 := rEk_of_rHpk m i.1 hhk
  have hck1 : sti.ck1 = str.ck1 := by
    rw [hck, hrck]
    unfold ikCk1 ikSsk rCk1
    rw [hssx, hc, he, hex]
    simp only [rC, hn, Decap, ite_true, atomOf]
    rw [Dh_comm]
  have hk : ck2 sti.ck1 sti.thf = ck2 str.ck1 str.thf := by rw [hck1, hth]
  refine ⟨?_, ?_, ?_, ?_, hp1, hp2, ?_, ?_, hpc, ?_, ?_⟩
  · rw [hs, hdr, hk, hth]
  · rw [hrv, hds, hk, hth]
  · rw [hrs, hdres, hk, hth]
  · rw [hcidi, hdcid, hk, hth]
  · rw [hal2, hal]
  · rw [had, hadd, hadr]
  · rw [hpr, hcr]
  · rw [hrcri, hrcr]

/-- Agreement of full handshakes, for any number of sessions, nodes and tickets: an initiator session and a responder
session that both finished a full handshake and hold the same final transcript hash hold the same application keys
(each one's send key is the other's receive key), the same resumption secret and connection id secret, name each other
as peer, and agree on the ALPN, the AEAD and the credit records of both sides. It holds against every attacker `kn`,
a broken half of the hybrid included: the keys are a function of the transcript. -/
theorem agreement_full {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done) (hri : (g.ist i).resumed = false) (hrr : (g.rst r).resumed = false)
    (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).send = (g.rst r).recv ∧ (g.ist i).recv = (g.rst r).send ∧ (g.ist i).res = (g.rst r).res ∧
    (g.ist i).cid = (g.rst r).cid ∧ (g.ist i).peer = r.1 ∧ (g.rst r).peer = i.1 ∧
    (g.ist i).al = (g.rst r).al ∧ (g.ist i).ad = (g.rst r).ad ∧
    (g.ist i).pcr = RCr r.1 ∧ (g.rst r).pcr = crd i.1 ∧ (g.ist i).rcr = (g.rst r).rcr := by
  have h3 := Inv3_reach h
  have hI := (h3.ic i).done hi hri
  obtain ⟨⟨m, hm⟩, hfin⟩ := (h3.rc r).signed ((h3.rc r).doneSgn hr) hrr
  have hne := (h3.ic i).ne (by simp [hi])
  have := agree_full_core i r _ _ m hI ((h3.rc r).done hr hrr) hm hfin hth
  rw [hne.2.1] at this
  exact this

/-- A full handshake and a resumed one never share a final transcript hash. -/
theorem agreement_resumed_flag {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done) (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).resumed = (g.rst r).resumed := by
  have h3 := Inv3_reach h
  by_cases a : (g.ist i).resumed = true <;> by_cases b : (g.rst r).resumed = true
  · simp [a, b]
  · exfalso
    have hb : (g.rst r).resumed = false := by simpa using b
    obtain ⟨x, ckp, thh, bb, rsc, e, -, hf1, -⟩ := (h3.ic i).resDone hi a
    obtain ⟨hd4, hd5, -⟩ := (h3.rc r).done hr hb
    rw [hf1, hd5] at hth
    cases hth
  · exfalso
    have ha : (g.ist i).resumed = false := by simpa using a
    have hb : (g.rst r).resumed = true := by simpa using b
    obtain ⟨-, hf5, -⟩ := (h3.ic i).done hi ha
    obtain ⟨p, e, -, h2, -⟩ := (h3.rc r).res (Or.inr ⟨hr, hb⟩)
    rw [hf5, h2] at hth
    cases hth
  · have a' : (g.ist i).resumed = false := by simpa using a
    have b' : (g.rst r).resumed = false := by simpa using b
    simp [a', b']

#audit_axioms Pinc.Hs.agreement_full
#audit_axioms Pinc.Hs.agreement_resumed_flag
#audit_axioms Pinc.Hs.Inv3_reach

end Pinc.Hs
