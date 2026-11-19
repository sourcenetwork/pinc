import Pinc.HandshakeAgree

/-!
# Secrecy of the full handshake, for unboundedly many sessions

The application keys, the resumption secret and the connection id secret of a finished full handshake with an honest
peer are not known to the attacker (`Known`, the Dolev-Yao deduction of `HandshakeModel`), for any number of sessions.
The chain key of the hybrid schedule needs both the KEM secret and the Diffie-Hellman secret, so one of them being out
of the attacker's reach suffices (`HandshakeHybrid` proves it with either half broken). The authentication witnesses of `HandshakeInv` (`iAuth`, `rAuth`) name the honest
peer session that signed the same transcript, and the local consistency of `HandshakeLocal` reads the peer's ephemeral
and prekey owner off that transcript.
-/

namespace Pinc.Hs
open Term

theorem Known_Dh (a b : Atom) : Known (Dh a b) ↔ owner a = att ∨ owner b = att := by
  unfold Dh
  split
  · simp only [Known]; constructor <;> intro h <;> rcases h with h | h <;> simp [h]
  · simp only [Known]

theorem not_Known_Dh (a b : Atom) (ha : owner a ≠ att) (hb : owner b ≠ att) : ¬ Known (Dh a b) := by
  rw [Known_Dh]; intro h; rcases h with h | h <;> contradiction

theorem not_Known_kem (c : Atom) (e : Term) (hc : owner c ≠ att) (ho : ekNode e ≠ att) : ¬ Known (kem c e) := by
  simp only [Known]; intro h; rcases h with h | h <;> contradiction

/-- The keys of a finished session are as secret as its chain key. -/
theorem keys_secret (ck : Term) (th : Term) (hk : ¬ Known ck) :
    ¬ Known (app (ck2 ck th) true th) ∧ ¬ Known (app (ck2 ck th) false th) ∧ ¬ Known (res (ck2 ck th) th)
    ∧ ¬ Known (cids (ck2 ck th) th) := by
  simp [Known, hk]

theorem ck1_secret_l (a b : Term) (h : ¬ Known a) : ¬ Known (ck1 a b) := by
  simp only [Known]; intro h'; exact h h'.1

theorem ck1_secret_r (a b : Term) (h : ¬ Known b) : ¬ Known (ck1 a b) := by
  simp only [Known]; intro h'; exact h h'.2

/-- Equal transcripts up to the responder's signature fix the Initial the responder saw. -/
theorem chain_th3 (i r : Nat × Nat) (sti : IState) (str : RState) (m : Msg) (hs : ISign i.1 sti)
    (hri : RInitM r.1 r.2 str m) (hrf : RFin r.1 r.2 str) (h3 : sti.th3 = str.th3) :
    sti.peer = r.1 ∧ sti.reply.e = pub (ry r.1 r.2) ∧ m.e = pub sti.x ∧ rHpk m = hash (ek i.1) := by
  obtain ⟨⟨⟨hb0, hbx, hbr⟩, hio, had, ht1, hssx⟩, hck, hid, hcrn, hpcr, ht2, ht3, ht4, hath, hsig, hhsi⟩ := hs
  obtain ⟨hver, hsv, hadn, h0, hhp, hek, hct, hr1, hr2, hra, hrck, -, -, -, -, hal, hadr, -, -, hpr, -⟩ := hri
  obtain ⟨hf3, -⟩ := hrf
  rw [ht3, hf3] at h3
  simp only [th3.injEq] at h3
  obtain ⟨h2, hs3⟩ := h3
  rw [ht2, hr2] at h2
  unfold rT2 at h2
  simp only [th2.injEq] at h2
  obtain ⟨h1, hp2, -⟩ := h2
  rw [ht1] at h1
  unfold rT1 at h1
  simp only [th1.injEq] at h1
  obtain ⟨h0', -, -, he, hc⟩ := h1
  have h0m : th0 ok sti.al sti.dc sti.sc sti.cr sti.of (pub sti.x) (hash (ek i.1)) = th0 m.ver m.al m.dc m.sc m.cr m.of m.e (rHpk m) := by
    rw [← hb0, h0']; rfl
  simp only [th0.injEq] at h0m
  obtain ⟨-, -, -, -, -, -, hex, hhk⟩ := h0m
  exact ⟨hp2, he, hex.symm, hhk.symm⟩

/-- The responder session a full initiator authenticated is a full one: the reply's ephemeral is its. -/
theorem iAuth_reply_e {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = false) (hp : (g.ist i).peer ≠ att) :
    ∃ k, (g.ist i).reply.e = pub (ry (g.ist i).peer k) := by
  have h1 := Inv1_reach h
  have h3 := Inv3_reach h
  obtain ⟨hsI, -⟩ := (h3.ic i).done hd hr
  obtain ⟨k, hsgn, hath⟩ := h1.iAuth i (Or.inr hd) hr hp
  refine ⟨k, ?_⟩
  have hr' : (g.rst ((g.ist i).peer, k)).resumed = false := by
    cases hv : (g.rst ((g.ist i).peer, k)).resumed
    · rfl
    exfalso
    have hdn : (g.rst ((g.ist i).peer, k)).ph = .resumed ∨ (g.rst ((g.ist i).peer, k)).ph = .done :=
      (h3.rc ((g.ist i).peer, k)).resFlag hv
    have hrd := (h3.rc ((g.ist i).peer, k)).res (by rcases hdn with e | e <;> simp [e, hv])
    obtain ⟨p, e, -, hh2, hh3, -⟩ := hrd
    have : (g.ist i).ath = (g.ist i).th2 := hsI.2.2.2.2.2.2.2.2.1
    rw [this, hsI.2.2.2.2.2.1, hh3, hh2] at hath
    cases hath
  obtain ⟨⟨m, hm⟩, hfin⟩ := (h3.rc ((g.ist i).peer, k)).signed hsgn hr'
  obtain ⟨hver, hsv, hadn, h0, hhp, hek, hct, hr1, hr2, hra, hrck, -, -, -, -, hal, hadr, -, -, hpr, -⟩ := hm
  obtain ⟨⟨⟨hb0, hbx, hbr⟩, hio, had, ht1, hssx⟩, hck, hid, hcrn, hpcr, ht2, ht3, ht4, hath', hsig, hhsi⟩ := hsI
  rw [hra, hath', hr2, ht2] at hath
  unfold rT2 at hath
  simp only [th2.injEq] at hath
  obtain ⟨hth1, -⟩ := hath
  rw [ht1] at hth1
  unfold rT1 at hth1
  simp only [th1.injEq] at hth1
  exact hth1.2.2.2.1.symm

/-- The initiator's keys of a finished full handshake with an honest peer are secret. -/
theorem secrecy_init_full {K C : Nat} {g : G} (h : Reach K C g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = false) (hp : (g.ist i).peer ≠ att) :
    ¬ Known (g.ist i).send ∧ ¬ Known (g.ist i).recv ∧ ¬ Known (g.ist i).res ∧ ¬ Known (g.ist i).cid := by
  have h3 := Inv3_reach h
  have hn : i.1 ≠ att := ((h3.ic i).ne (by simp [hd])).1
  obtain ⟨k, hk⟩ := iAuth_reply_e h i hd hr hp
  obtain ⟨⟨⟨⟨hb0, hbx, hbr⟩, hio, had, ht1, hssx⟩, hck, hid, hcrn, hpcr, ht2, ht3, ht4, hath, hsig, hhsi⟩, hf5, hs, hrv, hrs, hcid, -⟩ :=
    (h3.ic i).done hd hr
  have hx : owner (g.ist i).x ≠ att := by simp only [owner, hbx]; exact hn
  have he : owner (atomOf (g.ist i).reply.e) ≠ att := by simp [hk, atomOf, ry, atom, owner]; exact hp
  have hssx' : ¬ Known (g.ist i).ssx := by rw [hssx]; exact not_Known_Dh _ _ hx he
  have hck1 : ¬ Known (g.ist i).ck1 := by
    rw [hck]; exact ck1_secret_r _ _ hssx'
  obtain ⟨a, b, c, d⟩ := keys_secret _ (g.ist i).thf hck1
  rw [hs, hrv, hrs, hcid]; exact ⟨a, b, c, d⟩

/-- The responder's keys of a finished full handshake with an honest peer are secret. -/
theorem secrecy_resp_full {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (hd : (g.rst r).ph = .done)
    (hr : (g.rst r).resumed = false) (hp : (g.rst r).peer ≠ att) :
    ¬ Known (g.rst r).send ∧ ¬ Known (g.rst r).recv ∧ ¬ Known (g.rst r).res ∧ ¬ Known (g.rst r).cid := by
  have h1 := Inv1_reach h
  have h3 := Inv3_reach h
  have hn : r.1 ≠ att := (h3.rc r).ne (by simp [hd])
  obtain ⟨k, hid, hth4, hres⟩ := h1.rAuth r hd hr hp
  obtain ⟨⟨m, hm⟩, hfin⟩ := (h3.rc r).signed ((h3.rc r).doneSgn hd) hr
  obtain ⟨hd4, hd5, hds, hdr, hdres, hdcid⟩ := (h3.rc r).done hd hr
  have hth4' : (g.ist ((g.rst r).peer, k)).th4 = th4 (g.rst r).th3 (g.rst r).peer := by rw [hth4, hd4]
  obtain ⟨hsI, hf5, -⟩ := (h3.ic ((g.rst r).peer, k)).done hid hres
  have h4i := hsI.2.2.2.2.2.2.2.1
  rw [h4i] at hth4'
  simp only [th4.injEq] at hth4'
  obtain ⟨h3eq, hn2⟩ := hth4'
  obtain ⟨-, -, -, hhk⟩ := chain_th3 ((g.rst r).peer, k) r _ _ m hsI hm hfin h3eq
  have hnode : ekNode (rEk m) = (g.rst r).peer := by rw [rEk_of_rHpk m _ hhk]; rfl
  have hrck : (g.rst r).ck1 = rCk1 r.1 r.2 m := hm.2.2.2.2.2.2.2.2.2.2.1
  have hkem : ¬ Known (kem (rcoin r.1 r.2) (rEk m)) :=
    not_Known_kem _ _ (by simp [rcoin, atom, owner]; exact hn) (by rw [hnode]; exact hp)
  have hck1 : ¬ Known (g.rst r).ck1 := by
    rw [hrck]; unfold rCk1; exact ck1_secret_l _ _ hkem
  obtain ⟨a, b, c, d⟩ := keys_secret _ (g.rst r).thf hck1
  rw [hds, hdr, hdres, hdcid]; exact ⟨b, a, c, d⟩

#audit_axioms Pinc.Hs.secrecy_init_full
#audit_axioms Pinc.Hs.secrecy_resp_full

end Pinc.Hs
