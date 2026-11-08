import Vinc.HandshakeTicket

/-!
# Agreement, secrecy and authentication of resumptions, for unboundedly many sessions

`Inv4` of `HandshakeTicket` holds in every reachable state, for any number of nodes, sessions and tickets and any
store capacity. From it, with the local consistency of `HandshakeLocal` and the full-handshake results, follow for
resumptions: agreement (the same keys and peers), secrecy of the keys and of the early keys, and authentication of the
responder to the initiator (a responder session of the peer holds the same transcript) and of the initiator to the
responder (an initiator session of the peer sent the Hello).
-/

namespace Vinc.Hs
open Term

theorem Inv4_init (K : Nat) : Inv4 (G0 K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [G0]

theorem Inv4_step {K : Nat} {g g' : G} (hr : Reach K g) (h4 : Inv4 g) (hs : Step g g') : Inv4 g' :=
  ⟨Inv4_iss_step hs h4.iss, cli_step hr h4 hs, ires_step hr h4 hs, ires2_step hr h4 hs, rres_step hr h4 hs,
    secrres_step hr h4 hs, netConf_step hr h4 hs, netHello_step hr h4 hs, rres2_step hr h4 hs, nonethh_step h4 hs⟩

theorem Inv4_reach {K : Nat} {g : G} (h : Reach K g) : Inv4 g := by
  induction h with
  | init => exact Inv4_init K
  | step hr hs ih => exact Inv4_step hr ih hs

/-- Agreement of resumptions, for any number of sessions, nodes and tickets: an initiator session and a responder
session that both finished a resumption and hold the same final transcript hash hold the same application keys and
resumption secret and name each other as peer. -/
theorem agreement_resumed {K : Nat} {g : G} (h : Reach K g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hri : (g.ist i).resumed = true) (hr : (g.rst r).ph = .done) (hrr : (g.rst r).resumed = true)
    (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).send = (g.rst r).recv ∧ (g.ist i).recv = (g.rst r).send ∧ (g.ist i).res = (g.rst r).res ∧
    (g.ist i).peer = r.1 ∧ (g.rst r).peer = i.1 :=
  agree_res (Inv3_reach h) (Inv4_reach h) i r hi hri hr hrr hth

/-- Agreement, in full: two finished sessions with the same final transcript hash resumed alike, hold the same keys,
the same resumption secret, and name each other as peer. -/
theorem agreement {K : Nat} {g : G} (h : Reach K g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done) (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).resumed = (g.rst r).resumed ∧
    (g.ist i).send = (g.rst r).recv ∧ (g.ist i).recv = (g.rst r).send ∧ (g.ist i).res = (g.rst r).res ∧
    (g.ist i).peer = r.1 ∧ (g.rst r).peer = i.1 := by
  have hf := agreement_resumed_flag h i r hi hr hth
  refine ⟨hf, ?_⟩
  cases hres : (g.rst r).resumed
  · exact agreement_full h i r hi hr (by rw [hf, hres]) hres hth
  · exact agreement_resumed h i r hi (by rw [hf, hres]) hr hres hth

/-- Secrecy of the initiator's keys of a resumption. -/
theorem secrecy_init_resumed {K : Nat} {g : G} (h : Reach K g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = true) :
    ¬ Known (g.ist i).send ∧ ¬ Known (g.ist i).recv ∧ ¬ Known (g.ist i).res := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  have hn : i.1 ≠ att := (h3.ic i).1 (by simp [hd])
  obtain ⟨rn, rk, a, b, c, d, e, f⟩ := h4.ires i (Or.inr ⟨hd, hr⟩)
  obtain ⟨rp, ee, hf, -, hs, hrv, hrs⟩ := (h3.ic i).2.2.2.2.2.2 hd hr
  have hsec := issuer_res_secret h h4 d (by rw [f]; exact hn)
  have hck : ¬ Known (g.ist i).ckpsk := by
    rw [e]; simpa [Known] using hsec
  rw [hs, hrv, hrs]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Known] <;> intro hk <;> exact hck hk.1

/-- Secrecy of the early keys of an initiator that resumes, when its peer is honest (it always is: tickets are only
kept for honest peers). -/
theorem secrecy_init_early {K : Nat} {g : G} (h : Reach K g) (i : Nat × Nat)
    (hp : (g.ist i).ph = .resume ∨ ((g.ist i).ph = .done ∧ (g.ist i).resumed = true)) :
    ¬ Known (g.ist i).early := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  have hn : i.1 ≠ att := (h3.ic i).1 (by rcases hp with hp | hp <;> simp [hp])
  obtain ⟨rn, rk, a, b, c, d, e, f⟩ := h4.ires i hp
  obtain ⟨p, h1, h2, h3', h4', h5, h6⟩ := (h3.ic i).2.2.2.2.2.1 hp
  have hsec := issuer_res_secret h h4 d (by rw [f]; exact hn)
  rw [h6, e]
  simpa [Known] using hsec

/-- Secrecy of the responder's keys and early keys of a resumption with an honest peer. -/
theorem secrecy_resp_resumed {K : Nat} {g : G} (h : Reach K g) (r : Nat × Nat) (hd : (g.rst r).ph = .done)
    (hr : (g.rst r).resumed = true) (hp : (g.rst r).peer ≠ att) :
    ¬ Known (g.rst r).send ∧ ¬ Known (g.rst r).recv ∧ ¬ Known (g.rst r).res ∧ ¬ Known (g.rst r).early := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  obtain ⟨rk0, ht, hI, hpeer, hearly⟩ := h4.rres r hd hr
  obtain ⟨p, ee, b, hh1, hh2, hh3, hb, hs, hrv, hrs, he, -⟩ := (h3.rc r).2.2.2.2.2.2.2.1 hd hr
  have hsec := issuer_res_secret h h4 hI (by rw [← hpeer]; exact hp)
  have hpp : p = psk (g.rst (r.1, rk0)).res (g.rst r).tid := by
    rw [hearly] at he
    simp only [early.injEq, ckpsk.injEq] at he
    exact he.1.symm
  have hckp : ¬ Known p := by rw [hpp]; simpa [Known] using hsec
  refine ⟨?_, ?_, h4.secrres r hd hr hp, ?_⟩
  · rw [hs]; intro hk; simp [Known] at hk; exact hckp hk.1
  · rw [hrv]; intro hk; simp [Known] at hk; exact hckp hk.1
  · rw [he]; simpa [Known] using hckp

/-- Authentication of the responder to the initiator in a resumption: a responder session of the peer holds the same
transcript. -/
theorem authI_resumed {K : Nat} {g : G} (h : Reach K g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = true) :
    ∃ k, (g.rst ((g.ist i).peer, k)).sgn = true ∧ (g.rst ((g.ist i).peer, k)).ath = (g.ist i).ath := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  obtain ⟨r, hrd, hrr, hthf, -⟩ := h4.ires2 i hd hr
  obtain ⟨-, -, -, k4, -⟩ := agree_res h3 h4 i r hd hr hrd hrr hthf.symm
  obtain ⟨rp, ee, hf, hath, -⟩ := (h3.ic i).2.2.2.2.2.2 hd hr
  obtain ⟨p, e, b, hh1, hh2, hh3, -⟩ := (h3.rc r).2.2.2.2.2.2.2.1 hrd hrr
  refine ⟨r.2, ?_, ?_⟩
  · have : ((g.ist i).peer, r.2) = r := Prod.ext k4 rfl
    rw [this]; exact (h3.rc r).2.2.2.2.2.1 hrd
  · have : ((g.ist i).peer, r.2) = r := Prod.ext k4 rfl
    rw [this, hh3, hath]; exact hthf

/-- Authentication of the initiator to the responder in a resumption: an initiator session of the peer sent the
Hello this responder accepted. -/
theorem authR_resumed {K : Nat} {g : G} (h : Reach K g) (r : Nat × Nat) (hd : (g.rst r).ph = .done)
    (hr : (g.rst r).resumed = true) (hp : (g.rst r).peer ≠ att) :
    ∃ k, (g.ist ((g.rst r).peer, k)).thh = (g.rst r).thh :=
  (Inv4_reach h).rres2 r hd hr hp

#audit_axioms Vinc.Hs.Inv4_reach
#audit_axioms Vinc.Hs.agreement_resumed
#audit_axioms Vinc.Hs.agreement
#audit_axioms Vinc.Hs.secrecy_init_resumed
#audit_axioms Vinc.Hs.secrecy_init_early
#audit_axioms Vinc.Hs.secrecy_resp_resumed
#audit_axioms Vinc.Hs.authI_resumed
#audit_axioms Vinc.Hs.authR_resumed

end Vinc.Hs
