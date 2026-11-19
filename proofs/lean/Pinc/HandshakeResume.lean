import Pinc.HandshakeTicket3

/-!
# Agreement, secrecy and authentication of resumptions, for unboundedly many sessions

`Inv4` of `HandshakeTicket` holds in every reachable state, for any number of nodes, sessions and tickets and any
store capacities. From it, with the local consistency of `HandshakeLocal` and the full-handshake results, follow for
resumptions:

* agreement (`agreement_resumed`, and `agreement` for a full or a resumed session alike, `agreement_credit` for the
  ALPN, the AEAD, both credit records, the remembered credit record and the connection id secret): equal final
  transcripts mean equal keys, because the final transcript of a resumption binds the Hello (so the ticket's binder,
  hence its pre-shared key) and the Reply;
* secrecy of the application keys, the resumption secret, the connection id secret and the early keys, for both roles:
  the pre-shared key of a ticket of an honest peer is secret (the ledger), and every key of the resumed session is
  derived from it;
* authentication of the responder to the initiator (`authI_resumed`, also when the Reply arrived late) and of the
  initiator to the responder (`authR_resumed`);
* a Reply that arrives late, after the Hello gave way to a full Initial, completes the resumption only if it verifies
  against the Hello's own transcript (`lateSound`);
* a ticket that was used is gone from the store, so a restored copy of it is rejected (`restoredTicketSingleUse`);
* a client store holds only tickets of the ledger (`clientTicketsIssued`).
-/

namespace Pinc.Hs
open Term

/-- The agreement of a finished initiator session and an established responder session (the conclusion of
`agreement_full`). -/
def AgreeC (g : G) (i r : Nat × Nat) : Prop :=
  (g.ist i).send = (g.rst r).recv ∧ (g.ist i).recv = (g.rst r).send ∧ (g.ist i).res = (g.rst r).res ∧
  (g.ist i).cid = (g.rst r).cid ∧ (g.ist i).peer = r.1 ∧ (g.rst r).peer = i.1 ∧
  (g.ist i).al = (g.rst r).al ∧ (g.ist i).ad = (g.rst r).ad ∧
  (g.ist i).pcr = RCr r.1 ∧ (g.rst r).pcr = crd i.1 ∧ (g.ist i).rcr = (g.rst r).rcr

theorem rres_of {g : G} (h3 : Inv3 g) (r : Nat × Nat) (hrr : (g.rst r).resumed = true) :
    RResDone r.1 r.2 (g.rst r) :=
  (h3.rc r).res (by
    rcases (h3.rc r).resFlag hrr with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hrr⟩)

/-- Agreement of resumptions, for any number of sessions, nodes and tickets: an initiator session that finished a
resumption and a responder session that established one, with the same final transcript hash, hold the same
application keys (each one's send key is the other's receive key), the same resumption secret and connection id
secret, name each other as peer, and agree on the ALPN, the AEAD, the credit records of both sides and the credit
record the initiator remembered from the ticket. -/
theorem agreement_resumed {K C : Nat} {g : G} (h : Reach K C g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hri : (g.ist i).resumed = true) (hrr : (g.rst r).resumed = true)
    (hth : (g.ist i).thf = (g.rst r).thf) : AgreeC g i r := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  have hE := EInv_reach h
  have hI := h3.ic i
  have hcr0 := (hI.ne (by simp [hi])).2.1
  obtain ⟨x, ckp, thh, b, rsc, e, ⟨p, hckp, hthh, hb, hxn⟩, hf, hath, hs, hrv, hrs, hcid⟩ := hI.resDone hi hri
  obtain ⟨p', e', hthh', hf', hath', hs', hrv', hrs', hcid', hearly, htp, hsgn, hres, hty, hsc, hre, htids, hcr,
    hbind, hconf⟩ := rres_of h3 r hrr
  obtain ⟨D, b2, rsc2, e2, hres2, -⟩ := (h4.iloc i).done hi hri
  have hth0 := hth
  rw [hf, hf'] at hth
  obtain ⟨hthe, hth2, hth3, hth4, hth5⟩ := Term.thR.inj hth
  have hth1 := hthe
  rw [hthh, hthh'] at hth1
  obtain ⟨-, hal, hdc, hsc2, had, htid, hex, hcr2⟩ := Term.thH.inj hth1
  have hbb : binder p thh = binder p' (g.rst r).thh := hb.symm.trans hth2
  rw [hthe] at hbb
  have hpp : p = p' := (Term.binder.inj hbb).1
  have hdh : Dh x (atomOf e) = Dh (ry r.1 r.2) (atomOf e') := by
    rw [hth4, ← hex]; exact Dh_comm _ _
  have hck : ckp = (g.ist i).ckpsk := by
    have h1 := hrs.symm.trans hres2
    exact (Term.ck1r.inj (Term.ck2.inj (Term.res.inj h1).1).1).1
  have hckne : (g.ist i).ckpsk ≠ nil := by rw [← hck, hckp]; intro h; cases h
  obtain ⟨t, ht, hC⟩ := h4.ick i hckne
  have hpt : p = t.psk := Term.ckpsk.inj (hckp.symm.trans (hck.trans hC.ck))
  obtain ⟨tr, htr, htr1, htr2, htr3, htr4⟩ := h4.rok r hrr
  have htt : tr = t := h4.lfun tr t htr ht (htr1.trans (htp.trans (hpp.symm.trans hpt)))
  obtain ⟨k', hk'⟩ := (hE.ep r (by rw [hearly]; intro h; cases h)).2.2.2
  obtain ⟨k0, hk0⟩ := hC.sess
  rw [htp, ← hpp, hpt, hk0] at hk'
  have hpeer : (g.ist i).peer = r.1 := (Prod.mk.inj (Option.some.inj hk')).1
  refine ⟨?_, ?_, ?_, ?_, hpeer, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, hrv', ← hth0, hckp, hpp, hdh]
  · rw [hrv, hs', ← hth0, hckp, hpp, hdh]
  · rw [hrs, hrs', ← hth0, hckp, hpp, hdh]
  · rw [hcid, hcid', ← hth0, hckp, hpp, hdh]
  · rw [← htr3, htt, hC.own]
  · exact hal
  · exact had
  · exact hth5
  · rw [← hcr2, hcr0]
  · have := hC.rcr (fun _ => hri)
    rw [← this, ← htt, htr4]


/-- A full handshake and a resumption never share a final transcript hash, for an established responder of either
phase: the two sessions resumed alike. -/
theorem agreement_flag {K C : Nat} {g : G} (h : Reach K C g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done ∨ (g.rst r).ph = .resumed) (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).resumed = (g.rst r).resumed := by
  have h3 := Inv3_reach h
  rcases hr with hr | hr
  · exact agreement_resumed_flag h i r hi hr hth
  · have hrr := (h3.rc r).resPh hr
    rw [hrr]
    cases hv : (g.ist i).resumed
    · exfalso
      obtain ⟨-, hf5, -⟩ := (h3.ic i).done hi hv
      obtain ⟨p, e, -, h2, -⟩ := rres_of h3 r hrr
      rw [hf5, h2] at hth
      cases hth
    · rfl

/-- Agreement, in full: an initiator session that finished and an established responder session with the same final
transcript hash resumed alike, hold the same keys, the same resumption secret and connection id secret, name each
other as peer, and agree on the ALPN, the AEAD, the credit records of both sides and the remembered credit record. -/
theorem agreement {K C : Nat} {g : G} (h : Reach K C g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done ∨ (g.rst r).ph = .resumed) (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).resumed = (g.rst r).resumed ∧ AgreeC g i r := by
  have h3 := Inv3_reach h
  have hf := agreement_flag h i r hi hr hth
  refine ⟨hf, ?_⟩
  cases hres : (g.rst r).resumed
  · have hrd : (g.rst r).ph = .done := by
      rcases hr with hr | hr
      · exact hr
      · have := (h3.rc r).resPh hr; rw [hres] at this; cases this
    exact agreement_full h i r hi hrd (by rw [hf, hres]) hres hth
  · exact agreement_resumed h i r hi (by rw [hf, hres]) hres hth

/-- The ALPN, the AEAD, both credit records, the credit record the initiator remembered and the connection id secret
agree between an initiator session that finished and an established responder session with the same final
transcript hash. -/
theorem agreement_credit {K C : Nat} {g : G} (h : Reach K C g) (i r : Nat × Nat) (hi : (g.ist i).ph = .done)
    (hr : (g.rst r).ph = .done ∨ (g.rst r).ph = .resumed) (hth : (g.ist i).thf = (g.rst r).thf) :
    (g.ist i).al = (g.rst r).al ∧ (g.ist i).ad = (g.rst r).ad ∧ (g.ist i).pcr = RCr r.1 ∧
    (g.rst r).pcr = crd i.1 ∧ (g.ist i).rcr = (g.rst r).rcr ∧ (g.ist i).cid = (g.rst r).cid := by
  obtain ⟨-, -, -, -, hc, -, -, ha, hb, hc1, hc2, hc3⟩ := agreement h i r hi hr hth
  exact ⟨ha, hb, hc1, hc2, hc3, hc⟩

/-- Authentication of the responder to the initiator in a resumption, also when the Reply arrived late: a responder
session of the peer holds the same transcript, and signed (accepted the Hello of) it. -/
theorem authI_resumed {K C : Nat} {g : G} (h : Reach K C g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = true) :
    ∃ k, (g.rst ((g.ist i).peer, k)).sgn = true ∧ (g.rst ((g.ist i).peer, k)).ath = (g.ist i).ath := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  obtain ⟨r, hE, hres, hthf, -, -, -, hr1, -⟩ := h4.ires2 i hd hr
  obtain ⟨p, e, -, hf', hath', -, -, -, -, -, -, hsgn, -⟩ := rres_of h3 r hres
  obtain ⟨x, ckp, thh, b, rsc, e2, -, hf, hath, -⟩ := (h3.ic i).resDone hd hr
  have hrr : ((g.ist i).peer, r.2) = r := Prod.ext hr1.symm rfl
  refine ⟨r.2, ?_, ?_⟩
  · rw [hrr]; exact hsgn
  · rw [hrr, hath', hthf, hath]

/-- Authentication of the initiator to the responder in a resumption: an initiator session of the peer sent the
Hello this responder accepted (a resumed responder is established at the Hello). -/
theorem authR_resumed {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (hr : (g.rst r).resumed = true)
    (hp : (g.rst r).peer ≠ att) : ∃ k, (g.ist ((g.rst r).peer, k)).thh = (g.rst r).thh :=
  (Inv4_reach h).hauth r hr hp

/-- The pre-shared key of the ticket a finished resumption used is secret, and so are the keys derived from it. -/
theorem secrecy_init_resumed {K C : Nat} {g : G} (h : Reach K C g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = true) :
    ¬ Known (g.ist i).send ∧ ¬ Known (g.ist i).recv ∧ ¬ Known (g.ist i).res ∧ ¬ Known (g.ist i).cid := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  obtain ⟨x, ckp, thh, b, rsc, e, ⟨p, hckp, hthh, hb, hxn⟩, hf, hath, hs, hrv, hrs, hcid⟩ := (h3.ic i).resDone hd hr
  obtain ⟨D, b2, rsc2, e2, hres2, -⟩ := (h4.iloc i).done hd hr
  have hck : ckp = (g.ist i).ckpsk := by
    have h1 := hrs.symm.trans hres2
    exact (Term.ck1r.inj (Term.ck2.inj (Term.res.inj h1).1).1).1
  have hckne : (g.ist i).ckpsk ≠ nil := by rw [← hck, hckp]; intro h; cases h
  obtain ⟨t, ht, hC⟩ := h4.ick i hckne
  have hpt : p = t.psk := Term.ckpsk.inj (hckp.symm.trans (hck.trans hC.ck))
  have hk : ¬ Known (ck1r ckp (Dh x (atomOf e))) := by
    simp only [Known, hckp, hpt]
    exact fun hh => hC.sec hh.1
  obtain ⟨a, b', c, d⟩ := keys_secret _ (g.ist i).thf hk
  rw [hs, hrv, hrs, hcid]; exact ⟨a, b', c, d⟩

/-- The early keys of an initiator are none or derived from the pre-shared key of a ticket of an honest peer, which
the attacker does not know. -/
theorem secrecy_init_early {K C : Nat} {g : G} (h : Reach K C g) (i : Nat × Nat) : ¬ Known (g.ist i).early := by
  have h4 := Inv4_reach h
  rcases (h4.iloc i).early with he | he
  · rw [he]; simp [Known]
  · rw [he]
    by_cases hc : (g.ist i).ckpsk = nil
    · rw [hc]; simp [Known]
    · obtain ⟨t, ht, hC⟩ := h4.ick i hc
      rw [hC.ck]
      simpa [Known] using hC.sec

/-- Secrecy of the responder's keys and early keys of a resumption with an honest peer (the session is established at
the Hello, so this covers the resumed phase and the done phase alike). -/
theorem secrecy_resp_resumed {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (hr : (g.rst r).resumed = true)
    (hp : (g.rst r).peer ≠ att) :
    ¬ Known (g.rst r).send ∧ ¬ Known (g.rst r).recv ∧ ¬ Known (g.rst r).res ∧ ¬ Known (g.rst r).cid ∧
    ¬ Known (g.rst r).early := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  obtain ⟨p', e', hthh', hf', hath', hs', hrv', hrs', hcid', hearly, htp, -⟩ := rres_of h3 r hr
  obtain ⟨tr, htr, htr1, htr2, htr3, htr4⟩ := h4.rok r hr
  have hsec : ¬ Known p' := by
    have := h4.lsec tr htr (by rw [htr3]; exact hp)
    rwa [htr1, htp] at this
  have hk : ¬ Known (ck1r (ckpsk p') (Dh (ry r.1 r.2) (atomOf e'))) := by
    simp only [Known]; exact fun hh => hsec hh.1
  obtain ⟨a, b, c, d⟩ := keys_secret _ (g.rst r).thf hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs']; exact b
  · rw [hrv']; exact a
  · rw [hrs']; exact c
  · rw [hcid']; exact d
  · rw [hearly]; simpa [Known] using hsec

/-- A resumption whose Reply arrived late, after the Hello gave way to a full Initial under the same destination id,
is as sound as any other: the Reply verified against the Hello's own transcript, so a responder session of the peer
accepted that Hello and signed the transcript, and the keys are secret. -/
theorem lateSound {K C : Nat} {g : G} (h : Reach K C g) (i : Nat × Nat) (hd : (g.ist i).ph = .done)
    (hr : (g.ist i).resumed = true) (_hf : (g.ist i).fell = true) :
    (∃ k, (g.rst ((g.ist i).peer, k)).sgn = true ∧ (g.rst ((g.ist i).peer, k)).ath = (g.ist i).ath ∧
      (g.rst ((g.ist i).peer, k)).thh = (g.ist i).thh) ∧
    ¬ Known (g.ist i).send ∧ ¬ Known (g.ist i).recv ∧ ¬ Known (g.ist i).res ∧ ¬ Known (g.ist i).cid := by
  have h3 := Inv3_reach h
  have h4 := Inv4_reach h
  obtain ⟨r, hE, hres, hthf, -, -, -, hr1, -⟩ := h4.ires2 i hd hr
  obtain ⟨p, e, hthh, hf', hath', -, -, -, -, -, -, hsgn, -⟩ := rres_of h3 r hres
  obtain ⟨x, ckp, thh, b, rsc, e2, -, hf, hath, -⟩ := (h3.ic i).resDone hd hr
  obtain ⟨D, b2, rsc2, e2', -, hf2⟩ := (h4.iloc i).done hd hr
  have hrr : ((g.ist i).peer, r.2) = r := Prod.ext hr1.symm rfl
  refine ⟨⟨r.2, ?_, ?_, ?_⟩, secrecy_init_resumed h i hd hr⟩
  · rw [hrr]; exact hsgn
  · rw [hrr, hath', hthf, hath]
  · rw [hrr]
    rw [hf', hf2] at hthf
    exact (Term.thR.inj hthf).1

/-- A ticket that was used is gone from the responder's store, so a Hello that offers a copy of it (a client store
that was exported and restored after the ticket was used) is not usable: the responder answers with a reject and
neither establishes nor changes anything (`rejectRespRrej`). -/
theorem restoredTicketSingleUse {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (he : (g.rst r).early ≠ nil)
    (m : Msg) (hb : m.binder = binder (g.rst r).tpsk (rhThh m)) : ¬ rhUsable (g.sto r.1) m := by
  intro hu
  obtain ⟨i0, sl, hi0, hsl, hocc, htid, hslot⟩ := rhI0_spec hu.1
  have hbs := hu.2.2.2.2
  rw [hslot, hb] at hbs
  have hps : sl.psk = (g.rst r).tpsk := (Term.binder.inj hbs).1
  exact acceptedGone h r he i0 sl hsl hocc hps

/-- The Hello a client builds from a ticket in its store whose pre-shared key was already accepted by a responder
session is not usable at that responder's store. -/
theorem restoredTicketRejected {K C : Nat} {g : G} (h : Reach K C g) (r : Nat × Nat) (he : (g.rst r).early ≠ nil)
    (n : Nat) (x : Slot) (hx : x ∈ g.cli n) (hocc : x.occ = true) (hpsk : x.psk = (g.rst r).tpsk)
    (k peer : Nat) (al : Term) (short : Bool) :
    ∀ m ∈ (INew n k peer al short (some (TicketOf x))).out, ¬ rhUsable (g.sto r.1) m := by
  intro m hm
  simp only [INew, IBeginResume, Ok, List.mem_singleton] at hm
  subst hm
  exact restoredTicketSingleUse h r he _ (by simp [rhThh, TicketOf, hpsk])

/-- A slot of a client store holds an honest peer's ticket that the peer's responder session issued to this node. -/
theorem clientTicketsIssued {K C : Nat} {g : G} (h : Reach K C g) (n i : Nat) (sl : Slot)
    (hs : (g.cli n)[i]? = some sl) (ho : sl.occ = true) :
    sl.peer ≠ att ∧ ∃ t, g.issued t ∧ t.tid = sl.tid ∧ t.psk = sl.psk ∧ t.peer = n := by
  obtain ⟨hp, -, -, t, ht, e1, e2, e3, -⟩ := (Inv4_reach h).cli n sl (List.mem_of_getElem? hs) ho
  exact ⟨hp, t, ht, e1, e2, e3⟩

#audit_axioms Pinc.Hs.agreement_resumed
#audit_axioms Pinc.Hs.agreement_flag
#audit_axioms Pinc.Hs.agreement
#audit_axioms Pinc.Hs.agreement_credit
#audit_axioms Pinc.Hs.authI_resumed
#audit_axioms Pinc.Hs.authR_resumed
#audit_axioms Pinc.Hs.secrecy_init_resumed
#audit_axioms Pinc.Hs.secrecy_init_early
#audit_axioms Pinc.Hs.secrecy_resp_resumed
#audit_axioms Pinc.Hs.lateSound
#audit_axioms Pinc.Hs.restoredTicketSingleUse
#audit_axioms Pinc.Hs.restoredTicketRejected
#audit_axioms Pinc.Hs.clientTicketsIssued

end Pinc.Hs
