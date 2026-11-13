import Vinc.HandshakeSecrecy

/-!
# The hybrid: secrecy of the full handshake with one half broken, for unboundedly many sessions

The chain key of a full handshake is `extract(ck0, ss_K || ss_X)` (`ck1`): the KEM secret of ML-KEM-768 and the
Diffie-Hellman secret of X25519. This file runs the system of `HandshakeSys` against the attacker `KnownB bx bk` of
`HandshakeModel`, which with `bx` learns the Diffie-Hellman secret of every exchange and with `bk` the KEM secret of
every ciphertext (and every implicit-rejection value); it uses that knowledge in what it injects (`DerivableK`).
Signatures, hashes and the AEAD stay ideal.

* `secrecy_xbroken`, `secrecy_kbroken`: with exactly one half broken, the application keys, the resumption secret and
  the connection id secret of a finished full handshake with an honest peer are still secret, on both sides. Each side
  has its own proof through each half: the initiator's ciphertext is the one its authenticated peer made to its own
  prekey, and the responder's peer ephemeral is the one of the initiator session that signed the transcript.
* `bothbroken_init_known`, `bothbroken_resp_known`: with both broken, every finished full handshake's keys are known
  (TLC shows such a session with an honest peer is reachable: `Handshake_bothbroken`).
* Agreement and authentication hold against every attacker `kn`, a broken half included: `agreement_full`, `authI`
  and `authR` are stated for `ReachK kn` (`HandshakeInv`, `HandshakeAgree`); they rest on the signatures and on the
  keys being a function of the transcript.
* `resumed_init_as_psk`, `resumed_resp_as_psk`: a resumed session runs no ML-KEM, its chain key is
  `extract(extract(ck0, psk), ss_X)`; with X25519 broken its keys are known exactly when the pre-shared key it
  descends from is. This is the design limit of resumption, not a flaw: its post-quantum protection is the one of
  the full handshake that issued the ticket.
-/

namespace Vinc.Hs
open Term

theorem KnownB_Dh (bx bk : Bool) (a b : Atom) :
    KnownB bx bk (Dh a b) ↔ bx = true ∨ owner a = att ∨ owner b = att := by
  unfold Dh
  split
  · simp only [KnownB]; constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]
  · simp only [KnownB]

theorem not_KnownB_Dh (bk : Bool) (a b : Atom) (ha : owner a ≠ att) (hb : owner b ≠ att) :
    ¬ KnownB false bk (Dh a b) := by
  rw [KnownB_Dh]; intro h; rcases h with h | h | h <;> simp_all

theorem not_KnownB_kem (bx : Bool) (c : Atom) (e : Term) (hc : owner c ≠ att) (ho : ekNode e ≠ att) :
    ¬ KnownB bx false (kem c e) := by
  simp only [KnownB]; intro h; rcases h with h | h | h <;> simp_all

/-- The keys of a finished session are as secret as its chain key. -/
theorem keysB_secret (bx bk : Bool) (ck th : Term) (hk : ¬ KnownB bx bk ck) :
    ¬ KnownB bx bk (app (ck2 ck th) true th) ∧ ¬ KnownB bx bk (app (ck2 ck th) false th) ∧
    ¬ KnownB bx bk (res (ck2 ck th) th) ∧ ¬ KnownB bx bk (cids (ck2 ck th) th) := by
  simp [KnownB, hk]

theorem keysB_known (bx bk : Bool) (ck th : Term) (hk : KnownB bx bk ck) :
    KnownB bx bk (app (ck2 ck th) true th) ∧ KnownB bx bk (app (ck2 ck th) false th) ∧
    KnownB bx bk (res (ck2 ck th) th) ∧ KnownB bx bk (cids (ck2 ck th) th) := by
  simp [KnownB, hk]

/-- The responder session a finished full initiator authenticated made the reply's ephemeral and its ciphertext, the
latter to the initiator's own prekey. -/
theorem iAuth_full {kn : Term → Prop} {K C : Nat} {g : G} (h : ReachK kn K C g) (i : Nat × Nat)
    (hd : (g.ist i).ph = .done) (hr : (g.ist i).resumed = false) (hp : (g.ist i).peer ≠ att) :
    ∃ k m, (g.ist i).reply.e = pub (ry (g.ist i).peer k) ∧ (g.ist i).reply.ct = rC (g.ist i).peer k m ∧
      rEk m = ek i.1 := by
  have h1 := Inv1_reach h
  have h3 := Inv3_reach h
  obtain ⟨hsI, -⟩ := (h3.ic i).done hd hr
  obtain ⟨k, hsgn, hath⟩ := h1.iAuth i (Or.inr hd) hr hp
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
  obtain ⟨⟨m, hm⟩, -⟩ := (h3.rc ((g.ist i).peer, k)).signed hsgn hr'
  obtain ⟨-, -, -, -, -, -, -, -, hr2, hra, -⟩ := hm
  obtain ⟨⟨⟨hb0, -, -⟩, -, -, ht1, -⟩, -, -, -, -, ht2, -, -, hath', -, -⟩ := hsI
  rw [hra, hath', hr2, ht2] at hath
  unfold rT2 at hath
  simp only [th2.injEq] at hath
  obtain ⟨hth1, -⟩ := hath
  rw [ht1] at hth1
  unfold rT1 at hth1
  simp only [th1.injEq] at hth1
  obtain ⟨h0', -, -, he, hc⟩ := hth1
  have h0m : th0 ok (g.ist i).al (g.ist i).dc (g.ist i).sc (g.ist i).cr (g.ist i).of (pub (g.ist i).x) (hash (ek i.1))
      = th0 m.ver m.al m.dc m.sc m.cr m.of m.e (rHpk m) := by
    rw [← hb0, ← h0']; rfl
  simp only [th0.injEq] at h0m
  obtain ⟨-, -, -, -, -, -, -, hhk⟩ := h0m
  exact ⟨k, m, he.symm, hc.symm, rEk_of_rHpk m i.1 hhk.symm⟩

/-! ## The initiator -/

/-- Through the Diffie-Hellman half: with X25519 intact, the initiator's keys are secret whatever ML-KEM gives away. -/
theorem secrecy_init_dh {bk : Bool} {K C : Nat} {g : G} (h : ReachK (KnownB false bk) K C g) (i : Nat × Nat)
    (hd : (g.ist i).ph = .done) (hr : (g.ist i).resumed = false) (hp : (g.ist i).peer ≠ att) :
    ¬ KnownB false bk (g.ist i).send ∧ ¬ KnownB false bk (g.ist i).recv ∧ ¬ KnownB false bk (g.ist i).res ∧
    ¬ KnownB false bk (g.ist i).cid := by
  have h3 := Inv3_reach h
  have hn : i.1 ≠ att := ((h3.ic i).ne (by simp [hd])).1
  obtain ⟨k, hk⟩ := iAuth_reply_e h i hd hr hp
  obtain ⟨⟨⟨⟨-, hbx, -⟩, -, -, -, hssx⟩, hck, -⟩, -, hs, hrv, hrs, hcid, -⟩ := (h3.ic i).done hd hr
  have hx : owner (g.ist i).x ≠ att := by simp only [owner, hbx]; exact hn
  have he : owner (atomOf (g.ist i).reply.e) ≠ att := by simp [hk, atomOf, ry, atom, owner]; exact hp
  have hck1 : ¬ KnownB false bk (g.ist i).ck1 := by
    rw [hck]; unfold ikCk1; rw [hssx]; simp only [KnownB]
    exact fun h' => not_KnownB_Dh bk _ _ hx he h'.2
  rw [hs, hrv, hrs, hcid]; exact keysB_secret _ _ _ _ hck1

/-- Through the ML-KEM half: with ML-KEM intact, the initiator's keys are secret whatever X25519 gives away. The
ciphertext it decapsulated is the one its authenticated peer's responder session made to its own prekey. -/
theorem secrecy_init_kem {bx : Bool} {K C : Nat} {g : G} (h : ReachK (KnownB bx false) K C g) (i : Nat × Nat)
    (hd : (g.ist i).ph = .done) (hr : (g.ist i).resumed = false) (hp : (g.ist i).peer ≠ att) :
    ¬ KnownB bx false (g.ist i).send ∧ ¬ KnownB bx false (g.ist i).recv ∧ ¬ KnownB bx false (g.ist i).res ∧
    ¬ KnownB bx false (g.ist i).cid := by
  have h3 := Inv3_reach h
  have hn : i.1 ≠ att := ((h3.ic i).ne (by simp [hd])).1
  obtain ⟨k, m, -, hc, hek⟩ := iAuth_full h i hd hr hp
  obtain ⟨⟨-, hck, -⟩, -, hs, hrv, hrs, hcid, -⟩ := (h3.ic i).done hd hr
  have hssk : ikSsk (g.ist i) i.1 = kem (rcoin (g.ist i).peer k) (ek i.1) := by
    unfold ikSsk; rw [hc]; unfold rC; rw [hek]; simp [Decap]
  have hkem : ¬ KnownB bx false (kem (rcoin (g.ist i).peer k) (ek i.1)) :=
    not_KnownB_kem bx _ _ (by simp [rcoin, atom, owner]; exact hp) (by simp [ekNode]; exact hn)
  have hck1 : ¬ KnownB bx false (g.ist i).ck1 := by
    rw [hck]; unfold ikCk1; rw [hssk]; simp only [KnownB]; exact fun h' => hkem h'.1
  rw [hs, hrv, hrs, hcid]; exact keysB_secret _ _ _ _ hck1

/-! ## The responder -/

/-- Through the ML-KEM half: the responder's own coin, encapsulated to the prekey of the initiator that signed. -/
theorem secrecy_resp_kem {bx : Bool} {K C : Nat} {g : G} (h : ReachK (KnownB bx false) K C g) (r : Nat × Nat)
    (hd : (g.rst r).ph = .done) (hr : (g.rst r).resumed = false) (hp : (g.rst r).peer ≠ att) :
    ¬ KnownB bx false (g.rst r).send ∧ ¬ KnownB bx false (g.rst r).recv ∧ ¬ KnownB bx false (g.rst r).res ∧
    ¬ KnownB bx false (g.rst r).cid := by
  have h1 := Inv1_reach h
  have h3 := Inv3_reach h
  have hn : r.1 ≠ att := (h3.rc r).ne (by simp [hd])
  obtain ⟨k, hid, hth4, hres⟩ := h1.rAuth r hd hr hp
  obtain ⟨⟨m, hm⟩, hfin⟩ := (h3.rc r).signed ((h3.rc r).doneSgn hd) hr
  obtain ⟨hd4, -, hds, hdr, hdres, hdcid⟩ := (h3.rc r).done hd hr
  have hth4' : (g.ist ((g.rst r).peer, k)).th4 = th4 (g.rst r).th3 (g.rst r).peer := by rw [hth4, hd4]
  obtain ⟨hsI, -⟩ := (h3.ic ((g.rst r).peer, k)).done hid hres
  rw [hsI.2.2.2.2.2.2.2.1] at hth4'
  simp only [th4.injEq] at hth4'
  obtain ⟨h3eq, -⟩ := hth4'
  obtain ⟨-, -, -, hhk⟩ := chain_th3 ((g.rst r).peer, k) r _ _ m hsI hm hfin h3eq
  have hnode : ekNode (rEk m) = (g.rst r).peer := by rw [rEk_of_rHpk m _ hhk]; rfl
  have hrck : (g.rst r).ck1 = rCk1 r.1 r.2 m := hm.2.2.2.2.2.2.2.2.2.2.1
  have hkem : ¬ KnownB bx false (kem (rcoin r.1 r.2) (rEk m)) :=
    not_KnownB_kem bx _ _ (by simp [rcoin, atom, owner]; exact hn) (by rw [hnode]; exact hp)
  have hck1 : ¬ KnownB bx false (g.rst r).ck1 := by
    rw [hrck]; unfold rCk1; simp only [KnownB]; exact fun h' => hkem h'.1
  obtain ⟨a, b, c, d⟩ := keysB_secret _ _ _ (g.rst r).thf hck1
  rw [hds, hdr, hdres, hdcid]; exact ⟨b, a, c, d⟩

/-- Through the Diffie-Hellman half: the responder's own ephemeral and the ephemeral of the initiator that signed. -/
theorem secrecy_resp_dh {bk : Bool} {K C : Nat} {g : G} (h : ReachK (KnownB false bk) K C g) (r : Nat × Nat)
    (hd : (g.rst r).ph = .done) (hr : (g.rst r).resumed = false) (hp : (g.rst r).peer ≠ att) :
    ¬ KnownB false bk (g.rst r).send ∧ ¬ KnownB false bk (g.rst r).recv ∧ ¬ KnownB false bk (g.rst r).res ∧
    ¬ KnownB false bk (g.rst r).cid := by
  have h1 := Inv1_reach h
  have h3 := Inv3_reach h
  have hn : r.1 ≠ att := (h3.rc r).ne (by simp [hd])
  obtain ⟨k, hid, hth4, hres⟩ := h1.rAuth r hd hr hp
  obtain ⟨⟨m, hm⟩, hfin⟩ := (h3.rc r).signed ((h3.rc r).doneSgn hd) hr
  obtain ⟨hd4, -, hds, hdr, hdres, hdcid⟩ := (h3.rc r).done hd hr
  have hth4' : (g.ist ((g.rst r).peer, k)).th4 = th4 (g.rst r).th3 (g.rst r).peer := by rw [hth4, hd4]
  obtain ⟨hsI, -⟩ := (h3.ic ((g.rst r).peer, k)).done hid hres
  have hbx : (g.ist ((g.rst r).peer, k)).x.n = (g.rst r).peer := hsI.1.1.2.1
  rw [hsI.2.2.2.2.2.2.2.1] at hth4'
  simp only [th4.injEq] at hth4'
  obtain ⟨h3eq, -⟩ := hth4'
  obtain ⟨-, -, hme, -⟩ := chain_th3 ((g.rst r).peer, k) r _ _ m hsI hm hfin h3eq
  have hrck : (g.rst r).ck1 = rCk1 r.1 r.2 m := hm.2.2.2.2.2.2.2.2.2.2.1
  have hy : owner (ry r.1 r.2) ≠ att := by simp [ry, atom, owner]; exact hn
  have hx : owner (atomOf m.e) ≠ att := by rw [hme]; simp only [atomOf, owner, hbx]; exact hp
  have hck1 : ¬ KnownB false bk (g.rst r).ck1 := by
    rw [hrck]; unfold rCk1; simp only [KnownB]; exact fun h' => not_KnownB_Dh bk _ _ hy hx h'.2
  obtain ⟨a, b, c, d⟩ := keysB_secret _ _ _ (g.rst r).thf hck1
  rw [hds, hdr, hdres, hdcid]; exact ⟨b, a, c, d⟩

/-! ## One half broken -/

/-- With X25519 broken and ML-KEM intact, the keys of every finished full handshake with an honest peer are secret on
both sides, for any number of sessions. -/
theorem secrecy_xbroken {K C : Nat} {g : G} (h : ReachK (KnownB true false) K C g) :
    (∀ i, (g.ist i).ph = .done → (g.ist i).resumed = false → (g.ist i).peer ≠ att →
      ¬ KnownB true false (g.ist i).send ∧ ¬ KnownB true false (g.ist i).recv ∧
      ¬ KnownB true false (g.ist i).res ∧ ¬ KnownB true false (g.ist i).cid) ∧
    (∀ r, (g.rst r).ph = .done → (g.rst r).resumed = false → (g.rst r).peer ≠ att →
      ¬ KnownB true false (g.rst r).send ∧ ¬ KnownB true false (g.rst r).recv ∧
      ¬ KnownB true false (g.rst r).res ∧ ¬ KnownB true false (g.rst r).cid) :=
  ⟨fun i hd hr hp => secrecy_init_kem h i hd hr hp, fun r hd hr hp => secrecy_resp_kem h r hd hr hp⟩

/-- With ML-KEM broken and X25519 intact, the same. -/
theorem secrecy_kbroken {K C : Nat} {g : G} (h : ReachK (KnownB false true) K C g) :
    (∀ i, (g.ist i).ph = .done → (g.ist i).resumed = false → (g.ist i).peer ≠ att →
      ¬ KnownB false true (g.ist i).send ∧ ¬ KnownB false true (g.ist i).recv ∧
      ¬ KnownB false true (g.ist i).res ∧ ¬ KnownB false true (g.ist i).cid) ∧
    (∀ r, (g.rst r).ph = .done → (g.rst r).resumed = false → (g.rst r).peer ≠ att →
      ¬ KnownB false true (g.rst r).send ∧ ¬ KnownB false true (g.rst r).recv ∧
      ¬ KnownB false true (g.rst r).res ∧ ¬ KnownB false true (g.rst r).cid) :=
  ⟨fun i hd hr hp => secrecy_init_dh h i hd hr hp, fun r hd hr hp => secrecy_resp_dh h r hd hr hp⟩

/-! ## Both broken -/

/-- With both halves broken the chain key of every finished full initiator is known, so are its keys. -/
theorem bothbroken_init_known {K C : Nat} {g : G} (h : ReachK (KnownB true true) K C g) (i : Nat × Nat)
    (hd : (g.ist i).ph = .done) (hr : (g.ist i).resumed = false) :
    KnownB true true (g.ist i).send ∧ KnownB true true (g.ist i).recv ∧ KnownB true true (g.ist i).res ∧
    KnownB true true (g.ist i).cid := by
  have h3 := Inv3_reach h
  obtain ⟨⟨⟨-, -, -, -, hssx⟩, hck, -⟩, -, hs, hrv, hrs, hcid, -⟩ := (h3.ic i).done hd hr
  have hdec : ∀ n c, KnownB true true (Decap n c) := by
    intro n c; unfold Decap; split
    · split <;> simp [KnownB]
    · simp [KnownB]
  have hck1 : KnownB true true (g.ist i).ck1 := by
    rw [hck]; unfold ikCk1; rw [hssx]
    exact ⟨hdec _ _, (KnownB_Dh true true _ _).2 (Or.inl rfl)⟩
  rw [hs, hrv, hrs, hcid]; exact keysB_known _ _ _ _ hck1

/-- ... and of every finished full responder. -/
theorem bothbroken_resp_known {K C : Nat} {g : G} (h : ReachK (KnownB true true) K C g) (r : Nat × Nat)
    (hd : (g.rst r).ph = .done) (hr : (g.rst r).resumed = false) :
    KnownB true true (g.rst r).send ∧ KnownB true true (g.rst r).recv ∧ KnownB true true (g.rst r).res ∧
    KnownB true true (g.rst r).cid := by
  have h3 := Inv3_reach h
  obtain ⟨⟨m, hm⟩, -⟩ := (h3.rc r).signed ((h3.rc r).doneSgn hd) hr
  obtain ⟨-, -, hds, hdr, hdres, hdcid⟩ := (h3.rc r).done hd hr
  have hrck : (g.rst r).ck1 = rCk1 r.1 r.2 m := hm.2.2.2.2.2.2.2.2.2.2.1
  have hck1 : KnownB true true (g.rst r).ck1 := by
    rw [hrck]; unfold rCk1
    exact ⟨by simp [KnownB], (KnownB_Dh true true _ _).2 (Or.inl rfl)⟩
  obtain ⟨a, b, c, d⟩ := keysB_known _ _ _ (g.rst r).thf hck1
  rw [hds, hdr, hdres, hdcid]; exact ⟨b, a, c, d⟩

/-! ## Resumption runs no ML-KEM -/

/-- With X25519 broken, a resumed initiator's keys are known exactly when the pre-shared key it descends from is: the
key whose binder is in its final transcript. -/
theorem resumed_init_as_psk {bk : Bool} {K C : Nat} {g : G} (h : ReachK (KnownB true bk) K C g) (i : Nat × Nat)
    (hd : (g.ist i).ph = .done) (hr : (g.ist i).resumed = true) :
    ∃ p thh rsc e, (g.ist i).thf = thR thh (binder p thh) rsc e (g.ist i).pcr ∧
      (KnownB true bk (g.ist i).send ↔ KnownB true bk p) ∧ (KnownB true bk (g.ist i).recv ↔ KnownB true bk p) ∧
      (KnownB true bk (g.ist i).res ↔ KnownB true bk p) ∧ (KnownB true bk (g.ist i).cid ↔ KnownB true bk p) := by
  have h3 := Inv3_reach h
  obtain ⟨x, ckp, thh, b, rsc, e, ⟨p, hckp, -, hb, -⟩, hf, -, hs, hrv, hrs, hcid⟩ := (h3.ic i).resDone hd hr
  have hdh : KnownB true bk (Dh x (atomOf e)) := (KnownB_Dh true bk _ _).2 (Or.inl rfl)
  refine ⟨p, thh, rsc, e, by rw [hf, hb], ?_, ?_, ?_, ?_⟩ <;>
    first | rw [hs] | rw [hrv] | rw [hrs] | rw [hcid]
  all_goals simp only [KnownB, hckp]; exact ⟨fun h' => h'.1, fun h' => ⟨h', hdh⟩⟩

/-- With X25519 broken, a resumed responder's keys are known exactly when the pre-shared key of the ticket it accepted
is. -/
theorem resumed_resp_as_psk {bk : Bool} {K C : Nat} {g : G} (h : ReachK (KnownB true bk) K C g) (r : Nat × Nat)
    (hd : (g.rst r).ph = .resumed ∨ ((g.rst r).ph = .done ∧ (g.rst r).resumed = true)) :
    (KnownB true bk (g.rst r).send ↔ KnownB true bk (g.rst r).tpsk) ∧
    (KnownB true bk (g.rst r).recv ↔ KnownB true bk (g.rst r).tpsk) ∧
    (KnownB true bk (g.rst r).res ↔ KnownB true bk (g.rst r).tpsk) ∧
    (KnownB true bk (g.rst r).cid ↔ KnownB true bk (g.rst r).tpsk) := by
  have h3 := Inv3_reach h
  obtain ⟨p, e, -, -, -, hs, hrv, hrs, hcid, -, htp, -⟩ := (h3.rc r).res hd
  have hdh : KnownB true bk (Dh (ry r.1 r.2) (atomOf e)) := (KnownB_Dh true bk _ _).2 (Or.inl rfl)
  rw [hs, hrv, hrs, hcid, htp]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [KnownB] <;> exact ⟨fun h' => h'.1, fun h' => ⟨h', hdh⟩⟩

#audit_axioms Vinc.Hs.secrecy_xbroken
#audit_axioms Vinc.Hs.secrecy_kbroken
#audit_axioms Vinc.Hs.secrecy_init_kem
#audit_axioms Vinc.Hs.secrecy_resp_dh
#audit_axioms Vinc.Hs.bothbroken_init_known
#audit_axioms Vinc.Hs.bothbroken_resp_known
#audit_axioms Vinc.Hs.resumed_init_as_psk
#audit_axioms Vinc.Hs.resumed_resp_as_psk
#audit_axioms Vinc.Hs.KnownB_ff

end Vinc.Hs
