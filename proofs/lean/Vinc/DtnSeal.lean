import Vinc.DtnSealBytes

/-!
# One-shot encryption of a bundle: the symbolic model

`seal.rs` encrypts a bundle once to the recipient's static keys. This file is the symbolic (Dolev-Yao) model of
that exchange for unboundedly many bundles, senders and recipients; `proofs/tla/DtnSeal.tla` is its bounded
twin, and `Vinc.TraceDtnSeal` replays real runs of the code through the functions below.

Perfect cryptography is the stated hypothesis of this model and it is built into the term algebra: `T` is a free
inductive type, so two terms are equal iff their constructors and arguments are (collision resistance of the
transcript hash, proved at byte level in `Vinc.DtnSealBytes` as `thFields_inj` and `bundleId_inj`, and the
separation of the derivations). `Known a` is the attacker's deduction from the secrets of `Adv`:

* the X25519 shared value `ssX e kp` of an ephemeral public key and a static pair needs the static X25519 secret,
  or the ephemeral secret behind `e`, or a broken X25519 (`bX`);
* the ML-KEM shared value `ssK sm ek` needs the static decapsulation key, or the encapsulation message `sm`, or a
  broken ML-KEM (`bK`);
* the AEAD key `key ssK ssX th` is `expand(extract(ck0, ss_K || ss_X), th)`: it needs BOTH shared values, so one
  broken primitive is not enough;
* every public value (keys, ciphertext, transcript hash, bundle id, sealed slices) is known.

Nodes are naturals; secrets are named by the seed or key pair that holds them. The sender's per-bundle randomness
is a pair of seed ids `(se, sm)`; the recipient's static keys are a key pair id `kp`; node and epoch are bound by
the transcript, not by the keys. Nothing is declared beyond definitions and theorems.

## What is proved

* Secrecy (`known_key_iff`, `payload_secret`): the payload is unknown to the attacker unless it holds the sender,
  or both the X25519 side and the ML-KEM side of the key. Compromising other nodes' keys, other epochs' keys or
  other bundles' seeds changes nothing (`known_key_local`).
* No forward secrecy beyond static-key rotation (`no_forward_secrecy`, `late_reveal`): the recipient's static
  secrets of the key pair a bundle was sealed to reveal that bundle's payload whenever they leak, even long after.
  Only a rotation to NEW key pairs protects later bundles; the epoch label is bound into the key
  (`key_binding`) but an epoch bump without new keys protects nothing. This is a design limit, not a defect.
* Binding (`key_binding`, `decap_agree`, `decap_wrong_iff`, `forged_ct_other_key`): the key determines the
  ephemeral key, the static pair, the node, the epoch, the KEM ciphertext and the bundle id; a wrong recipient or
  epoch is refused exactly when `head.destination != own.node || head.epoch != own.epoch`; a forged KEM
  ciphertext gives another key, so the first slice fails to authenticate.
* Nonces (`openSlice_other_index`, `sealIdx_nodup`, `seal_nonces_distinct`, `keys_distinct_of_fresh`): each data
  index is sealed once per bundle, the nonce is injective in the index, two bundles with different seeds have
  different keys, so a (key, nonce) pair is never used twice.
* Authenticity (`head_authentic`, `root_binds_slices`, in `Vinc.DtnSealAuth`): a head that verifies under a source
  whose signing key has not leaked is a head that source signed, in every field, and the signed root binds every
  slice.
-/

namespace Vinc.DtnSeal

/-- Symbolic terms; a free algebra (perfect primitives). -/
inductive T where
  | epub (se : Nat)
  | xpub (kp : Nat)
  | ek (kp : Nat)
  | junk (n : Nat)
  | ct (sm : Nat) (e : T)
  | ssX (e : T) (kp : Nat)
  | ssK (sm : Nat) (e : T)
  | rej (kp : Nat) (c : T)
  | bid (src wall counter : Nat) (e : T)
  | th (e : T) (kp node epoch : Nat) (c i : T)
  | key (k x t : T)
  | sealed (k : T) (n : List Nat) (p : T)
  | pl (src se : Nat)
  deriving DecidableEq

open T

/-- What the attacker holds: the secrets it owns or was given, and the primitives it can break. -/
structure Adv where
  /-- Ephemeral X25519 seeds. -/
  eK : Nat → Prop
  /-- KEM encapsulation messages. -/
  mK : Nat → Prop
  /-- Static X25519 secrets, by key pair. -/
  xK : Nat → Prop
  /-- Static ML-KEM decapsulation keys, by key pair. -/
  kK : Nat → Prop
  /-- Senders whose state (and so payloads) the attacker holds. -/
  srcK : Nat → Prop
  /-- X25519 is broken. -/
  bX : Prop
  /-- ML-KEM is broken. -/
  bK : Prop

/-- The attacker can compute the ephemeral secret behind `e`. An unknown shape is attacker-made. -/
def ephK (a : Adv) : T → Prop
  | epub se => a.eK se
  | _ => True

/-- The attacker can decapsulate to `e`. An unknown shape is an attacker-made key. -/
def ekK (a : Adv) : T → Prop
  | ek kp => a.kK kp
  | _ => True

/-- The Dolev-Yao deduction of the attacker from its own secrets. -/
def Known (a : Adv) : T → Prop
  | ssX e kp => a.bX ∨ a.xK kp ∨ ephK a e
  | ssK sm e => a.bK ∨ a.mK sm ∨ ekK a e
  | rej kp _ => a.bK ∨ a.kK kp
  | key k x _ => Known a k ∧ Known a x
  | pl src _ => a.srcK src
  | _ => True

/-! ## The sender and the recipient -/

/-- One bundle sealed by an honest sender: its seeds, the recipient's key pair, node and epoch, and the creation
time. -/
structure Bun where
  src : Nat
  se : Nat
  sm : Nat
  kp : Nat
  dest : Nat
  epoch : Nat
  wall : Nat
  counter : Nat

def Bun.eph (b : Bun) : T := epub b.se
def Bun.ctT (b : Bun) : T := ct b.sm (ek b.kp)
def Bun.idT (b : Bun) : T := bid b.src b.wall b.counter b.eph
def Bun.thT (b : Bun) : T := th b.eph b.kp b.dest b.epoch b.ctT b.idT

/-- `encapsulate`: `key = expand(extract(ck0, ss_K || ss_X), th)`. -/
def Bun.key (b : Bun) : T := T.key (ssK b.sm (ek b.kp)) (ssX b.eph b.kp) b.thT

/-- The head fields the recipient reads: destination node, epoch, ephemeral key, KEM ciphertext, bundle id, and
whether the ephemeral key is a low-order point. -/
structure HeadT where
  dst : Nat
  epoch : Nat
  eph : T
  ct : T
  id : T
  lo : Bool

def Bun.head (b : Bun) : HeadT := ⟨b.dest, b.epoch, b.eph, b.ctT, b.idT, false⟩

/-- The recipient's own record: node, epoch and the key pair whose secrets it holds. -/
structure Own where
  node : Nat
  epoch : Nat
  kp : Nat

/-- ML-KEM decapsulation with implicit rejection: the genuine shared value for a ciphertext made to this key, the
rejection value (unrelated to the sender's) for anything else. -/
def decapK (kp : Nat) : T → T
  | ct sm e => if e = ek kp then ssK sm e else rej kp (ct sm e)
  | c => rej kp c

inductive Verdict where
  | wrong
  | crypto
  | ok (k : T)
  deriving DecidableEq

/-- `decapsulate`: the recipient and epoch check first, then the Diffie-Hellman value, then the key. -/
def decap (o : Own) (h : HeadT) : Verdict :=
  if h.dst ≠ o.node ∨ h.epoch ≠ o.epoch then .wrong
  else if h.lo then .crypto
  else .ok (T.key (decapK o.kp h.ct) (ssX h.eph o.kp) (th h.eph o.kp o.node o.epoch h.ct h.id))

def Bun.own (b : Bun) : Own := ⟨b.dest, b.epoch, b.kp⟩

/-- The recipient's key for a genuine head is the sender's key. -/
theorem decap_agree (b : Bun) : decap b.own b.head = .ok b.key := by
  simp [decap, Bun.own, Bun.head, Bun.key, Bun.thT, decapK, Bun.ctT]

/-- A head is refused as addressed elsewhere exactly when its destination or epoch is not the recipient's. -/
theorem decap_wrong_iff (o : Own) (h : HeadT) : decap o h = .wrong ↔ (h.dst ≠ o.node ∨ h.epoch ≠ o.epoch) := by
  unfold decap
  split <;> rename_i hc
  · simp [hc]
  · split <;> simp [hc]

/-- A wrong recipient and a wrong epoch both fail. -/
theorem decap_wrong_recipient (o : Own) (h : HeadT) (hn : h.dst ≠ o.node) : decap o h = .wrong :=
  (decap_wrong_iff o h).2 (Or.inl hn)

theorem decap_wrong_epoch (o : Own) (h : HeadT) (he : h.epoch ≠ o.epoch) : decap o h = .wrong :=
  (decap_wrong_iff o h).2 (Or.inr he)

/-! ## Secrecy -/

/-- The key of a bundle is known exactly when both of its halves are. -/
theorem known_key_iff (a : Adv) (b : Bun) :
    Known a b.key ↔ (a.bX ∨ a.xK b.kp ∨ a.eK b.se) ∧ (a.bK ∨ a.mK b.sm ∨ a.kK b.kp) := by
  simp only [Bun.key, Known, ephK, ekK, Bun.eph]
  exact And.comm

/-- The attacker learns a payload by holding its key or its sender. -/
def PayloadKnown (a : Adv) (b : Bun) : Prop := Known a b.key ∨ a.srcK b.src

/-- Secret to anyone but the recipient's static keys: if one half of the key (the X25519 side or the ML-KEM side)
is out of the attacker's reach, the payload is secret, whatever else it holds, unless it holds the sender. -/
theorem payload_secret (a : Adv) (b : Bun) (hs : ¬ a.srcK b.src)
    (hn : ¬ (a.bX ∨ a.xK b.kp ∨ a.eK b.se) ∨ ¬ (a.bK ∨ a.mK b.sm ∨ a.kK b.kp)) : ¬ PayloadKnown a b := by
  rintro (h | h)
  · rcases (known_key_iff a b).1 h with ⟨h1, h2⟩
    rcases hn with hn | hn <;> contradiction
  · exact hs h

/-- Neither static secret, nor a seed, nor a broken primitive on the X25519 side: the payload is secret. -/
theorem payload_secret_of_x (a : Adv) (b : Bun) (hx : ¬ a.bX) (hk : ¬ a.xK b.kp) (he : ¬ a.eK b.se)
    (hs : ¬ a.srcK b.src) : ¬ PayloadKnown a b :=
  payload_secret a b hs (Or.inl (fun h => h.elim hx (fun h => h.elim hk he)))

/-- The same for the ML-KEM side. -/
theorem payload_secret_of_k (a : Adv) (b : Bun) (hb : ¬ a.bK) (hk : ¬ a.kK b.kp) (hm : ¬ a.mK b.sm)
    (hs : ¬ a.srcK b.src) : ¬ PayloadKnown a b :=
  payload_secret a b hs (Or.inr (fun h => h.elim hb (fun h => h.elim hm hk)))

/-- Two attackers that hold the same secrets about this bundle (its seeds and its recipient's key pair) and break
the same primitives learn the same about its key: other nodes', other epochs' and other bundles' secrets, and the
ability to sign as another node, are irrelevant. -/
theorem known_key_local (a a' : Adv) (b : Bun) (h1 : a.bX ↔ a'.bX) (h2 : a.bK ↔ a'.bK) (h3 : a.xK b.kp ↔ a'.xK b.kp)
    (h4 : a.kK b.kp ↔ a'.kK b.kp) (h5 : a.eK b.se ↔ a'.eK b.se) (h6 : a.mK b.sm ↔ a'.mK b.sm) :
    Known a b.key ↔ Known a' b.key := by
  rw [known_key_iff, known_key_iff, h1, h2, h3, h4, h5, h6]

/-- No forward secrecy beyond key rotation: whenever the recipient's static secrets of the key pair a bundle was
sealed to leak, at any later time, its key and so its payload are known. -/
theorem no_forward_secrecy (a : Adv) (b : Bun) (hx : a.xK b.kp) (hk : a.kK b.kp) : Known a b.key :=
  (known_key_iff a b).2 ⟨Or.inr (Or.inl hx), Or.inr (Or.inr hk)⟩

theorem late_reveal (a : Adv) (b : Bun) (hx : a.xK b.kp) (hk : a.kK b.kp) : PayloadKnown a b :=
  Or.inl (no_forward_secrecy a b hx hk)

/-- A broken primitive alone reveals nothing: with only X25519 broken the ML-KEM side still protects the key. -/
theorem only_x_broken (a : Adv) (b : Bun) (hk : ¬ a.kK b.kp) (hm : ¬ a.mK b.sm) (hbk : ¬ a.bK) :
    ¬ Known a b.key := fun h => by
  rcases (known_key_iff a b).1 h with ⟨-, h2⟩
  exact h2.elim hbk (fun h => h.elim hm hk)

/-- ... and with only ML-KEM broken the X25519 side still protects it. -/
theorem only_k_broken (a : Adv) (b : Bun) (hx : ¬ a.xK b.kp) (he : ¬ a.eK b.se) (hbx : ¬ a.bX) :
    ¬ Known a b.key := fun h => by
  rcases (known_key_iff a b).1 h with ⟨h1, -⟩
  exact h1.elim hbx (fun h => h.elim hx he)

/-! ## Binding -/

/-- The key is injective in everything it is derived from: the sender seeds, the recipient's key pair, node and
epoch, the creation time and the sender: two bundles with equal keys are the same bundle. -/
theorem key_binding (b b' : Bun) (h : b.key = b'.key) : b = b' := by
  obtain ⟨src, se, sm, kp, dest, epoch, wall, counter⟩ := b
  obtain ⟨src', se', sm', kp', dest', epoch', wall', counter'⟩ := b'
  simp [Bun.key, Bun.thT, Bun.idT, Bun.ctT, Bun.eph] at h
  simp [h]

/-- Bundles sealed with different seeds have different keys (and so share no nonce space). -/
theorem keys_distinct_of_fresh (b b' : Bun) (h : b.se ≠ b'.se ∨ b.sm ≠ b'.sm) : b.key ≠ b'.key := by
  intro e
  have := key_binding b b' e
  subst this
  rcases h with h | h <;> exact h rfl

/-- Any key a recipient derives binds what it was derived from: node, epoch, key pair, ephemeral key, KEM
ciphertext and bundle id. -/
theorem decap_key_binding (o o' : Own) (h h' : HeadT) (k : T) (e1 : decap o h = .ok k) (e2 : decap o' h' = .ok k) :
    o.node = o'.node ∧ o.epoch = o'.epoch ∧ o.kp = o'.kp ∧ h.eph = h'.eph ∧ h.ct = h'.ct ∧ h.id = h'.id := by
  simp only [decap] at e1 e2
  split at e1 <;> try simp at e1
  split at e1 <;> try simp at e1
  split at e2 <;> try simp at e2
  split at e2 <;> try simp at e2
  rw [← e2] at e1
  simp only [T.key.injEq, T.th.injEq] at e1
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6⟩ := e1
  exact ⟨h3, h4, h2, h1, h5, h6⟩

/-- A recipient of a head whose KEM ciphertext was forged (any ciphertext but the sender's) derives another key
than the sender's: the first slice fails to authenticate. -/
theorem forged_ct_other_key (b : Bun) (c : T) (hc : c ≠ b.ctT) (k : T)
    (h : decap b.own { b.head with ct := c } = .ok k) : k ≠ b.key := by
  intro e
  simp only [decap, Bun.own, Bun.head] at h
  simp at h
  rw [← h] at e
  simp only [Bun.key, Bun.thT, T.key.injEq] at e
  obtain ⟨hk, -⟩ := e
  apply hc
  cases c with
  | ct sm e' =>
    simp only [decapK] at hk
    split at hk
    · rename_i he
      simp only [T.ssK.injEq] at hk
      obtain ⟨h1, -⟩ := hk
      subst h1
      simp [Bun.ctT, he]
    · simp at hk
  | _ => simp [decapK] at hk

theorem nodup_map_on {β : Type} {f : Nat → β} {l : List Nat} (h : l.Nodup) (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun hx hy hne he => hne (hf _ hx _ hy he)) h

/-! ## Sealed slices -/

/-- The AEAD output of a slice: key, nonce and plaintext (the nonce is the injective `nonce idx`). -/
def sealSlice (k : T) (idx : Nat) (p : T) : T := sealed k (nonce idx) p

/-- Opening succeeds exactly under the same key and the same nonce. -/
def openSlice (k : T) (idx : Nat) : T → Option T
  | sealed k' n p => if k' = k ∧ n = nonce idx then some p else none
  | _ => none

theorem openSlice_same (k : T) (idx : Nat) (p : T) : openSlice k idx (sealSlice k idx p) = some p := by
  simp [openSlice, sealSlice]

/-- A slice sealed at one index opens at no other (indices below `2^64`, the range of a slice index). -/
theorem openSlice_other_index (k : T) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (hne : i ≠ j) (p : T) :
    openSlice k j (sealSlice k i p) = none := by
  have := slice_binding [] i j hi hj hne
  show (if k = k ∧ nonce i = nonce j then some p else none) = none
  split
  · rename_i h
    exact absurd h.2 this.1
  · rfl

/-- A slice opens under no key but the one that sealed it. -/
theorem openSlice_other_key (k k' : T) (i : Nat) (hne : k ≠ k') (p : T) : openSlice k' i (sealSlice k i p) = none := by
  simp [openSlice, sealSlice, hne]

/-- The recipient of a genuine head opens every slice the sender sealed. -/
theorem genuine_opens (b : Bun) (i : Nat) (p : T) :
    ∃ k, decap b.own b.head = .ok k ∧ openSlice k i (sealSlice b.key i p) = some p :=
  ⟨b.key, decap_agree b, openSlice_same _ _ _⟩

/-- The data slice indices `seal_bundle` seals in block `b` (`bk` data symbols of a block of `k` data symbols). -/
def blockIdx (k bk b : Nat) : List Nat := (List.range bk).map (fun t => b * k + t)

/-- The indices `seal_bundle` seals over `nb` blocks, in order: block `b` seals `b * k + t` for `t < bk b`. -/
def sealIdx (k : Nat) (bk : Nat → Nat) : Nat → List Nat
  | 0 => []
  | nb + 1 => sealIdx k bk nb ++ blockIdx k (bk nb) nb

theorem sealIdx_lt (k : Nat) (bk : Nat → Nat) (hb : ∀ b, bk b ≤ k) :
    ∀ nb d, d ∈ sealIdx k bk nb → d < nb * k
  | 0, d, h => by simp [sealIdx] at h
  | nb + 1, d, h => by
    simp only [sealIdx, List.mem_append, blockIdx, List.mem_map, List.mem_range] at h
    rcases h with h | ⟨t, ht, rfl⟩
    · have := sealIdx_lt k bk hb nb d h
      rw [Nat.succ_mul]; omega
    · have := hb nb
      rw [Nat.succ_mul]; omega

/-- Each data slice index is sealed once per bundle. -/
theorem sealIdx_nodup (k : Nat) (bk : Nat → Nat) (hk : 0 < k) (hb : ∀ b, bk b ≤ k) :
    ∀ nb, (sealIdx k bk nb).Nodup
  | 0 => List.nodup_nil
  | nb + 1 => by
    simp only [sealIdx]
    rw [List.nodup_append]
    refine ⟨sealIdx_nodup k bk hk hb nb, ?_, ?_⟩
    · apply nodup_map_on List.nodup_range
      intro x _ y _ h
      omega
    · intro a ha b hb' hab
      have h1 := sealIdx_lt k bk hb nb a ha
      simp only [blockIdx, List.mem_map, List.mem_range] at hb'
      obtain ⟨t, -, rfl⟩ := hb'
      omega

/-- A key never seals two slices under one nonce: the nonces of the slices of one bundle are distinct, while the
indices stay below `2^64`. -/
theorem seal_nonces_distinct (k : Nat) (bk : Nat → Nat) (hk : 0 < k) (hb : ∀ b, bk b ≤ k) (nb : Nat)
    (hlim : nb * k ≤ 2 ^ 64) : ((sealIdx k bk nb).map nonce).Nodup := by
  apply nodup_map_on (f := nonce) (sealIdx_nodup k bk hk hb nb)
  intro x hx y hy h
  have := sealIdx_lt k bk hb nb x hx
  have := sealIdx_lt k bk hb nb y hy
  exact nonce_inj x y (by omega) (by omega) h

end Vinc.DtnSeal

#audit_axioms Vinc.DtnSeal.decap_agree
#audit_axioms Vinc.DtnSeal.decap_wrong_iff
#audit_axioms Vinc.DtnSeal.known_key_iff
#audit_axioms Vinc.DtnSeal.payload_secret
#audit_axioms Vinc.DtnSeal.known_key_local
#audit_axioms Vinc.DtnSeal.no_forward_secrecy
#audit_axioms Vinc.DtnSeal.only_x_broken
#audit_axioms Vinc.DtnSeal.only_k_broken
#audit_axioms Vinc.DtnSeal.key_binding
#audit_axioms Vinc.DtnSeal.keys_distinct_of_fresh
#audit_axioms Vinc.DtnSeal.decap_key_binding
#audit_axioms Vinc.DtnSeal.forged_ct_other_key
#audit_axioms Vinc.DtnSeal.openSlice_other_index
#audit_axioms Vinc.DtnSeal.seal_nonces_distinct
