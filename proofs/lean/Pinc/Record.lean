import Pinc.Axioms

/-!
# Packet keys: nonces, usage limits, the key roll and header-protection masks

A model of `pinc-security/src/record.rs`. A `PacketKey` is one key generation with its usage counters: `sealed`
(packets sealed under it, `u64` saturating), `failed` (packets that failed to open, `u64` saturating) and
`last_sealed` (the highest packet number it sealed), plus the limits. The AEAD itself is below the line.

* `sealK pn` is refused with `PacketNumber` for `pn > MAX_PACKET_NUMBER`, then with `NotIncreasing` unless `pn` is
  above `last_sealed`, then with `KeyRollRequired` for an AES-128-GCM key whose `sealed` reached its limit;
  otherwise `sealed` grows by a saturating 1 and `last_sealed := pn`. A refusal changes nothing.
* `openK` of a packet is refused with `PacketNumber`, then with `KeyRollRequired` for a ChaCha20-Poly1305 key whose
  `failed` reached its limit; otherwise a packet that fails authentication counts (saturating) and is refused with
  `Authentication`, and one that verifies changes no counter.
* `rolled dh` fails with `GenerationExhausted` exactly when the generation is `u32::MAX` (`checked_add`); otherwise
  the next generation has the secret `roll_secret(secret, dh)`, generation + 1 and fresh counters (`sealed`,
  `failed`, `last_sealed` reset). The header key belongs to generation 0 and is not rolled (`Key.hdr`).

The key derivation is the free term algebra `Sec` of the perfect-primitive model (as in the handshake model): the
secret of generation `g` is `roll (... (roll (base b) dh0) ...) dh_{g-1}`, two secrets are equal iff built the same
way, so a secret determines its depth, which is the generation (`Sec.depth`). The packet key and the IV are
functions of the secret that the theorems take as parameters, the key injective (the stated hypothesis about the
primitive `expand`, only a hypothesis), the IV 12 bytes long. The nonce is the IV with the packet number, big-endian,
XORed into its last 8 bytes; it is injective in `pn` below `2^64`.

`no_nonce_reuse` is unconditional: it holds for every sequence of seals (any packet number offered, refusals
included), failed or successful opens and rolls (any Diffie-Hellman value, refusals included). Nothing is assumed
about the caller: the strictly increasing numbers come from `sealK` itself and the distinct keys from `Sec`.
One modelling choice is stated here, not hidden: a roll replaces the key (the transport does `pk = pk.rolled(..)`);
`rolled` takes `&self`, so a caller could keep the old key and roll one key twice into two equal children, which
this model does not cover.

The header-protection arithmetic of `apply`, `protect` and `unprotect` is modelled on byte values (`Nat`): the mask
changes only the low 4 (long header) or 5 (short header) bits of the first byte, applying it twice is the identity,
the revealed packet-number length is 1 to 4, and `unprotect (protect x) = x`.
-/

namespace Pinc.Record

/-- `u64::MAX`. -/
def u64max : Nat := 2 ^ 64 - 1
/-- `u32::MAX`, the largest generation. -/
def u32max : Nat := 2 ^ 32 - 1
/-- `MAX_PACKET_NUMBER`. -/
def maxPn : Nat := 2 ^ 62 - 1
/-- `AES_GCM_PACKET_LIMIT`. -/
def aesLimit : Nat := 2 ^ 22
/-- `CHACHA_FAILURE_LIMIT`. -/
def chachaLimit : Nat := 2 ^ 36

/-- Saturating `u64` addition of one. -/
def inc (a : Nat) : Nat := min (a + 1) u64max

/-- The AEAD of a key. -/
inductive Aead where
  | chacha
  | aes
  deriving DecidableEq

/-- `Limits`. -/
structure Limits where
  aesGcmPackets : Nat
  chachaFailures : Nat

/-- The protocol's limits (`Limits::default`). -/
def Limits.default : Limits := ⟨aesLimit, chachaLimit⟩

/-- The `RecordError` variants that `seal`, `open` and `rolled` return here. -/
inductive Err where
  | packetNumber
  | notIncreasing
  | authentication
  | keyRollRequired
  | generationExhausted
  deriving DecidableEq

/-- Traffic secrets: the free algebra of `roll_secret`. `base b` is a secret out of the handshake (`b` names it),
`roll s dh` is `roll_secret(s, dh)` for the Diffie-Hellman value named `dh`. -/
inductive Sec where
  | base (b : Nat)
  | roll (s : Sec) (dh : Nat)
  deriving DecidableEq

/-- The number of rolls behind a secret. -/
def Sec.depth : Sec → Nat
  | .base _ => 0
  | .roll s _ => s.depth + 1

/-- The state of a `PacketKey` that the operations read and write. -/
structure Key where
  aead : Aead
  secret : Sec
  generation : Nat
  sealed : Nat
  failed : Nat
  last : Option Nat
  limits : Limits
  /-- The secret the header key derives from: generation 0, never rolled. -/
  hdr : Sec

/-- `PacketKey::from_secret`: generation 0, counters 0, nothing sealed. -/
def Key.fresh (a : Aead) (l : Limits) (b : Nat) : Key := ⟨a, .base b, 0, 0, 0, none, l, .base b⟩

/-- Whether `pn` is at or below the last sealed number (`last_sealed.is_some_and(|l| pn <= l)`). -/
def atOrBelow (last : Option Nat) (pn : Nat) : Bool :=
  match last with
  | some l => decide (pn ≤ l)
  | none => false

/-- `PacketKey::seal`: the new state and the outcome. A refusal returns the state unchanged. -/
def sealK (k : Key) (pn : Nat) : Key × Option Err :=
  if pn > maxPn then (k, some .packetNumber)
  else if atOrBelow k.last pn then (k, some .notIncreasing)
  else if k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets then (k, some .keyRollRequired)
  else ({ k with sealed := inc k.sealed, last := some pn }, none)

/-- `PacketKey::open`; `valid` says whether the tag verifies. -/
def openK (k : Key) (pn : Nat) (valid : Bool) : Key × Option Err :=
  if pn > maxPn then (k, some .packetNumber)
  else if k.aead = .chacha ∧ k.failed ≥ k.limits.chachaFailures then (k, some .keyRollRequired)
  else if valid then (k, none)
  else ({ k with failed := inc k.failed }, some .authentication)

/-- `PacketKey::open` of a packet that fails authentication. -/
def openFail (k : Key) (pn : Nat) : Key × Option Err := openK k pn false

/-- `PacketKey::rolled` with the Diffie-Hellman value named `dh`. -/
def rolled (k : Key) (dh : Nat) : Key × Option Err :=
  if k.generation + 1 > u32max then (k, some .generationExhausted)
  else ({ k with secret := .roll k.secret dh, generation := k.generation + 1, sealed := 0, failed := 0, last := none },
        none)

/-! ## Refusals and counters -/

theorem seal_packet_number (k : Key) (pn : Nat) (h : pn > maxPn) :
    sealK k pn = (k, some .packetNumber) := by simp [sealK, h]

/-- A number at or below the last sealed one is refused and nothing changes. -/
theorem seal_not_increasing (k : Key) (pn l : Nat) (hp : pn ≤ maxPn) (hl : k.last = some l) (h : pn ≤ l) :
    sealK k pn = (k, some .notIncreasing) := by
  have : ¬ pn > maxPn := by omega
  simp [sealK, this, atOrBelow, hl, h]

theorem openFail_packet_number (k : Key) (pn : Nat) (h : pn > maxPn) :
    openFail k pn = (k, some .packetNumber) := by simp [openFail, openK, h]

theorem seal_aes_limit (k : Key) (pn : Nat) (hp : pn ≤ maxPn) (hn : atOrBelow k.last pn = false)
    (ha : k.aead = .aes) (hl : k.sealed ≥ k.limits.aesGcmPackets) : sealK k pn = (k, some .keyRollRequired) := by
  have : ¬ pn > maxPn := by omega
  simp [sealK, this, hn, ha, hl]

theorem seal_ok (k : Key) (pn : Nat) (hp : pn ≤ maxPn) (hn : atOrBelow k.last pn = false)
    (hl : k.aead = .aes → k.sealed < k.limits.aesGcmPackets) :
    sealK k pn = ({ k with sealed := inc k.sealed, last := some pn }, none) := by
  have h1 : ¬ pn > maxPn := by omega
  have h2 : ¬ (k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets) := by
    intro ⟨a, b⟩; have := hl a; omega
  simp [sealK, h1, hn, h2]

/-- A successful seal raises `last_sealed` strictly: the new value is `pn`, above every earlier one. -/
theorem seal_last_increases (k : Key) (pn : Nat) (h : (sealK k pn).2 = none) :
    (sealK k pn).1.last = some pn ∧ ∀ l, k.last = some l → l < pn := by
  unfold sealK at h ⊢
  by_cases a1 : pn > maxPn
  · simp [a1] at h
  · by_cases a2 : atOrBelow k.last pn = true
    · simp [a1, a2] at h
    · have a2' : atOrBelow k.last pn = false := by simpa using a2
      by_cases a3 : k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets
      · simp [a1, a2', a3] at h
      · refine ⟨by simp [a1, a2', a3], fun l hl => ?_⟩
        simp [atOrBelow, hl] at a2'
        exact a2'

/-- A refused seal returns the key unchanged. -/
theorem seal_refusal_unchanged (k : Key) (pn : Nat) (e : Err) (h : (sealK k pn).2 = some e) :
    (sealK k pn).1 = k := by
  unfold sealK at h ⊢
  by_cases a1 : pn > maxPn
  · simp [a1]
  · by_cases a2 : atOrBelow k.last pn = true
    · simp [a1, a2]
    · by_cases a3 : k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets
      · simp [a1, a2, a3]
      · simp [a1, a2, a3] at h

theorem openFail_chacha_limit (k : Key) (pn : Nat) (hp : pn ≤ maxPn) (ha : k.aead = .chacha)
    (hl : k.failed ≥ k.limits.chachaFailures) : openFail k pn = (k, some .keyRollRequired) := by
  have : ¬ pn > maxPn := by omega
  simp [openFail, openK, this, ha, hl]

theorem openFail_counts (k : Key) (pn : Nat) (hp : pn ≤ maxPn)
    (hl : k.aead = .chacha → k.failed < k.limits.chachaFailures) :
    openFail k pn = ({ k with failed := inc k.failed }, some .authentication) := by
  have h1 : ¬ pn > maxPn := by omega
  have h2 : ¬ (k.aead = .chacha ∧ k.failed ≥ k.limits.chachaFailures) := by
    intro ⟨a, b⟩; have := hl a; omega
  simp [openFail, openK, h1, h2]

/-- A packet that verifies changes no counter. -/
theorem open_valid_unchanged (k : Key) (pn : Nat) (hp : pn ≤ maxPn)
    (hl : k.aead = .chacha → k.failed < k.limits.chachaFailures) : openK k pn true = (k, none) := by
  have h1 : ¬ pn > maxPn := by omega
  have h2 : ¬ (k.aead = .chacha ∧ k.failed ≥ k.limits.chachaFailures) := by
    intro ⟨a, b⟩; have := hl a; omega
  simp [openK, h1, h2]

/-- `rolled` fails exactly when `checked_add` overflows `u32`. -/
theorem rolled_exhausted_iff (k : Key) (dh : Nat) :
    rolled k dh = (k, some .generationExhausted) ↔ k.generation ≥ u32max := by
  unfold rolled
  by_cases h : k.generation + 1 > u32max
  · simp [h]; omega
  · simp only [h, ite_false]
    constructor
    · intro e
      have := congrArg (fun r => r.1.generation) e
      simp only [] at this; omega
    · intro e; omega

/-- With the generation within `u32`, it fails exactly at `u32::MAX`. -/
theorem rolled_exhausted_at_max (k : Key) (dh : Nat) (hk : k.generation ≤ u32max) :
    rolled k dh = (k, some .generationExhausted) ↔ k.generation = u32max := by
  rw [rolled_exhausted_iff]; omega

/-- Otherwise the next key has the secret `roll secret dh`, one more generation and zero counters (`sealed`,
`failed`, nothing sealed); the AEAD, the limits and the header key are the same. -/
theorem rolled_ok (k : Key) (dh : Nat) (h : k.generation < u32max) :
    rolled k dh = ({ k with secret := .roll k.secret dh, generation := k.generation + 1, sealed := 0, failed := 0,
                            last := none }, none) := by
  have : ¬ k.generation + 1 > u32max := by omega
  simp [rolled, this]

/-- The header key is not rolled. -/
theorem rolled_hdr (k : Key) (dh : Nat) : (rolled k dh).1.hdr = k.hdr := by
  unfold rolled; split <;> rfl

/-- A rolled key starts with zero counters and nothing sealed. -/
theorem rolled_fresh_counters (k : Key) (dh : Nat) (h : (rolled k dh).2 = none) :
    (rolled k dh).1.sealed = 0 ∧ (rolled k dh).1.failed = 0 ∧ (rolled k dh).1.last = none := by
  unfold rolled at h ⊢
  by_cases a : k.generation + 1 > u32max
  · simp [a] at h
  · simp [a]

/-- Two rolls of one secret with different Diffie-Hellman values give different secrets. -/
theorem roll_distinct (s : Sec) (d e : Nat) (h : d ≠ e) : Sec.roll s d ≠ Sec.roll s e := by
  intro c; injection c with _ c2; exact h c2

/-- A secret is never equal to a roll of itself or of anything built from it: the depth grows. -/
theorem roll_depth_ne (s t : Sec) (d : Nat) (h : t.depth ≤ s.depth) : t ≠ Sec.roll s d := by
  intro c; subst c; simp only [Sec.depth] at h; omega

/-! ## The nonce -/

/-- The 8 bytes of a packet number, big-endian (`pn.to_be_bytes()`), taken modulo `2^64`. -/
def be8 (pn : Nat) : List Nat :=
  [pn / 2 ^ 56 % 256, pn / 2 ^ 48 % 256, pn / 2 ^ 40 % 256, pn / 2 ^ 32 % 256,
   pn / 2 ^ 24 % 256, pn / 2 ^ 16 % 256, pn / 2 ^ 8 % 256, pn % 256]

theorem be8_injective (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : be8 a = be8 b) : a = b := by
  simp only [be8, List.cons.injEq, and_true] at h
  omega

theorem xor_cancel (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  have := congrArg (fun x => a ^^^ x) h
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  exact this

theorem xor_twice (a b : Nat) : a ^^^ b ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem zipWith_xor_cancel : ∀ (l a b : List Nat), a.length = l.length → b.length = l.length →
    List.zipWith (· ^^^ ·) l a = List.zipWith (· ^^^ ·) l b → a = b
  | [], [], [], _, _, _ => rfl
  | x :: l, y :: a, z :: b, ha, hb, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq] at h
    have := zipWith_xor_cancel l a b (by simpa using ha) (by simpa using hb) h.2
    rw [xor_cancel x y z h.1, this]
  | [], _ :: _, _, ha, _, _ => by simp at ha
  | _ :: _, [], _, ha, _, _ => by simp at ha
  | [], [], _ :: _, _, hb, _ => by simp at hb
  | _ :: _, _ :: _, [], _, hb, _ => by simp at hb

/-- `PacketKey::nonce`: the IV with the big-endian packet number XORed into its last 8 bytes. -/
def nonce (iv : List Nat) (pn : Nat) : List Nat :=
  iv.take 4 ++ List.zipWith (· ^^^ ·) (iv.drop 4) (be8 pn)

/-- For one IV the nonce is injective in the packet number (below `2^64`, which includes every packet number
the code accepts). -/
theorem nonce_injective (iv : List Nat) (hiv : iv.length = 12) (a b : Nat)
    (ha : a ≤ maxPn) (hb : b ≤ maxPn) (h : nonce iv a = nonce iv b) : a = b := by
  unfold nonce at h
  have h2 := List.append_cancel_left h
  have hl : (iv.drop 4).length = 8 := by simp [hiv]
  have := zipWith_xor_cancel _ _ _ (by simp [be8]; omega) (by simp [be8]; omega) h2
  apply be8_injective a b (by unfold maxPn at ha; omega) (by unfold maxPn at hb; omega) this

/-! ## Every reachable sequence of operations -/

/-- A key together with the (secret, packet number) of every successful seal. -/
structure Sys where
  key : Key
  log : List (Sec × Nat)

/-- Offer `pn` to `seal`: a success is logged, a refusal changes nothing. -/
def Sys.seal (s : Sys) (pn : Nat) : Sys :=
  match sealK s.key pn with
  | (k, none) => ⟨k, s.log ++ [(s.key.secret, pn)]⟩
  | (_, some _) => s

/-- Offer a packet to `open`; `valid` says whether its tag verifies. -/
def Sys.open_ (s : Sys) (pn : Nat) (valid : Bool) : Sys := ⟨(openK s.key pn valid).1, s.log⟩

/-- Roll with the Diffie-Hellman value named `dh`; the key is replaced (a refusal changes nothing). -/
def Sys.roll (s : Sys) (dh : Nat) : Sys := ⟨(rolled s.key dh).1, s.log⟩

/-- The states reachable by ANY sequence of operations: any packet number offered to `seal`, any packet offered to
`open`, any Diffie-Hellman value offered to `rolled`, in any order. -/
inductive Reach (a : Aead) (l : Limits) (b : Nat) : Sys → Prop where
  | init : Reach a l b ⟨Key.fresh a l b, []⟩
  | sealStep {s : Sys} (pn : Nat) : Reach a l b s → Reach a l b (s.seal pn)
  | openStep {s : Sys} (pn : Nat) (valid : Bool) : Reach a l b s → Reach a l b (s.open_ pn valid)
  | rollStep {s : Sys} (dh : Nat) : Reach a l b s → Reach a l b (s.roll dh)

/-- The invariant of every reachable state. -/
structure Inv (a : Aead) (l : Limits) (b : Nat) (s : Sys) : Prop where
  fixed : s.key.aead = a ∧ s.key.limits = l ∧ s.key.hdr = .base b
  gen : s.key.generation = s.key.secret.depth ∧ s.key.generation ≤ u32max
  pns : ∀ e ∈ s.log, e.2 ≤ maxPn ∧ e.1.depth ≤ s.key.generation
  lastEntries : ∀ e ∈ s.log, e.1 = s.key.secret → ∃ l, s.key.last = some l ∧ e.2 ≤ l
  nodup : s.log.Nodup
  aesB : a = .aes → s.key.sealed ≤ l.aesGcmPackets
  chachaB : a = .chacha → s.key.failed ≤ l.chachaFailures

theorem seal_ok_cases (k : Key) (pn : Nat) (h : (sealK k pn).2 = none) :
    pn ≤ maxPn ∧ atOrBelow k.last pn = false ∧ (k.aead = .aes → k.sealed < k.limits.aesGcmPackets) ∧
    (sealK k pn).1 = { k with sealed := inc k.sealed, last := some pn } := by
  unfold sealK at h ⊢
  by_cases a1 : pn > maxPn
  · simp [a1] at h
  · by_cases a2 : atOrBelow k.last pn = true
    · simp [a1, a2] at h
    · have a2' : atOrBelow k.last pn = false := by simpa using a2
      by_cases a3 : k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets
      · simp [a1, a2', a3] at h
      · refine ⟨by omega, a2', fun ha => ?_, by simp [a1, a2', a3]⟩
        by_cases c : k.sealed ≥ k.limits.aesGcmPackets
        · exact absurd ⟨ha, c⟩ a3
        · omega

theorem openK_fields (k : Key) (pn : Nat) (v : Bool) :
    (openK k pn v).1.generation = k.generation ∧ (openK k pn v).1.aead = k.aead ∧
    (openK k pn v).1.limits = k.limits ∧ (openK k pn v).1.sealed = k.sealed ∧
    (openK k pn v).1.secret = k.secret ∧ (openK k pn v).1.last = k.last ∧ (openK k pn v).1.hdr = k.hdr := by
  unfold openK
  split <;> try simp
  split <;> try simp
  split <;> simp

theorem openK_failed_le (k : Key) (pn : Nat) (v : Bool) (ha : k.aead = .chacha)
    (h : k.failed ≤ k.limits.chachaFailures) : (openK k pn v).1.failed ≤ k.limits.chachaFailures := by
  unfold openK
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · rename_i _ n _
        have : k.failed < k.limits.chachaFailures := by
          rcases Nat.lt_or_ge k.failed k.limits.chachaFailures with c | c
          · exact c
          · exact absurd ⟨ha, c⟩ n
        show inc k.failed ≤ _
        simp only [inc]; omega

/-- The invariant holds in every reachable state. -/
theorem reach_inv {a : Aead} {l : Limits} {b : Nat} {s : Sys} (h : Reach a l b s) : Inv a l b s := by
  induction h with
  | init =>
    refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, by simp [Key.fresh, u32max]⟩, by simp, by simp, List.nodup_nil, ?_, ?_⟩
    · intro _; simp [Key.fresh]
    · intro _; simp [Key.fresh]
  | @sealStep s pn _ ih =>
    unfold Sys.seal
    cases hs : sealK s.key pn with
    | mk k' r =>
      cases r with
      | some e => exact ih
      | none =>
        have hn : (sealK s.key pn).2 = none := by rw [hs]
        obtain ⟨hp, hd, hlt, hk⟩ := seal_ok_cases s.key pn hn
        rw [hs] at hk
        simp only at hk
        subst hk
        obtain ⟨⟨f1, f2, f3⟩, ⟨g1, g2⟩, p1, l1, n1, a1, c1⟩ := ih
        refine ⟨⟨f1, f2, f3⟩, ⟨g1, g2⟩, ?_, ?_, ?_, ?_, ?_⟩
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | he
          · exact p1 e he
          · subst he; exact ⟨hp, by simp [g1]⟩
        · intro e he hs'
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | he
          · obtain ⟨l0, hl0, hle⟩ := l1 e he hs'
            simp only [atOrBelow, hl0, decide_eq_false_iff_not] at hd
            exact ⟨pn, rfl, by omega⟩
          · subst he; exact ⟨pn, rfl, Nat.le_refl _⟩
        · rw [List.nodup_append]
          refine ⟨n1, by simp, ?_⟩
          intro x hx y hy hxy
          simp only [List.mem_singleton] at hy
          subst hy; subst hxy
          obtain ⟨l0, hl0, hle⟩ := l1 _ hx rfl
          simp only [atOrBelow, hl0, decide_eq_false_iff_not] at hd
          omega
        · intro ha
          have := hlt (by rw [f1]; exact ha)
          rw [f2] at this
          simp only [inc]; omega
        · intro ha; simpa using c1 ha
  | @openStep s pn v _ ih =>
    obtain ⟨⟨f1, f2, f3⟩, ⟨g1, g2⟩, p1, l1, n1, a1, c1⟩ := ih
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := openK_fields s.key pn v
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, n1, ?_, ?_⟩
    · show (openK s.key pn v).1.aead = a; rw [o2]; exact f1
    · show (openK s.key pn v).1.limits = l; rw [o3]; exact f2
    · show (openK s.key pn v).1.hdr = _; rw [o7]; exact f3
    · show (openK s.key pn v).1.generation = (openK s.key pn v).1.secret.depth; rw [o1, o5]; exact g1
    · show (openK s.key pn v).1.generation ≤ _; rw [o1]; exact g2
    · intro e he; show _ ∧ _ ≤ (openK s.key pn v).1.generation; rw [o1]; exact p1 e he
    · intro e he hs'
      change e.1 = (openK s.key pn v).1.secret at hs'
      show ∃ l0, (openK s.key pn v).1.last = some l0 ∧ _
      rw [o6]; rw [o5] at hs'; exact l1 e he hs'
    · intro ha; show (openK s.key pn v).1.sealed ≤ _; rw [o4]; exact a1 ha
    · intro ha
      have := openK_failed_le s.key pn v (by rw [f1]; exact ha) (by rw [f2]; exact c1 ha)
      show (openK s.key pn v).1.failed ≤ _
      rw [f2] at this; exact this
  | @rollStep s dh _ ih =>
    obtain ⟨⟨f1, f2, f3⟩, ⟨g1, g2⟩, p1, l1, n1, a1, c1⟩ := ih
    unfold Sys.roll rolled
    by_cases e : s.key.generation + 1 > u32max
    · simp only [e, ite_true]; exact ⟨⟨f1, f2, f3⟩, ⟨g1, g2⟩, p1, l1, n1, a1, c1⟩
    · simp only [e, ite_false]
      refine ⟨⟨f1, f2, f3⟩, ⟨?_, ?_⟩, ?_, ?_, n1, ?_, ?_⟩
      · simp [Sec.depth, g1]
      · show s.key.generation + 1 ≤ u32max; omega
      · intro x hx
        have := p1 x hx
        exact ⟨this.1, by show _ ≤ s.key.generation + 1; omega⟩
      · intro x hx hs'
        have := (p1 x hx).2
        rw [g1] at this
        have h2 := congrArg Sec.depth hs'
        simp [Sec.depth] at h2
        omega
      · intro ha; show 0 ≤ _; exact Nat.zero_le _
      · intro ha; show 0 ≤ _; exact Nat.zero_le _

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ l : List α, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, h, inj => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, nodup_map_on f l h.2 (fun a ha b hb => inj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    rintro ⟨y, hy, e⟩
    exact h.1 (by have := inj y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self) e; rw [this] at hy; exact hy)

/-- UNCONDITIONAL: over every reachable sequence of seals, opens and rolls, no (key, nonce) pair is used by two
seals. The only hypotheses are about the primitives: the packet key is an injective function of the secret
(`expand` is collision free) and the IV is 12 bytes. Nothing is assumed of the caller: the packet numbers offered to
`seal` need not increase, repeat or stay in range. -/
theorem no_nonce_reuse {K : Type} (keyOf : Sec → K) (iv : Sec → List Nat) (hk : ∀ s t, keyOf s = keyOf t → s = t)
    (hiv : ∀ s, (iv s).length = 12) {a : Aead} {l : Limits} {b : Nat} {s : Sys} (h : Reach a l b s) :
    (s.log.map fun e => (keyOf e.1, nonce (iv e.1) e.2)).Nodup := by
  obtain ⟨-, -, p1, -, n1, -, -⟩ := reach_inv h
  apply nodup_map_on _ _ n1
  intro x hx y hy hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨e1, e2⟩ := hxy
  have g := hk _ _ e1
  rw [g] at e2
  have := nonce_injective (iv y.1) (hiv _) x.2 y.2 (p1 x hx).1 (p1 y hy).1 e2
  exact Prod.ext g this

/-- An AES-128-GCM key never seals more than its limit, a ChaCha20-Poly1305 key never counts more failed opens
than its limit, the generation is the depth of the secret and stays within `u32`, and the header key is the
generation-0 secret: it is never rolled. -/
theorem counters_bounded {a : Aead} {l : Limits} {b : Nat} {s : Sys} (h : Reach a l b s) :
    s.key.generation = s.key.secret.depth ∧ s.key.generation ≤ u32max ∧ s.key.hdr = .base b ∧
    (a = .aes → s.key.sealed ≤ l.aesGcmPackets) ∧ (a = .chacha → s.key.failed ≤ l.chachaFailures) := by
  obtain ⟨⟨-, -, f3⟩, ⟨g1, g2⟩, -, -, -, a1, c1⟩ := reach_inv h
  exact ⟨g1, g2, f3, a1, c1⟩

/-! ## Header protection -/

/-- The bits of the first byte a mask covers: `first_byte_mask`. -/
def fbMask (long : Bool) : Nat := if long then 0x0f else 0x1f

/-- `apply`: XOR the mask into the first byte (under the first-byte mask) and the packet-number bytes. -/
def apply (mask : List Nat) (first : Nat) (pn : List Nat) (long : Bool) : Nat × List Nat :=
  match mask with
  | [] => (first, pn)
  | m0 :: rest => (first ^^^ (m0 &&& fbMask long), List.zipWith (· ^^^ ·) pn rest)

/-- Only the low 4 (long) or 5 (short) bits of the first byte change. -/
theorem apply_first_low (m0 : Nat) (rest : List Nat) (first : Nat) (pn : List Nat) (long : Bool) :
    ((apply (m0 :: rest) first pn long).1 ^^^ first) ≤ fbMask long := by
  simp only [apply]
  rw [Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  exact Nat.and_le_right

/-- Applying the same mask twice is the identity on the first byte and on the packet-number bytes. -/
theorem apply_involutive (mask : List Nat) (first : Nat) (pn : List Nat) (long : Bool)
    (hl : pn.length ≤ mask.tail.length) :
    (apply mask (apply mask first pn long).1 (apply mask first pn long).2 long) = (first, pn) := by
  cases mask with
  | nil => simp [apply]
  | cons m0 rest =>
    simp only [apply]
    refine Prod.ext ?_ ?_
    · simp only [xor_twice]
    · simp only
      induction pn generalizing rest with
      | nil => simp
      | cons x xs ih =>
        cases rest with
        | nil => simp at hl
        | cons r rs =>
          simp only [List.zipWith_cons_cons, xor_twice]
          have := ih rs (by simpa using hl)
          rw [this]

/-- `HeaderKey::protect`: refuses a packet-number field that is not 1 to 4 bytes. -/
def protect (mask : List Nat) (first : Nat) (pn : List Nat) (long : Bool) : Option (Nat × List Nat) :=
  if 1 ≤ pn.length ∧ pn.length ≤ 4 then some (apply mask first pn long) else none

/-- `HeaderKey::unprotect`: the unmasked first byte, the field and the length it reveals. -/
def unprotect (mask : List Nat) (first : Nat) (pn : List Nat) (long : Bool) : Option (Nat × List Nat × Nat) :=
  let unmasked := (apply mask first [] long).1
  let len := (unmasked &&& 3) + 1
  if len ≤ pn.length then
    let r := apply mask first (pn.take len) long
    some (r.1, r.2 ++ pn.drop len, len)
  else none

/-- The revealed length is 1 to 4. -/
theorem unprotect_len_range (mask : List Nat) (first : Nat) (pn : List Nat) (long : Bool) (r : Nat × List Nat × Nat)
    (h : unprotect mask first pn long = some r) : 1 ≤ r.2.2 ∧ r.2.2 ≤ 4 := by
  unfold unprotect at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    have : (apply mask first [] long).1 &&& 3 ≤ 3 := Nat.and_le_right
    simp only; omega
  · simp at h

/-- Protect then unprotect restores the header: the first byte, the packet-number field (followed by whatever
bytes come after it) and its length, when the caller wrote `len - 1` into the low two bits of the first byte. -/
theorem unprotect_protect (m0 : Nat) (rest : List Nat) (first : Nat) (pn tail : List Nat) (long : Bool)
    (hlen : 1 ≤ pn.length ∧ pn.length ≤ 4) (hrest : pn.length ≤ rest.length)
    (hbits : first &&& 3 = pn.length - 1) :
    ∃ f' p', protect (m0 :: rest) first pn long = some (f', p') ∧
      unprotect (m0 :: rest) f' (p' ++ tail) long = some (first, pn ++ tail, pn.length) := by
  have hprot : protect (m0 :: rest) first pn long =
      some (first ^^^ (m0 &&& fbMask long), List.zipWith (· ^^^ ·) pn rest) := by
    unfold protect
    simp [hlen.1, hlen.2, apply]
  refine ⟨_, _, hprot, ?_⟩
  have hun : (apply (m0 :: rest) (first ^^^ (m0 &&& fbMask long)) [] long).1 = first := by
    simp only [apply, xor_twice]
  have hlenp : (List.zipWith (· ^^^ ·) pn rest).length = pn.length := by
    simp; omega
  have e : pn.length - 1 + 1 = pn.length := by omega
  unfold unprotect
  dsimp only
  rw [hun, hbits, e]
  rw [if_pos (by simp [hlenp])]
  have t1 : (List.zipWith (· ^^^ ·) pn rest ++ tail).take pn.length = List.zipWith (· ^^^ ·) pn rest := by
    rw [List.take_append_of_le_length (by omega)]
    exact List.take_of_length_le (by omega)
  have t2 : (List.zipWith (· ^^^ ·) pn rest ++ tail).drop pn.length = tail := by
    rw [List.drop_append_of_le_length (by omega)]
    simp [List.drop_of_length_le, hlenp]
  rw [t1, t2]
  have inv := apply_involutive (m0 :: rest) first pn long (by simpa using hrest)
  simp only [apply] at inv ⊢
  simp only [Prod.mk.injEq] at inv ⊢
  rw [inv.1, inv.2]

#audit_axioms Pinc.Record.seal_packet_number
#audit_axioms Pinc.Record.seal_not_increasing
#audit_axioms Pinc.Record.seal_aes_limit
#audit_axioms Pinc.Record.seal_ok
#audit_axioms Pinc.Record.seal_last_increases
#audit_axioms Pinc.Record.seal_refusal_unchanged
#audit_axioms Pinc.Record.openFail_packet_number
#audit_axioms Pinc.Record.openFail_chacha_limit
#audit_axioms Pinc.Record.openFail_counts
#audit_axioms Pinc.Record.open_valid_unchanged
#audit_axioms Pinc.Record.rolled_exhausted_iff
#audit_axioms Pinc.Record.rolled_exhausted_at_max
#audit_axioms Pinc.Record.rolled_ok
#audit_axioms Pinc.Record.rolled_hdr
#audit_axioms Pinc.Record.rolled_fresh_counters
#audit_axioms Pinc.Record.roll_distinct
#audit_axioms Pinc.Record.be8_injective
#audit_axioms Pinc.Record.nonce_injective
#audit_axioms Pinc.Record.reach_inv
#audit_axioms Pinc.Record.no_nonce_reuse
#audit_axioms Pinc.Record.counters_bounded
#audit_axioms Pinc.Record.apply_first_low
#audit_axioms Pinc.Record.apply_involutive
#audit_axioms Pinc.Record.unprotect_len_range
#audit_axioms Pinc.Record.unprotect_protect

end Pinc.Record
