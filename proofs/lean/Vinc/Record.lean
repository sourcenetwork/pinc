import Vinc.Axioms

/-!
# Packet keys: nonces, usage limits, generations and header-protection masks

A model of `vinc-security/src/record.rs`. A `PacketKey` is a key generation with two counters: `sealed` (packets
sealed under it, `u64` saturating) and `failed` (packets that failed to open, `u64` saturating), plus the limits.
The model keeps exactly that state; the AEAD itself is below the line.

* `seal pn` is refused with `PacketNumber` for `pn > MAX_PACKET_NUMBER`, then with `KeyUpdateRequired` for an
  AES-128-GCM key whose `sealed` reached its limit; otherwise `sealed` grows by a saturating 1.
* `open` of a packet that fails authentication is refused the same two ways (limit on a ChaCha20-Poly1305 key);
  otherwise `failed` grows by a saturating 1. A successful open changes no counter and is not modelled.
* `next_generation` fails with `GenerationExhausted` exactly when the generation is `u32::MAX` (`checked_add`);
  otherwise it increments the generation and starts both counters at 0.

What the caller must do, and what is assumed of the derivation. `seal` does not reject a repeated packet number:
nonce uniqueness holds for a caller that seals with strictly increasing packet numbers across generations (`Reach`
only extends a state by `seal` with `pn >= nxt`, then sets `nxt := pn + 1`). Distinct generations have distinct
keys (`keyOf` injective): the hypothesis stated about the key derivation, a dependency assumption. The nonce is the
IV with the packet number, big-endian, XORed into its last 8 bytes; it is injective in `pn` below `2^64`.

The header-protection arithmetic of `apply`, `protect` and `unprotect` is modelled on byte values (`Nat`): the mask
changes only the low 4 (long header) or 5 (short header) bits of the first byte, applying it twice is the identity,
the revealed packet-number length is 1 to 4, and `unprotect (protect x) = x`.
-/

namespace Vinc.Record

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

/-- The `RecordError` variants that `seal`, `open` and `next_generation` return here. -/
inductive Err where
  | packetNumber
  | authentication
  | keyUpdateRequired
  | generationExhausted
  deriving DecidableEq

/-- The state of a `PacketKey` that the operations read and write. -/
structure Key where
  aead : Aead
  generation : Nat
  sealed : Nat
  failed : Nat
  limits : Limits

/-- `PacketKey::from_secret`: generation 0, both counters 0. -/
def Key.fresh (a : Aead) (l : Limits) : Key := ⟨a, 0, 0, 0, l⟩

/-- `PacketKey::seal`: the new state and the outcome. A refusal returns the state unchanged. -/
def sealK (k : Key) (pn : Nat) : Key × Option Err :=
  if pn > maxPn then (k, some .packetNumber)
  else if k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets then (k, some .keyUpdateRequired)
  else ({ k with sealed := inc k.sealed }, none)

/-- `PacketKey::open` of a packet that fails authentication. -/
def openFail (k : Key) (pn : Nat) : Key × Option Err :=
  if pn > maxPn then (k, some .packetNumber)
  else if k.aead = .chacha ∧ k.failed ≥ k.limits.chachaFailures then (k, some .keyUpdateRequired)
  else ({ k with failed := inc k.failed }, some .authentication)

/-- `PacketKey::next_generation`. -/
def next (k : Key) : Key × Option Err :=
  if k.generation + 1 > u32max then (k, some .generationExhausted)
  else ({ k with generation := k.generation + 1, sealed := 0, failed := 0 }, none)

/-! ## Refusals and counters -/

theorem seal_packet_number (k : Key) (pn : Nat) (h : pn > maxPn) :
    sealK k pn = (k, some .packetNumber) := by simp [sealK, h]

theorem openFail_packet_number (k : Key) (pn : Nat) (h : pn > maxPn) :
    openFail k pn = (k, some .packetNumber) := by simp [openFail, h]

theorem seal_aes_limit (k : Key) (pn : Nat) (hp : pn ≤ maxPn) (ha : k.aead = .aes)
    (hl : k.sealed ≥ k.limits.aesGcmPackets) : sealK k pn = (k, some .keyUpdateRequired) := by
  have : ¬ pn > maxPn := by omega
  simp [sealK, this, ha, hl]

theorem seal_ok (k : Key) (pn : Nat) (hp : pn ≤ maxPn)
    (hl : k.aead = .aes → k.sealed < k.limits.aesGcmPackets) :
    sealK k pn = ({ k with sealed := inc k.sealed }, none) := by
  have h1 : ¬ pn > maxPn := by omega
  have h2 : ¬ (k.aead = .aes ∧ k.sealed ≥ k.limits.aesGcmPackets) := by
    intro ⟨a, b⟩; have := hl a; omega
  simp [sealK, h1, h2]

theorem openFail_chacha_limit (k : Key) (pn : Nat) (hp : pn ≤ maxPn) (ha : k.aead = .chacha)
    (hl : k.failed ≥ k.limits.chachaFailures) : openFail k pn = (k, some .keyUpdateRequired) := by
  have : ¬ pn > maxPn := by omega
  simp [openFail, this, ha, hl]

theorem openFail_counts (k : Key) (pn : Nat) (hp : pn ≤ maxPn)
    (hl : k.aead = .chacha → k.failed < k.limits.chachaFailures) :
    openFail k pn = ({ k with failed := inc k.failed }, some .authentication) := by
  have h1 : ¬ pn > maxPn := by omega
  have h2 : ¬ (k.aead = .chacha ∧ k.failed ≥ k.limits.chachaFailures) := by
    intro ⟨a, b⟩; have := hl a; omega
  simp [openFail, h1, h2]

/-- `next_generation` fails exactly when `checked_add` overflows `u32`. -/
theorem next_exhausted_iff (k : Key) :
    next k = (k, some .generationExhausted) ↔ k.generation ≥ u32max := by
  unfold next
  by_cases h : k.generation + 1 > u32max
  · simp [h]; omega
  · simp only [h, ite_false]
    constructor
    · intro e
      have := congrArg (fun r => r.1.generation) e
      simp only [] at this; omega
    · intro e; omega

/-- With the generation within `u32`, it fails exactly at `u32::MAX`. -/
theorem next_exhausted_at_max (k : Key) (hk : k.generation ≤ u32max) :
    next k = (k, some .generationExhausted) ↔ k.generation = u32max := by
  rw [next_exhausted_iff]; omega

/-- Otherwise it increments the generation and restarts both counters, keeping the AEAD and the limits. -/
theorem next_ok (k : Key) (h : k.generation < u32max) :
    next k = ({ k with generation := k.generation + 1, sealed := 0, failed := 0 }, none) := by
  have : ¬ k.generation + 1 > u32max := by omega
  simp [next, this]

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

/-! ## Reachable sequences of operations -/

section
variable {K : Type} (keyOf : Nat → K) (iv : Nat → List Nat)

/-- A key together with what the caller did: the next packet number it may use, and the (generation, packet
number) of every successful seal. -/
structure Sys where
  key : Key
  nxt : Nat
  log : List (Nat × Nat)

/-- States reachable by a caller that seals with strictly increasing packet numbers across generations, fails
opens at will and updates keys. A refused operation changes nothing, so it adds no step. -/
inductive Reach (a : Aead) (l : Limits) : Sys → Prop where
  | init : Reach a l ⟨Key.fresh a l, 0, []⟩
  | sealStep {s : Sys} (pn : Nat) : Reach a l s → s.nxt ≤ pn → (sealK s.key pn).2 = none →
      Reach a l ⟨(sealK s.key pn).1, pn + 1, s.log ++ [(s.key.generation, pn)]⟩
  | openStep {s : Sys} (pn : Nat) : Reach a l s → Reach a l ⟨(openFail s.key pn).1, s.nxt, s.log⟩
  | nextStep {s : Sys} : Reach a l s → Reach a l ⟨(next s.key).1, s.nxt, s.log⟩

theorem seal_none_pn {k : Key} {pn : Nat} (h : (sealK k pn).2 = none) : pn ≤ maxPn := by
  unfold sealK at h
  by_cases h1 : pn > maxPn <;> simp [h1] at h
  omega

theorem openFail_fields (k : Key) (pn : Nat) :
    (openFail k pn).1.generation = k.generation ∧ (openFail k pn).1.aead = k.aead ∧
    (openFail k pn).1.limits = k.limits ∧ (openFail k pn).1.sealed = k.sealed := by
  unfold openFail
  split <;> try simp
  split <;> simp

theorem openFail_failed_le (k : Key) (pn : Nat) (ha : k.aead = .chacha) (h : k.failed ≤ k.limits.chachaFailures) :
    (openFail k pn).1.failed ≤ k.limits.chachaFailures := by
  unfold openFail
  split
  · exact h
  · split
    · exact h
    · rename_i n
      have : k.failed < k.limits.chachaFailures := by
        rcases Nat.lt_or_ge k.failed k.limits.chachaFailures with c | c
        · exact c
        · exact absurd ⟨ha, c⟩ n
      show inc k.failed ≤ _
      simp only [inc]; omega

/-- Every logged seal used a packet number below `nxt` and a generation reached so far. -/
theorem reach_inv {a : Aead} {l : Limits} {s : Sys} (h : Reach a l s) :
    (∀ e ∈ s.log, e.2 < s.nxt ∧ e.2 ≤ maxPn ∧ e.1 ≤ s.key.generation) ∧ s.log.Nodup ∧
    s.key.generation ≤ u32max ∧ s.key.aead = a ∧ s.key.limits = l ∧
    (a = .aes → s.key.sealed ≤ l.aesGcmPackets) ∧
    (a = .chacha → s.key.failed ≤ l.chachaFailures) := by
  induction h with
  | init => simp [Key.fresh, u32max]
  | @sealStep s pn _ hn hs ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    have hp := seal_none_pn hs
    have hk : (sealK s.key pn).1 = { s.key with sealed := inc s.key.sealed } := by
      unfold sealK at hs ⊢
      by_cases a1 : pn > maxPn
      · simp [a1] at hs
      · by_cases a2 : s.key.aead = .aes ∧ s.key.sealed ≥ s.key.limits.aesGcmPackets
        · simp [a1, a2] at hs
        · simp [a1, a2]
    have hlt : s.key.aead = .aes → s.key.sealed < s.key.limits.aesGcmPackets := by
      intro ha; unfold sealK at hs
      by_cases a1 : pn > maxPn
      · simp [a1] at hs
      · by_cases a2 : s.key.sealed ≥ s.key.limits.aesGcmPackets
        · simp [a1, ha, a2] at hs
        · omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [hk, List.mem_append, List.mem_singleton] at he ⊢
      rcases he with he | he
      · have := h1 e he; refine ⟨?_, this.2.1, this.2.2⟩; omega
      · subst he; exact ⟨by omega, hp, Nat.le_refl _⟩
    · simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil, List.nodup_nil, and_true, List.mem_singleton,
        not_false_eq_true, true_and, ne_eq]
      refine ⟨h2, ?_⟩
      intro x hx y hy hxy
      subst hy; have := (h1 x hx).1; subst hxy; simp at this; omega
    · simpa [hk] using h3
    · simpa [hk] using h4
    · simpa [hk] using h5
    · intro ha
      have := hlt (by rw [h4]; exact ha)
      simp only [hk, inc]; rw [h5] at this; omega
    · intro ha; simpa [hk] using h7 ha
  | @openStep s pn _ ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    have hf := openFail_fields s.key pn
    obtain ⟨g, ae, li, se⟩ := hf
    refine ⟨?_, h2, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he; have := h1 e he; rw [g]; exact this
    · rw [g]; exact h3
    · rw [ae]; exact h4
    · rw [li]; exact h5
    · intro ha; show (openFail s.key pn).1.sealed ≤ _; rw [se]; exact h6 ha
    · intro ha
      have := openFail_failed_le s.key pn (by rw [h4]; exact ha) (by rw [h5]; exact h7 ha)
      show (openFail s.key pn).1.failed ≤ _
      rw [h5] at this; exact this
  | @nextStep s _ ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    unfold next
    by_cases a1 : s.key.generation + 1 > u32max
    · simp only [a1, ite_true]; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · simp only [a1, ite_false]
      refine ⟨?_, h2, ?_, h4, h5, ?_, ?_⟩
      · intro e he; have := h1 e he; show _ ∧ _ ∧ e.1 ≤ s.key.generation + 1; omega
      · show s.key.generation + 1 ≤ u32max; omega
      · intro _; exact Nat.zero_le _
      · intro _; exact Nat.zero_le _

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ l : List α, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, h, inj => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, nodup_map_on f l h.2 (fun a ha b hb => inj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    rintro ⟨y, hy, e⟩
    exact h.1 (by have := inj y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self) e; rw [this] at hy; exact hy)

/-- No (key, nonce) pair is used by two seals, for a caller that numbers packets strictly increasingly, given that
distinct generations have distinct keys. -/
theorem no_nonce_reuse (keyOf : Nat → K) (iv : Nat → List Nat) (hk : ∀ g h, keyOf g = keyOf h → g = h)
    (hiv : ∀ g, (iv g).length = 12) {a : Aead} {l : Limits} {s : Sys} (h : Reach a l s) :
    (s.log.map fun e => (keyOf e.1, nonce (iv e.1) e.2)).Nodup := by
  obtain ⟨h1, h2, -⟩ := reach_inv h
  apply nodup_map_on _ _ h2
  intro x hx y hy hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨e1, e2⟩ := hxy
  have g := hk _ _ e1
  have hx' := h1 x hx
  have hy' := h1 y hy
  rw [g] at e2
  have := nonce_injective (iv y.1) (hiv _) x.2 y.2 hx'.2.1 hy'.2.1 e2
  exact Prod.ext g this
end

/-- An AES-128-GCM key never seals more than its limit, a ChaCha20-Poly1305 key never counts more failed opens
than its limit, and the generation stays within `u32`. -/
theorem counters_bounded {a : Aead} {l : Limits} {s : Sys} (h : Reach a l s) :
    s.key.generation ≤ u32max ∧ (a = .aes → s.key.sealed ≤ l.aesGcmPackets) ∧
    (a = .chacha → s.key.failed ≤ l.chachaFailures) := by
  obtain ⟨-, -, h3, -, -, h6, h7⟩ := reach_inv h
  exact ⟨h3, h6, h7⟩

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

#audit_axioms Vinc.Record.seal_packet_number
#audit_axioms Vinc.Record.openFail_packet_number
#audit_axioms Vinc.Record.seal_aes_limit
#audit_axioms Vinc.Record.seal_ok
#audit_axioms Vinc.Record.openFail_chacha_limit
#audit_axioms Vinc.Record.openFail_counts
#audit_axioms Vinc.Record.next_exhausted_iff
#audit_axioms Vinc.Record.next_exhausted_at_max
#audit_axioms Vinc.Record.next_ok
#audit_axioms Vinc.Record.be8_injective
#audit_axioms Vinc.Record.nonce_injective
#audit_axioms Vinc.Record.reach_inv
#audit_axioms Vinc.Record.no_nonce_reuse
#audit_axioms Vinc.Record.counters_bounded
#audit_axioms Vinc.Record.apply_first_low
#audit_axioms Vinc.Record.apply_involutive
#audit_axioms Vinc.Record.unprotect_len_range
#audit_axioms Vinc.Record.unprotect_protect

end Vinc.Record
