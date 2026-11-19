import Pinc.Axioms

/-!
# Packet numbers: truncation and expansion

A model of `pinc-transport` `packet/number.rs`, as `proofs/tla/PnOps.tla` has it, over unbounded `Nat`: a packet
number is 62 bits, truncated to the low 2 or 3 bytes for the wire and expanded to the candidate closest to the next
number expected. The theorems hold for every number, every width from 1 to 4 and every largest received:

- the expansion is congruent to the truncated number modulo the window of the width (`decode_mod`);
- it gives the packet number back whenever that number is within half a window of the next one expected
  (`decode_exact`), so with the 2-byte width a number is recovered while it is within 32,768 of the next expected;
- the encoding writes the low bytes big-endian, and expanding what it wrote gives the number back within the window
  (`encode_ok`, `encode_decode`);
- the errors are exact: a number above `2^62 - 1` is `PacketNumber` before the width is looked at; a width other
  than 2 or 3 is `PnLength` (`encode_err_number`, `encode_err_len`);
- the width is 3 exactly when the granted window is above 40 MB (`pnLenFor_wide`).

`Pinc.TracePn` replays the recorded calls of the real code through these functions.
-/

namespace Pinc.TransportPn

def u64max : Nat := 2 ^ 64 - 1
def maxPn : Nat := 2 ^ 62 - 1
def wideWindow : Nat := 40000000

def satAdd (a b : Nat) : Nat := min (a + b) u64max

/-- The next packet number expected: one above the largest received, or 0. -/
def expd (lg : Option Nat) : Nat := match lg with | some v => satAdd v 1 | none => 0

/-- The step of `decode_pn` from the candidate in the block of the next number expected: forward a window when it
lies at least half a window behind, back one when it lies more than half a window ahead. -/
def adjust (c e w h : Nat) : Nat :=
  if satAdd c h ≤ e ∧ c < 2 ^ 62 - w then c + w
  else if satAdd e h < c ∧ w ≤ c then c - w
  else c

/-- `decode_pn`: the truncated number, its byte width and the largest received. -/
def decodePn (t len : Nat) (lg : Option Nat) : Nat :=
  let l := max 1 (min len 4)
  let e := expd lg
  let w := 256 ^ l
  adjust ((e - e % w) + t % w) e w (w / 2)

/-- `encode_pn`: the error, or the three bytes. -/
def encodePn (full len : Nat) : Except String (List Nat) :=
  if maxPn < full then .error "PacketNumber"
  else if len < 2 ∨ 3 < len then .error "PnLength"
  else .ok ((List.range 3).map (fun i => if i < len then (full / 256 ^ (len - 1 - i)) % 256 else 0))

def pnLenFor (w : Nat) : Nat := if wideWindow < w then 3 else 2

theorem adjust_mod (c e w h t : Nat) (hw : 0 < w) (hc : c % w = t % w) : adjust c e w h % w = t % w := by
  unfold adjust
  split
  · rw [Nat.add_mod_right]; exact hc
  · split
    · rename_i _ h2
      have h3 : c = (c - w) + w := by omega
      have h4 : (c - w) % w = c % w := by
        conv => rhs; rw [h3, Nat.add_mod_right]
      rw [h4]; exact hc
    · exact hc

theorem decode_mod (t len : Nat) (lg : Option Nat) :
    decodePn t len lg % 256 ^ (max 1 (min len 4)) = t % 256 ^ (max 1 (min len 4)) := by
  unfold decodePn
  generalize hl : max 1 (min len 4) = l
  have hw : 0 < 256 ^ l := by
    apply Nat.pos_of_ne_zero; intro h; simp at h
  generalize expd lg = e
  simp only []
  apply adjust_mod _ _ _ _ _ hw
  have : e - e % 256 ^ l = 256 ^ l * (e / 256 ^ l) := by
    have := Nat.div_add_mod e (256 ^ l)
    omega
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- The expansion gives `n` back whenever `n` is within half a window of the next number expected. -/
theorem decode_exact (n len : Nat) (lg : Option Nat) (hn : n < 2 ^ 62) (h1 : 1 ≤ len) (h4 : len ≤ 4)
    (hw1 : expd lg < n + 256 ^ len / 2) (hw2 : n ≤ expd lg + 256 ^ len / 2) :
    decodePn (n % 256 ^ len) len lg = n := by
  unfold decodePn
  have hl : max 1 (min len 4) = len := by omega
  rw [hl]
  generalize expd lg = e at hw1 hw2 ⊢
  unfold adjust satAdd u64max at *
  have hcase : len = 1 ∨ len = 2 ∨ len = 3 ∨ len = 4 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    (simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceSub] at *; split <;> (try split) <;> omega)

theorem encode_err_number (full len : Nat) (h : maxPn < full) : encodePn full len = .error "PacketNumber" := by
  unfold encodePn; simp [h]

theorem encode_err_len (full len : Nat) (h : full ≤ maxPn) (hl : len < 2 ∨ 3 < len) : encodePn full len = .error "PnLength" := by
  unfold encodePn
  have : ¬ maxPn < full := by omega
  simp [this, hl]

/-- The bytes written are the low `len` bytes of the number, big-endian, and 0 after. -/
theorem encode_ok (full len : Nat) (h : full ≤ maxPn) (hl : 2 ≤ len ∧ len ≤ 3) :
    ∃ b0 b1 b2, encodePn full len = .ok [b0, b1, b2] ∧
      (len = 2 → b0 * 256 + b1 = full % 65536 ∧ b2 = 0) ∧
      (len = 3 → (b0 * 256 + b1) * 256 + b2 = full % 16777216) := by
  unfold encodePn
  have : ¬ maxPn < full := by omega
  have hl' : ¬ (len < 2 ∨ 3 < len) := by omega
  simp only [this, hl', if_false]
  rcases (by omega : len = 2 ∨ len = 3) with rfl | rfl
  · refine ⟨full / 256 % 256, full % 256, 0, ?_, fun _ => ⟨?_, rfl⟩, fun h => by omega⟩
    · simp [List.range, List.range.loop]
    · omega
  · refine ⟨full / 65536 % 256, full / 256 % 256, full % 256, ?_, fun h => by omega, fun _ => ?_⟩
    · simp [List.range, List.range.loop]
    · omega

theorem encode_decode (n : Nat) (lg : Option Nat) (hn : n ≤ maxPn) (len : Nat) (hl : 2 ≤ len ∧ len ≤ 3)
    (hw1 : expd lg < n + 256 ^ len / 2) (hw2 : n ≤ expd lg + 256 ^ len / 2) :
    ∃ b0 b1 b2, encodePn n len = .ok [b0, b1, b2] ∧
      decodePn (if len = 2 then b0 * 256 + b1 else (b0 * 256 + b1) * 256 + b2) len lg = n := by
  obtain ⟨b0, b1, b2, he, h2, h3⟩ := encode_ok n len hn hl
  refine ⟨b0, b1, b2, he, ?_⟩
  have hn' : n < 2 ^ 62 := by unfold maxPn at hn; omega
  rcases (by omega : len = 2 ∨ len = 3) with rfl | rfl
  · obtain ⟨h2a, _⟩ := h2 rfl
    have hx := decode_exact n 2 lg hn' (by omega) (by omega) hw1 hw2
    have e2 : (256 : Nat) ^ 2 = 65536 := by decide
    rw [e2] at hx
    have hv : (if (2 : Nat) = 2 then b0 * 256 + b1 else (b0 * 256 + b1) * 256 + b2) = n % 65536 := by simp [h2a]
    rw [hv]; exact hx
  · have h3a := h3 rfl
    have hx := decode_exact n 3 lg hn' (by omega) (by omega) hw1 hw2
    have e3 : (256 : Nat) ^ 3 = 16777216 := by decide
    rw [e3] at hx
    have hv : (if (3 : Nat) = 2 then b0 * 256 + b1 else (b0 * 256 + b1) * 256 + b2) = n % 16777216 := by simp [h3a]
    rw [hv]; exact hx

theorem pnLenFor_wide (w : Nat) : pnLenFor w = 3 ↔ wideWindow < w := by
  unfold pnLenFor
  split <;> simp_all

end Pinc.TransportPn
