import Pinc.CryptoDrbg

/-!
# Secrets (`secret.rs`)

`ct_eq` compares two byte strings and answers equality of contents (a difference in length returns early, which is
the one thing it reveals); `Secret` equality is `ct_eq` on its bytes; `Debug` never prints the bytes; a `Secret` is
wiped when dropped (`ZeroizeOnDrop`) and `Zeroize` writes zeros over the same length.

What the code can show about zeroization, and what it cannot: every `Secret` field and every `Zeroizing` local of the
crate is wiped when it goes out of scope or is overwritten (the derive), and the named buffers of the DRBG are wiped on
every path (`Pinc.CryptoDrbg.fill_clean`, `fillErr_clean`, `reseed_clean`). A secret passed by value to a dependency
(the 32-byte scalar of an X25519 call) is copied into the callee's argument, which this crate cannot wipe, so the
statement is about the named buffers of this crate, not about every copy a compiler makes.
-/

namespace Pinc.CryptoSecret
open Pinc.CryptoKdf (Bytes)
open Pinc.CryptoDrbg

/-- `ct_eq`. -/
def ctEq (a b : Bytes) : Bool := decide (a = b)

theorem ctEq_iff (a b : Bytes) : ctEq a b = true ↔ a = b := by simp [ctEq]

/-- Strings of different lengths are never equal (the early return). -/
theorem ctEq_length_ne (a b : Bytes) (h : a.length ≠ b.length) : ctEq a b = false := by
  simp only [ctEq, decide_eq_false_iff_not]
  intro e
  exact h (by rw [e])

theorem ctEq_symm (a b : Bytes) : ctEq a b = ctEq b a := by simp [ctEq, eq_comm]

/-- The `Debug` text of a secret does not depend on its bytes. -/
def debug (_s : Bytes) : String := "Secret(..)"

theorem debug_independent (s t : Bytes) : debug s = debug t := rfl

/-- `Zeroize::zeroize`: zeros over the same length. -/
def zeroize (b : Bytes) : Bytes := List.replicate b.length 0

theorem zeroize_length (b : Bytes) : (zeroize b).length = b.length := by simp [zeroize]

theorem zeroize_zero (b : Bytes) : ∀ x ∈ zeroize b, x = 0 := fun _ h => List.eq_of_mem_replicate h

/-- Dropping a `ZeroizeOnDrop` value leaves nothing readable. -/
theorem drop_leaves_nothing (h : Heap) (c : String) : h.drop c c = none := by simp [Heap.drop]

end Pinc.CryptoSecret

#audit_axioms Pinc.CryptoSecret.ctEq_iff
#audit_axioms Pinc.CryptoSecret.ctEq_length_ne
#audit_axioms Pinc.CryptoSecret.zeroize_zero
#audit_axioms Pinc.CryptoSecret.drop_leaves_nothing
