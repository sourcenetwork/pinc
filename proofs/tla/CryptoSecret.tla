----------------------------- MODULE CryptoSecret -----------------------------
(***************************************************************************)
(* The secrets of pinc-crypto (secret.rs): ct_eq and Secret equality, the  *)
(* Debug text and zeroization.                                             *)
(*                                                                         *)
(* ct_eq answers equality of contents; a difference in length returns      *)
(* early (the one thing it reveals). Secret equality is ct_eq on the       *)
(* bytes. Zeroize writes zeros over the same length; a dropped Secret is   *)
(* wiped (ZeroizeOnDrop). What the code can show about the buffers of the  *)
(* DRBG is CryptoDrbg.tla NoResidue; copies a dependency makes of a        *)
(* scalar passed by value are outside what this crate can wipe.            *)
(*                                                                         *)
(* Checked over every byte string of up to 3 bytes of a 2-letter alphabet: *)
(*   CtEqIff, CtEqLength, CtEqSymmetric, DebugHidesBytes, ZeroizeShape     *)
(* Lean counterpart: proofs/lean/Pinc/CryptoSecret.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

CtEq(a, b) == a = b
Debug(s) == "Secret(..)"
Zeroize(b) == [i \in 1..Len(b) |-> 0]

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

Strs == UNION {[1..n -> {0, 1}] : n \in 0..3}

CtEqIff == \A a, b \in Strs : CtEq(a, b) <=> (Len(a) = Len(b) /\ \A i \in 1..Len(a) : a[i] = b[i])
CtEqLength == \A a, b \in Strs : Len(a) # Len(b) => ~CtEq(a, b)
CtEqSymmetric == \A a, b \in Strs : CtEq(a, b) = CtEq(b, a)
DebugHidesBytes == \A a, b \in Strs : Debug(a) = Debug(b)
ZeroizeShape == \A a \in Strs : Len(Zeroize(a)) = Len(a) /\ \A i \in 1..Len(a) : Zeroize(a)[i] = 0
=============================================================================
