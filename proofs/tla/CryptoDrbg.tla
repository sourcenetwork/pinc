------------------------------ MODULE CryptoDrbg ------------------------------
(***************************************************************************)
(* The DRBG of pinc-crypto (drbg.rs): ChaCha20 with fast key erasure,      *)
(* and the zeroization of its buffers, step for step.                      *)
(*                                                                         *)
(* A key is a pair [b, m]: a base (the seed, or the stream of the key      *)
(* before it: a fresh term after every fill) and the set m of entropy      *)
(* atoms XORed into it since (reseeding twice with the same atom cancels,  *)
(* a zero entropy "Z" changes nothing). The stream of a key is abstract    *)
(* and perfect: a fill of n bytes reads the first 32 + n bytes of the      *)
(* stream; the first 32 are the next key, a fresh base, the rest the       *)
(* output, so the output is the term <<key, n>>. Host entropy is an atom   *)
(* chosen independently of the state (the assumption of reseed).           *)
(*                                                                         *)
(* A fill or reseed is a sequence of steps that touches the named          *)
(* buffers of the code: the cipher state (a copy of the key), the local    *)
(* next, the key field and the caller's output. residue is the set of      *)
(* buffers other than the key and the output that hold secret bytes.       *)
(*                                                                         *)
(* Checked over every sequence of 4 operations (fills of 0, 1, MAX_FILL    *)
(* and MAX_FILL + 1 bytes, reseeds with Z, E1 and E2):                     *)
(*   NeverReuse       the key a fill reads was never read by an earlier    *)
(*                    fill, so no (key, nonce) pair and no output byte     *)
(*                    repeats, also across reseeds                         *)
(*   OutputsDisjoint  two outputs come from different keys                 *)
(*   RefuseKeeps      a request over MAX_FILL leaves the state as it was   *)
(*   StreamHolds      every accepted request fits the 2^32 - 1 blocks the  *)
(*                    stream serves, so the error path (which wipes the    *)
(*                    output) is unreachable                               *)
(*   NoResidue        whenever no operation is in progress, no buffer but  *)
(*                    the key and the output holds secret bytes            *)
(*   ToggleLaws       reseed is an involution, commutative, Z is identity  *)
(* TraceCrypto.tla replays the recorded runs against Next. Lean            *)
(* counterpart: proofs/lean/Pinc/CryptoDrbg.lean (fill_too_long,           *)
(* fill_within_stream, same_key_same_output, reseed_involutive,            *)
(* reseed_nonzero_changes, fill_clean, reseed_clean).                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLES key, used, outs, pc, residue, steps
vars == <<key, used, outs, pc, residue, steps>>

U == INSTANCE U64

MaxFill == 2 ^ 30
Lens == {0, 1, MaxFill, MaxFill + 1}
Ents == {"Z", "E1", "E2"}
MaxSteps == 4

(* the stream serves 2^32 - 1 blocks of 64 bytes; a fill reads 32 + n bytes *)
StreamLimit == U!Shl(U!Sub(U!Pw(32), U!One), 6)
Fits(n) == U!Le(U!Add(U!W(32), U!W(n)), StreamLimit)

Toggle(m, e) == IF e = "Z" THEN m ELSE (m \ {e}) \cup ({e} \ m)

Init == /\ key = [b |-> <<"seed">>, m |-> {}]
        /\ used = {}
        /\ outs = <<>>
        /\ pc = <<"idle", 0>>
        /\ residue = {}
        /\ steps = 0

(* Drbg::fill *)
Refuse(n) == /\ pc[1] = "idle" /\ steps < MaxSteps /\ n > MaxFill
             /\ steps' = steps + 1 /\ UNCHANGED <<key, used, outs, pc, residue>>

FillBegin(n) == /\ pc[1] = "idle" /\ steps < MaxSteps /\ n <= MaxFill
                /\ pc' = <<"cipher", n>> /\ residue' = {"cipher"}        \* ChaCha20::new(key): the cipher holds a copy
                /\ UNCHANGED <<key, used, outs, steps>>

FillNext == /\ pc[1] = "cipher"
            /\ pc' = <<"next", pc[2]>> /\ residue' = {"cipher", "next"}   \* try_write_keystream(&mut next)
            /\ UNCHANGED <<key, used, outs, steps>>

FillOut == /\ pc[1] = "next"
           /\ Fits(pc[2])                                                 \* the writes cannot fail
           /\ pc' = <<"assign", pc[2]>>                                   \* try_write_keystream(out)
           /\ UNCHANGED <<key, used, outs, steps, residue>>

(* the failure of a write: unreachable because Fits holds for every accepted request *)
FillFail == /\ pc[1] = "next"
            /\ ~Fits(pc[2])
            /\ pc' = <<"wipe", pc[2]>> /\ UNCHANGED <<key, used, outs, steps, residue>>

FillAssign == /\ pc[1] = "assign"
              /\ used' = used \cup {key}
              /\ outs' = Append(outs, <<key, pc[2]>>)
              /\ key' = [b |-> <<"next", key>>, m |-> {}]                 \* self.key = Secret::new(next); the old key is dropped
              /\ pc' = <<"wipe", pc[2]>>
              /\ UNCHANGED <<steps, residue>>

FillWipe == /\ pc[1] = "wipe"
            /\ residue' = residue \ {"next"}                              \* next.zeroize()
            /\ pc' = <<"end", pc[2]>>
            /\ UNCHANGED <<key, used, outs, steps>>

FillEnd == /\ pc[1] = "end"
           /\ residue' = residue \ {"cipher"}                             \* the cipher is dropped
           /\ pc' = <<"idle", 0>> /\ steps' = steps + 1
           /\ UNCHANGED <<key, used, outs>>

(* Drbg::reseed *)
ReseedBegin(e) == /\ pc[1] = "idle" /\ steps < MaxSteps
                  /\ pc' = <<"rs", e>> /\ residue' = {"next"}             \* let mut next = *self.key.expose()
                  /\ UNCHANGED <<key, used, outs, steps>>

ReseedAssign == /\ pc[1] = "rs"
                /\ key' = [key EXCEPT !.m = Toggle(@, pc[2])]            \* the XOR, then self.key = Secret::new(next)
                /\ pc' = <<"rswipe", pc[2]>>
                /\ UNCHANGED <<used, outs, steps, residue>>

ReseedWipe == /\ pc[1] = "rswipe"
              /\ residue' = {} /\ pc' = <<"idle", 0>> /\ steps' = steps + 1      \* next.zeroize()
              /\ UNCHANGED <<key, used, outs>>

Next == \/ \E n \in Lens : Refuse(n) \/ FillBegin(n)
        \/ FillNext \/ FillOut \/ FillFail \/ FillAssign \/ FillWipe \/ FillEnd
        \/ \E e \in Ents : ReseedBegin(e)
        \/ ReseedAssign \/ ReseedWipe

Spec == Init /\ [][Next]_vars

NeverReuse == pc[1] = "cipher" => key \notin used
OutputsDisjoint == \A i, j \in 1..Len(outs) : i # j => outs[i][1] # outs[j][1]
StreamHolds == \A n \in Lens : n <= MaxFill => Fits(n)
NoResidue == pc[1] = "idle" => residue = {}
FailUnreachable == pc[1] = "wipe" => Fits(pc[2])

(* the refusal leaves everything: checked as a property of the step *)
RefuseKeeps == [][\A n \in Lens : Refuse(n) => UNCHANGED <<key, used, outs, pc, residue>>]_vars

Subsets == SUBSET {"E1", "E2"}
ToggleLaws ==
    /\ \A m \in Subsets : \A e \in Ents : Toggle(Toggle(m, e), e) = m
    /\ \A m \in Subsets : \A e, f \in Ents : Toggle(Toggle(m, e), f) = Toggle(Toggle(m, f), e)
    /\ \A m \in Subsets : Toggle(m, "Z") = m
    /\ \A m \in Subsets : \A e \in {"E1", "E2"} : Toggle(m, e) # m

(* 2^32 - 1 blocks: a request one byte over the bound is not within the stream either *)
LimitTight == Fits(MaxFill + 1) /\ ~U!Le(U!Add(U!W(32), U!Pw(38)), StreamLimit)
=============================================================================
