---------------------------- MODULE KeystoreRefresh ----------------------------
(***************************************************************************)
(* Where a software key store's random bytes come from and how fresh       *)
(* entropy reaches them: crates/pinc-keystore/src/software.rs (`Source`    *)
(* Os (std only) and Drbg, `Source::fill`, `SoftwareStore::new`,           *)
(* `from_entropy`, `reseed`, `KeyStore::random`, `seal`'s key, `refresh`)  *)
(* and the trait default of `refresh` (lib.rs: a no-op).                   *)
(*                                                                         *)
(* The generator is CryptoDrbg.tla's abstraction: a key is [b, m], a base  *)
(* term and the set of entropy atoms XORed in since (Toggle, reused from   *)
(* CryptoDrbg); a fill of n bytes outputs the term <<key, n>> and moves    *)
(* the key to the fresh base <<"next", key>>. `from_entropy(seed)` seeds   *)
(* the generator and fills the 32-byte sealing key first. A store on the   *)
(* operating system (STD only) gives a fresh atom per fill. The refused    *)
(* fill (over MAX_FILL) is CryptoDrbg's; 32-byte fills never refuse, so    *)
(* `seal_key` is never None here.                                          *)
(*                                                                         *)
(* Checked, from the docs of `from_entropy`, `reseed`, `refresh` (the      *)
(* store's and the trait's) and the module:                                *)
(*  - OsNeverAsked: a store on the operating system never calls `fresh`;   *)
(*  - RefreshRule: a refresh of a generator store calls `fresh` once and   *)
(*    mixes the bytes in exactly when it returned true; of an operating    *)
(*    system store it changes nothing;                                     *)
(*  - ReseedRule: `reseed` mixes the entropy into a generator store and an *)
(*    operating system store ignores it;                                   *)
(*  - SealFixed: the sealing key is set at creation and nothing changes it *)
(*    (a reseed does not);                                                 *)
(*  - SealNotOutput, NoRepeat: no output repeats an earlier one or the     *)
(*    sealing key;                                                         *)
(*  - SameSeed: the store is a function of its entropy and its calls (two  *)
(*    stores from the same entropy have the same sealing key; from         *)
(*    different entropy, different ones).                                  *)
(* KeystoreRefresh_mix is a witness: a generator store's key takes the     *)
(* entropy of a reseed or a refresh (NeverReseeded fails).                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS STD, MAXSTEPS
ASSUME STD \in BOOLEAN /\ MAXSTEPS \in Nat

D == INSTANCE CryptoDrbg WITH key <- [b |-> <<"seed">>, m |-> {}], used <- {}, outs <- <<>>, pc <- <<"idle", 0>>,
                              residue <- {}, steps <- 0

Seeds == {"S1", "S2"}
Ents == {"Z", "E1", "E2"}
\* what `fresh` does in a refresh: return false ("no"), or write the entropy and return true
Answers == {"no"} \cup Ents

SeedKey(seed) == [b |-> <<seed>>, m |-> {}]
\* the fill of `from_entropy`: the sealing key is the first 32 bytes of the seed's stream
SealOf(seed) == <<SeedKey(seed), 32>>
FirstKey(seed) == [b |-> <<"next", SeedKey(seed)>>, m |-> {}]
\* the k-th draw of the operating system, a fresh atom (a base of three elements, so TLC never compares its parts with
\* a generator's base of one or two)
OsAtom(k) == [b |-> <<"os", k, "atom">>, m |-> {}]

VARIABLES src, key, asked, outs, sealk, steps
vars == <<src, key, asked, outs, sealk, steps>>

Init == /\ \/ \E seed \in Seeds : src = "drbg" /\ key = FirstKey(seed) /\ sealk = SealOf(seed)
           \/ STD /\ src = "os" /\ key = OsAtom(0) /\ sealk = <<OsAtom(0), 32>>
        /\ asked = 0 /\ outs = <<>> /\ steps = 0

\* The calls as pure operators on a store [src, key, asked, outs] (TraceKeystoreRefresh applies them to the recorded
\* calls). KeyStore::random of 32 bytes (Source::fill); atom is the operating system's draw.
RandomOf(st, atom) ==
    IF st.src = "drbg"
    THEN [st EXCEPT !.outs = Append(@, <<st.key, 32>>), !.key = [b |-> <<"next", st.key>>, m |-> {}]]
    ELSE [st EXCEPT !.outs = Append(@, <<atom, 32>>)]
\* SoftwareStore::reseed(e)
ReseedOf(st, e) == IF st.src = "drbg" THEN [st EXCEPT !.key.m = D!Toggle(@, e)] ELSE st
\* KeyStore::refresh with a `fresh` that answers a: only a generator store calls it, once
RefreshOf(st, a) ==
    IF st.src = "drbg"
    THEN [st EXCEPT !.asked = @ + 1, !.key.m = IF a = "no" THEN @ ELSE D!Toggle(@, a)]
    ELSE st

St == [src |-> src, key |-> key, asked |-> asked, outs |-> outs]
Apply(r) == src' = r.src /\ key' = r.key /\ asked' = r.asked /\ outs' = r.outs /\ UNCHANGED sealk
Random == Apply(RandomOf(St, OsAtom(Len(outs) + 1)))
Reseed(e) == Apply(ReseedOf(St, e))
Refresh(a) == Apply(RefreshOf(St, a))

Next == /\ steps < MAXSTEPS /\ steps' = steps + 1
        /\ \/ Random
           \/ \E e \in Ents : Reseed(e)
           \/ \E a \in Answers : Refresh(a)
Spec == Init /\ [][Next]_vars

OsNeverAsked == src = "os" => asked = 0
RefreshRule == [][\A a \in Answers :
    (Refresh(a) /\ steps' = steps + 1) =>
        /\ asked' - asked = (IF src = "drbg" THEN 1 ELSE 0)
        /\ key'.m = (IF src = "drbg" /\ a # "no" THEN D!Toggle(key.m, a) ELSE key.m)
        /\ key'.b = key.b]_vars
ReseedRule == [][\A e \in Ents :
    (Reseed(e) /\ steps' = steps + 1) =>
        /\ key'.m = (IF src = "drbg" THEN D!Toggle(key.m, e) ELSE key.m)
        /\ key'.b = key.b /\ asked' = asked]_vars
SealFixed == [][sealk' = sealk]_vars
SealNotOutput == \A k \in 1..Len(outs) : outs[k] # sealk
NoRepeat == \A j, k \in 1..Len(outs) : j # k => outs[j] # outs[k]
SameSeed == \A s1, s2 \in Seeds : (SealOf(s1) = SealOf(s2)) = (s1 = s2)

\* witness: a generator store's key took entropy
NeverReseeded == src = "drbg" => key.m = {}
=============================================================================
