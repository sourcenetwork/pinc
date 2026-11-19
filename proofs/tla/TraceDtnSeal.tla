----------------------------- MODULE TraceDtnSeal -----------------------------
(***************************************************************************)
(* Trace validation of the one-shot encryption: pinc-dtn seal.rs           *)
(* (encapsulate, decapsulate, the slice cipher), bundle.rs (seal_bundle)   *)
(* and head.rs (the signed head).                                          *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_seal.rs runs the real code: sealings to   *)
(* several recipients, epochs and key pairs (with repeated and half-       *)
(* repeated seeds), the decapsulation of every head under four recipient   *)
(* records and under heads changed in one field (a flipped ciphertext, a   *)
(* flipped ephemeral key or id, the all-zero ephemeral key, another        *)
(* destination or epoch, another bundle's ciphertext or ephemeral key),    *)
(* slices sealed under one cipher and opened under another at the same and *)
(* at other indices, multi-slice bundles whose equal plaintext slices must *)
(* seal to different symbols, and the bytes of a signed head flipped one   *)
(* at a time. Each event must be the step the operators of DtnSeal.tla     *)
(* compute: Decap for the verdict and the derived key, BKey for the        *)
(* sender's key, OpenSlice for a slice.                                    *)
(*                                                                         *)
(* A public value, a seed and an AEAD key are recorded as ids (one id per  *)
(* distinct byte string; ids are unique across kinds). The checker keeps   *)
(* one oracle, a bijection between ids and model terms: a sealing binds    *)
(* the ephemeral key, the ciphertext, the bundle id and the key probe to   *)
(* the terms of the model; an id first met in a decapsulation is a value   *)
(* the attacker made (a junk term), unless the code found the id to be the one derived from the head's source and creation time, in which case it is that derived term. Equal ids must be equal terms and      *)
(* equal terms equal ids, so the key a recipient derives equals the        *)
(* sender's exactly when the terms say so.                                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_seal.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, om
vars == <<i, om>>

DS == INSTANCE DtnSeal WITH Srcs <- {}, Nodes <- {}, Kps <- {}, Epochs <- {}, Walls <- {}, MaxB <- 0,
                            SeedReuse <- FALSE, LeakKinds <- {}, BX0 <- FALSE, BK0 <- FALSE, Pays <- {},
                            bundles <- <<>>, L <- {}

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_seal.ndjson")
Ev == Trace[i]

Bound(id) == \E p \in om : p[2] = id
TermOf(id) == IF Bound(id) THEN (CHOOSE p \in om : p[2] = id)[1] ELSE DS!Junk(id)
Consistent(t, id) == (\E p \in om : p[1] = t \/ p[2] = id) => <<t, id>> \in om

Init == i = 1 /\ om = {}

BeginEv == /\ Ev.e = "begin" /\ om' = {}

EncEv ==
    LET b == [src |-> Ev.src, se |-> Ev.se, sm |-> Ev.sm, kp |-> Ev.kp, dest |-> Ev.dest, epoch |-> Ev.ep,
              wall |-> Ev.wall, ctr |-> Ev.ctr, pay |-> 0]
        ts == <<<<DS!BEph(b), Ev.eph>>, <<DS!BCt(b), Ev.ct>>, <<DS!BId(b), Ev.id>>, <<DS!BKey(b), Ev.kid>>>>
    IN /\ Ev.e = "enc"
       /\ \A k \in 1..4 : Consistent(ts[k][1], ts[k][2])
       /\ om' = om \cup {ts[k] : k \in 1..4}

DecEv ==
    LET own == [node |-> Ev.node, epoch |-> Ev.ep, kp |-> Ev.kp]
        eph == TermOf(Ev.eph)
        ct == TermOf(Ev.ct)
        id == IF Ev.idok THEN DS!Bid(Ev.hsrc, Ev.hwall, Ev.hctr, eph) ELSE TermOf(Ev.id)
        h == [src |-> Ev.hsrc, wall |-> Ev.hwall, ctr |-> Ev.hctr, dst |-> Ev.dst, epoch |-> Ev.hep, eph |-> eph, ct |-> ct, id |-> id, lo |-> Ev.lo]
        v == DS!Decap(own, h)
        base == om \cup {<<eph, Ev.eph>>, <<ct, Ev.ct>>, <<id, Ev.id>>}
        ok == v.t = "ok"
    IN /\ Ev.e = "dec"
       /\ Consistent(eph, Ev.eph) /\ Consistent(ct, Ev.ct) /\ Consistent(id, Ev.id)
       /\ Ev.v = v.t
       /\ IF ok THEN /\ \A p \in base : (p[1] = v.k \/ p[2] = Ev.kid) => p = <<v.k, Ev.kid>>
                     /\ om' = base \cup {<<v.k, Ev.kid>>}
                ELSE Ev.kid = 0 /\ om' = base

Pt == <<"pl", 0, 0>>

OpenEv ==
    LET ka == TermOf(Ev.ka)
        kb == TermOf(Ev.kb)
        model == ~Ev.tamper /\ DS!OpenSlice(kb, Ev.j, DS!SealSlice(ka, Ev.i, Pt)).ok
    IN /\ Ev.e = "open"
       /\ Bound(Ev.ka) /\ Bound(Ev.kb)
       /\ Ev.ok = model
       /\ om' = om

Sum(s) == LET RECURSIVE S(_, _) S(n, a) == IF n = 0 THEN a ELSE S(n - 1, a + s[n]) IN S(Len(s), 0)

(* the data indices seal_bundle seals: block b seals b * k + t for t < block_k(b) *)
SealIdx(k, bk) == UNION {{b * k + t : t \in 0..(bk[b + 1] - 1)} : b \in 0..(Len(bk) - 1)}

NoncesEv ==
    /\ Ev.e = "nonces"
       \* the indices are pairwise different (so are the nonces, injective in the index), as many as data symbols
    /\ Cardinality(SealIdx(Ev.k, Ev.bk)) = Sum(Ev.bk)
    /\ Sum(Ev.bk) = Ev.data
    /\ \A b \in 1..Len(Ev.bk) : Ev.bk[b] <= Ev.k
    /\ Ev.k > 0
    /\ Ev.distinct
    /\ om' = om

Widths == <<<<"id", 32>>, <<"stag", 1>>, <<"src", 32>>, <<"dtag", 1>>, <<"dst", 32>>, <<"wall", 8>>, <<"ctr", 4>>,
            <<"life", 8>>, <<"copies", 2>>, <<"k", 1>>, <<"m", 1>>, <<"log", 1>>, <<"plen", 8>>, <<"root", 32>>,
            <<"epoch", 4>>, <<"eph", 32>>, <<"kct", 1088>>>>
Start(n) == LET RECURSIVE S(_, _) S(m, a) == IF m = 0 THEN a ELSE S(m - 1, a + Widths[m][2]) IN S(n - 1, 0)
HeadLen == Start(18)
FieldAt(pos) == (CHOOSE f \in 1..17 : Start(f) <= pos /\ pos < Start(f) + Widths[f][2])

GoodEv ==
    /\ Ev.e = "hgood"
    /\ HeadLen = Ev.len /\ Ev.ok
    /\ om' = om

FlipEv ==
    /\ Ev.e = "hflip"
    /\ Ev.pos < HeadLen
    /\ Widths[FieldAt(Ev.pos)][1] = Ev.f
    /\ Ev.rej
    /\ om' = om

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "ds"
    /\ \/ BeginEv \/ EncEv \/ DecEv \/ OpenEv \/ NoncesEv \/ GoodEv \/ FlipEv
    /\ i' = i + 1

Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of DtnSeal.tla
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
