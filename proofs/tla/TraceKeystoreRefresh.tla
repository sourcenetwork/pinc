------------------------- MODULE TraceKeystoreRefresh -------------------------
(***************************************************************************)
(* Trace validation of a software key store's sources, reseed and refresh: *)
(* crates/pinc-keystore/src/software.rs (`from_entropy`, `new`, `reseed`,  *)
(* `random`, `seal`, `unseal`, `refresh`), against the operators of        *)
(* KeystoreRefresh.tla (RandomOf, ReseedOf, RefreshOf, FirstKey, SealOf).  *)
(*                                                                         *)
(* The Rust test tests/trace_keystore_refresh.rs (std) runs stores from    *)
(* entropy S1 and S2 through every sequence of three calls among random    *)
(* 32, reseed Z, E1, E2 and refresh answering no, Z, E1, E2, then a final  *)
(* random, and stores on the operating system through the same calls. A    *)
(* "run" event has the calls, every output in hex and how often `fresh`    *)
(* was called. A "ref" event has the first two 32-byte fills of a          *)
(* reference `Drbg::new(seed)`: the first is the sealing key's draw, the   *)
(* second the store's first output. An "unseal" event says whether data    *)
(* one store sealed (after its calls) another store, or the same, unsealed. *)
(*                                                                         *)
(* The generator's stream is abstract in the model, so the check is that   *)
(* the code's bytes are a faithful image of the model's terms: every term  *)
(* maps to one output (a function: two runs that reach the same key give   *)
(* the same bytes, which checks the XOR cancellation of two equal reseeds  *)
(* and that a refresh answering false or zero changes nothing) and         *)
(* different terms to different bytes (injective: a reseed or refresh that *)
(* mixes entropy in changes every later output, and no output repeats the  *)
(* sealing key's draw). Checked by cardinality: |pairs| = |terms| =        *)
(* |bytes|. Each run's `fresh` count must be the model's.                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* keystore_refresh.ndjson.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLE x

K == INSTANCE KeystoreRefresh WITH STD <- TRUE, MAXSTEPS <- 0, src <- "drbg", key <- [b |-> <<"S1">>, m |-> {}],
                                   asked <- 0, outs <- <<>>, sealk <- <<>>, steps <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/keystore_refresh.ndjson")
Runs == {r \in DOMAIN Trace : Trace[r].op = "run"}
Refs == {r \in DOMAIN Trace : Trace[r].op = "ref"}
Unseals == {r \in DOMAIN Trace : Trace[r].op = "unseal"}

\* the store a run starts with; the operating system's draws of run r are atoms of their own
Start(ev) == IF ev.src = "drbg"
             THEN [src |-> "drbg", key |-> K!FirstKey(ev.seed), asked |-> 0, outs |-> <<>>]
             ELSE [src |-> "os", key |-> K!OsAtom(0), asked |-> 0, outs |-> <<>>]
RECURSIVE Fold(_, _, _, _)
Fold(st, ops, k, r) ==
    IF k > Len(ops) THEN st
    ELSE LET op == ops[k]
             nx == CASE op[1] = "random" -> K!RandomOf(st, K!OsAtom(r * 100 + Len(st.outs) + 1))
                     [] op[1] = "reseed" -> K!ReseedOf(st, op[2])
                     [] op[1] = "refresh" -> K!RefreshOf(st, op[2])
         IN Fold(nx, ops, k + 1, r)
Model(r) == Fold(Start(Trace[r]), Trace[r].ops, 1, r)

OpsOK(ev) == \A k \in 1..Len(ev.ops) :
    \/ ev.ops[k][1] = "random"
    \/ ev.ops[k][1] = "reseed" /\ ev.ops[k][2] \in K!Ents
    \/ ev.ops[k][1] = "refresh" /\ ev.ops[k][2] \in K!Answers

RunOK(r) == LET ev == Trace[r]
                m == Model(r)
            IN /\ ev.src \in {"drbg", "os"}
               /\ ev.src = "drbg" => ev.seed \in K!Seeds
               /\ OpsOK(ev)
               /\ Len(m.outs) = Len(ev.outs)
               /\ m.asked = ev.asked

\* every (term, bytes) pair: the outputs of the runs and the two reference fills of each seed
RunPairs == UNION {{<<Model(r).outs[k], Trace[r].outs[k]>> : k \in 1..Len(Trace[r].outs)} : r \in Runs}
RefPairs == UNION {{<<K!SealOf(Trace[r].seed), Trace[r].fills[1]>>,
                    <<<<K!FirstKey(Trace[r].seed), 32>>, Trace[r].fills[2]>>} : r \in Refs}
Pairs == RunPairs \cup RefPairs
Terms == {p[1] : p \in Pairs}
Bytes == {p[2] : p \in Pairs}

\* a store's sealing key: the seed's draw, or (operating system) one of its own per store id
SealKey(label, id) == IF label \in K!Seeds THEN K!SealOf(label) ELSE <<K!OsAtom(-id), 32>>
UnsealOK(r) == LET ev == Trace[r]
               IN ev.ok = (ev.same \/ SealKey(ev.a, ev.aid) = SealKey(ev.b, ev.bid))

Init == x = 0
Next == UNCHANGED x
TraceSpec == Init /\ [][Next]_x

AllOK == /\ \A r \in DOMAIN Trace : Trace[r].t = "ksr" /\ Trace[r].op \in {"run", "ref", "unseal"}
         /\ \A r \in Runs : RunOK(r)
         /\ \A r \in Refs : Trace[r].seed \in K!Seeds /\ Len(Trace[r].fills) = 2
         /\ \A r \in Unseals : UnsealOK(r)
         /\ Cardinality(Pairs) = Cardinality(Terms)
         /\ Cardinality(Terms) = Cardinality(Bytes)
         \* the operating system stores never call fresh (also part of RunOK, stated for the reader)
         /\ \A r \in Runs : Trace[r].src = "os" => Trace[r].asked = 0
\* the end check (TraceEnd.tla): the one state checks every line of a trace that has one
ReplayAtEnd == ReplaySeen(TRUE)
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
