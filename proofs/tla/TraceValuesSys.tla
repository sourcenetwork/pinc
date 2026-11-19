---------------------------- MODULE TraceValuesSys ----------------------------
(***************************************************************************)
(* Trace validation of the multi-provider value fetch: pinc-values          *)
(* fetch/{mod,sched,recv,rx,wt,stall}.rs against ValuesSys.tla.             *)
(*                                                                          *)
(* The Rust test tests/trace_values_sys.rs runs the real Fetch against real *)
(* Servers through the in-memory harness (1 to 4 providers, a provider      *)
(* dropped, a silent provider that is robbed, a liar among honest           *)
(* providers, every provider lying, a restart in the middle, loss and       *)
(* reordering with write-through, the deadline, a refusing store, an empty  *)
(* value, no provider, ranges over a store with holes) and writes, per run, *)
(* a start line, one line per event and trace record the fetcher reported   *)
(* in the order it reported them, and an end line. This spec reads the      *)
(* lines and checks, record by record, that the run is a behaviour of the   *)
(* model:                                                                   *)
(*   - the start record, the first record and the final event agree with    *)
(*     StartBegin of ValuesSys.tla (BadRoot, then Complete when nothing is  *)
(*     missing, then NoProvider, else the fetch starts);                    *)
(*   - every request asks only for groups of the wanted set that the store  *)
(*     had not verified when it was sent (so nothing verified at a restart  *)
(*     is asked again), and never goes to an evicted provider;              *)
(*   - a group verifies at most once, from a provider that is still a       *)
(*     candidate, and the store snapshot after it is the committed set the  *)
(*     model computes; the bytes written are the true ones (genuine);       *)
(*   - an event Readable names a verified group, the first granule is only  *)
(*     announced after it was held and released (HEAD_HOLD), Complete       *)
(*     follows only when everything wanted is verified and announced, and   *)
(*     the other final events have the reasons of ReasonOk;                 *)
(*   - only a provider that lies is evicted, and it is never asked, robbed  *)
(*     from or given work again;                                            *)
(*   - there is exactly one final event and no record after it.             *)
(* The bookkeeping and the predicates are the definitions of ValuesSysCore, *)
(* the same operators ValuesSys.tla model checks over all behaviours. The   *)
(* scheduling records (dial, top-up, steal, retry, stall redial) are        *)
(* checked for the provider they name; their byte arithmetic is the         *)
(* ValuesSched slice.                                                       *)
(*                                                                          *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment      *)
(* variable PINC_TRACE_DIR, the directory that holds values_sys.ndjson.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, ValuesSysCore

VARIABLES i, T
vars == <<i, T>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/values_sys.ndjson")

Ev == Trace[i]
SetOf(s) == {s[k] : k \in 1..Len(s)}
Snap(pairs) == UNION {pairs[k][1]..(pairs[k][2] - 1) : k \in 1..Len(pairs)}
Grps == 0..(T.g - 1)

Init == i = 1 /\ T = [run |-> "none"]

StartEv ==
    /\ Ev.op = "start" /\ T.run \in {"none", "ended"}
    /\ LET ver0 == SetOf(Ev.ver0)
       IN T' = [run |-> "idle", fin |-> NONE, nfin |-> 0, late |-> 0, g |-> Ev.g,
                ann |-> [g \in 0..(Ev.g - 1) |-> 0],
                wr |-> [g \in 0..(Ev.g - 1) |-> IF g \in ver0 THEN "true" ELSE "none"],
                ver |-> ver0, ver0 |-> ver0, hd |-> -1, rel |-> FALSE, relp |-> -1,
                inP |-> [p \in 1..Ev.np |-> p \in SetOf(Ev.listed)], lied |-> {}, now |-> 0,
                W |-> SetOf(Ev.want), L |-> SetOf(Ev.listed), lr |-> SetOf(Ev.liars), dl |-> Ev.dl,
                empty |-> Ev.empty = 1, badroot |-> Ev.badroot = 1, first |-> Ev.first]

Live == T.run \in {"idle", "run"}
Started == T.run = "run"

(* the final event the start of a fetch produces, in the order of Fetch::start *)
StartFinal ==
    IF T.empty /\ T.badroot THEN "BadRoot"
    ELSE IF T.W \ T.ver = {} THEN "Complete"
    ELSE IF T.L = {} THEN "NoProvider"
    ELSE NONE

Cand(p) == p \in DOMAIN T.inP /\ T.inP[p]
Tick == [T EXCEPT !.now = Ev.now]

FstartEv ==
    /\ Ev.k = "fstart" /\ T.run = "idle" /\ StartFinal = NONE /\ Ev.n = Cardinality(T.L)
    /\ T' = [Tick EXCEPT !.run = "run"]

ReqEv ==
    /\ Ev.k = "req" /\ Started /\ Cand(Ev.p)
    /\ SetOf(Ev.groups) \subseteq T.W /\ SetOf(Ev.groups) \cap T.ver = {}
    /\ T' = Tick

VerEv ==
    /\ Ev.k = "ver" /\ Started /\ Cand(Ev.p) /\ Ev.g \in T.W /\ Ev.g \notin T.ver
    /\ LET T1 == [Tick EXCEPT !.ver = T.ver \cup {Ev.g}, !.wr[Ev.g] = IF Ev.genuine = 1 THEN "true" ELSE "junk"]
       IN /\ Snap(Ev.snap) = T1.ver
          /\ T' = T1

HeldEv ==
    /\ Ev.k = "held" /\ Started /\ Ev.g = T.first /\ Ev.g \in T.ver /\ ~T.rel /\ T.hd = -1
    /\ T' = [Tick EXCEPT !.hd = Ev.g]

RelEv ==
    /\ Ev.k = "rel" /\ Started /\ T.hd = Ev.g
    /\ T' = [Tick EXCEPT !.relp = Ev.g]

(* Readable: the held first granule goes out through its release; any other group needs the first one released *)
ReadableEv ==
    /\ Ev.k = "ev" /\ Ev.e = "R" /\ Started
    /\ IF T.hd = Ev.g
       THEN T.relp = Ev.g /\ T' = [ReleaseHd(Tick) EXCEPT !.relp = -1]
       ELSE /\ (Ev.g = T.first => T.rel) /\ T.relp = -1
            /\ T' = Readable(Tick, Ev.g)

FinalEv ==
    /\ Ev.k = "ev" /\ Ev.e \in {"C", "F"} /\ Live
    /\ LET f == IF Ev.e = "C" THEN "Complete" ELSE Ev.why
           T1 == Final(Tick, f)
       IN /\ IF T.run = "idle" THEN f = StartFinal ELSE T.relp = -1
          /\ ReasonOk(T1, T.W, T.L, T.empty, ~T.badroot, FALSE \/ f = "Store", T.dl >= 0, T.dl)
          /\ T' = T1

LiarEv ==
    /\ Ev.k = "liar" /\ Started /\ Cand(Ev.p) /\ Ev.p \in T.lr
    /\ T' = [Tick EXCEPT !.inP[Ev.p] = FALSE, !.lied = T.lied \cup {Ev.p}]

SchedEv ==
    /\ Started
    /\ \/ Ev.k \in {"dial", "retry", "topup"} /\ Cand(Ev.p)
       \/ Ev.k = "steal" /\ Cand(Ev.from) /\ Cand(Ev.to) /\ Ev.from # Ev.to
       \/ Ev.k \in {"stall", "proofrej"}
    /\ T' = Tick

RecEv ==
    /\ Ev.op = "rec" /\ Live /\ Ev.now >= T.now
    /\ \/ FstartEv \/ ReqEv \/ VerEv \/ HeldEv \/ RelEv \/ ReadableEv \/ FinalEv \/ LiarEv \/ SchedEv

EndEv ==
    /\ Ev.op = "end" /\ T.run \in {"run", "done"}
    /\ (T.run = "done") = (Ev.done = 1)
    /\ Snap(Ev.snap) = T.ver
    /\ T' = [T EXCEPT !.run = "ended"]

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "vsys"
    /\ \/ StartEv \/ RecEv \/ EndEv
    /\ i' = i + 1

\* the trace has ended: every line was a step of the model
Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

(* the facts of the model hold on every recorded state *)
Inv ==
    T.run \in {"idle", "run", "done"} =>
        /\ SoundStore(T, Grps) /\ SoundEvents(T, Grps) /\ OneFinalP(T)
        /\ ReasonOk(T, T.W, T.L, T.empty, ~T.badroot, T.fin = "Store", T.dl >= 0, T.dl)

=============================================================================
