----------------------------- MODULE TraceDtnWant -----------------------------
(***************************************************************************)
(* Trace validation of `Dtn::want` (pinc-node dtn.rs), the request rule of *)
(* DtnRequest.tla, over its whole input space at the model's geometry.     *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_want.rs calls the real rule through the   *)
(* `trace` probe `pinc_node::dtn_want_probe::want` on a layout of k = 2,   *)
(* m = 1 and two blocks (symbols 0, 1, 2 and 3, 4, 5, parity 2 and 5) with *)
(* slices of 16 KiB, so a run holds at most 4 symbols, for every held set  *)
(* and every lost set of the six symbols (4^6 pairs, a symbol may be both) *)
(* and every cursor the receiver can have (up to the first block short of  *)
(* k), and records the answer: a run [a, e) to ask for, decodable, or      *)
(* stuck.                                                                  *)
(*                                                                         *)
(* Each event must be the model's Want for that held and lost set, and the *)
(* receiver asking that run of that holder must satisfy the model's        *)
(* request invariants NoParityWithoutLoss, AskWithinNeed and AskFresh; a   *)
(* decodable answer must be Decodable. ActiveReachable is not checked      *)
(* here: it holds of the states a transfer reaches, not of every pair of   *)
(* sets (a run that ends in block 0 is asked for without looking at a      *)
(* block 1 that a pair may make stuck); TraceDtnRequest checks it on real  *)
(* transfers.                                                              *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_want.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_want.ndjson")
Ev == Trace[c.i]

Set(s) == {s[j] : j \in 1..Len(s)}
H == Set(Ev.have)
L == Set(Ev.lost)
\* The run asked for, as a set (empty for an answer that is not an ask).
A == IF Ev.kind = "ask" THEN Ev.a..(Ev.e - 1) ELSE {}

\* One holder asked the recorded run with the recorded held and lost sets; a run holds at most 4 symbols (64 KiB of
\* 16 KiB slices).
D == INSTANCE DtnRequest WITH NH <- 1, Case <- "none", MaxRun <- 4, MaxDrops <- 0, MarkLost <- TRUE,
                              DataFirst <- TRUE, NeedCap <- TRUE, PerTransfer <- TRUE, StopStuck <- TRUE,
                              have <- H, lost <- [x \in {1} |-> L], shared <- {},
                              st <- [x \in {1} |-> IF Ev.kind = "ask" THEN "asking" ELSE "idle"],
                              ask <- [x \in {1} |-> A], base <- [x \in {1} |-> H], refused <- {},
                              done <- FALSE, drops <- 0

Init == c = [t |-> "root"]

EvOK == /\ Ev.t = "want"
        /\ Ev.k = 2 /\ Ev.m = 1 /\ Ev.blocks = 2 /\ Ev.max = 4
        /\ H \subseteq D!Syms /\ L \subseteq D!Syms
        /\ LET w == D!Want(H, L)
           IN /\ w.kind = Ev.kind
              /\ w.kind = "ask" => w.run = <<Ev.a, Ev.e>>
        /\ D!NoParityWithoutLoss /\ D!AskWithinNeed /\ D!AskFresh
        /\ Ev.kind = "decodable" => D!Decodable(H)

(* Every event is an independent call, so the events are the states of one machine: the root state has one successor
   per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded answer is the model's
EventsOK == c.t = "event" => EvOK

\* every answer kind occurs
Covered == c.t = "root" =>
               \A kd \in {"ask", "decodable", "stuck"} : \E j \in 1..Len(Trace) : Trace[j].kind = kd
=============================================================================
