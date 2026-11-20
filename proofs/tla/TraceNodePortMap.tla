--------------------------- MODULE TraceNodePortMap ---------------------------
(***************************************************************************)
(* Trace validation of the node's port-mapping client (pinc-node           *)
(* portmap.rs) against the properties of NodePortMap.tla, on a real node.  *)
(*                                                                         *)
(* tests/trace_node_portmap.rs drives a node (the Member of                 *)
(* tests/node_portmap.rs) through starts, stops, restarts, gateway answers *)
(* (grants, releases answered), HTTP answers and timeouts, at times up to   *)
(* u64::MAX, and writes after every call one line {"t": "pm", "call": c,   *)
(* "v": view} with the view of the probe Node::pm_view (cargo feature      *)
(* `trace`): on (a Pm exists), cli (it has a client), held (the address    *)
(* the client holds), given, conn (the mapped address the connectivity     *)
(* client holds), ret (retiring slots taken), ovf (release_overflows),    *)
(* halted, dl (the Pm arms a timer), nf (nonce_failures), sent (datagrams  *)
(* the node gave the gateway during the call). Addresses are small        *)
(* numbers the test assigns, 0 for none; counts stay far below 2^31.       *)
(*                                                                         *)
(* Checked on every line: ConnHolds (conn = held = given with a Pm, conn = *)
(* 0 without), the queue within RETIRING (4), no Pm arms no timer.  On     *)
(* every step: with no Pm before and after, nothing is sent (NoPmNothing); *)
(* the overflow count grows by at most one, and only on a start that finds *)
(* the queue full; a halted Pm starts no client until a start (HaltedStays). *)
(* The file holds several runs, each from the line "init" of a new node:  *)
(* there the step rules give way to NewRun (no Pm, nothing sent, no       *)
(* overflow), since a run that ended with overflows would otherwise break *)
(* the overflow rule at the next run's first line.                        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds node_portmap.ndjson.                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, v
vars == <<i, v>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/node_portmap.ndjson")
Ev0 == Trace[i]
RETIRING == 4
V0 == [on |-> FALSE, cli |-> FALSE, held |-> 0, given |-> 0, conn |-> 0, ret |-> 0, ovf |-> 0, halted |-> FALSE,
       dl |-> FALSE, nf |-> 0, sent |-> 0]

StepOK(c, a, b) ==
    /\ ~a.on /\ ~b.on => b.sent = 0
    /\ b.ovf \in {a.ovf, a.ovf + 1} \/ (~a.on /\ b.ovf = 0)
    /\ b.ovf = a.ovf + 1 => c = "start" /\ a.ret = RETIRING /\ b.ret = RETIRING
    /\ a.halted /\ b.halted /\ c # "start" => ~b.cli

\* the line "init" starts a run on a new node: no Pm, nothing sent, no overflow counted; the counters of the run before
\* do not carry over, so the step rules do not apply across it
NewRun(b) == ~b.on /\ b.sent = 0 /\ b.ovf = 0

Init == i = 1 /\ v = V0
Step == /\ i <= Len(Trace) /\ Ev0.t = "pm"
        /\ IF Ev0.call = "init" THEN NewRun(Ev0.v) ELSE StepOK(Ev0.call, v, Ev0.v)
        /\ v' = Ev0.v /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TraceSpec == Init /\ [][Step \/ Finished]_vars

\* every line was taken: a step that broke StepOK leaves i short of the end
Done == i > Len(Trace) \/ ENABLED Step
Inv == /\ v.on => v.conn = v.held /\ v.given = v.held
       /\ ~v.on => v.conn = 0 /\ ~v.dl
       /\ v.ret \in 0..RETIRING
       /\ Done
=============================================================================
