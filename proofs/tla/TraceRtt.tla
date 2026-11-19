------------------------------ MODULE TraceRtt ------------------------------
(***************************************************************************)
(* Trace validation of the node's round trips: pinc-core rtt.rs (NodeRtt). *)
(*                                                                         *)
(* The Rust test tests/trace_rtt.rs drives real nodes with seeded calls of *)
(* note_handshake, restore_peer, note_peak and note_timeout, with values   *)
(* on the edges (zero, one, 250 ms and one nanosecond either side, 500 ms, *)
(* 8 s, and up to u64::MAX so that the arithmetic saturates), a few peers  *)
(* and, in three long runs, 300 peers so that the table of 256 fills and   *)
(* refuses. A u64 is four 16-bit limbs; an absent value is []. Every call  *)
(* must be the step RttOps.tla computes, with the answer the code gave,    *)
(* and after every call the recorded peers (in order; their values too     *)
(* while the table holds at most 8), average, peak and floor, and the      *)
(* readers for four peers (krtt, first_resend, remembered_for, hub_resend) *)
(* and thin_node and thin must be the model's.                             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds rtt.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, r, cap
vars == <<i, r, cap>>
INSTANCE RttOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/rtt.ndjson")
Ev0 == Trace[i]
Lm(l) == U!FromLimbs(l)
Op(l) == IF l = <<>> THEN None ELSE Some(Lm(l))

Same(m, v) ==
    /\ Len(m.tab) = v.len /\ Len(v.peers) = v.len
    /\ \A k \in 1..v.len : m.tab[k][1] = v.peers[k]
    /\ (v.len <= 8 => \A k \in 1..v.len : m.tab[k][2] = Lm(v.tab[k][2]))
    /\ m.lrtt = Lm(v.lrtt) /\ m.tgr = Lm(v.tgr) /\ m.floor = Lm(v.floor)
    /\ ThinNode(m) = v.tn
    /\ \A j \in 1..Len(v.q) :
        LET e == v.q[j]
            p == e[1]
        IN /\ Krtt(m, p) = Op(e[2]) /\ FirstResendOf(m, p) = Lm(e[3])
           /\ Remembered(m, p) = Op(e[4]) /\ HubOf(m, p) = Op(e[5])
    /\ Thin(m, Lm(v.th[1]), Lm(v.th[2])) = v.th[3]

InitEv == /\ Ev0.op = "init" /\ cap' = Ev0.cap /\ r' = Rtt0 /\ Same(r', Ev0.v)
HsEv == /\ Ev0.op = "hs" /\ r' = Handshake(r, cap, Ev0.p, Lm(Ev0.x)) /\ Same(r', Ev0.v) /\ UNCHANGED cap
RestoreEv == LET x == Restore(r, cap, Ev0.p, Lm(Ev0.x))
             IN /\ Ev0.op = "restore" /\ x.ok = Ev0.ok /\ r' = x.r /\ Same(r', Ev0.v) /\ UNCHANGED cap
PeakEv == /\ Ev0.op = "peak" /\ r' = Peak(r, Lm(Ev0.x)) /\ Same(r', Ev0.v) /\ UNCHANGED cap
TimeoutEv == /\ Ev0.op = "timeout" /\ r' = Timeout(r) /\ Same(r', Ev0.v) /\ UNCHANGED cap

Init == i = 1 /\ r = Rtt0 /\ cap = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "corr" /\ (InitEv \/ HsEv \/ RestoreEv \/ PeakEv \/ TimeoutEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the table never grows past its bound, and the floor is one of its six values
Inv == /\ Len(r.tab) <= cap \/ cap = 0
       /\ r.floor \in {Zero, Ms(500), N!Sec(1), N!Sec(2), N!Sec(4), N!Sec(8)}
=============================================================================
