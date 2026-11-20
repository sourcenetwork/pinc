--------------------------- MODULE TraceBroadcastSubs ---------------------------
(***************************************************************************)
(* Trace validation of a hub's subscriber table across a member's absence: *)
(* pinc-broadcast gap.rs `on_sub` and `on_unsub`, subs.rs `hold`,          *)
(* `restore` and `release`, msg.rs `hub_store` (the push).                 *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_subs.rs drives one hub (built with  *)
(* the cargo feature `trace`, whose probe `Topics::sub_state` reads an     *)
(* entry) with members 1 to 3 on topics 1 and 2, and a publisher, node 4,  *)
(* that subscribes to nothing. It records one event per call: SUB and      *)
(* UNSUB frames from a member, hold, restore and release of a member, and  *)
(* a publish; with the RESTORED frames a restore sent (their topics), the  *)
(* members a publish was pushed to, and the whole table after the call.    *)
(* Every event must be a step of BroadcastSubs.tla (Sub, Unsub, Hold,      *)
(* Restore, Release, Push) for that member or topic, whose table is the   *)
(* recorded one, and the model's invariants hold on every state. The code's *)
(* table cap (TABLE_MAX, 4096) is above the 3 members: the trace never     *)
(* reaches it (BroadcastSubs.cfg checks the cap).                          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/subs.ndjson.                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS Members, Topics, TableMax

VARIABLES i, subs, step
vars == <<i, subs, step>>

M == INSTANCE BroadcastSubs

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/subs.ndjson")
Ev == Trace[i]
Range(s) == {s[j] : j \in 1..Len(s)}
Recorded == [t \in Topics |-> [m \in Members |-> Ev.subs[t][m]]]

SubEv == Ev.op = "sub" /\ M!Sub /\ subs'[Ev.topic][Ev.m] = "live"
UnsubEv == Ev.op = "unsub" /\ M!Unsub /\ subs'[Ev.topic][Ev.m] = "none"
HoldEv == Ev.op = "hold" /\ M!Hold /\ step'.member = Ev.m
RestoreEv == Ev.op = "restore" /\ M!Restore /\ step'.member = Ev.m /\ step'.told = Range(Ev.told)
ReleaseEv == Ev.op = "release" /\ M!Release /\ step'.member = Ev.m
PushEv == Ev.op = "push" /\ M!Push /\ step'.topic = Ev.topic /\ step'.pushed = Range(Ev.pushed)

Init == i = 1 /\ M!Init
Step == /\ i <= Len(Trace) /\ Ev.t = "subs"
        /\ (SubEv \/ UnsubEv \/ HoldEv \/ RestoreEv \/ ReleaseEv \/ PushEv)
        /\ subs' = Recorded
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == /\ M!TypeOK /\ M!HeldGetsNoPush /\ M!RestoreTellsExactly /\ M!RestoreOnlyHeld /\ M!HoldKeeps
       /\ M!ReleaseForgets /\ M!TableBound
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
