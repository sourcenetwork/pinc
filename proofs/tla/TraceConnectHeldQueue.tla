------------------------ MODULE TraceConnectHeldQueue ------------------------
(***************************************************************************)
(* Trace validation of the packets a relay's carrier holds while it is not *)
(* open: pinc-connect client/queue.rs, HeldQueue, at the code's sizes      *)
(* (Q = QUEUED = 512, B = QUEUE_BYTES = 49152, M = MAX_PACKET_LEN = 1452). *)
(*                                                                         *)
(* The Rust test tests/trace_connect_queue.rs drives real queues with      *)
(* seeded calls: pushes of every length class (0, 1, small, full size, one *)
(* past MAX_PACKET_LEN), runs of small packets that fill the count, runs   *)
(* of large ones that fill the bytes, a large packet after many small ones *)
(* (several drops at once), pops down to empty and past it, and retains    *)
(* with random and edge choices (none, all, the first, the last), with     *)
(* pushes after them. Every packet has a serial number, written into its   *)
(* destination and its bytes. After every call it records the result and   *)
(* the whole queue as `get` shows it, oldest first: the serial and length  *)
(* of each packet. Every call must be the step the documented queue of     *)
(* ConnectHeldQueueOps.tla takes (AbsPush, the oldest for pop, AbsRetain): *)
(* the same count of drops, the same packet popped, the same queue after.  *)
(* The slot and byte layout behind it is checked by ConnectHeldQueue.cfg   *)
(* at small sizes; the code's private fields are not recorded.             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_queue.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS Q, B, M

VARIABLES i, aq
vars == <<i, aq>>

INSTANCE ConnectHeldQueueOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_queue.ndjson")
Ev0 == Trace[i]

KeepSet(flags) == {k - 1 : k \in {j \in 1..Len(flags) : flags[j]}}

NewEv == /\ Ev0.op = "new"
         /\ aq' = <<>>
PushEv == LET a == AbsPush(aq, Ev0.d, Ev0.len)
          IN /\ Ev0.op = "push"
             /\ a.k = Ev0.dropped
             /\ aq' = a.q
PopEv == /\ Ev0.op = "pop"
         /\ IF aq = <<>> THEN ~Ev0.some
            ELSE Ev0.some /\ Ev0.d = Head(aq)[1] /\ Ev0.len = Head(aq)[2]
         /\ aq' = IF aq = <<>> THEN aq ELSE Tail(aq)
RetainEv == /\ Ev0.op = "retain"
            /\ Len(Ev0.keep) = Len(aq)
            /\ aq' = AbsRetain(aq, KeepSet(Ev0.keep))

Init == i = 1 /\ aq = <<>>
Step == /\ i <= Len(Trace)
        /\ Ev0.t = "hq"
        /\ (NewEv \/ PushEv \/ PopEv \/ RetainEv)
        /\ aq' = Ev0.view
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the documented bounds hold on every recorded queue
Inv == Len(aq) <= Q /\ SumLen(aq) <= B
=============================================================================
