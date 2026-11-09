------------------------- MODULE TraceConnectMailbox -------------------------
(***************************************************************************)
(* Trace validation of the mailbox: vinc-connect/src/mailbox.rs.           *)
(*                                                                         *)
(* The Rust test tests/trace_connect_mailbox.rs runs the real Mailbox      *)
(* through seeded schedules of pushes (every body size around the quota    *)
(* and the packet bound), pops (with and without a length limit), sweeps   *)
(* and clears at times around the age, checks the bytes it hands out       *)
(* against what was stored, and writes each call with its answer, the      *)
(* messages and bytes held for the member, and the counters. Every event   *)
(* must be the step the operators of ConnectMailboxOps.tla (Push, Pop,     *)
(* Sweep, Clear) compute: the same answer, the same sequence number, the   *)
(* same number of dropped messages, the same held (messages, bytes) and    *)
(* the same counters.                                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds                       *)
(* connect_mailbox.ndjson.                                                 *)
(***************************************************************************)
EXTENDS ConnectMailboxOps, Json, IOUtils

VARIABLES i, c, mb
vars == <<i, c, mb>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/connect_mailbox.ndjson")
Ev == Trace[i]

StOf(a) == [stored |-> a[1], delivered |-> a[2], dropped |-> a[3], droppedBytes |-> a[4], expired |-> a[5],
            oversize |-> a[6], members |-> a[7]]

Init == i = 1 /\ c = [H |-> 0, B |-> 1, N |-> 0, MaxPkt |-> 0, Age |-> 0, Rearm |-> 0] /\ mb = Empty

Seen(m2, ev) == m2.st = StOf(ev.st)

New == /\ Ev.t = "mbnew"
       /\ c' = [H |-> Ev.h, B |-> Ev.b, N |-> Ev.n, MaxPkt |-> Ev.maxpkt, Age |-> Ev.age, Rearm |-> 0]
       /\ mb' = Empty /\ i' = i + 1

PushEv == /\ Ev.t = "mpush"
          /\ LET r == Push(c, mb, Ev.now, Ev.node, Ev.src, Ev.flag, Ev.len) IN
             /\ r.res = Ev.res
             /\ Ev.res = "stored" => r.seq = Ev.seq /\ r.dropped = Ev.dropped /\ r.first = Ev.first
             /\ mb' = r.mb
             /\ Seen(r.mb, Ev)
             /\ Pending(r.mb, Ev.node) = <<Ev.pc, Ev.pu>>
          /\ c' = c /\ i' = i + 1

PopEv == /\ Ev.t = "mpop"
         /\ LET r == Pop(c, mb, Ev.now, Ev.node, Ev.max) IN
            /\ r.got = Ev.got
            /\ Ev.got => /\ r.m.src = Ev.src /\ r.m.flag = Ev.flag /\ r.m.len = Ev.len /\ r.m.seq = Ev.seq
                         /\ r.m.t = Ev.mt
            /\ mb' = r.mb
            /\ Seen(r.mb, Ev)
            /\ Pending(r.mb, Ev.node) = <<Ev.pc, Ev.pu>>
         /\ c' = c /\ i' = i + 1

SweepEv == /\ Ev.t = "msweep"
           /\ mb' = Sweep(c, mb, Ev.now) /\ Seen(mb', Ev)
           /\ c' = c /\ i' = i + 1

ClearEv == /\ Ev.t = "mclear"
           /\ mb' = Clear(mb, Ev.node) /\ Seen(mb', Ev)
           /\ c' = c /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (New \/ PushEv \/ PopEv \/ SweepEv \/ ClearEv)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectMailboxOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
