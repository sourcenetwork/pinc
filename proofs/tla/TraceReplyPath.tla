---------------------------- MODULE TraceReplyPath ----------------------------
(***************************************************************************)
(* Trace validation of the path a dialing side's handshake reply arrives   *)
(* on and of its path table: vinc-transport conn/recv.rs, conn/drive.rs    *)
(* follow_reply, conn/path.rs.                                             *)
(*                                                                         *)
(* The Rust test tests/trace_reply_path.rs drives real dialing sides       *)
(* against a real responder: the host adds and removes paths, the          *)
(* responder's datagrams are handed to the dialing side on the dialed      *)
(* path, on another it holds, on paths it does not hold or gave up, cut    *)
(* over two paths, with forged Replies and a reject among them, and a      *)
(* resume Reply with a 1-RTT packet behind it, also at a full table; the   *)
(* key requests are answered one by one. Every call must be the step the   *)
(* operators of PathOps.tla compute, for the kind of message the code      *)
(* answered (rx: k), and the table recorded after it (the held paths in    *)
(* slot order, the active one), whether the session is established,        *)
(* whether the round trip has a sample and the dropped count must be the   *)
(* model's. reply_from is not recorded: the model carries it, and the path *)
(* a later key answer moves the session to checks it.                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds reply_path.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
CONSTANTS NP
VARIABLES i, c
vars == <<i, c>>
INSTANCE PathOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/reply_path.ndjson")
Ev0 == Trace[i]

\* the dialing side on path id: the path validated and active in the first slot
C0(id) == [t |-> [j \in 1..NP |-> IF j = 1 THEN [id |-> id, v |-> TRUE] ELSE Empty], act |-> 1, hs |-> "wait",
           rf |-> 0, pend |-> 0, smp |-> FALSE, hd |-> 0]

\* the held paths in slot order, as path_list gives them
RECURSIVE HeldFrom(_, _)
HeldFrom(t, j) == IF j > NP THEN <<>>
                  ELSE (IF t[j].id # 0 THEN <<[id |-> t[j].id, v |-> t[j].v]>> ELSE <<>>) \o HeldFrom(t, j + 1)

Same(x, v) == /\ HeldFrom(x.t, 1) = v.paths
              /\ x.t[x.act].id = v.act
              /\ (x.hs = "done") = v.est
              /\ x.smp = v.smp
              /\ x.hd = v.hd

InitEv == Ev0.op = "init" /\ Ev0.np = NP /\ c' = C0(Ev0.id) /\ Same(c', Ev0.v)
AddEv == Ev0.op = "add" /\ LET a == AddPath(c.t, c.act, Ev0.id)
                           IN /\ (IF a.i = 0 THEN "toomany" ELSE "ok") = Ev0.r
                              /\ c' = [c EXCEPT !.t = a.t] /\ Same(c', Ev0.v)
RmEv == Ev0.op = "rm" /\ LET a == RemovePath(c.t, c.act, Ev0.id)
                         IN a.r = Ev0.r /\ c' = [c EXCEPT !.t = a.t] /\ Same(c', Ev0.v)
\* the sample a step may give is the one recorded (smp only ever turns on, at the establishment)
RxEv == Ev0.op = "rx" /\ Ev0.k \in Kinds /\ c' = Rx(c, Ev0.id, Ev0.k, Ev0.coal, Ev0.v.smp, FALSE, TRUE) /\ Same(c', Ev0.v)
KeyEv == Ev0.op = "key" /\ c' = Key(c, Ev0.r, Ev0.v.smp) /\ Same(c', Ev0.v)

Init == i = 1 /\ c = C0(1)
Step == /\ i <= Len(Trace) /\ Ev0.t = "rp"
        /\ (InitEv \/ AddEv \/ RmEv \/ RxEv \/ KeyEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the active path is held and validated, and no path is held twice, throughout
Inv == /\ c.t[c.act].id # 0 /\ c.t[c.act].v
       /\ \A a, b \in 1..NP : (c.t[a].id # 0 /\ c.t[a].id = c.t[b].id) => a = b
=============================================================================
