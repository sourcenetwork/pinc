------------------------------ MODULE TraceConnect ------------------------------
(***************************************************************************)
(* Trace validation of the relay: vinc-connect/src/relay (clients.rs,      *)
(* route.rs, records.rs, discovery.rs) with the mailbox it holds.          *)
(*                                                                         *)
(* The Rust test tests/trace_connect.rs drives the real Relay through      *)
(* seeded schedules (carriers opened, replaced and closed, frames of every *)
(* kind from nodes and from peer relays, UDP sessions and SPU datagrams,   *)
(* sleep notices, records, peers added and removed, the sweep) at times    *)
(* around every rule constant, and writes each call with its answer and    *)
(* every effect, trace transition included, in order. Every event must be  *)
(* the step the operators of ConnectRelayOps.tla compute: the same answer  *)
(* and the same effects in the same order, from the same hash buckets (the *)
(* buckets of the real tables are recorded first).                         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds connect.ndjson.       *)
(***************************************************************************)
EXTENDS ConnectRelayOps, Json, IOUtils

VARIABLES i, cf, R
vars == <<i, cf, R>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/connect.ndjson")
Ev == Trace[i]

Init == i = 1 /\ cf = [me |-> 0, C |-> 1, R |-> 1, MN |-> 1, MB |-> 1, Bytes |-> 0, Window |-> 1, SessT |-> 1, Age |-> 1,
                old |-> FALSE]
        /\ R = NewRelay(cf)

Step(o) == /\ o.res = Ev.res /\ o.ef = Ev.out /\ R' = o.R /\ cf' = cf /\ i' = i + 1

NewE == /\ Ev.t = "rnew"
        /\ cf' = [me |-> Ev.me, C |-> Ev.c, R |-> Ev.r, MN |-> Ev.mn, MB |-> Ev.mb, Bytes |-> Ev.bytes,
                  Window |-> Ev.window, SessT |-> Ev.sess, Age |-> Ev.age,
                  old |-> FALSE]
        /\ R' = NewRelay(cf') /\ i' = i + 1
BkE == /\ Ev.t = "rbk" /\ R' = [R EXCEPT !.bk = Put(R.bk, Ev.n, Ev.b)] /\ cf' = cf /\ i' = i + 1
AddE == /\ Ev.t = "radd"
        /\ LET a == AddPeer(R, Ev.p) IN /\ (a.ok = (Ev.res = "ok")) /\ Ev.out = <<>> /\ R' = a.R
        /\ cf' = cf /\ i' = i + 1
RemE == /\ Ev.t = "rrem" /\ R' = RemovePeer(R, Ev.p) /\ cf' = cf /\ i' = i + 1
OpenE == /\ Ev.t = "ropen" /\ Step(CarrierOpened(cf, R, Ev.now, Ev.n))
CloseE == /\ Ev.t = "rclose" /\ Step(CarrierClosed(cf, R, Ev.now, Ev.n, Ev.sid))
FrameE == /\ Ev.t = "rframe" /\ Step(CarrierFrame(cf, R, Ev.now, Ev.n, Ev.sid, Ev.f))
PeerE == /\ Ev.t = "rpeer" /\ Step(PeerFrame(cf, R, Ev.now, Ev.from, Ev.f))
UdpHE == /\ Ev.t = "rudph" /\ Step(UdpHeard(cf, R, Ev.now, Ev.n))
RdyE == /\ Ev.t = "rready" /\ Ev.out = <<>> /\ R' = SetReady(R, Ev.n, Ev.ok) /\ cf' = cf /\ i' = i + 1
UdpGE == /\ Ev.t = "rudpg" /\ Ev.out = <<>> /\ R' = UdpGone(R, Ev.n) /\ cf' = cf /\ i' = i + 1
SpuE == /\ Ev.t = "rspu" /\ Step(Spu(cf, R, Ev.now, Ev.m, Ev.dst, Ev.flag, Ev.len))
RetE == /\ Ev.t = "rret" /\ Step(MemberReturned(cf, R, Ev.now, Ev.n))
TimeE == /\ Ev.t = "rtime" /\ Step(Timeout(cf, R, Ev.now))

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (NewE \/ BkE \/ AddE \/ RemE \/ OpenE \/ CloseE \/ FrameE \/ PeerE \/ UdpHE \/ RdyE \/ UdpGE \/ SpuE \/ RetE \/ TimeE))
         \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectRelayOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
