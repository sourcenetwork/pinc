-------------------------- MODULE TraceFacadeStandby --------------------------
(***************************************************************************)
(* Trace validation of the facade's standby slab: crates/vinc/src/standby.rs. *)
(*                                                                         *)
(* The Rust test tests/trace_standby.rs drives real slabs (the facade      *)
(* built with the cargo feature `trace`, StandbyProbe) with seeded calls:  *)
(* alloc, arm, notify, baton, notify_all and release, with tickets that    *)
(* are held, released, released twice or forged, slots reused while the   *)
(* entry of their released ticket is still queued, and one slot reused    *)
(* 200 times (each reuse queues a ticket, so the queue is compacted).      *)
(* Every call must be the step the operators of StandbyOps.tla compute:    *)
(* the ticket alloc hands out, the wakers woken in order, and the slots,   *)
(* the free stack and the queue of tickets recorded after the call. Beside *)
(* the slab the check keeps the documented order (ord): every alloc hands  *)
(* out a ticket no entry of the queue names, the live entries of the queue *)
(* are that order, and every baton wakes its oldest armed ticket.          *)
(*                                                                         *)
(* The code's generations wrap at 2^32, which TLC cannot write; the        *)
(* recorded generations stay below 2^31 - 2, where a release adds one      *)
(* whatever the modulus and none brings a generation round. The wrap, and  *)
(* the drop of the stale entries it makes, are FacadeStandby.tla's and     *)
(* Lean's: the probe has no way to set a generation, and releasing a slot  *)
(* 2^32 times is out of a trace test's reach.                              *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds standby.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, sb, ord
vars == <<i, sb, ord>>
INSTANCE StandbyOps

TGENS == 2147483647
Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/standby.ndjson")
Ev == Trace[i]
\* the recorded slab: each slot as [generation, waker (0 for none), queued, live]; the queue as [slot, generation]
Slots(v) == [k \in 1..Len(v.slots) |->
                [gen |-> v.slots[k][1], waker |-> v.slots[k][2], queued |-> v.slots[k][3], live |-> v.slots[k][4]]]
Same(s, v) == s.slots = Slots(v) /\ s.free = v.free /\ s.queue = v.queue

InitEv == /\ Ev.op = "init" /\ Same(Sb0, Ev.v) /\ sb' = Sb0 /\ ord' = <<>>
AllocEv == LET x == Alloc(sb)
           IN /\ Ev.op = "alloc" /\ x.t = Ev.out /\ Same(x.s, Ev.v) /\ sb' = x.s
              /\ x.t \notin Range(sb.queue) /\ ord' = ord
ArmEv == LET y == Arm(sb, Ev.tk, Ev.w)
         IN /\ Ev.op = "arm" /\ Ev.woke = <<>> /\ Same(y, Ev.v) /\ sb' = y /\ ord' = OrderArm(sb, Ev.tk, ord)
NotifyEv == LET x == Notify(sb, Ev.tk)
            IN /\ Ev.op = "notify" /\ x.w = Ev.woke /\ Same(x.s, Ev.v) /\ sb' = x.s /\ ord' = ord
BatonEv == LET x == Baton(sb)
           IN /\ Ev.op = "baton" /\ x.w = Ev.woke /\ Same(x.s, Ev.v) /\ sb' = x.s
              /\ x.w = OrderWoken(sb, ord) /\ ord' = OrderBaton(sb, ord)
AllEv == LET x == NotifyAll(sb)
         IN /\ Ev.op = "all" /\ x.w = Ev.woke /\ Same(x.s, Ev.v) /\ sb' = x.s /\ ord' = ord
ReleaseEv == LET y == Release(sb, Ev.tk, TGENS)
             IN /\ Ev.op = "release" /\ Ev.woke = <<>> /\ Same(y, Ev.v) /\ sb' = y
                /\ ord' = OrderRelease(sb, Ev.tk, ord)

Init == i = 1 /\ sb = Sb0 /\ ord = <<>>
Step == /\ i <= Len(Trace) /\ Ev.t = "fsb"
        /\ (InitEv \/ AllocEv \/ ArmEv \/ NotifyEv \/ BatonEv \/ AllEv \/ ReleaseEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the slab's invariants on every recorded state
Inv == /\ QueueLive(sb) /\ QueueExact(sb) /\ LiveEntries(sb) = ord
       /\ \A k \in 0..Len(sb.slots) - 1 : Slot(sb, k).waker # 0 => Slot(sb, k).live /\ Slot(sb, k).queued
       /\ Distinct(sb.free)
       /\ Range(sb.free) = {k \in 0..Len(sb.slots) - 1 : ~Slot(sb, k).live}
=============================================================================
