--------------------------- MODULE TraceFacadeTurn ---------------------------
(***************************************************************************)
(* Trace validation of the drive's turn against FacadeTurn.tla:            *)
(* crates/pinc/src/drive.rs `Shared::run_as` (294-448), `Turn::drop`       *)
(* (188-207), `flush` (451-490), over the slab of standby.rs.              *)
(*                                                                         *)
(* The test `tests/trace_facade_turn.rs` (file facade_turn.ndjson) runs     *)
(* one endpoint A and a peer in the shared world tests/facade_world.rs and *)
(* drives several facade calls of A at once (dials, opens, sends, accepts), *)
(* each an Exec task 1..NF; it writes the marks of the probe module        *)
(* pinc::trace_turn, each one step of the model:                           *)
(*   start {f}           run_as entered for task f                         *)
(*   io {f}  done {f}    the attempt ended in Io / Done (PollIo, PollDone) *)
(*   wait {f, tk, drv, took, flush}  the attempt waits: the ticket after   *)
(*                       ([slot, generation]), whether f now drives, how   *)
(*                       many datagrams the burst took, whether it goes on *)
(*                       to flush (anything moved) or returns Pending      *)
(*   flush {f}           a flush finished (then Done returns, else polls)  *)
(*   drop {f}            the host dropped f's future (Turn::drop)          *)
(*   notify {f}          the endpoint notified f's ticket                  *)
(*   notifyall           every armed ticket was woken                      *)
(*   arrive              one datagram for A reached its socket             *)
(*   hostwake            a sleep of A fired (a no-op when the driver was   *)
(*                       not waiting: its task was already to be polled)   *)
(* and on every mark of the probe the turn's flag and the core's driver    *)
(* ticket ([] or [slot, generation]) after it (arrive and hostwake, which  *)
(* the test writes, carry neither). The Flush mark of a call that returns  *)
(* and the Drop mark are written after the guard's Drop ran (the release  *)
(* and the baton, one model step); a baton's wake is part of that step and *)
(* is not marked; only notify and notify_all are.                          *)
(*                                                                         *)
(* Bounds of the instance: NF tasks, DRAIN 256 as the code, DMAX and       *)
(* STARTS large enough not to bind, GENS 2^30 (the code's u32 generation  *)
(* wraps at 2^32 and does not reach 2^30 in a run: the test asserts every *)
(* generation stays below), ROLE FALSE (no Endpoint::run in the test), PASS and DROP TRUE.  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds facade_turn.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES sb, st, tk, drv, flag, driver, sock, fed, arrived, starts, done, took, hw, i
mvars == <<sb, st, tk, drv, flag, driver, sock, fed, arrived, starts, done, took, hw>>

NF == 8
M == INSTANCE FacadeTurn WITH F <- 1..NF, OWNER <- 1, ROLE <- FALSE, DRAIN <- 256, DMAX <- 100000,
                              STARTS <- 100000, GENS <- 1073741824, PASS <- TRUE, DROP <- TRUE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_turn.ndjson")
Ev == Trace[i]
Tk(x) == IF x = <<>> THEN <<>> ELSE <<x[1], x[2]>>

Step ==
    /\ CASE Ev.op = "start" -> M!Start(Ev.f)
         [] Ev.op = "io" -> M!PollIo(Ev.f)
         [] Ev.op = "done" -> M!PollDone(Ev.f)
         [] Ev.op = "wait" -> /\ M!PollWait(Ev.f)
                              /\ tk'[Ev.f] = Tk(Ev.tk) /\ drv'[Ev.f] = Ev.drv /\ took' = Ev.took
                              /\ st'[Ev.f] = IF Ev.flush THEN "flush" ELSE "wait"
         [] Ev.op = "flush" -> M!Flush(Ev.f)
         [] Ev.op = "drop" -> M!Drop(Ev.f)
         [] Ev.op = "notify" -> M!NotifyE(Ev.f)
         [] Ev.op = "notifyall" -> M!NotifyAllE
         [] Ev.op = "arrive" -> M!Arrive
         [] Ev.op = "hostwake" -> \/ M!HostWake
                                  \/ M!HostWoken(st) = st /\ UNCHANGED mvars
         [] OTHER -> FALSE
    /\ "flag" \in DOMAIN Ev => flag' = Ev.flag
    /\ "driver" \in DOMAIN Ev => driver' = Tk(Ev.driver)

Init == M!Init /\ i = 1
Next == \/ i <= Len(Trace) /\ Step /\ i' = i + 1
        \* Finished: the trace was read to its end (a mismatch deadlocks before it)
        \/ i > Len(Trace) /\ UNCHANGED <<mvars, i>>
TraceSpec == Init /\ [][Next]_<<mvars, i>>

Inv == M!Inv
=============================================================================
