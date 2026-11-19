--------------------------- MODULE TraceFinishResend ---------------------------
(***************************************************************************)
(* Trace validation of the Finish resend schedule (pinc-transport          *)
(* conn/handshake.rs `finish_sent` and the Stage::Finish arm of            *)
(* `on_timer`) against FinishResend.tla.                                   *)
(*                                                                         *)
(* The Rust test tests/trace_finish_resend.rs establishes dialing          *)
(* connections whose Finish never reaches the peer (every datagram from    *)
(* the dialer is dropped once it sent the Finish), on paths of 1 ms to     *)
(* 1.5 s one way, ordinary and thin nodes, with zero to three first        *)
(* flights lost before (so the count of sends differs), and runs the       *)
(* dialer's timers until the connection gives up. Per connection it        *)
(* records "est" when the Finish first goes out (the probe timeout, the    *)
(* round trip a thin node waits on, whether the node is thin, the sends so *)
(* far, the first wait armed) and "fire" at every resend (the sends before *)
(* it, the wait armed for the next one). Times are microseconds: every     *)
(* constant of the code is a whole number of them, and the operators of    *)
(* the model do not depend on the unit.                                    *)
(*                                                                         *)
(* Each "est" must be FinishResend's Init for those inputs, each "fire"    *)
(* its Fire, and every state the invariants of FinishResend.cfg.           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds finish_resend.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLES pto, rtt, thin, sends, first, waits, i
mvars == <<pto, rtt, thin, sends, first, waits>>
vars == <<pto, rtt, thin, sends, first, waits, i>>

\* FINISH_FIRST, FINISH_CAP, FINISH_SHIFT and THIN_FINISH_MAX of the code, in microseconds. The sets of inputs are
\* the model checker's; here each run's inputs come from its "est" event. FIRES is no bound on a recorded run.
F == INSTANCE FinishResend WITH FIRST <- 999000, CAP <- 2000000, SHIFT <- 3, THINMAX <- 20000000,
                                PTOS <- {1}, RTTS <- {0}, SENDS <- {1}, FIRES <- 1000000, BUG <- "none"

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/finish_resend.ndjson")
Ev == Trace[i]

Init == /\ i = 1 /\ pto = 1 /\ rtt = 0 /\ thin = FALSE /\ sends = 0 /\ first = 0 /\ waits = <<>>

\* A connection sent its Finish: the run starts, as FinishResend's Init with the recorded inputs.
Est == /\ Ev.t = "est"
       /\ Ev.pto >= 1
       /\ pto' = Ev.pto /\ rtt' = Ev.rtt /\ thin' = (Ev.thin = 1) /\ sends' = Ev.sends
       /\ first' = F!FirstWait(Ev.pto) /\ waits' = <<F!FirstWait(Ev.pto)>>
       /\ Ev.wait = F!FirstWait(Ev.pto)
       /\ i' = i + 1

\* The timer fired with the peer silent: FinishResend's Fire, the wait it arms the one recorded, from the same sends.
Fire == /\ Ev.t = "fire"
        /\ waits # <<>>
        /\ Ev.sent = sends /\ (Ev.thin = 1) = thin /\ Ev.rtt = rtt /\ Ev.first = first
        /\ F!Fire
        /\ waits'[Len(waits')] = Ev.wait
        /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (Est \/ Fire)) \/ Done
TraceSpec == Init /\ [][TNext]_vars

\* the invariants of FinishResend.cfg, in every run (none before the first Finish)
Inv == waits # <<>> => /\ F!FirstBounded /\ F!FirstAtPto /\ F!WaitsCapped /\ F!WaitsGrow /\ F!ThinWaits
                       /\ F!WaitsPositive
=============================================================================
