---------------------------- MODULE TraceConnectWs ----------------------------
(***************************************************************************)
(* Trace validation of the WebSocket framing of the carrier: pinc-connect  *)
(* carrier/ws.rs.                                                          *)
(*                                                                         *)
(* The Rust test tests/trace_connect_ws.rs calls the real `encode` for     *)
(* every opcode, with and without a mask key, with payloads of every       *)
(* boundary length and output buffers from empty to roomy, and the real    *)
(* `Decoder::decode`: on streams of frames the encoder wrote and of        *)
(* fragmented messages with control frames between the fragments, read in  *)
(* random splits and decoded after every read (so on every partial         *)
(* prefix), and on crafted headers (every reserved bit, every opcode, the  *)
(* wrong mask for both roles, every length form around its threshold and   *)
(* MAX_PAYLOAD up to u64::MAX, control frames that are fragmented or       *)
(* long, frames out of sequence, every cut of a header, trailing bytes,    *)
(* the header of an oversized frame without its payload). One event per    *)
(* call: the input and the result (the bytes written or the refusal; idle, *)
(* the refusal or the frame with its payload, close status and bytes used).*)
(* A decoder's one bit of state (a fragmented message is open) cannot be   *)
(* read from outside, so the model tracks it per decoder from its calls:   *)
(* every later answer then checks it. Each call must be exactly what the   *)
(* operators of ConnectWsOps.tla give, whose properties TLC checks in      *)
(* ConnectWs.tla. MAX_PAYLOAD is recorded by the init event.               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_ws.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, mp, pr, im
vars == <<i, mp, pr, im>>
INSTANCE ConnectWsOps WITH MP <- mp, Wrong <- "none"

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_ws.ndjson")
Ev == Trace[i]
Ids == 1..5000

InitEv == /\ Ev.op = "init" /\ Ev.mp <= 65535 /\ mp' = Ev.mp /\ UNCHANGED <<pr, im>>

NewEv == /\ Ev.op = "new" /\ pr' = [pr EXCEPT ![Ev.id] = Ev.peer] /\ im' = [im EXCEPT ![Ev.id] = FALSE]
         /\ UNCHANGED mp

EncEv == LET r == Encode(Ev.code, Ev.pl, Ev.mask, Ev.cap) IN
         /\ Ev.op = "enc"
         /\ IF r.ok THEN Ev.res = "ok" /\ Ev.b = r.b ELSE Ev.res = r.e
         /\ UNCHANGED <<mp, pr, im>>

DecEv == LET r == Decode(pr[Ev.id], im[Ev.id], Ev.buf) IN
         /\ Ev.op = "dec"
         /\ CASE Ev.res = "idle" -> r.k = "idle" /\ UNCHANGED im
              [] Ev.res = "err" -> r.k = "err" /\ r.e = Ev.e /\ UNCHANGED im
              [] OTHER -> /\ r.k = "frame" /\ r.f = Ev.f /\ r.pl = Ev.pl /\ r.st = Ev.st /\ r.used = Ev.used
                          /\ im' = [im EXCEPT ![Ev.id] = r.inm]
         /\ UNCHANGED <<mp, pr>>

Init == i = 1 /\ mp = 0 /\ pr = [k \in Ids |-> ""] /\ im = [k \in Ids |-> FALSE]
Step == /\ i <= Len(Trace) /\ Ev.t = "ws" /\ (InitEv \/ NewEv \/ EncEv \/ DecEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == mp <= 65535
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
