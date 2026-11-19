--------------------------- MODULE TraceConnectPack ---------------------------
(***************************************************************************)
(* Trace validation of the batch builder: carrier/frame.rs BatchBuilder.   *)
(*                                                                         *)
(* The Rust test tests/trace_connect_pack.rs runs the real BatchBuilder    *)
(* over buffers of every length from the real size down to one smaller     *)
(* than the header room, offering frames of every kind and size (packets   *)
(* with a short and a long header, sleep notices, BATCH frames, frames the *)
(* encoder refuses), rebuilding the builder from its state now and then,   *)
(* and closing the batch. It writes each offer with the frame's encoded    *)
(* length and kind, the answer and the number of frames held, and each     *)
(* close with the kind of record, its length and the lengths of the frames *)
(* the real decoder reads back from it. Every event must be the step the   *)
(* operators of ConnectPackOps.tla (Offer, Seal) compute.                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_pack.ndjson.  *)
(***************************************************************************)
EXTENDS ConnectPackOps, Json, IOUtils

VARIABLES i, c, st
vars == <<i, c, st>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_pack.ndjson")
Ev == Trace[i]

Init == i = 1 /\ c = [F |-> 1, B |-> 1, Head |-> 5, Cap |-> 0] /\ st = Empty

New == /\ Ev.t = "bbnew"
       /\ c' = [F |-> Ev.f, B |-> Ev.b, Head |-> Ev.head, Cap |-> Ev.cap]
       /\ st' = Empty /\ i' = i + 1

OfferEv == /\ Ev.t = "bboffer"
           /\ LET r == Offer(c, st, [n |-> Ev.n, long |-> Ev.long, isbatch |-> Ev.isbatch, bad |-> Ev.bad,
                                     err |-> Ev.err, raw |-> <<>>]) IN
              /\ r.r = Ev.res /\ r.e = Ev.e
              /\ Count(r.st) = Ev.cnt
              /\ st' = r.st
           /\ c' = c /\ i' = i + 1

FinEv == /\ Ev.t = "bbfin"
         /\ LET r == Seal(c, st) IN
            /\ r.kind = Ev.kind /\ r.ok
            /\ r.len = Ev.len
            /\ st.lens = Ev.lens
         /\ st' = Empty /\ c' = c /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (New \/ OfferEv \/ FinEv)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectPackOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
