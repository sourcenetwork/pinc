---------------------------- MODULE TraceDgramSize ----------------------------
(***************************************************************************)
(* Trace validation of the datagram sizes build_datagram writes            *)
(* (pinc-transport conn/send.rs) against DgramSize.tla.                    *)
(*                                                                         *)
(* The Rust test tests/trace_dgram_size.rs runs real connection pairs      *)
(* (first flights sent whole and cut, resumed dials with early data, MTU   *)
(* probes, interfaces of 1200 to 9000 bytes on IPv4 and IPv6, small and    *)
(* GSO buffers) with the `trace` feature's datagram log on. Every call of  *)
(* build_datagram records its inputs (the path's size, the interface MTU   *)
(* and family, the buffer, the amplification room, the probe size, the     *)
(* whole flight with its framing, the padding the handshake owes) and what *)
(* it wrote (the handshake fragment, the application packet, the padding,  *)
(* the length; 0 for no datagram).                                         *)
(*                                                                         *)
(* The model's inputs hs and app are what each part would take; the trace  *)
(* gives what each part took, which is the model's input exactly when the  *)
(* part took no more than its room. So each event is checked as the model  *)
(* input with hs and app set to the recorded parts: the fragment within    *)
(* the datagram's room, the packet within its room behind the fragment     *)
(* (App = app), the length, the packet and the padding equal to the        *)
(* model's, and every invariant of DgramSize.cfg on that input.            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dgram_size.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dgram_size.ndjson")

\* The model's input of the event the state stands on (only read when c.t = "event").
X == LET ev == Trace[c.i]
     IN [p |-> ev.p, f |-> ev.f, v6 |-> ev.v6 = 1, o |-> ev.o, a |-> ev.a, q |-> ev.q, fl |-> ev.fl,
         hs |-> ev.hs, app |-> ev.app, pad |-> ev.pad]

D == INSTANCE DgramSize WITH GUARD <- TRUE, IFACE <- TRUE, x <- X

Init == c = [t |-> "root"]

\* The padding the model writes: none without a datagram, all of the length when the datagram is the owed padding
\* alone, else Pad.
PadOf(i) == IF D!MaxLen(i) < D!MinRoom THEN 0
            ELSE IF D!Hs(i) = 0 /\ i.pad > 0 THEN D!Len(TRUE, i)
            ELSE D!Pad(TRUE, i)

EvOK(ev) ==
    /\ ev.t = "dgram"
    /\ D!Valid(X)
    \* the parts took no more than their rooms
    /\ ev.hs <= D!MaxLen(X)
    /\ D!Hs(X) = ev.hs
    /\ D!Pkt(TRUE, X) = ev.app
    \* the datagram is the model's
    /\ D!Len(TRUE, X) = ev.len
    /\ PadOf(X) = ev.pd
    /\ ev.len = (IF ev.len = 0 THEN 0 ELSE ev.hs + ev.app + ev.pd)
    \* the invariants of DgramSize.cfg, on this input
    /\ D!AppFits /\ D!SizeOK /\ D!Bounded /\ D!IfaceOK /\ D!Unchanged

(* Every event is an independent call, so the events are the states of one machine: the root state has one successor
   per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded datagram is the model's
EventsOK == c.t = "event" => EvOK(Trace[c.i])
=============================================================================
