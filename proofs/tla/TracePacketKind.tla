-------------------------- MODULE TracePacketKind --------------------------
(***************************************************************************)
(* Trace validation of the classification of a packet's frames and the    *)
(* kind of packet the builder seals (PacketKind.tla): pinc-transport       *)
(* conn/recv.rs scan and process_payload, conn/send.rs build_app and       *)
(* fill_frames.                                                            *)
(*                                                                         *)
(* The Rust test tests/trace_packet_kind.rs records four kinds of event,   *)
(* each the frame kinds of one real packet in order:                       *)
(*  early  a 0-RTT packet sealed by a real resuming dialing side, with     *)
(*         crafted frames in front of its own (inject_frames), handed to   *)
(*         the resumed responder: r is "refused" when it returned          *)
(*         Drop::EarlyFrame and counted it in early_refused, else          *)
(*         "applied";                                                      *)
(*  short  the same frames in a 1-RTT packet handed to an established      *)
(*         responder (inject_payload): r as above;                         *)
(*  move   a 1-RTT packet, the highest numbered, on a validated direct     *)
(*         path while the active one is relayed (through a node that       *)
(*         carries the relay role): moved is whether the active path       *)
(*         moved to the packet's;                                          *)
(*  sent   every packet a real dialing side sealed in a resumed session    *)
(*         with early data and after it (trace_pack_take): its kind and    *)
(*         frames.                                                         *)
(* Each must be the model's: Decide for early and short, Scan's nonprobing *)
(* for move, and a 0-RTT packet sent is never one the receiver refuses.    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds packet_kind.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

P == INSTANCE PacketKind WITH FACTS <- TRUE, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/packet_kind.ndjson")

EvOK(ev) ==
    /\ ev.t = "pk"
    /\ \A k \in 1..Len(ev.frames) : ev.frames[k] \in P!Frames
    /\ CASE ev.op = "early" -> P!Decide(TRUE, ev.frames) = ev.r
         [] ev.op = "short" -> P!Decide(FALSE, ev.frames) = ev.r
         [] ev.op = "move" -> P!Scan(ev.frames).nonprobing = ev.moved
         [] ev.op = "sent" -> ev.kind \in {"zrtt", "short"} /\ (ev.kind = "zrtt" => P!Decide(TRUE, ev.frames) = "applied")
         [] OTHER -> FALSE

Init == c = 0
Next == UNCHANGED c
TraceSpec == Init /\ [][Next]_c

\* every recorded event is the model's (one state: the invariant quantifies over the events)
EventsOK == Len(Trace) > 0 /\ \A k \in 1..Len(Trace) : EvOK(Trace[k])
\* the end check (TraceEnd.tla): the one state checks every line of a trace that has one
ReplayAtEnd == ReplaySeen(TRUE)
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
