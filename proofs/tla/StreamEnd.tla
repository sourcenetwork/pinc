------------------------------- MODULE StreamEnd -------------------------------
(***************************************************************************)
(* The end of a received stream and the events that announce it           *)
(* (pinc-transport stream/recv.rs on_data and store, stream/table.rs      *)
(* on_stream_frame, which say whether a frame brought something new;       *)
(* conn/recv.rs, which pushes Readable only then; the readers that act on  *)
(* StreamReadable: pinc-sim suite/node/events.rs read_stream, pinc-node    *)
(* hub_readable, the pinc engine).                                         *)
(*                                                                         *)
(* The story. The peer sends the last bytes of a stream and its end, in    *)
(* one frame ("be") or apart ("b", then an empty frame with the end, "e"),  *)
(* and sends them again while no acknowledgement came back: up to C        *)
(* frames arrive, of any of the three kinds and in any order. A frame is   *)
(* new when it brings bytes not held yet or the end for the first time     *)
(* (on_data: held < end - lo, or the final size newly known); only a new   *)
(* frame raises StreamReadable. The core's event queue does not merge the  *)
(* events of two datagrams, so each new frame queues one. A reader that    *)
(* handles the event reads what is there; once the bytes are read and the  *)
(* end known, the read answers Finished, and the first Finished reports    *)
(* the end to its layers. A read after that finds the end again (Consume   *)
(* of 0 bytes answers Finished while the stream is kept for its send       *)
(* half).                                                                  *)
(*                                                                         *)
(* What must never happen: StreamReadable for a frame that brought nothing *)
(* new (Fresh: "A stream has bytes to read"); the end reported to the      *)
(* layers twice (EndOnce); the bytes and the end both there with no event  *)
(* left to wake the reader and the end not reported (Woken).               *)
(*                                                                         *)
(* RED configurations:                                                     *)
(*  - StreamEnd_stale: every frame raises the event (the code before the   *)
(*    fix of conn/recv.rs): Fresh fails.                                   *)
(*  - StreamEnd_twice: that, and a reader that reports every Finished it   *)
(*    reads (the code before the fix of read_stream): EndOnce fails, as in *)
(*    EPHYRA_REPLAY=11:148 of world.                                       *)
(*  - StreamEnd_queued: the transport fix alone, with the reader before    *)
(*    its fix: the bytes and the end arrive apart, two new frames queue two *)
(*    events, and the second Finished is reported again: EndOnce fails, so *)
(*    the reader's fix is needed too.                                      *)
(*  - StreamEnd_bytesonly: only new bytes count as new, an end alone does  *)
(*    not: the end that arrives after its bytes wakes nobody: Woken fails. *)
(*                                                                         *)
(* Why the earlier models let it through: StreamsAnnounce and EvQueueOps   *)
(* check the event queue and the stream table on their own, each copy of a *)
(* frame taken as news; none had a reader that acts on a late event.       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS C, ALWAYS_EVENT, REPORT_AGAIN, BYTES_ONLY

Kinds == {"b", "be", "e"}

\* frames: arrived so far; bytes, fin: what the stream holds; events: StreamReadable queued; read: the bytes were read;
\* told: the end was reported; stale: events raised for a frame that brought nothing new; ends: reports of the end
VARIABLES frames, bytes, fin, events, read, told, stale, ends
vars == <<frames, bytes, fin, events, read, told, stale, ends>>

Init == /\ frames = 0 /\ bytes = FALSE /\ fin = FALSE /\ events = 0
        /\ read = FALSE /\ told = FALSE /\ stale = 0 /\ ends = 0

\* A frame of kind k arrives.
Arrive(k) ==
    LET nb == k \in {"b", "be"} /\ ~bytes
        ne == k \in {"e", "be"} /\ ~fin
        news == nb \/ (ne /\ ~BYTES_ONLY)
        raise == news \/ ALWAYS_EVENT
    IN /\ frames < C
       /\ frames' = frames + 1
       /\ bytes' = (bytes \/ k \in {"b", "be"})
       /\ fin' = (fin \/ k \in {"e", "be"})
       /\ events' = IF raise THEN events + 1 ELSE events
       /\ stale' = IF raise /\ ~news THEN stale + 1 ELSE stale
       /\ UNCHANGED <<read, told, ends>>

\* The reader handles one StreamReadable.
Handle ==
    /\ events > 0
    /\ events' = events - 1
    /\ read' = (read \/ bytes)
    /\ IF bytes /\ fin
       THEN /\ told' = TRUE
            /\ ends' = IF ~told \/ REPORT_AGAIN THEN ends + 1 ELSE ends
       ELSE UNCHANGED <<told, ends>>
    /\ UNCHANGED <<frames, bytes, fin, stale>>

Next == (\E k \in Kinds : Arrive(k)) \/ Handle
Spec == Init /\ [][Next]_vars

Fresh == stale = 0
EndOnce == ends <= 1
Woken == (bytes /\ fin) => (told \/ events > 0)
=============================================================================
