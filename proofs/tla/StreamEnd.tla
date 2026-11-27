------------------------------- MODULE StreamEnd -------------------------------
(***************************************************************************)
(* The end of a received stream and the events that announce it           *)
(* (pinc-transport conn/recv.rs, which pushes Readable for a STREAM frame; *)
(* the readers that act on StreamReadable: pinc-sim suite/node/events.rs   *)
(* read_stream, pinc-node hub_readable, the pinc engine).                  *)
(*                                                                         *)
(* The story. The peer sends the last frame of a stream (its bytes and its *)
(* end) and sends it again while no acknowledgement came back: up to C     *)
(* copies arrive. A frame may raise StreamReadable. A reader that handles  *)
(* the event reads what is there; the first read takes the bytes and the   *)
(* end, and reports the end to its layers. A read after that finds the end *)
(* again (Consume of 0 bytes answers Finished while the stream is kept for *)
(* its send half).                                                         *)
(*                                                                         *)
(* What must never happen: StreamReadable for a frame that brought nothing *)
(* new (Fresh: "A stream has bytes to read"); the end reported to the      *)
(* layers twice (EndOnce).                                                 *)
(*                                                                         *)
(* RED configurations:                                                     *)
(*  - StreamEnd_stale: every frame raises the event (the code before the   *)
(*    fix of conn/recv.rs): Fresh fails.                                   *)
(*  - StreamEnd_twice: that, and a reader that reports every Finished it   *)
(*    reads (the code before the fix of read_stream): EndOnce fails, as in *)
(*    EPHYRA_REPLAY=11:148 of world.                                       *)
(*                                                                         *)
(* Why the earlier models let it through: StreamsAnnounce and EvQueueOps   *)
(* check the event queue and the stream table on their own, each copy of a *)
(* frame taken as news; none had a reader that acts on a late event.       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS C, ALWAYS_EVENT, REPORT_AGAIN

VARIABLES copies, got, read, events, stale, ends
vars == <<copies, got, read, events, stale, ends>>

Init == copies = 0 /\ got = FALSE /\ read = FALSE /\ events = 0 /\ stale = 0 /\ ends = 0

\* A copy of the last frame arrives.
Arrive == /\ copies < C
          /\ copies' = copies + 1
          /\ got' = TRUE
          /\ IF ~got \/ ALWAYS_EVENT
             THEN /\ events' = 1  \* Readable events of one stream coalesce in the queue
                  /\ stale' = IF got THEN stale + 1 ELSE stale
             ELSE UNCHANGED <<events, stale>>
          /\ UNCHANGED <<read, ends>>

\* The reader handles StreamReadable.
Handle == /\ events > 0
          /\ events' = 0
          /\ IF got /\ ~read
             THEN read' = TRUE /\ ends' = ends + 1
             ELSE /\ read' = read
                  /\ ends' = IF read /\ REPORT_AGAIN THEN ends + 1 ELSE ends
          /\ UNCHANGED <<copies, got, stale>>

Next == Arrive \/ Handle
Spec == Init /\ [][Next]_vars

Fresh == stale = 0
EndOnce == ends <= 1
=============================================================================
