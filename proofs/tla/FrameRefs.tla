------------------------------ MODULE FrameRefs ------------------------------
(***************************************************************************)
(* pinc-transport recovery/frame_ref.rs: FrameRefs, the frames one sent    *)
(* packet carried, kept for its acknowledgement or loss (FrameRefsOps.tla).*)
(* There is no encoding: the list lives in memory beside the packet's      *)
(* record, so the property is the documented list, not a round trip.       *)
(*                                                                         *)
(* Every sequence of pushes of the descriptors VALS (D0, the descriptor    *)
(* every place holds at the start, among them). pushed is the list the doc *)
(* describes: the frames in the order they were pushed, at most MAX.       *)
(* Checked:                                                                *)
(*  - Ordered: `as_slice` is exactly the frames pushed, in push order, and *)
(*    `len` and `is_empty` agree with it;                                  *)
(*  - Bounded: never more than MAX_FRAME_REFS;                             *)
(*  - RefusedKeeps: a push refused with FrameRefsFull changes nothing, and *)
(*    a push is refused only when the list is full.                        *)
(* FrameRefs_full is a reachability witness: the list fills, so the        *)
(* refusal is among the checked steps.                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS MAX, VALS, D0
ASSUME MAX >= 1 /\ D0 \in VALS
VARIABLES r, pushed, last
vars == <<r, pushed, last>>

INSTANCE FrameRefsOps

Init == r = FNew(MAX, D0) /\ pushed = <<>> /\ last = "init"
Push == \E f \in VALS :
    LET p == FPush(r, MAX, f)
    IN /\ r' = p.r
       /\ pushed' = IF Len(pushed) < MAX THEN Append(pushed, f) ELSE pushed
       /\ last' = IF p.ok THEN "pushed" ELSE "refused"
Next == Push
Spec == Init /\ [][Next]_vars

Ordered == /\ FSlice(r) = pushed
           /\ r.len = Len(pushed)
           /\ (r.len = 0) = (pushed = <<>>)
Bounded == r.len \in 0..MAX
RefusedKeeps == [][/\ last' = "refused" => (r' = r /\ r.len = MAX)
                   /\ last' = "pushed" => r.len < MAX]_vars

\* a reachability witness: the list fills
NotFull == r.len < MAX
=============================================================================
