------------------------------- MODULE ExtInOps -------------------------------
(***************************************************************************)
(* The operations of vinc-core ext_in.rs (ExtRing), step for step: the     *)
(* extension frames received for the application, in a ring of CAP         *)
(* (EXT_SLOTS = 8) places, read oldest first. The ring is its head, its    *)
(* length and the frames in order (the cells from the head on; the code    *)
(* keeps them in an array and takes both ends modulo CAP, which the head   *)
(* tracks here).                                                           *)
(*                                                                         *)
(* A frame is <<id, session, ty, len>>: its place in the order of puts (0  *)
(* where a trace does not know it), its session and type, and the length   *)
(* of its body (the body itself is carried, not looked at; the trace       *)
(* compares its first byte). MX is EXT_BODY_MAX = 1200.                    *)
(*                                                                         *)
(* Put: a body longer than MX is refused and nothing changes; otherwise a  *)
(* full ring drops its oldest frame (the head moves on), and the frame is  *)
(* appended. Nothing counts the refusal or the dropped frame: the code     *)
(* has no counter (put returns whether the frame was kept, and the         *)
(* endpoint ignores it). Take: the oldest frame, or None for an empty      *)
(* ring, or, when it is longer than the buffer, its length with the frame  *)
(* left held. dropNewest is the wrong rule of a witness config: a full     *)
(* ring gives up the newest frame it holds, not the oldest.                *)
(***************************************************************************)
EXTENDS Integers, Sequences

None == "none"
Ring0 == [head |-> 0, len |-> 0, q |-> <<>>]

Front(q) == SubSeq(q, 1, Len(q) - 1)

EPut(r, cap, mx, it, dropNewest) ==
    IF it[4] > mx THEN [ok |-> FALSE, r |-> r]
    ELSE LET r1 == IF r.len = cap
                   THEN IF dropNewest
                        THEN [head |-> r.head, len |-> r.len - 1, q |-> Front(r.q)]
                        ELSE [head |-> (r.head + 1) % cap, len |-> r.len - 1, q |-> Tail(r.q)]
                   ELSE r
         IN [ok |-> TRUE, r |-> [head |-> r1.head, len |-> r1.len + 1, q |-> Append(r1.q, it)]]

\* res is "none" (empty ring), "err" (the oldest frame does not fit; out is its length) or "ok" (out is the frame)
ETake(r, cap, oc) ==
    IF r.len = 0 THEN [res |-> "none", r |-> r, out |-> None]
    ELSE IF r.q[1][4] > oc THEN [res |-> "err", r |-> r, out |-> r.q[1][4]]
    ELSE [res |-> "ok", r |-> [head |-> (r.head + 1) % cap, len |-> r.len - 1, q |-> Tail(r.q)], out |-> r.q[1]]
=============================================================================
