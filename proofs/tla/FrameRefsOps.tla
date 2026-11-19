---------------------------- MODULE FrameRefsOps ----------------------------
(***************************************************************************)
(* pinc-transport recovery/frame_ref.rs, FrameRefs: the fixed list of the  *)
(* frame descriptors a sent packet carried (`items: [FrameRef;            *)
(* MAX_FRAME_REFS]`, `len: u8`). The state r is [items, len]; items is a   *)
(* function 0..max-1 -> descriptor, every place D0 (`Control { kind: 0,    *)
(* id: 0 }`) at the start. FrameRefs.tla checks them; TraceFrameRefs.tla  *)
(* replays the real list.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

\* `new()`
FNew(max, d0) == [items |-> [j \in 0..(max - 1) |-> d0], len |-> 0]

\* `push(frame)`: Err(FrameRefsFull) and nothing changed when all max places are used, else the frame at place len
FPush(r, max, f) ==
    IF r.len = max THEN [ok |-> FALSE, r |-> r]
    ELSE [ok |-> TRUE, r |-> [items |-> [r.items EXCEPT ![r.len] = f], len |-> r.len + 1]]

\* `as_slice()` (and `iter()`, `into_iter()`): the first len places, in order
FSlice(r) == [j \in 1..r.len |-> r.items[j - 1]]
=============================================================================
