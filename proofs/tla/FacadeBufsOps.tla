---------------------------- MODULE FacadeBufsOps ----------------------------
(***************************************************************************)
(* The receive and transmit buffer pools of the facade's endpoints,        *)
(* crates/pinc/src/drive.rs: `pools` (two shapes), `pooled`, `Buf::drop`, *)
(* `POOLED`. The receive and the transmit pool run the same two functions  *)
(* and never meet, so one pool kind is written; two endpoints of a thread  *)
(* are numbered 1 and 2.                                                   *)
(*                                                                         *)
(* A pool is a Vec used as a stack (push and pop at the end); a buffer is  *)
(* a record [id, len]; cap is the capacity of a pool's own Vec, whose      *)
(* growth is the allocation a buffer that goes back can cause. With `std`  *)
(* (std = TRUE) both endpoints take the thread's pool (pool 1, built empty *)
(* by `Pool::default()`, capacity 0); without it each has its own (pool e) *)
(* holding one buffer of its length from the build, with room for POOLED   *)
(* (`Vec::with_capacity(POOLED)`). A holder is a future holding at most    *)
(* one buffer of the pool (the driving future's receive buffer, a          *)
(* flush's transmit buffer).                                               *)
(*                                                                         *)
(* One thread drives an endpoint, so a pool is never borrowed when         *)
(* `pooled` or `Buf::drop` runs (the code's comment) and the branches the  *)
(* `try_borrow_mut` failure takes are not reached; they are not written.   *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANT POOLED
ASSUME POOLED \in Nat \ {0}

NoBuf == [id |-> 0, len |-> 0]
Home(std, e) == IF std THEN 1 ELSE e
Mx(a, b) == IF a < b THEN b ELSE a

\* the pools when the two endpoints are built (Shared::new -> pools), holders hs, buffer lengths lens
Built(std, hs, lens) ==
    IF std
    THEN [pools |-> <<<<>>, <<>>>>, cap |-> <<0, 0>>, held |-> [h \in hs |-> NoBuf], nb |-> 1]
    ELSE [pools |-> <<<<[id |-> 1, len |-> lens[1]]>>, <<[id |-> 2, len |-> lens[2]]>>>>,
          cap |-> <<POOLED, POOLED>>, held |-> [h \in hs |-> NoBuf], nb |-> 3]

\* `pooled(home, len)` for holder h of endpoint e: the last buffer of the pool cut or zero-extended to len, or a new
\* buffer of len bytes when the pool is empty
Take(std, st, h, e, len) ==
    LET q == Home(std, e)
        P == st.pools[q]
    IN IF Len(P) > 0
       THEN [st EXCEPT !.pools[q] = SubSeq(P, 1, Len(P) - 1), !.held[h] = [id |-> P[Len(P)].id, len |-> len]]
       ELSE [st EXCEPT !.held[h] = [id |-> st.nb, len |-> len], !.nb = st.nb + 1]

\* the buffer `pooled` hands out comes from the pool, and the length it had there
Popped(std, st, e) == Len(st.pools[Home(std, e)]) > 0
TopOf(std, st, e) == LET P == st.pools[Home(std, e)] IN P[Len(P)]

\* the capacity a Vec of capacity c grows to for one more element than c (the standard library's amortized growth:
\* twice the capacity, at least 4 for elements of this size); only the fact that it allocates matters here
Grown(c) == Mx(2 * c, 4)

\* `Buf::drop` of holder h of endpoint e: back onto the pool when it holds fewer than POOLED, else freed
Give(std, st, h, e) ==
    LET q == Home(std, e)
        P == st.pools[q]
    IN IF Len(P) < POOLED
       THEN [st EXCEPT !.pools[q] = Append(P, st.held[h]), !.held[h] = NoBuf,
                       !.cap[q] = IF Len(P) = st.cap[q] THEN Grown(st.cap[q]) ELSE st.cap[q]]
       ELSE [st EXCEPT !.held[h] = NoBuf]
=============================================================================
