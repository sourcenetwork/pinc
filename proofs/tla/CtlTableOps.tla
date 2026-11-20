----------------------------- MODULE CtlTableOps -----------------------------
(***************************************************************************)
(* The control-frame state of a connection, pinc-transport conn/ctl.rs     *)
(* (Ctl, and `apply` for the control frame references of a packet), step   *)
(* for step, with the glue of its callers that sets the flags: drive.rs    *)
(* `issue_tickets` and `send_ready`, send.rs building the tickets, READY   *)
(* and extension frames, recv.rs clearing `tickets_pending` when tickets   *)
(* are acknowledged. CtlTable.tla checks them; TraceCtlTable.tla replays   *)
(* them.                                                                   *)
(*                                                                         *)
(* The state c is [tab, nk, ready, tk, tp, ext, ne]: tab the stream-frame  *)
(* table (each place 0 for None or the key it holds; the frame itself goes *)
(* back to the stream layer whole and is not looked into), nk `next_key`,  *)
(* ready, tk the ticket batch held (0 for None, else its generation), tp   *)
(* `tickets_pending`, ext the extension slots ([on, key, pend]), ne        *)
(* `next_ext`. The pool is the number of chunks charged, of p. Kinds:      *)
(* "sc" K_STREAM_CTL, "ext" K_EXT, "tk" K_TICKETS, "rd" K_READY.           *)
(***************************************************************************)
EXTENDS Integers

NoExt == [on |-> FALSE, key |-> 0, pend |-> FALSE]
CNew(t, e) == [tab |-> [j \in 0..(t - 1) |-> 0], nk |-> 1, ready |-> FALSE, tk |-> 0, tp |-> FALSE,
               ext |-> [j \in 0..(e - 1) |-> NoExt], ne |-> 1]

Places(f) == DOMAIN f
\* the first place satisfying a predicate, as `iter().find`, or -1
FirstFreeTab(c) == IF \E j \in Places(c.tab) : c.tab[j] = 0
                   THEN CHOOSE j \in Places(c.tab) : c.tab[j] = 0 /\ \A m \in Places(c.tab) : m < j => c.tab[m] # 0
                   ELSE -1
FirstKeyTab(c, key) == IF \E j \in Places(c.tab) : c.tab[j] = key /\ key # 0
                       THEN CHOOSE j \in Places(c.tab) : c.tab[j] = key /\ \A m \in Places(c.tab) : m < j => c.tab[m] # key
                       ELSE -1
FirstFreeExt(c) == IF \E j \in Places(c.ext) : ~c.ext[j].on
                   THEN CHOOSE j \in Places(c.ext) : ~c.ext[j].on /\ \A m \in Places(c.ext) : m < j => c.ext[m].on
                   ELSE -1
FirstKeyExt(c, key) ==
    IF \E j \in Places(c.ext) : c.ext[j].on /\ c.ext[j].key = key
    THEN CHOOSE j \in Places(c.ext) : c.ext[j].on /\ c.ext[j].key = key
                                      /\ \A m \in Places(c.ext) : m < j => ~(c.ext[m].on /\ c.ext[m].key = key)
    ELSE -1

\* `track(frame)`: the key of the frame now in flight, or refused (ok FALSE) when the table is full
Track(c) == LET j == FirstFreeTab(c)
            IN IF j < 0 THEN [ok |-> FALSE, key |-> 0, c |-> c]
               ELSE [ok |-> TRUE, key |-> c.nk, c |-> [c EXCEPT !.tab[j] = c.nk, !.nk = c.nk + 1]]
\* `take(key)`: the frame out of the table (ok), or nothing
Take(c, key) == LET j == FirstKeyTab(c, key)
                IN IF j < 0 THEN [ok |-> FALSE, c |-> c] ELSE [ok |-> TRUE, c |-> [c EXCEPT !.tab[j] = 0]]

\* `hold_ext(pool, ty, body)`: refused with no free slot, a body over EXT_BODY_MAX (long) or no chunk; else the
\* frame waits to be sent, its body in one chunk
HoldExt(c, used, p, long) ==
    LET j == FirstFreeExt(c)
    IN IF j < 0 \/ long \/ used >= p THEN [ok |-> FALSE, c |-> c, used |-> used]
       ELSE [ok |-> TRUE, c |-> [c EXCEPT !.ext[j] = [on |-> TRUE, key |-> c.ne, pend |-> TRUE], !.ne = c.ne + 1],
             used |-> used + 1]
\* `free_ext`: the slot emptied and its chunk given back
FreeExt(c, used, j) == IF c.ext[j].on THEN [c |-> [c EXCEPT !.ext[j] = NoExt], used |-> used - 1]
                       ELSE [c |-> c, used |-> used]
\* send.rs: a waiting extension frame put in a packet
SendExt(c, j) == [c EXCEPT !.ext[j].pend = FALSE]

\* drive.rs `issue_tickets`: batch g held, to be sent
Issue(c, g) == [c EXCEPT !.tk = g, !.tp = TRUE]
\* send.rs: the held batch put in a packet when pending (ok), with its generation
SendTickets(c) == IF c.tp /\ c.tk # 0 THEN [ok |-> TRUE, g |-> c.tk, c |-> [c EXCEPT !.tp = FALSE]]
                  ELSE [ok |-> FALSE, g |-> 0, c |-> c]
\* drive.rs `send_ready`; send.rs building READY
SendReady(c) == [c EXCEPT !.ready = TRUE]
BuildReady(c) == IF c.ready THEN [ok |-> TRUE, c |-> [c EXCEPT !.ready = FALSE]] ELSE [ok |-> FALSE, c |-> c]

\* `acked(kind, id)` for a reference of batch g, then the recv.rs glue (`tickets_acked` clears `tickets_pending`).
\* layer: what the stream layer is handed ("acked" or "none"). With doc, an acknowledgement of tickets clears only the
\* batch it carried (the doc of `issue_tickets`, and the code with fix T1: `tickets_acked(gen)`); without, the code
\* before T1: any.
Acked(c, used, k, id, g, doc) ==
    CASE k = "sc" -> LET t == Take(c, id) IN [c |-> t.c, used |-> used, layer |-> IF t.ok THEN "acked" ELSE "none"]
      [] k = "ext" -> LET j == FirstKeyExt(c, id)
                      IN IF j < 0 THEN [c |-> c, used |-> used, layer |-> "none"]
                         ELSE LET f == FreeExt(c, used, j) IN [c |-> f.c, used |-> f.used, layer |-> "none"]
      [] k = "tk" -> IF doc /\ c.tk # g THEN [c |-> c, used |-> used, layer |-> "none"]
                     ELSE [c |-> [c EXCEPT !.tk = 0, !.tp = FALSE], used |-> used, layer |-> "none"]
      [] OTHER -> [c |-> c, used |-> used, layer |-> "none"]

\* `lost(kind, id)` of a packet to be requeued; layer: "lost" when the stream layer is handed its frame back. For
\* tickets of batch g: with doc (the code with fix T1, `tickets_lost(gen)`) only the batch held is pending again, a
\* newer one is left as it is; without, the code before T1: whatever is held.
Lost(c, k, id, g, doc) ==
    CASE k = "sc" -> LET t == Take(c, id) IN [c |-> t.c, layer |-> IF t.ok THEN "lost" ELSE "none"]
      [] k = "ext" -> LET j == FirstKeyExt(c, id)
                      IN [c |-> IF j < 0 THEN c ELSE [c EXCEPT !.ext[j].pend = TRUE], layer |-> "none"]
      [] k = "tk" -> IF doc /\ c.tk # g THEN [c |-> c, layer |-> "none"]
                     ELSE [c |-> [c EXCEPT !.tp = (c.tk # 0)], layer |-> "none"]
      [] k = "rd" -> [c |-> [c EXCEPT !.ready = TRUE], layer |-> "none"]
      [] OTHER -> [c |-> c, layer |-> "none"]
=============================================================================
