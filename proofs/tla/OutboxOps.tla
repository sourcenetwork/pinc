------------------------------ MODULE OutboxOps ------------------------------
(***************************************************************************)
(* The output queue of the handshake state machines (pinc-security        *)
(* outbox.rs, Outbox), one operator per method, on a record o with the     *)
(* fields of the struct:                                                   *)
(*   len, buf   the message buffer: the length of the message and its     *)
(*              first BUF bytes (the model's messages are at most BUF      *)
(*              bytes; the buffer of the code is MAX_MESSAGE_LEN);         *)
(*   minl       min_len; send; announced (ann);                            *)
(*   req        the outstanding request, by mark (0 none);                 *)
(*   early, est the early keys and the established event, by mark (0 none);*)
(*   rr         resume_rejected; failed: the failure, by code (0 none).    *)
(* A message built with mark k is k bytes of value k (Build); a refused    *)
(* build (a write closure that fails) has written w bytes of value 9 into  *)
(* the buffer before its error and keeps len, min_len and send (Refuse):   *)
(* build maps the error to BadPayload after the closure ran.               *)
(* PollOut is the item poll hands out, as a triple <<code, data, x>>:      *)
(* 0 nothing, 1 key request (x its mark), 2 message (data, x its min_len), *)
(* 3 early keys, 4 resume rejected, 5 established (x the mark), 6 failure  *)
(* (x the code); PollNext the state after it. The triples have one shape   *)
(* so that TLC compares them field by field and labels carry no strings.   *)
(***************************************************************************)
EXTENDS Integers, Sequences

BUF == 2
TORN == 9

Ob0 == [len |-> 0, buf |-> <<0, 0>>, minl |-> 0, send |-> FALSE, req |-> 0, ann |-> FALSE,
        early |-> 0, est |-> 0, rr |-> FALSE, failed |-> 0]

Fill(buf, k, v) == [i \in 1..BUF |-> IF i <= k THEN v ELSE buf[i]]
Msg(k) == [i \in 1..k |-> k]
Data(o) == SubSeq(o.buf, 1, o.len)

\* build: the closure writes the message, then len, min_len and send are set
Build(o, k, ml) == [o EXCEPT !.buf = Fill(@, k, k), !.len = k, !.minl = ml, !.send = TRUE]
\* build whose closure fails after writing w bytes: only the bytes written change
Refuse(o, w) == [o EXCEPT !.buf = Fill(@, w, TORN)]
\* clear_message
Clear(o) == [o EXCEPT !.len = 0, !.send = FALSE]
\* resend
Resend(o) == [o EXCEPT !.send = o.len > 0]
\* set_request
SetRequest(o, r) == [o EXCEPT !.req = r, !.ann = FALSE]
\* take_request (returns o.req)
TakeRequest(o) == [o EXCEPT !.req = 0, !.ann = FALSE]
\* the public fields early and established, assigned by the machines
SetEarly(o, e) == [o EXCEPT !.early = e]
SetEst(o, e) == [o EXCEPT !.est = e]
\* set_resume_rejected
SetRR(o) == [o EXCEPT !.rr = TRUE]
\* fail: announced and the buffer are left as they are
Fail(o, f) == [o EXCEPT !.send = FALSE, !.req = 0, !.early = 0, !.est = 0, !.rr = FALSE, !.failed = f]

\* poll, in the order of the code
PollOut(o) ==
    IF ~o.ann /\ o.req # 0 THEN <<1, <<>>, o.req>>
    ELSE IF o.send THEN <<2, Data(o), o.minl>>
    ELSE IF o.early # 0 THEN <<3, <<>>, o.early>>
    ELSE IF o.rr THEN <<4, <<>>, 0>>
    ELSE IF o.est # 0 THEN <<5, <<>>, o.est>>
    ELSE IF o.failed # 0 THEN <<6, <<>>, o.failed>>
    ELSE <<0, <<>>, 0>>
PollNext(o) ==
    IF ~o.ann /\ o.req # 0 THEN [o EXCEPT !.ann = TRUE]
    ELSE IF o.send THEN [o EXCEPT !.send = FALSE]
    ELSE IF o.early # 0 THEN [o EXCEPT !.early = 0]
    ELSE IF o.rr THEN [o EXCEPT !.rr = FALSE]
    ELSE IF o.est # 0 THEN [o EXCEPT !.est = 0]
    ELSE [o EXCEPT !.failed = 0]
=============================================================================
