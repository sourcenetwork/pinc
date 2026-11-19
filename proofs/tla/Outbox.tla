-------------------------------- MODULE Outbox --------------------------------
(***************************************************************************)
(* The output queue of the handshake state machines (pinc-security        *)
(* outbox.rs, Outbox) against its documented contract, over every sequence *)
(* of calls: build, a refused build, clear_message, resend, set_request,   *)
(* take_request, the early keys and the established event, set_resume_    *)
(* rejected, fail and poll (OutboxOps.tla has the operators of the code).  *)
(*                                                                         *)
(* The module doc: "it holds at most one outgoing message (the last        *)
(* flight, kept so it can be sent again), at most one outstanding key      *)
(* request, and at most one of each event. poll hands them out in a fixed  *)
(* order (key request, message, early keys, established, failure) and each *)
(* exactly once; a failure discards everything else queued." Beside the    *)
(* code's record ob, the model keeps that contract as a set q of queued    *)
(* items (one per kind, as triples of PollOut's shape), the outstanding    *)
(* request pend and the kept message kept; each call changes them as the   *)
(* doc says, and poll takes the item of the lowest kind. The doc does not  *)
(* place the resume-rejected event; the code hands it out after the early  *)
(* keys and before the established event, and so does q.                  *)
(*                                                                         *)
(* Checked in every state:                                                 *)
(*  - TypeOK: the record holds one of each, by construction of the struct; *)
(*  - Agrees: what the code has queued is q (the request while it is not   *)
(*    announced, the message while send is set, each event), the request   *)
(*    it holds is pend, and the bytes and min_len in its buffer are the    *)
(*    kept message;                                                        *)
(*  - PollAgrees: the next poll of the code hands out the item of q of the *)
(*    lowest kind (nothing when q is empty), so each queued item is handed *)
(*    out once, in the fixed order, and after a failure the only item left *)
(*    is the failure.                                                      *)
(* FAILW is the number of bytes a refused build writes before its error.   *)
(* Outbox.cfg takes {0}: no caller of build can make it fail (every        *)
(* message fits MAX_MESSAGE_LEN, MessageCodec.tla Fits, and the fields     *)
(* that would overflow a length prefix cannot be built by the machines).   *)
(* Outbox_torn.cfg takes {1} and TLC finds Agrees violated: a refused      *)
(* build overwrites the head of the kept message while its length and     *)
(* send flag stay, so a later poll or resend would hand out torn bytes.    *)
(* The machines make that unreachable (BadPayload is fatal, settle calls   *)
(* fail, which clears send, and a failed machine never calls resend).      *)
(* Outbox_full.cfg is a reachability witness: every kind queued at once.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS KS, MLS, FAILW, REQS, EARLYS, ESTS, FAILS
VARIABLES ob, q, pend, kept
vars == <<ob, q, pend, kept>>

INSTANCE OutboxOps

NoKept == [d |-> <<>>, ml |-> -1]
None == <<0, <<>>, 0>>

\* the queue of the contract: one item per kind, the kind is the first field
Replace(Q, item) == {y \in Q : y[1] # item[1]} \cup {item}
Drop(Q, kind) == {y \in Q : y[1] # kind}
AbsPoll(Q) == IF Q = {} THEN None ELSE CHOOSE y \in Q : \A z \in Q : y[1] <= z[1]

Init == ob = Ob0 /\ q = {} /\ pend = 0 /\ kept = NoKept

Next ==
    \/ \E k \in KS, ml \in MLS :
          /\ ob' = Build(ob, k, ml)
          /\ q' = Replace(q, <<2, Msg(k), ml>>)
          /\ kept' = [d |-> Msg(k), ml |-> ml]
          /\ UNCHANGED pend
    \/ \E w \in FAILW : ob' = Refuse(ob, w) /\ UNCHANGED <<q, pend, kept>>
    \/ ob' = Clear(ob) /\ q' = Drop(q, 2) /\ kept' = NoKept /\ UNCHANGED pend
    \/ /\ ob' = Resend(ob)
       /\ q' = IF kept # NoKept THEN Replace(q, <<2, kept.d, kept.ml>>) ELSE q
       /\ UNCHANGED <<pend, kept>>
    \/ \E r \in REQS : ob' = SetRequest(ob, r) /\ q' = Replace(q, <<1, <<>>, r>>) /\ pend' = r /\ UNCHANGED kept
    \/ ob' = TakeRequest(ob) /\ q' = Drop(q, 1) /\ pend' = 0 /\ UNCHANGED kept
    \/ \E e \in EARLYS : ob' = SetEarly(ob, e) /\ q' = Replace(q, <<3, <<>>, e>>) /\ UNCHANGED <<pend, kept>>
    \/ ob' = SetRR(ob) /\ q' = Replace(q, <<4, <<>>, 0>>) /\ UNCHANGED <<pend, kept>>
    \/ \E e \in ESTS : ob' = SetEst(ob, e) /\ q' = Replace(q, <<5, <<>>, e>>) /\ UNCHANGED <<pend, kept>>
    \/ \E f \in FAILS : ob' = Fail(ob, f) /\ q' = {<<6, <<>>, f>>} /\ pend' = 0 /\ UNCHANGED kept
    \/ ob' = PollNext(ob) /\ q' = q \ {AbsPoll(q)} /\ UNCHANGED <<pend, kept>>
Spec == Init /\ [][Next]_vars

TypeOK == /\ ob.len \in 0..BUF
          /\ ob.buf \in [1..BUF -> {0, TORN} \cup KS]
          /\ ob.send \in BOOLEAN /\ ob.ann \in BOOLEAN /\ ob.rr \in BOOLEAN
          /\ ob.req \in {0} \cup REQS
          /\ ob.early \in {0} \cup EARLYS /\ ob.est \in {0} \cup ESTS /\ ob.failed \in {0} \cup FAILS

\* what the code has queued, as the contract's items
View(o) == (IF ~o.ann /\ o.req # 0 THEN {<<1, <<>>, o.req>>} ELSE {})
           \cup (IF o.send THEN {<<2, Data(o), o.minl>>} ELSE {})
           \cup (IF o.early # 0 THEN {<<3, <<>>, o.early>>} ELSE {})
           \cup (IF o.rr THEN {<<4, <<>>, 0>>} ELSE {})
           \cup (IF o.est # 0 THEN {<<5, <<>>, o.est>>} ELSE {})
           \cup (IF o.failed # 0 THEN {<<6, <<>>, o.failed>>} ELSE {})

Agrees == /\ View(ob) = q
          /\ ob.req = pend
          /\ IF ob.len > 0 THEN kept = [d |-> Data(ob), ml |-> ob.minl] ELSE kept = NoKept
PollAgrees == PollOut(ob) = AbsPoll(q)

\* a reachability witness: every kind is queued at once
NotAllQueued == Cardinality(q) < 6
=============================================================================
