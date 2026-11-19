------------------------------ MODULE MbtOutbox ------------------------------
(***************************************************************************)
(* Model-based tests of the handshake's output queue (pinc-security        *)
(* outbox.rs, Outbox, through the OutboxProbe of the cargo feature         *)
(* `trace`): the state graph of the operators of OutboxOps.tla, for        *)
(* tests/mbt_outbox.rs to walk. One action per call of the code, with its  *)
(* result as a parameter where it has one (as in MbtHalfOpen.tla):         *)
(*   CallBuild(k, ml)    build a message of k bytes of value k, min_len ml;*)
(*   CallRefuse(w)       build with a closure that writes w bytes of value *)
(*                       9 and then fails (build returns BadPayload);      *)
(*   CallClear, CallResend, CallRR (set_resume_rejected);                  *)
(*   CallSetRequest(r)   set_request of the request of mark r;             *)
(*   CallTake(r)         take_request, which returned the request of mark  *)
(*                       r (0 none);                                       *)
(*   CallPending(r)      pending(), which returned mark r (0 none);        *)
(*   CallEarly(e), CallEst(e)  the early keys or the established event of  *)
(*                       mark e assigned;                                  *)
(*   CallFail(f)         fail with the failure of code f;                  *)
(*   CallPoll(out)       poll, which handed out out (PollOut's triple).    *)
(* The state is the record of the code (OutboxOps.tla), which the test     *)
(* reads through the probe after every call and compares field by field.  *)
(* The refused builds are in the graph with the code's behaviour (the      *)
(* bytes written stay, the length and send flag too), so the test checks   *)
(* the code as it is; Outbox.tla states the contract it is compared with.  *)
(* The graph is finite: no constraint.                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS KS, MLS, FAILW, REQS, EARLYS, ESTS, FAILS
VARIABLE ob

INSTANCE OutboxOps

Datas == UNION {[1..n -> {0, TORN} \cup KS] : n \in 0..BUF}
Outs == {<<0, <<>>, 0>>, <<4, <<>>, 0>>}
        \cup {<<1, <<>>, r>> : r \in REQS}
        \cup {<<2, d, ml>> : d \in Datas, ml \in MLS}
        \cup {<<3, <<>>, e>> : e \in EARLYS}
        \cup {<<5, <<>>, e>> : e \in ESTS}
        \cup {<<6, <<>>, f>> : f \in FAILS}

Init == ob = Ob0

CallBuild(k, ml) == ob' = Build(ob, k, ml)
CallRefuse(w) == ob' = Refuse(ob, w)
CallClear == ob' = Clear(ob)
CallResend == ob' = Resend(ob)
CallSetRequest(r) == ob' = SetRequest(ob, r)
CallTake(r) == r = ob.req /\ ob' = TakeRequest(ob)
CallPending(r) == r = ob.req /\ UNCHANGED ob
CallEarly(e) == ob' = SetEarly(ob, e)
CallEst(e) == ob' = SetEst(ob, e)
CallRR == ob' = SetRR(ob)
CallFail(f) == ob' = Fail(ob, f)
CallPoll(out) == out = PollOut(ob) /\ ob' = PollNext(ob)

Next ==
    \/ \E k \in KS, ml \in MLS : CallBuild(k, ml)
    \/ \E w \in FAILW : CallRefuse(w)
    \/ CallClear
    \/ CallResend
    \/ \E r \in REQS : CallSetRequest(r)
    \/ \E r \in {0} \cup REQS : CallTake(r)
    \/ \E r \in {0} \cup REQS : CallPending(r)
    \/ \E e \in EARLYS : CallEarly(e)
    \/ \E e \in ESTS : CallEst(e)
    \/ CallRR
    \/ \E f \in FAILS : CallFail(f)
    \/ \E out \in Outs : CallPoll(out)
Spec == Init /\ [][Next]_ob

\* every call has its result in the set Next ranges over
Complete == PollOut(ob) \in Outs /\ ob.req \in {0} \cup REQS
=============================================================================
