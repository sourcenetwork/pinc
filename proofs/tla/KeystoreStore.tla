---------------------------- MODULE KeystoreStore ----------------------------
(***************************************************************************)
(* The software stores and the key host of pinc-keystore (software.rs,     *)
(* host.rs, lib.rs): the request and answer state machine.                 *)
(*                                                                         *)
(* A handle comes from one counter shared by all stores (KeyHandle::next), *)
(* a store is a table from handles to keys (an identity key of one of      *)
(* three algorithms, or a KEM key), and a key host binds handshake handles *)
(* to keys of one store. The machine adds keys, removes keys, binds        *)
(* handles and takes requests (sign with an algorithm, decapsulate) that   *)
(* the host answers from the binding and the store; a request is answered  *)
(* once, from the state at the time.                                       *)
(*                                                                         *)
(* Checked over every sequence of 6 steps, 2 stores, 2 handshake handles:  *)
(*   HandlesFresh    every handle is below the counter, appears once and   *)
(*                   in one table only, so a handle shown to another store *)
(*                   is unknown there                                      *)
(*   StateBounded    the entries held are at most the keys ever added      *)
(*   CounterGrows    (action) the counter never decreases and only an add  *)
(*                   moves it, by one                                      *)
(*   TablesChange    (action) a table only loses entries or gains one with *)
(*                   the fresh handle                                      *)
(*   BindingUnique   the host binds each handshake handle at most once     *)
(*   AnswerMatches   a sign request gets a signature of the algorithm asked*)
(*                   for or Failed, a decapsulation a secret or Failed;    *)
(*                   never the other kind                                  *)
(*   AnswerSound     a signature or a secret only for a bound key that the *)
(*                   store holds, of the right kind, with the algorithm    *)
(*   NoAnswerWithoutRequest  an answer exists only for a request taken     *)
(*   GenerateBounded  key generation draws at most 8 seeds, one for every  *)
(*                   algorithm but P-256                                   *)
(* TraceKeystore.tla checks the recorded calls against the operators.      *)
(* Lean counterpart: proofs/lean/Pinc/KeystoreStore.lean (add_fresh,       *)
(* add_inv, remove_removes, bind_nodup, answer_signature_iff,              *)
(* answer_sign_not_secret, answer_decap_not_signature, generate_bounded).  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLES next, tables, bound, req, ans, steps, taken, answered
vars == <<next, tables, bound, req, ans, steps, taken, answered>>

Stores == {0, 1}
Kinds == {"ed", "p256", "kem"}
Secs == {1, 2}
MaxSteps == 6
Idle == [kind |-> "none"]

Init == /\ next = 1
        /\ tables = [s \in Stores |-> {}]
        /\ bound = {}
        /\ req = Idle /\ ans = Idle
        /\ steps = 0 /\ taken = 0 /\ answered = 0

Add(s, k) == /\ steps < MaxSteps
             /\ tables' = [tables EXCEPT ![s] = @ \cup {[h |-> next, kind |-> k]}]
             /\ next' = next + 1
             /\ steps' = steps + 1
             /\ UNCHANGED <<bound, req, ans, taken, answered>>

Remove(s, h) == /\ steps < MaxSteps
                /\ tables' = [tables EXCEPT ![s] = {e \in @ : e.h # h}]
                /\ steps' = steps + 1
                /\ UNCHANGED <<next, bound, req, ans, taken, answered>>

(* the host serves store 0; bind replaces any earlier binding of the handle *)
Bind(sec, h) == /\ steps < MaxSteps
                /\ bound' = {b \in bound : b.sec # sec} \cup {[sec |-> sec, h |-> h]}
                /\ steps' = steps + 1
                /\ UNCHANGED <<next, tables, req, ans, taken, answered>>

Ask(r) == /\ steps < MaxSteps /\ req = Idle
          /\ req' = r /\ ans' = Idle /\ taken' = taken + 1
          /\ steps' = steps + 1
          /\ UNCHANGED <<next, tables, bound, answered>>

Lookup(h) == {e \in tables[0] : e.h = h}

(* the answer of KeyHost::answer *)
Answer(r) ==
    LET bs == {b \in bound : b.sec = r.sec}
        k == IF bs = {} THEN {} ELSE Lookup((CHOOSE b \in bs : TRUE).h)
        e == IF k = {} THEN [kind |-> "none"] ELSE CHOOSE e \in k : TRUE
    IN IF r.kind = "sign"
       THEN IF bs = {} \/ k = {} \/ e.kind = "kem" \/ e.kind # r.alg THEN [kind |-> "failed"]
            ELSE [kind |-> "signature", alg |-> e.kind]
       ELSE IF bs = {} \/ k = {} \/ e.kind # "kem" THEN [kind |-> "failed"]
            ELSE [kind |-> "secret"]

Serve == /\ req # Idle
         /\ ans' = Answer(req) /\ req' = Idle /\ answered' = answered + 1
         /\ UNCHANGED <<next, tables, bound, steps, taken>>

Reqs == {[kind |-> "sign", sec |-> sec, alg |-> a] : sec \in Secs, a \in {"ed", "p256"}}
        \cup {[kind |-> "decap", sec |-> sec] : sec \in Secs}

Next == \/ \E s \in Stores, k \in Kinds : Add(s, k)
        \/ \E s \in Stores, h \in 1..3 : Remove(s, h)
        \/ \E sec \in Secs, h \in 1..3 : Bind(sec, h)
        \/ \E r \in Reqs : Ask(r)
        \/ Serve

Spec == Init /\ [][Next]_vars

AllEntries == UNION {tables[s] : s \in Stores}
HandlesFresh ==
    /\ \A s \in Stores : \A e \in tables[s] : e.h < next
    /\ \A s, t \in Stores : s # t => \A e \in tables[s] : \A f \in tables[t] : e.h # f.h
    /\ \A s \in Stores : \A e, f \in tables[s] : e.h = f.h => e = f

StateBounded == Cardinality(AllEntries) <= next - 1
CounterGrows == [][next' >= next /\ (next' # next => \E s \in Stores, k \in Kinds : Add(s, k))]_vars
TablesChange ==
    [][\A s \in Stores : tables'[s] \subseteq tables[s] \/ \E k \in Kinds : tables'[s] = tables[s] \cup {[h |-> next, kind |-> k]}]_vars
BindingUnique == \A a, b \in bound : a.sec = b.sec => a = b

AnswerMatches ==
    /\ (ans.kind = "signature") => ans.alg \in {"ed", "p256"}
    /\ \A r \in Reqs : (r.kind = "sign") => Answer(r).kind \in {"signature", "failed"}
    /\ \A r \in Reqs : (r.kind = "decap") => Answer(r).kind \in {"secret", "failed"}
    /\ \A r \in Reqs : (r.kind = "sign" /\ Answer(r).kind = "signature") => Answer(r).alg = r.alg

AnswerSound ==
    \A r \in Reqs :
        /\ (Answer(r).kind = "signature") => \E b \in bound : b.sec = r.sec /\ \E e \in tables[0] : e.h = b.h /\ e.kind = r.alg
        /\ (Answer(r).kind = "secret") => \E b \in bound : b.sec = r.sec /\ \E e \in tables[0] : e.h = b.h /\ e.kind = "kem"
        /\ ~(\E b \in bound : b.sec = r.sec) => Answer(r).kind = "failed"

NoAnswerWithoutRequest == answered <= taken /\ (ans # Idle => answered >= 1)

Draws(alg, firstValid) == IF alg # "p256" THEN 1 ELSE IF firstValid < 8 THEN firstValid + 1 ELSE 0
GenerateBounded ==
    /\ \A a \in Kinds \ {"kem"} : \A j \in 0..9 : Draws(a, j) <= 8
    /\ \A j \in 0..7 : Draws("p256", j) = j + 1
    /\ Draws("p256", 8) = 0 /\ Draws("ed", 5) = 1
=============================================================================
