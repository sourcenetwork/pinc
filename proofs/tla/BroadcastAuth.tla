------------------------------ MODULE BroadcastAuth ------------------------------
(***************************************************************************)
(* Origin authentication of pinc-broadcast auth.rs and msg.rs (on_msg).    *)
(*                                                                         *)
(* A signature is an unforgeable oracle per identity: the term <<signer,   *)
(* statement>> exists only if the signer's Sign step produced it, and a    *)
(* verifier accepts a message only if its signature term names the         *)
(* message's origin as signer and the statement the message presents. The  *)
(* statement is the bytes `topic | mid | H(body) | ts | isb` (auth.rs      *)
(* `statement`); H is collision free (a body stands for its hash). Cover   *)
(* is the set of fields the statement holds: the code covers all five; the *)
(* witness configs drop one, and TLC finds a message that a relay rewrote  *)
(* and a receiver still delivered.                                         *)
(*                                                                         *)
(* The environment is every relay and hub: it holds every signature ever   *)
(* produced and may present any message made of any of them or of junk,    *)
(* with any origin, topic, id, body, timestamp and flag (Receive). Honest  *)
(* origins sign only through Publish. A second kind of origin, Byz, is     *)
(* controlled by the adversary: it signs any statement with its own key,   *)
(* which authenticates the message as the Byz node's, never as an honest   *)
(* node's.                                                                 *)
(*                                                                         *)
(* Checked: every delivered message equals, in every field, one that its  *)
(* origin published (DeliverExact). With a field dropped from Cover (the   *)
(* witness configs) a message that differs from every published one in     *)
(* that field alone is delivered, so DeliverExact is violated: each of the *)
(* five fields is needed.                                                  *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastAuth.lean (delivered_exact, *)
(* statement_injective, mutated_*_refused). TraceBroadcast.tla checks the  *)
(* recorded verdicts of the real code against Verify.                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Honest, Byz, Topics, Mids, Bodies, Stamps, Cover, MaxPub

Origins == Honest \union Byz
Fields == {"topic", "mid", "body", "ts", "isb"}
Junk == <<"junk", "junk">>

\* the statement of a message: the covered fields (the others are not in the signed bytes)
Stmt(m) == [f \in Cover |-> m[f]]

Shape == [origin : Origins, topic : Topics, mid : Mids, body : Bodies, ts : Stamps, isb : BOOLEAN]
SigTerms(S) == {<<s.by, s.stmt>> : s \in S}

VARIABLES pubd, dlv
vars == <<pubd, dlv>>

\* the signatures that exist: one per published message, made by its origin
Sigs == {<<p.origin, Stmt(p)>> : p \in pubd}

\* auth.rs verify: the signature is the origin's over exactly this statement
Verify(m, sig) == sig[1] = m.origin /\ sig[2] = Stmt(m)

NoMsg == [none |-> TRUE]

Init == pubd = {} /\ dlv = NoMsg

\* an origin signs and publishes a message (only its own key signs for it)
Publish ==
    /\ Cardinality(pubd) < MaxPub
    /\ \E m \in Shape : pubd' = pubd \union {m}
    /\ UNCHANGED dlv

\* a relay presents any message with any signature it holds; the receiver delivers it iff Verify says so
Receive ==
    /\ \E m \in Shape, sig \in Sigs \union {Junk} :
          dlv' = IF Verify(m, sig) THEN m ELSE dlv
    /\ UNCHANGED pubd

Next == Publish \/ Receive
Spec == Init /\ [][Next]_vars

TypeOK == pubd \subseteq Shape /\ (dlv = NoMsg \/ dlv \in Shape)

\* whatever a receiver delivered was published, field for field, by its origin
DeliverExact == dlv = NoMsg \/ dlv \in pubd
=============================================================================
