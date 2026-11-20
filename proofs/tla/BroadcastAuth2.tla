------------------------------ MODULE BroadcastAuth2 ------------------------------
(***************************************************************************)
(* What a version 2 signature binds: pinc-broadcast auth2.rs `sign2` and   *)
(* `verify2`, with auth.rs `origin_signed` and pinc-crypto identity.rs     *)
(* `verify_node` (the key must match the origin's node id).                *)
(*                                                                         *)
(* Crypto is ideal and not modelled: a signature is the term <<signer,     *)
(* statement>> and exists only if the signer's key made it; the statement *)
(* stands for its content id (BroadcastStatement.tla shows the encoding is *)
(* injective; the hash is assumed collision free). A node is its own key:  *)
(* the node id of key k is k, and AlgOf(k) is its algorithm. Tag 1 is     *)
(* Ed25519, whose node id is the key itself (the verifier takes the key    *)
(* from the origin); every other tag carries the key in the head (pk) and  *)
(* the verifier requires it to be the origin's (KeyCheck).                 *)
(*                                                                         *)
(* Cover is the set of fields the statement holds: the code covers all of *)
(* them (alg, origin, inc, seq, topic, wall, ctr, flags, parents, body).   *)
(* sign2 refuses (writes nothing) for a key whose algorithm is not the     *)
(* fields' and for fields that make no statement (a reserved flag here);   *)
(* it does not check that the origin is the signer: an honest node signs   *)
(* only its own messages, a Byz node signs anything with its own key.      *)
(*                                                                         *)
(* The environment (every node that relays, the hubs, a node that carries  *)
(* the relay role) holds every signature made and presents the fields of   *)
(* one with any one field changed, any key in the head, and any held       *)
(* signature (Receive; junk never verifies, so it is left out); verify2's *)
(* verdict decides delivery. One                                           *)
(* changed field is enough: a message verifies iff its covered fields are  *)
(* those of the signature, so a change of several uncovered fields is      *)
(* found as soon as one of them is.                                        *)
(*                                                                         *)
(* Checked: DeliverExact (every delivered message whose origin is honest   *)
(* equals, in every field, one its origin signed). Witnesses:              *)
(* BroadcastAuth2_delivers.cfg (a message is delivered),                   *)
(* BroadcastAuth2_notopic.cfg (without the topic in the statement a        *)
(* message is accepted for another topic) and BroadcastAuth2_nokey.cfg     *)
(* (without the key check a Byz node's signature is accepted for an honest *)
(* sender). TraceBroadcastAuth2.tla checks the real sign2 and verify2      *)
(* against Verify.                                                         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Honest, Byz, Algs, Cover, KeyCheck, MaxSig, AlgOf(_)

\* the small configs: node 1 Ed25519, every other node a key-carrying algorithm
AlgSmall(n) == IF n = 1 THEN 1 ELSE 2

Nodes == Honest \union Byz
FieldNames == {"alg", "origin", "inc", "seq", "topic", "wall", "ctr", "flags", "parents", "body"}
Dom(x) == CASE x = "origin" -> Nodes [] x = "alg" -> Algs [] x = "flags" -> {0, 1, 2}
          [] x \notin {"origin", "alg", "flags"} -> {0, 1}
NoMsg == [none |-> TRUE]

\* fields that make a statement (statement.rs encode refuses a reserved flag; the other refusals are alike)
MakesStmt(g) == g.flags \in {0, 1}
Stmt(g) == [x \in Cover |-> g[x]]
FieldsOf(m) == [x \in FieldNames |-> m[x]]

\* the key the verifier checks the signature with: the origin itself for Ed25519, the head's key otherwise
PresentedKey(m) == IF m.alg = 1 THEN m.origin ELSE m.pk

\* verify2: the fields make a statement, the signature is by the presented key under the head's algorithm, the key
\* is the origin's (verify_node: the id matches the key), and it signed exactly this statement
Verify(m, sig) ==
    /\ MakesStmt(m)
    /\ sig[1] = PresentedKey(m)
    /\ AlgOf(sig[1]) = m.alg
    /\ KeyCheck => PresentedKey(m) = m.origin
    /\ sig[2] = Stmt(m)

Base(o, a, v, fl) == [alg |-> a, origin |-> o, inc |-> v, seq |-> v, topic |-> v, wall |-> v, ctr |-> v,
                      flags |-> fl, parents |-> v, body |-> v]
Near(g) == {g} \union UNION {{[g EXCEPT ![x] = y] : y \in Dom(x)} : x \in FieldNames}

VARIABLES made, dlv
vars == <<made, dlv>>

Sigs == {<<e[1], Stmt(e[2])>> : e \in made}
Published == {e[2] : e \in {d \in made : d[1] \in Honest}}

Init == made = {} /\ dlv = NoMsg

\* sign2 by key s over fields of origin o: refused (nothing made) for another algorithm or no statement
Sign ==
    /\ Cardinality(made) < MaxSig
    /\ \E s \in Nodes, o \in Nodes, a \in Algs, v \in {0, 1}, fl \in {0, 2} :
          /\ (s \in Byz \/ o = s)
          /\ LET g == Base(o, a, v, fl)
             IN made' = IF a = AlgOf(s) /\ MakesStmt(g) THEN made \union {<<s, g>>} ELSE made
    /\ UNCHANGED dlv

\* a relay presents a message near one it saw signed, with any key and any held signature
Receive ==
    /\ \E e \in made, k \in Nodes, sig \in Sigs :
          \E g \in Near(e[2]) :
             LET m == [x \in FieldNames \union {"pk"} |-> IF x = "pk" THEN k ELSE g[x]]
             IN dlv' = IF Verify(m, sig) THEN m ELSE dlv
    /\ UNCHANGED made

Next == Sign \/ Receive
Spec == Init /\ [][Next]_vars

DeliverExact == dlv = NoMsg \/ dlv.origin \in Byz \/ FieldsOf(dlv) \in Published

\* witness (must be violated): a message is delivered
NoDelivery == dlv = NoMsg
=============================================================================
