------------------------------ MODULE ReplyPath ------------------------------
(***************************************************************************)
(* The path a dialing side's handshake reply arrives on (vinc#399), and    *)
(* the bound of the path table for every path a connection learns by       *)
(* receiving on it, through the operators of PathOps.tla (conn/recv.rs     *)
(* handle_inner, on_handshake, process_payload; conn/drive.rs              *)
(* follow_reply; conn/path.rs learn_path, new_path_slot, add_path,         *)
(* remove_path).                                                           *)
(*                                                                         *)
(* Who acts. One connection, a dialing side or a responder (Roles). The    *)
(* network and an attacker deliver any datagram on any path (Ids): what    *)
(* its handshake packet completes (Kinds) is theirs to choose, and a 1-RTT *)
(* packet may follow it in the same datagram. The key host answers         *)
(* a Reply's request. The host adds and removes paths. A dialing side     *)
(* starts from any table its endpoint can give it: the dialed path         *)
(* validated and active in the first slot, the other slots empty or        *)
(* holding another path, validated or not (a parent session hands its     *)
(* validated paths to a sub-session, adopt_paths). A responder starts with *)
(* no path.                                                                *)
(*                                                                         *)
(* Checked in every reachable state, for every input from it:              *)
(*  ReplyTaken  a dialing side takes a reply on any path, held or not: a   *)
(*              message that authenticates establishes the session, on the *)
(*              path it came on (held, validated, active) unless that path *)
(*              is not held and the table has no room, and then the table  *)
(*              and the active path are as they were; a Reply that passed  *)
(*              its first checks waits for the key host with its path;     *)
(*  KeyTaken    a key answer that establishes moves the session to the     *)
(*              path the Reply came on, by the same rule;                  *)
(*  Quiet       before the session is established, a datagram whose       *)
(*              message does not authenticate and a key answer that does   *)
(*              not establish change no path state: no path added or given *)
(*              up, the active path as it was, no round trip sample;       *)
(*  Counted     one that fails authentication is counted, on any path;    *)
(*  GiveUpRule  a step of either role gives a path up only when every     *)
(*              slot is held, and only an unvalidated path that is not the *)
(*              active one, one path at most (remove_path aside, which the *)
(*              host asks for): a reply with a 1-RTT packet behind it at a *)
(*              full table gives up one path, not the one it moves from;   *)
(*  LeavesRule  a session that moves to the path its Reply came on leaves  *)
(*              the path it was on according to its kind: a direct path   *)
(*              is no longer validated, a relay path stays valid for as   *)
(*              long as the connection tracks it; RelayValid, a relay      *)
(*              path the connection holds is validated, in every state;    *)
(*  Unique      no path is held twice, also when a 1-RTT packet follows    *)
(*              the reply that learnt the path in the same datagram;       *)
(*              ActiveHeld, ActiveValid, KeyWaits;                         *)
(*  RankRule    the choice of the active path moves the session onto a     *)
(*              relay path that is not seen only from an active path       *)
(*              that is not usable or has failed PTO_FALLBACK probe        *)
(*              timeouts, and only when no usable path is seen or is a     *)
(*              direct path (the choice is made from the table as it       *)
(*              is, and after the endpoint named a path's kind);           *)
(*  EscapeRule  an active relay path that is not seen and failed           *)
(*              PTO_FALLBACK probe timeouts gives way to a usable path     *)
(*              that is not such a relay path, when there is one;          *)
(*  BackRule    after the session leaves a relay path at the probe-        *)
(*              timeout bound with nothing acknowledged on it, it does     *)
(*              not go back to that path while the path it moved to is     *)
(*              usable and nothing was acknowledged on the path it         *)
(*              left (a stamp on the path it left is not an                *)
(*              acknowledgement);                                          *)
(*  FallRule    the fall-back of a failed direct path takes a relay        *)
(*              path: the usable one of least rank, so a seen one when     *)
(*              there is one, else the last relay path; the failed         *)
(*              path is no longer validated;                               *)
(*  SlotFresh   a path that takes a slot takes it with no cost and         *)
(*              unseen, whatever the path that held it had.                *)
(*                                                                         *)
(* The bound itself is the table's shape: NP slots, and every path the     *)
(* connection holds takes one (TypeOK).                                    *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc):                              *)
(*  _relay      the rule before the correction, RelayKeep = FALSE: the     *)
(*              session leaves a relay path unvalidated whatever its kind, *)
(*              and nothing validates it again (a relay path is never      *)
(*              challenged); RelayValid fails.                             *)
(*  _held       the rule before #399, Old: a dialing side drops a          *)
(*              handshake packet on a path it does not hold (NoPath), so a *)
(*              reply that comes back on another path is never taken;      *)
(*              ReplyTaken fails.                                          *)
(*  _coalesced  the rule before the correction that followed #399,        *)
(*              Lookup = FALSE: new_path_slot did not look the id up. A    *)
(*              datagram whose handshake packet completes the reply, on a  *)
(*              path the dial does not hold, with a 1-RTT packet behind    *)
(*              it: follow_reply learns the path, and process_payload,     *)
(*              which still has the slot handle_inner found at the start   *)
(*              of the datagram (none), adds it a second time; Unique      *)
(*              fails. The model found it; the code now looks the id up.  *)
(*  _rank       the rule before the second round of #598, Rank = "none":  *)
(*              the cost and the slot alone, so a relay path that is not   *)
(*              seen ties with, and by its slot beats, the relay path the  *)
(*              session is on; RankRule fails.                             *)
(*  _escape     Rank = "noescape": no escape, so an active relay path that *)
(*              failed and is not seen never gives way to a seen relay     *)
(*              path; EscapeRule fails.                                    *)
(*  _fall       Rank = "none": the fall-back of a failed direct path takes *)
(*              a relay path that is not seen before a seen one; FallRule  *)
(*              fails.                                                     *)
(*  _back       Rank = "cost", the rule of the second round, which read    *)
(*              "seen" off the cost: the stamp on the relay path the       *)
(*              session leaves at the bound makes it seen, and the next    *)
(*              timer pass takes the session back to it; BackRule fails.   *)
(*  _slot       Forget = FALSE: an evicted path hands its cost and its     *)
(*              seen fact to the path that takes its slot; SlotFresh       *)
(*              fails.                                                     *)
(***************************************************************************)
EXTENDS PathOps, TLC

CONSTANTS Ids,    \* the path ids a datagram may arrive on; 1 is the dialed path
          Roles,  \* a subset of {"dial", "resp"}
          Old,    \* TRUE: the rule before #399
          \* RelayKeep (PathOps): FALSE is the rule before the correction that keeps a relay path valid
          Lookup, \* FALSE: the rule before the correction (learning does not look the id up)
          \* Forget (PathOps): FALSE is the rule before the slot forgets its path
          \* RT, Rank (PathOps): RT = 0 has no costs (the rule of the first round); Rank "none", "noescape" and "cost"
          \* are the rules before the third round
          HDMAX   \* the dropped-packet counts explored

VARIABLES role, c
vars == <<role, c>>

\* a datagram carries a 1-RTT packet behind its handshake packet, or not
Coals == BOOLEAN
\* a path of a table: a relay path is validated; a seen path has a cost (the acknowledgement that makes it seen gives it
\* the session's estimate); L is the values of the ghost lf
SlotOf(S, L) ==
    {x \in [id : S, v : BOOLEAN, k : {"direct"}, r : 0..RT, sn : BOOLEAN, lf : L] \cup
           [id : S, v : {TRUE}, k : {"relay"}, r : 0..RT, sn : BOOLEAN, lf : L] : x.sn => x.r > 0}
SlotVals == {Empty} \cup SlotOf(Ids \ {1}, {FALSE})
UniqueT(t) == \A i, j \in 1..NP : (t[i].id # 0 /\ t[i].id = t[j].id) => i = j
Dialed(d) == [id |-> 1, v |-> TRUE, k |-> d, r |-> 0, sn |-> FALSE, lf |-> FALSE]
DialTables ==
    {t \in {[i \in 1..NP |-> IF i = 1 THEN Dialed(d) ELSE f[i]] : f \in [1..NP -> SlotVals], d \in PKinds} :
        UniqueT(t)}
C0(t) == [t |-> t, act |-> 1, hs |-> "wait", rf |-> 0, pend |-> 0, smp |-> FALSE, f |-> FALSE, hd |-> 0]

Init ==
    /\ role \in Roles
    /\ c \in IF role = "dial" THEN {C0(t) : t \in DialTables} ELSE {C0([i \in 1..NP |-> Empty])}

\* a datagram reaches the dialing side
DRx == role = "dial" /\ \E id \in Ids, k \in Kinds, co \in Coals, s \in BOOLEAN : c' = Rx(c, id, k, co, s, Old, Lookup)
\* the key host answers the dialing side
DKey == role = "dial" /\ \E r \in {"ok", "more", "bad"}, s \in BOOLEAN : c' = Key(c, r, s)
\* a handshake datagram reaches the responder, establishing its session or not
RRxA == role = "resp" /\ \E id \in Ids, est \in BOOLEAN : c' = RRx(c, id, est)
\* a 1-RTT datagram on a path the established session does not hold
AppA == \E id \in Ids : c' = App(c, id)
\* the host adds or removes a path
AddA == \E id \in Ids : c' = [c EXCEPT !.t = AddPath(c.t, c.act, id).t]
RmA == \E id \in Ids : c' = [c EXCEPT !.t = RemovePath(c.t, c.act, id).t]
\* a timer pass; the endpoint names a path's kind; an acknowledged packet gives the active path a round trip; the third
\* probe timeout in a row; the fall-back of a failed direct path alone. They need round trips to rank by.
TimerA == RT > 0 /\ c' = Timer(c)
InfoA == RT > 0 /\ \E id \in Ids, kd \in PKinds : c' = SetInfo(c, id, kd)
MeasureA == RT > 0 /\ \E r \in 1..RT : c' = Measure(c, r)
FailA == RT > 0 /\ c' = Fail(c)
FallA == RT > 0 /\ c' = Fallback(c)

Next == (DRx \/ DKey \/ RRxA \/ AppA \/ AddA \/ RmA \/ TimerA \/ InfoA \/ MeasureA \/ FailA \/ FallA) /\ UNCHANGED role
Spec == Init /\ [][Next]_vars
Bound == c.hd <= HDMAX

TypeOK ==
    /\ role \in {"dial", "resp"}
    /\ c.t \in [1..NP -> {Empty} \cup SlotOf(Ids, BOOLEAN)]
    /\ c.act \in 1..NP /\ c.hs \in {"wait", "key", "done"}
    /\ c.rf \in Ids \cup {0} /\ c.pend \in Ids \cup {0} /\ c.smp \in BOOLEAN /\ c.f \in BOOLEAN /\ c.hd \in Nat

Unique == UniqueT(c.t)
\* a relay path the connection holds is validated: nothing but a challenge validates a direct path, and a relay path
\* is never challenged but valid from the moment the connection tracks it (the endpoint's naming of a path a relay's
\* validates it, SetInfo)
RelayValid == \A i \in 1..NP : (c.t[i].id # 0 /\ c.t[i].k = "relay") => c.t[i].v
ActiveHeld == (\E i \in 1..NP : c.t[i].id # 0) => c.t[c.act].id # 0
\* a dialing side's active path is validated: the dialed one, then the reply's
ActiveValid == role = "dial" => c.t[c.act].v
\* a Reply that waits for the key host is the message the handshake took last
KeyWaits == (role = "dial" /\ c.hs = "key") => (c.pend # 0 /\ c.rf = c.pend)

\* the session c1 that followed c is on path p (held, validated, active), unless p was not held and c's table had no
\* room for it, and then nothing of the table moved
Taken(c0, c1, p) ==
    IF Find(c0.t, p) # 0 \/ Slot(c0.t, c0.act) # 0
    THEN c1.t[c1.act].id = p /\ c1.t[c1.act].v
    ELSE c1.t = c0.t /\ c1.act = c0.act

ReplyTaken ==
    (role = "dial" /\ c.hs # "done") =>
        \A id \in Ids, co \in Coals, s \in BOOLEAN :
            /\ LET a == Rx(c, id, "auth", co, s, Old, Lookup) IN a.hs = "done" /\ Taken(c, a, id)
            /\ c.hs = "wait" => LET p == Rx(c, id, "pend", co, s, Old, Lookup) IN p.hs = "key" /\ p.pend = id /\ p.rf = id

KeyTaken ==
    (role = "dial" /\ c.hs = "key") => \A s \in BOOLEAN : LET a == Key(c, "ok", s) IN a.hs = "done" /\ Taken(c, a, c.pend)

\* the path c0 was on, once c1 is on another: a relay path stays valid, a direct path is no longer validated
Left1(c0, c1) ==
    c1.act # c0.act =>
        LET s == c1.t[c0.act] IN s.id = c0.t[c0.act].id /\ (s.k = "relay" => s.v) /\ (s.k = "direct" => ~s.v)

LeavesRule ==
    (role = "dial" /\ c.hs # "done") =>
        /\ \A id \in Ids, co \in Coals, s \in BOOLEAN : Left1(c, Rx(c, id, "auth", co, s, Old, Lookup))
        /\ c.hs = "key" => \A s \in BOOLEAN : Left1(c, Key(c, "ok", s))

Still(c0, c1) == c1.t = c0.t /\ c1.act = c0.act /\ c1.smp = c0.smp /\ c1.hs # "done"
Quiet ==
    (role = "dial" /\ c.hs # "done") =>
        /\ \A id \in Ids, k \in Kinds \ {"auth"}, co \in Coals, s \in BOOLEAN : Still(c, Rx(c, id, k, co, s, Old, Lookup))
        /\ \A r \in {"more", "bad"}, s \in BOOLEAN : Still(c, Key(c, r, s))

Counted ==
    (role = "dial" /\ c.hs # "done") => \A id \in Ids, co \in Coals, s \in BOOLEAN : Rx(c, id, "bad", co, s, Old, Lookup).hd = c.hd + 1

\* every path of c that c1 no longer holds in its slot was an unvalidated path other than the active one, at a full table,
\* and a step gives up one path at most
Kept(c0, c1) ==
    /\ \A i \in 1..NP : (c0.t[i].id # 0 /\ c1.t[i].id # c0.t[i].id) =>
           (i # c0.act /\ ~c0.t[i].v /\ \A j \in 1..NP : c0.t[j].id # 0)
    /\ Cardinality({i \in 1..NP : c0.t[i].id # 0 /\ c1.t[i].id # c0.t[i].id}) <= 1
GiveUpRule ==
    /\ role = "dial" => \A id \in Ids, k \in Kinds, co \in Coals, s \in BOOLEAN : Kept(c, Rx(c, id, k, co, s, Old, Lookup))
    /\ role = "dial" => \A r \in {"ok", "more", "bad"}, s \in BOOLEAN : Kept(c, Key(c, r, s))
    /\ role = "resp" => \A id \in Ids, est \in BOOLEAN : Kept(c, RRx(c, id, est))
    /\ \A id \in Ids : Kept(c, App(c, id)) /\ Kept(c, [c EXCEPT !.t = AddPath(c.t, c.act, id).t])

\* the tables the choice of the active path may be made from: c as it is, or after the endpoint named one path's kind
Pre(c0) == {c0} \cup {SetKind(c0, id, kd) : id \in Ids, kd \in PKinds}

\* a usable path that is not a relay path that is unseen: a direct path, or a seen one
Proven(c0, j) == Usable(c0, j) /\ ~(c0.t[j].k = "relay" /\ ~c0.t[j].sn)

RankStep(c0) ==
    LET c1 == Choose(c0)
    IN (c1.act # c0.act /\ c1.t[c1.act].k = "relay" /\ ~c1.t[c1.act].sn) =>
           /\ (~Usable(c0, c0.act) \/ c0.f)
           /\ \A j \in 1..NP : ~Proven(c0, j)
RankRule == \A c0 \in Pre(c) : RankStep(c0)

EscapeStep(c0) ==
    LET c1 == Choose(c0)
        a == c0.t[c0.act]
    IN (a.id # 0 /\ a.k = "relay" /\ ~a.sn /\ c0.f /\ \E j \in 1..NP : Proven(c0, j)) =>
           /\ c1.act # c0.act
           /\ Proven(c0, c1.act)
EscapeRule == \A c0 \in Pre(c) : EscapeStep(c0)

FallStep(c0) ==
    LET c1 == Fallback(c0)
        a == c0.t[c0.act]
        rel == {i \in 1..NP : c0.t[i].id # 0 /\ c0.t[i].k = "relay"}
        vrel == {i \in rel : c0.t[i].v}
    IN (c0.f /\ a.id # 0 /\ a.k = "direct" /\ a.v /\ rel # {}) =>
           /\ c1.act \in rel
           /\ ~c1.t[c0.act].v
           /\ (vrel # {} => c1.act \in vrel)
           /\ ((\E j \in vrel : c0.t[j].sn) => c0.t[c1.act].sn)
           /\ (vrel = {} => c1.act = Last(rel))
FallRule == FallStep(c)

\* a relay path the session left at the bound, with nothing acknowledged on it since (a stamp is not an
\* acknowledgement), is not the choice while the path the session is on is usable
BackStep(c0) ==
    \A i \in 1..NP :
        (c0.t[i].id # 0 /\ c0.t[i].lf /\ c0.t[i].k = "relay" /\ ~c0.t[i].sn /\ Usable(c0, c0.act)) =>
            Choose(c0).act # i
\* the tables the choice may be made from, as Pre, without the endpoint naming the kind of the path the session is on: a
\* path the session moved to that is named a relay path afterwards is a new relay path that has not been acknowledged
\* either, and it ties with the path left (found by TLC: the left path wins by its slot)
PreMoved(c0) == {c0} \cup {SetKind(c0, id, kd) : id \in Ids \ {c0.t[c0.act].id}, kd \in PKinds}
BackRule == \A c0 \in PreMoved(c) : BackStep(c0)

\* every path that a step puts in a slot that held another path comes with no cost and unseen
Fresh1(c0, c1) ==
    \A i \in 1..NP : (c1.t[i].id # 0 /\ c1.t[i].id # c0.t[i].id) => (c1.t[i].r = 0 /\ ~c1.t[i].sn)
SlotFresh ==
    /\ role = "dial" => \A id \in Ids, k \in Kinds, co \in Coals, s \in BOOLEAN :
           Fresh1(c, Rx(c, id, k, co, s, Old, Lookup))
    /\ role = "dial" => \A r \in {"ok", "more", "bad"}, s \in BOOLEAN : Fresh1(c, Key(c, r, s))
    /\ role = "resp" => \A id \in Ids, est \in BOOLEAN : Fresh1(c, RRx(c, id, est))
    /\ \A id \in Ids : Fresh1(c, App(c, id)) /\ Fresh1(c, [c EXCEPT !.t = AddPath(c.t, c.act, id).t])
=============================================================================
