------------------------------ MODULE ReplyPath ------------------------------
(***************************************************************************)
(* The path a dialing side's handshake reply arrives on (pinc#399), the    *)
(* paths a responder owes its flight and validates at its establishment,   *)
(* and the bound of the path table for every path a connection learns by  *)
(* receiving on it, through the operators of PathOps.tla (conn/recv.rs     *)
(* handle_inner, on_handshake, process_payload; conn/drive.rs              *)
(* follow_reply, on_hs_event; conn/hooks.rs the fan-out set; conn/path.rs  *)
(* learn_path, new_path_slot, add_path, remove_path).                      *)
(*                                                                         *)
(* Who acts. One connection, a dialing side or a responder (Roles). The    *)
(* network and an attacker deliver any datagram on any path (Ids): what    *)
(* its handshake packet completes (Kinds, RMsgs) is theirs to choose, and  *)
(* a 1-RTT packet may follow it in the same datagram. The key host answers *)
(* a Reply's request. The host adds and removes paths. A dialing side     *)
(* starts from any table its endpoint can give it: the dialed path         *)
(* validated and active in the first slot, the other slots empty or        *)
(* holding another path, validated or not (a parent session hands its     *)
(* validated paths to a sub-session, adopt_paths). A responder starts with *)
(* no path.                                                                *)
(*                                                                         *)
(* Checked in every reachable state, for every input from it:              *)
(*  ReplyTaken  a dialing side takes a reply on any path, held or not: a   *)
(*              message that authenticates establishes the session; on a   *)
(*              path the dial held, the session is there, validated and    *)
(*              active; on a path only the reply named (anyone can send a  *)
(*              copy of a reply from any source) the session stays on its  *)
(*              path, and the reply's path joins unvalidated and is owed   *)
(*              a copy of the Finish (unless the table has no room, and    *)
(*              then the table and the active path are as they were); a    *)
(*              Reply that passed its first checks waits for the key host  *)
(*              with its path; while a Reply waits for its verdict this    *)
(*              holds of the held message once the verdict fails;          *)
(*  KeyTaken    a key answer that establishes follows the path the Reply   *)
(*              came on by the same rule;                                  *)
(*  Held        while a Reply waits for its verdict a handshake datagram   *)
(*              is held, whatever it completes, and changes nothing else:  *)
(*              no path, no count, no answer (conn/recv.rs hold_part);     *)
(*  HeldTried   a failed verdict is the same failed verdict with nothing   *)
(*              held, followed by the held datagrams in arrival order, as  *)
(*              if they had arrived after it: each is tried once, and one  *)
(*              that fails authentication is counted then (after_verdict); *)
(*  HeldDropped any other answer drops them; HeldOnlyWaiting nothing is    *)
(*              held but while a Reply waits for its verdict;              *)
(*  NotLost     a Reply that arrives while the verdict on another waits    *)
(*              (nothing held before it) is tried once that verdict fails: *)
(*              it waits for the key host with its path, or, if it         *)
(*              authenticates, it is taken by the rule of ReplyTaken;      *)
(*  ActiveValid a dialing side's active path is validated, before and      *)
(*              after the establishment;                                   *)
(*  Quiet       before the session is established, a datagram whose       *)
(*              message does not authenticate and a key answer that does   *)
(*              not establish (a failed verdict with no held message that  *)
(*              authenticates) change no path state: no path added or      *)
(*              given up, the active path as it was, no round trip sample; *)
(*  Counted     one that fails authentication is counted, on any path, at  *)
(*              once when no verdict is awaited, else when it is tried;    *)
(*  GiveUpRule  a step of either role gives a path up only when every     *)
(*              slot is held, and only an unvalidated path that is not the *)
(*              active one, one path at most (remove_path aside, which the *)
(*              host asks for): a reply with a 1-RTT packet behind it at a *)
(*              full table gives up one path, not the one it moves from;   *)
(*  Unique      no path is held twice, also when a 1-RTT packet follows    *)
(*              the reply that learnt the path in the same datagram;       *)
(*              ActiveHeld, KeyWaits;                                      *)
(*  Answered    a responder in its handshake owes its flight to every      *)
(*              held path its first message completed on (the first time   *)
(*              or the same message again), not only to the active one;    *)
(*  RespValid   a path a responder's establishment validates is the one    *)
(*              path its flight went to: the Finish answers that flight,   *)
(*              so whoever sent it received there; a flight that went to   *)
(*              several paths proves none of them, and a resumption Hello  *)
(*              (no flight before it) proves nothing;                      *)
(*  FinishSettles a Finish on a held path after a flight to one path      *)
(*              alone validates that path and makes it active;             *)
(*  ResumeProvesNothing a resumption Hello establishes a responder and     *)
(*              validates no path: anyone who saw it can send a copy of it *)
(*              from any source;                                           *)
(*  ConfirmValidates, EarlyProvesNothing, ProofOnePath a resumed           *)
(*              responder's Reply path is validated by the dialer's first  *)
(*              1-RTT packet, never by a 0-RTT one, and only while the     *)
(*              Reply went to that path alone.                             *)
(* The bound itself is the table's shape: NP slots, and every path the     *)
(* connection holds takes one (TypeOK).                                    *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc):                              *)
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
(*  _resume     the rule before the anti-amplification fix, ResumeValid:  *)
(*              a resumed responder validated its active path at the       *)
(*              Hello, so a copy of the Hello from a forged source made    *)
(*              the endpoint validate that source; ResumeProvesNothing     *)
(*              fails.                                                     *)
(*  _move       the rule before the handshake fix, MOVE: a dialing side    *)
(*              moved to the path of a reply it did not hold, so a copy of *)
(*              the Reply from any address took the dial there and its     *)
(*              Finish never reached the responder; ActiveValid fails.     *)
(*  _active     the rule before the handshake fix, RESP = "active": a      *)
(*              responder sent its flight on its active path only (the     *)
(*              path of the first datagram), so a copy of the first flight *)
(*              from another address that arrived first took every answer  *)
(*              away from the dialer; Answered fails.                      *)
(*  _loose      a broken variant, RESP = "loose": the Finish's path is     *)
(*              validated after a flight to several paths, so a copy of    *)
(*              the Finish from a forged source validates that source;     *)
(*              RespValid fails.                                           *)
(*  _nohold     the rule before the hold, HOLD = FALSE: a Reply that       *)
(*              arrives while the verdict on another waits is refused, so  *)
(*              a forged Reply ahead of the genuine one makes the dial     *)
(*              lose it; NotLost fails.                                    *)
(*                                                                         *)
(* The held datagrams are bounded by HMAX (the code by the bytes of one    *)
(* pool chunk and the path ids it can name); one that finds no room is     *)
(* dropped, the same as a datagram the network lost.                       *)
(***************************************************************************)
EXTENDS PathOps, TLC

CONSTANTS Ids,    \* the path ids a datagram may arrive on; 1 is the dialed path
          Roles,  \* a subset of {"dial", "resp"}
          Old,    \* TRUE: the rule before #399
          Lookup, \* FALSE: the rule before the correction (learning does not look the id up)
          HDMAX,  \* the dropped-packet counts explored
          ResumeValid, \* TRUE: the rule before the fix (a resumption Hello validates the responder's path)
          MOVE,   \* TRUE: the rule before the handshake fix (the dial moves to a reply's path it did not hold)
          RESP,   \* "fan" the code's rule; "active" the rule before (flight on the active path); "loose" broken
          HMAX,   \* the held datagrams explored while a Reply waits for its verdict
          HOLD    \* FALSE: the rule before the hold (a Reply or a reject that arrives while the verdict waits is refused)

\* what a responder's handshake datagram completes
RMsgs == {"part", "first", "finish", "resume"}

VARIABLES role, c
vars == <<role, c>>

\* a datagram carries a 1-RTT packet behind its handshake packet, or not
Coals == BOOLEAN
SlotVals == {Empty} \cup [id : Ids \ {1}, v : BOOLEAN]
UniqueT(t) == \A i, j \in 1..NP : (t[i].id # 0 /\ t[i].id = t[j].id) => i = j
DialTables ==
    {t \in {[i \in 1..NP |-> IF i = 1 THEN [id |-> 1, v |-> TRUE] ELSE f[i]] : f \in [1..NP -> SlotVals]} : UniqueT(t)}
C0(t) == [t |-> t, act |-> 1, hs |-> "wait", rf |-> 0, pend |-> 0, smp |-> FALSE, hd |-> 0,
          fan |-> {}, asked |-> {}, ev |-> [fan |-> {}, val |-> {}], rp |-> 0, hq |-> <<>>]

Init ==
    /\ role \in Roles
    /\ c \in IF role = "dial" THEN {C0(t) : t \in DialTables} ELSE {C0([i \in 1..NP |-> Empty])}

DRxOp(x, id, k, co, s) == RxM(x, id, k, co, s, Old, Lookup, MOVE, HOLD)
DKeyOp(x, r, s) == KeyM(x, r, s, MOVE, HOLD)
RRxOp(x, id, m) == RRx(x, id, m, ResumeValid, RESP)

\* a datagram reaches the dialing side
DRx == role = "dial" /\ \E id \in Ids, k \in Kinds, co \in Coals, s \in BOOLEAN : c' = DRxOp(c, id, k, co, s)
\* the key host answers the dialing side
DKey == role = "dial" /\ \E r \in {"ok", "more", "bad"}, s \in BOOLEAN : c' = DKeyOp(c, r, s)
\* a handshake datagram reaches the responder, establishing its session or not
RRxA == role = "resp" /\ \E id \in Ids, m \in RMsgs : c' = RRxOp(c, id, m)
\* a 1-RTT datagram on a path the established session does not hold
AppA == \E id \in Ids : c' = App(c, id)
\* the responder re-sends its Reply; a packet authenticates after the establishment
ResendA == role = "resp" /\ c' = Resend(c, RESP)
ConfirmA == role = "resp" /\ \E k \in {"app", "early"} : c' = Confirm(c, k)
\* the host adds or removes a path
AddA == \E id \in Ids : c' = [c EXCEPT !.t = AddPath(c.t, c.act, id).t]
RmA == \E id \in Ids : c' = [c EXCEPT !.t = RemovePath(c.t, c.act, id).t]

Next == (DRx \/ DKey \/ RRxA \/ AppA \/ ResendA \/ ConfirmA \/ AddA \/ RmA) /\ UNCHANGED role
Spec == Init /\ [][Next]_vars
Bound == c.hd <= HDMAX /\ Len(c.hq) <= HMAX

TypeOK ==
    /\ role \in {"dial", "resp"}
    /\ c.t \in [1..NP -> SlotVals \cup {[id |-> 1, v |-> b] : b \in BOOLEAN}]
    /\ c.act \in 1..NP /\ c.hs \in {"wait", "key", "sign", "done"}
    /\ c.rf \in Ids \cup {0} /\ c.pend \in Ids \cup {0} /\ c.smp \in BOOLEAN /\ c.hd \in Nat
    /\ c.fan \subseteq Ids /\ c.asked \subseteq Ids /\ c.ev.fan \subseteq Ids /\ c.ev.val \subseteq Ids
    /\ c.rp \in Ids \cup {0}
    /\ c.hq \in Seq([id : Ids, k : Kinds])

Unique == UniqueT(c.t)
ActiveHeld == (\E i \in 1..NP : c.t[i].id # 0) => c.t[c.act].id # 0
\* a dialing side's active path is validated: the dialed one, then a reply's path the dial held
ActiveValid == role = "dial" => c.t[c.act].v
\* a Reply that waits for the key host is the message the handshake took last
KeyWaits == (role = "dial" /\ c.hs \in {"key", "sign"}) => (c.pend # 0 /\ c.rf = c.pend)
\* nothing is held but while a Reply waits for its verdict
HeldOnlyWaiting == c.hq # <<>> => (role = "dial" /\ c.hs = "key")

\* the session c1 that followed c, after a reply on path p: on a path c held, the session is on p, validated; on a path
\* c did not hold, the session is where it was and p is held, unvalidated and owed the Finish, unless c's table had no
\* room for it, and then nothing of the table moved
Taken(c0, c1, p) ==
    IF Find(c0.t, p) # 0 THEN c1.t[c1.act].id = p /\ c1.t[c1.act].v
    ELSE IF Slot(c0.t, c0.act) # 0
         THEN /\ c1.act = c0.act /\ c1.t[c1.act] = c0.t[c0.act]
              /\ Find(c1.t, p) # 0 /\ ~c1.t[Find(c1.t, p)].v /\ p \in c1.fan
         ELSE c1.t = c0.t /\ c1.act = c0.act

ReplyTaken ==
    (role = "dial" /\ c.hs \in {"wait", "sign"}) =>
        \A id \in Ids, co \in Coals, s \in BOOLEAN :
            /\ LET a == DRxOp(c, id, "auth", co, s) IN a.hs = "done" /\ Taken(c, a, id)
            /\ c.hs = "wait" => LET p == DRxOp(c, id, "pend", co, s) IN p.hs = "key" /\ p.pend = id /\ p.rf = id

KeyTaken ==
    (role = "dial" /\ c.hs \in {"key", "sign"}) => \A s \in BOOLEAN : LET a == DKeyOp(c, "ok", s) IN a.hs = "done" /\ Taken(c, a, c.pend)

Still(c0, c1) == c1.t = c0.t /\ c1.act = c0.act /\ c1.smp = c0.smp /\ c1.hs # "done"
\* a held message that authenticates
HeldAuth(x) == \E j \in 1..Len(x.hq) : x.hq[j].k = "auth"
Quiet ==
    (role = "dial" /\ c.hs # "done") =>
        /\ \A id \in Ids, k \in Kinds \ {"auth"}, co \in Coals, s \in BOOLEAN : Still(c, DRxOp(c, id, k, co, s))
        /\ \A r \in {"more", "bad"}, s \in BOOLEAN : (r = "more" \/ ~HeldAuth(c)) => Still(c, DKeyOp(c, r, s))

\* counted at once while no verdict is awaited; while one is, held uncounted (Held) and counted when tried (HeldTried)
Counted ==
    (role = "dial" /\ c.hs \in {"wait", "sign"}) =>
        \A id \in Ids, co \in Coals, s \in BOOLEAN : DRxOp(c, id, "bad", co, s).hd = c.hd + 1

Held ==
    (role = "dial" /\ c.hs = "key") =>
        \A id \in Ids, k \in Kinds, co \in Coals, s \in BOOLEAN :
            DRxOp(c, id, k, co, s) = [c EXCEPT !.hq = Append(@, [id |-> id, k |-> k])]

\* the datagrams q arriving at x one after the other, in order (a held one carries no 1-RTT packet: that part of its
\* datagram was taken when it arrived)
RECURSIVE Delayed(_, _, _)
Delayed(x, q, s) == IF q = <<>> THEN x ELSE Delayed(DRxOp(x, Head(q).id, Head(q).k, FALSE, s), Tail(q), s)

HeldTried ==
    (role = "dial" /\ c.hs = "key") =>
        \A s \in BOOLEAN : DKeyOp(c, "bad", s) = Delayed(DKeyOp([c EXCEPT !.hq = <<>>], "bad", s), c.hq, s)

HeldDropped == (role = "dial" /\ c.hs = "key") => \A r \in {"ok", "more"}, s \in BOOLEAN : DKeyOp(c, r, s).hq = <<>>

NotLost ==
    (role = "dial" /\ c.hs = "key" /\ c.hq = <<>>) =>
        \A id \in Ids, co \in Coals, s, s2 \in BOOLEAN :
            /\ LET x == DKeyOp(DRxOp(c, id, "pend", co, s), "bad", s2) IN x.hs = "key" /\ x.pend = id /\ x.rf = id
            /\ LET x == DKeyOp(DRxOp(c, id, "auth", co, s), "bad", s2) IN x.hs = "done" /\ Taken(c, x, id)

\* every path of c that c1 no longer holds in its slot was an unvalidated path other than the active one, at a full table,
\* and a step gives up one path at most
Kept(c0, c1) ==
    /\ \A i \in 1..NP : (c0.t[i].id # 0 /\ c1.t[i].id # c0.t[i].id) =>
           (i # c0.act /\ ~c0.t[i].v /\ \A j \in 1..NP : c0.t[j].id # 0)
    /\ Cardinality({i \in 1..NP : c0.t[i].id # 0 /\ c1.t[i].id # c0.t[i].id}) <= 1
GiveUpRule ==
    /\ role = "dial" => \A id \in Ids, k \in Kinds, co \in Coals, s \in BOOLEAN : Kept(c, DRxOp(c, id, k, co, s))
    /\ role = "dial" => \A r \in {"ok", "more", "bad"}, s \in BOOLEAN : Kept(c, DKeyOp(c, r, s))
    /\ role = "resp" => \A id \in Ids, m \in RMsgs : Kept(c, RRxOp(c, id, m))
    /\ \A id \in Ids : Kept(c, App(c, id)) /\ Kept(c, [c EXCEPT !.t = AddPath(c.t, c.act, id).t])
    /\ Kept(c, Resend(c, RESP)) /\ Kept(c, Confirm(c, "app")) /\ Kept(c, Confirm(c, "early"))

\* a responder in its handshake owes its flight to every held path its first message completed on
Answered == (role = "resp" /\ c.hs # "done") => c.asked \subseteq Targets(c, RESP)

\* a path a responder's establishment validated is the one path its flight had gone to
RespValid ==
    (role = "resp" /\ c.hs = "done") => c.ev.val \subseteq (IF Cardinality(c.ev.fan) = 1 THEN c.ev.fan ELSE {})

\* a Finish on a held path, after a flight to one path alone, validates that path and makes it active
FinishSettles ==
    (role = "resp" /\ c.hs # "done" /\ Cardinality(Targets(c, RESP)) = 1) =>
        \A id \in HeldIds(c.t) : LET a == RRxOp(c, id, "finish")
                                 IN a.hs = "done" => (a.t[a.act].v /\ a.t[a.act].id \in Targets(c, RESP))

\* a resumption Hello validates no path the responder did not hold validated before it
ResumeProvesNothing ==
    role = "resp" => \A id \in Ids, i \in 1..NP : RRxOp(c, id, "resume").t[i].v => c.t[i].v

\* the dialer's first 1-RTT packet validates the path a resumed responder's Reply went to, if it is still held
ConfirmValidates ==
    (role = "resp" /\ c.rp # 0 /\ Find(c.t, c.rp) # 0) => Confirm(c, "app").t[Find(c.t, c.rp)].v
\* a 0-RTT packet validates nothing
EarlyProvesNothing == Confirm(c, "early") = c
\* a proof is owed only by an established responder whose Reply left on that path alone, and a 1-RTT packet
\* validates no other path
ProofOnePath ==
    /\ c.rp # 0 => (role = "resp" /\ c.hs = "done" /\ Dest(c, RESP) = {c.rp})
    /\ \A i \in 1..NP : (Confirm(c, "app").t[i].v /\ ~c.t[i].v) => c.t[i].id = c.rp
=============================================================================
