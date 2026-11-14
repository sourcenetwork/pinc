-------------------------------- MODULE Early --------------------------------
(***************************************************************************)
(* The buffer of packets that arrive before their keys (vinc-transport     *)
(* conn/recv.rs, drive.rs, life.rs and stream/datagram.rs) over every      *)
(* interleaving of packets (0-RTT and 1-RTT, opening or not), the early    *)
(* keys, the establishment of the session and the close, at small sizes    *)
(* (EarlyOps.tla has the operators).                                       *)
(*                                                                         *)
(* Checked, as state invariants over the state and the step before it:     *)
(*  - the buffer holds at most CAP packets, oldest first in the order of   *)
(*    arrival, and only while the connection is handshaking (Bound,        *)
(*    Order, Phase);                                                       *)
(*  - only the documented packets are held: a 0-RTT packet on a server     *)
(*    only, in a handshake (Kinds, HoldRight, Refused);                    *)
(*  - when the buffer is full the packet that arrives is refused and the   *)
(*    packets held stay: the newest is lost, not the oldest (FullRefuses); *)
(*  - an eligible packet is held exactly when the buffer has a place and   *)
(*    the pool has room, and then goes last (HoldRight);                   *)
(*  - the held and the refused add up to the packets that were eligible    *)
(*    (HoldCount);                                                         *)
(*  - establishing the session tries the packets held once each, oldest    *)
(*    first, only after the 1-RTT keys exist, and leaves none; a close in  *)
(*    the middle ends it (Drain, DrainOnce);                               *)
(*  - a packet that does not open is lost, counted as undecryptable if it  *)
(*    is a 1-RTT one and not counted if it is a 0-RTT one (Counted);       *)
(*  - nothing held survives the close (Phase, Closed);                     *)
(*  - amplification: every datagram a live connection receives counts      *)
(*    toward the bytes received on arrival, held, refused or opened; the   *)
(*    drain adds nothing (Amp).                                            *)
(* RULE picks the rule: "code" is what the code does; the witnesses give   *)
(* a wrong one each and the matching property fails: "oldest" (a full      *)
(* buffer loses the oldest packet, not the new one: FullRefuses),          *)
(* "anyphase" (a client keeps 0-RTT packets too: Kinds), "noclear" (the    *)
(* close keeps the buffer: Phase), "redrain" (the drain leaves the packets *)
(* in the buffer: Drain) and "ampopen" (a packet counts only when it       *)
(* opens: Amp). Lean counterpart: proofs/lean/Vinc/TransportEarly*.lean.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CAP, KMAX, RULE
VARIABLES c, prev, lst, nid, held, att
vars == <<c, prev, lst, nid, held, att>>

INSTANCE EarlyOps

Init == /\ \E cl \in BOOLEAN : c = Early0(cl)
        /\ prev = c /\ lst = [op |-> "init"] /\ nid = 0 /\ held = {} /\ att = 0

Pkts == {[kind |-> k, fate |-> f] : k \in {"z", "s"}, f \in {"open", "fail", "close"}}

RecvStep == \E q \in Pkts, room \in BOOLEAN, dlen \in 1..2 :
    LET p == [id |-> nid + 1, kind |-> q.kind, fate |-> q.fate]
        base == IF RULE = "anyphase" /\ p.kind = "z" /\ c.client /\ c.ph = "hs" /\ ~c.er
                THEN HoldPkt([c EXCEPT !.rx = c.rx + dlen], CAP, room, p)
                ELSE Recv(c, CAP, room, p, dlen)
        x == IF RULE = "oldest" /\ base.out = "full" /\ room /\ Len(c.q) = CAP
             THEN [out |-> "held", c |-> [base.c EXCEPT !.q = Append(Tail(c.q), p)]]
             ELSE IF RULE = "ampopen" /\ base.out # "ok" /\ c.ph # "closed"
             THEN [out |-> base.out, c |-> [base.c EXCEPT !.rx = c.rx]]
             ELSE base
    IN /\ nid < KMAX
       /\ c' = x.c /\ prev' = c /\ nid' = nid + 1
       /\ lst' = [op |-> "recv", out |-> x.out, p |-> p, dlen |-> dlen, room |-> room]
       /\ held' = IF x.out = "held" THEN held \cup {p.id} ELSE held
       /\ att' = IF x.out \in {"held", "full"} THEN att + 1 ELSE att

KeysStep == /\ ~c.client /\ c.ph = "hs" /\ ~c.er
            /\ c' = EarlyKeys(c) /\ prev' = c /\ lst' = [op |-> "keys"]
            /\ UNCHANGED <<nid, held, att>>

EstStep == LET d == Established(c)
               d2 == IF RULE = "redrain" THEN [c |-> [d.c EXCEPT !.q = c.q], done |-> d.done] ELSE d
           IN /\ c.ph = "hs"
              /\ c' = d2.c /\ prev' = c /\ lst' = [op |-> "est", done |-> d.done]
              /\ UNCHANGED <<nid, held, att>>

CloseStep == /\ c.ph # "closed"
             /\ c' = IF RULE = "noclear" THEN [Shut(c) EXCEPT !.q = c.q] ELSE Shut(c)
             /\ prev' = c /\ lst' = [op |-> "close"]
             /\ UNCHANGED <<nid, held, att>>

Next == RecvStep \/ KeysStep \/ EstStep \/ CloseStep
Spec == Init /\ [][Next]_vars
Bounded == nid <= KMAX

IsIncreasing(s) == \A i, j \in DOMAIN s : i < j => s[i] < s[j]
Prefix(s, t) == Len(s) <= Len(t) /\ \A i \in DOMAIN s : s[i] = t[i]

Bound == Len(c.q) <= CAP
Order == IsIncreasing(Ids(c.q)) /\ \A i \in DOMAIN c.q : c.q[i].id \in held
Phase == (c.q # <<>> => c.ph = "hs") /\ (c.ph = "closed" => c.q = <<>>)
Kinds == \A i \in DOMAIN c.q : c.q[i].kind = "z" => ~c.client
HoldCount == c.nb + c.nd = att

RecvPre == [prev EXCEPT !.rx = prev.rx + lst.dlen]
RecvElig == lst.op = "recv" /\ prev.ph # "closed" /\ Eligible(RecvPre, lst.p)

\* a packet the code keeps goes last, and is counted
HoldRight == (RecvElig /\ Len(prev.q) < CAP /\ lst.room) =>
    (/\ lst.out = "held" /\ c.q = Append(prev.q, lst.p) /\ c.nb = prev.nb + 1 /\ c.nd = prev.nd)
\* a packet that finds the buffer full (or the pool without room) is the one that is lost; the ones held stay
FullRefuses == (RecvElig /\ (Len(prev.q) >= CAP \/ ~lst.room)) =>
    (/\ lst.out = "full" /\ c.q = prev.q /\ c.nd = prev.nd + 1 /\ c.nb = prev.nb)
\* any other packet is not held, and changes the buffer only by a close
Refused == (lst.op = "recv" /\ ~RecvElig) =>
    (/\ (c.q = prev.q \/ (c.ph = "closed" /\ c.q = <<>>))
     /\ c.nb = prev.nb /\ c.nd = prev.nd /\ lst.out \notin {"held", "full"})
Counted == lst.op = "recv" =>
    c.nu = prev.nu + (IF prev.ph # "closed" /\ lst.p.kind = "s" /\ prev.rv /\ lst.p.fate = "fail" THEN 1 ELSE 0)
Amp == lst.op = "recv" => (IF prev.ph # "closed" THEN c.rx = prev.rx + lst.dlen ELSE c = prev)
Drain == lst.op = "est" =>
    (/\ c.rv /\ c.q = <<>> /\ c.rx = prev.rx /\ c.nb = prev.nb /\ c.nd = prev.nd
     /\ Prefix(lst.done, Ids(prev.q))
     /\ ((\A i \in DOMAIN prev.q : prev.q[i].fate # "close") => lst.done = Ids(prev.q))
     /\ c.nu = prev.nu + Cardinality({i \in DOMAIN lst.done : prev.q[i].kind = "s" /\ prev.q[i].fate = "fail"}))
DrainOnce == lst.op = "est" => (IsIncreasing(lst.done) /\ \A i \in DOMAIN lst.done : lst.done[i] \in held)
Closed == c.ph = "closed" => c.q = <<>>

Inv == Bound /\ Order /\ Phase /\ Kinds /\ HoldCount /\ HoldRight /\ FullRefuses /\ Refused /\ Counted /\ Amp
       /\ Drain /\ DrainOnce /\ Closed
=============================================================================
