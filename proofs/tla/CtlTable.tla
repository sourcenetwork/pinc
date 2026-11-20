------------------------------- MODULE CtlTable -------------------------------
(***************************************************************************)
(* The control frames a connection must send again when their packet is    *)
(* lost, pinc-transport conn/ctl.rs (Ctl, `apply` for Control frame        *)
(* references), as the operators of CtlTableOps.tla, over every sequence   *)
(* of: frames put in flight (`track`, `hold_ext` and the extension frame   *)
(* sent, tickets issued and sent, READY asked for and built), extension    *)
(* frames shed, the pool's other users, and recovery reporting each        *)
(* reference in flight acknowledged, or lost and then possibly             *)
(* acknowledged late. PARTS picks which frames a configuration runs:       *)
(* "sc" the stream-frame table, "ext" the extension slots, "flags" tickets *)
(* and READY. A loss with `requeue` false (repair packets and path MTU     *)
(* probes) leaves Ctl alone and is not modelled; REKEY sets only flags of  *)
(* the Outcome, read outside this unit, and is not modelled.               *)
(*                                                                         *)
(* Checked, the invariants of the module doc:                              *)
(*  - TableKeys, RefusedKeeps: at most TABLE stream frames and EXT_SLOTS   *)
(*    extension frames in flight; a frame the table cannot record is       *)
(*    refused and changes nothing;                                         *)
(*  - Accounted, NoTwice: a stream frame stays in the table until its      *)
(*    packet is acknowledged (then it is gone) or lost (then it is handed  *)
(*    back to the stream layer), and it is handed on once, whatever        *)
(*    further reports of the same frame arrive (the audit's "queued again  *)
(*    once");                                                              *)
(*  - ExtChunks: a held extension frame owns exactly one pool chunk,       *)
(*    freed when its slot is;                                              *)
(*  - ExtResent: a held extension frame waits to be sent or is in flight,  *)
(*    so a lost one is sent again;                                         *)
(*  - TicketsOwed, ReadyOwed: the frames described by a flag are derived   *)
(*    again: the newest ticket batch issued, until a packet carrying it is *)
(*    acknowledged, is pending or in flight; READY, once asked for, is set *)
(*    or in flight until one is acknowledged.                              *)
(* DOC = TRUE: an acknowledgement of tickets clears only the batch it      *)
(* carried, and a loss makes only that batch pending again, as             *)
(* `issue_tickets` documents ("send them to the peer") and as the code     *)
(* does with fix T1 (the tickets frame carries its generation). DOC =      *)
(* FALSE is the code before T1 (id 0: any acknowledgement clears the batch *)
(* held); no config runs it any more. CtlTable_full and CtlTable_extfull   *)
(* are reachability witnesses: the table and the extension slots fill.     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS PARTS, DOC, T, E, P, KMAX, NEMAX, GMAX, SMAX
ASSUME PARTS \subseteq {"sc", "ext", "flags"} /\ DOC \in BOOLEAN /\ T >= 1 /\ E >= 1 /\ P >= 0
VARIABLES c, pu, oth, fl, sent, fate, tg, tacked, rdy, last
vars == <<c, pu, oth, fl, sent, fate, tg, tacked, rdy, last>>

INSTANCE CtlTableOps

Keys == 1..KMAX
HeldExt == {j \in Places(c.ext) : c.ext[j].on}
Ref(k, id, g) == [k |-> k, id |-> id, g |-> g, st |-> "out", pn |-> sent + 1]
Fly(r) == /\ fl' = fl \cup {r} /\ sent' = sent + 1
Handed(f, id, layer) == IF layer = "none" THEN f ELSE [f EXCEPT ![id] = IF f[id] = "tab" THEN layer ELSE "twice"]
Did(op, ok) == last' = [op |-> op, ok |-> ok]

Init == /\ c = CNew(T, E) /\ pu = 0 /\ oth = 0 /\ fl = {} /\ sent = 0
        /\ fate = [k \in Keys |-> "none"] /\ tg = 0 /\ tacked = FALSE /\ rdy = FALSE
        /\ last = [op |-> "init", ok |-> TRUE]

TrackA == /\ "sc" \in PARTS /\ c.nk <= KMAX /\ sent < SMAX
          /\ LET r == Track(c)
             IN IF r.ok
                THEN /\ c' = r.c /\ Fly(Ref("sc", r.key, 0)) /\ fate' = [fate EXCEPT ![r.key] = "tab"]
                     /\ UNCHANGED <<pu, oth, tg, tacked, rdy>> /\ Did("track", TRUE)
                ELSE UNCHANGED <<c, pu, oth, fl, sent, fate, tg, tacked, rdy>> /\ Did("track", FALSE)
HoldA == /\ "ext" \in PARTS /\ c.ne <= NEMAX
         /\ \E long \in BOOLEAN :
              LET r == HoldExt(c, pu, P, long)
              IN /\ c' = r.c /\ pu' = r.used /\ Did("hold", r.ok)
                 /\ UNCHANGED <<oth, fl, sent, fate, tg, tacked, rdy>>
SendExtA == /\ "ext" \in PARTS /\ sent < SMAX
            /\ \E j \in HeldExt : /\ c.ext[j].pend /\ c' = SendExt(c, j) /\ Fly(Ref("ext", c.ext[j].key, 0))
            /\ UNCHANGED <<pu, oth, fate, tg, tacked, rdy>> /\ Did("send_ext", TRUE)
\* conn/api.rs `shed_extensions` or `release_ext`: a held frame given up, its chunk back
ShedA == /\ "ext" \in PARTS
         /\ \E j \in HeldExt : LET f == FreeExt(c, pu, j) IN c' = f.c /\ pu' = f.used
         /\ UNCHANGED <<oth, fl, sent, fate, tg, tacked, rdy>> /\ Did("shed", TRUE)
OtherTake == /\ "ext" \in PARTS /\ pu < P /\ pu' = pu + 1 /\ oth' = oth + 1
             /\ UNCHANGED <<c, fl, sent, fate, tg, tacked, rdy>> /\ Did("env", TRUE)
OtherGive == /\ "ext" \in PARTS /\ oth > 0 /\ pu' = pu - 1 /\ oth' = oth - 1
             /\ UNCHANGED <<c, fl, sent, fate, tg, tacked, rdy>> /\ Did("env", TRUE)
IssueA == /\ "flags" \in PARTS /\ tg < GMAX
          /\ c' = Issue(c, tg + 1) /\ tg' = tg + 1 /\ tacked' = FALSE
          /\ UNCHANGED <<pu, oth, fl, sent, fate, rdy>> /\ Did("issue", TRUE)
SendTkA == /\ "flags" \in PARTS /\ sent < SMAX
           /\ LET r == SendTickets(c) IN r.ok /\ c' = r.c /\ Fly(Ref("tk", 0, r.g))
           /\ UNCHANGED <<pu, oth, fate, tg, tacked, rdy>> /\ Did("send_tickets", TRUE)
SendReadyA == /\ "flags" \in PARTS /\ c' = SendReady(c) /\ rdy' = TRUE
              /\ UNCHANGED <<pu, oth, fl, sent, fate, tg, tacked>> /\ Did("send_ready", TRUE)
BuildReadyA == /\ "flags" \in PARTS /\ sent < SMAX
               /\ LET r == BuildReady(c) IN r.ok /\ c' = r.c /\ Fly(Ref("rd", 0, 0))
               /\ UNCHANGED <<pu, oth, fate, tg, tacked, rdy>> /\ Did("build_ready", TRUE)

\* an acknowledgement of a reference in flight, or a late one of a reference reported lost
AckOf(r) == LET a == Acked(c, pu, r.k, r.id, r.g, DOC)
            IN /\ c' = a.c /\ pu' = a.used /\ fl' = fl \ {r}
               /\ fate' = IF r.k = "sc" THEN Handed(fate, r.id, a.layer) ELSE fate
               /\ tacked' = (tacked \/ (r.k = "tk" /\ r.g = tg))
               /\ rdy' = (rdy /\ r.k # "rd")
               /\ UNCHANGED <<oth, sent, tg>>
AckA == \E r \in fl : r.st = "out" /\ AckOf(r) /\ Did("ack", TRUE)
LateAckA == \E r \in fl : r.st = "lost" /\ AckOf(r) /\ Did("late_ack", TRUE)
LoseA == \E r \in fl :
    /\ r.st = "out"
    /\ LET l == Lost(c, r.k, r.id, r.g, DOC)
       IN /\ c' = l.c /\ fl' = (fl \ {r}) \cup {[r EXCEPT !.st = "lost"]}
          /\ fate' = IF r.k = "sc" THEN Handed(fate, r.id, l.layer) ELSE fate
    /\ UNCHANGED <<pu, oth, sent, tg, tacked, rdy>> /\ Did("lose", TRUE)

Next == TrackA \/ HoldA \/ SendExtA \/ ShedA \/ OtherTake \/ OtherGive \/ IssueA \/ SendTkA \/ SendReadyA
        \/ BuildReadyA \/ AckA \/ LateAckA \/ LoseA
Spec == Init /\ [][Next]_vars

TypeOK == /\ \A j \in Places(c.tab) : c.tab[j] \in 0..KMAX
          /\ pu \in 0..P /\ oth \in 0..P /\ sent \in 0..SMAX
          /\ \A k \in Keys : fate[k] \in {"none", "tab", "acked", "lost", "twice"}
TableKeys == /\ \A i, j \in Places(c.tab) : (i # j /\ c.tab[i] # 0) => c.tab[i] # c.tab[j]
             /\ \A i, j \in HeldExt : i # j => c.ext[i].key # c.ext[j].key
             /\ Cardinality(HeldExt) <= E
Accounted == \A k \in Keys : k < c.nk => ((\E j \in Places(c.tab) : c.tab[j] = k) <=> fate[k] = "tab")
NoTwice == \A k \in Keys : fate[k] # "twice"
ExtChunks == pu = Cardinality(HeldExt) + oth
ExtResent == \A j \in HeldExt :
    c.ext[j].pend \/ \E r \in fl : r.k = "ext" /\ r.id = c.ext[j].key /\ r.st = "out"
TicketsOwed == (tg > 0 /\ ~tacked) =>
    (c.tk = tg /\ (c.tp \/ \E r \in fl : r.k = "tk" /\ r.g = tg /\ r.st = "out"))
ReadyOwed == rdy => (c.ready \/ \E r \in fl : r.k = "rd" /\ r.st = "out")
RefusedKeeps == [][last'.ok = FALSE => (c' = c /\ pu' = pu)]_vars

\* reachability witnesses: the stream-frame table fills; every extension slot is held
TableNotFull == \E j \in Places(c.tab) : c.tab[j] = 0
ExtNotFull == Cardinality(HeldExt) < E
=============================================================================
