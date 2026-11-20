---------------------------------- MODULE Tx ----------------------------------
(***************************************************************************)
(* The datagrams out of pinc-core tx.rs (Endpoint::poll_transmit, gate,    *)
(* send_stash, batch) with the two send queues it serves, over every       *)
(* interleaving of calls and queue changes at small sizes. TxOps.tla has   *)
(* the operators.                                                          *)
(*                                                                         *)
(* A call is a run of steps (pc): "idle" between calls; the kept datagram  *)
(* first (it leaves through the gate alone, or is dropped when the gate    *)
(* holds it or its path has no address); "loop", the first session's       *)
(* connection asked for a datagram; "batch", the next sessions asked while *)
(* the buffer can take more; "out", the buffer returned. The connections  *)
(* and the ledger are the environment: a connection answers any transmit   *)
(* of Shapes that fits the window, or nothing, or its slot is gone; the    *)
(* gate's answer is either (Ledger.tla checks the ledger's decision); a    *)
(* transmit with destination 0 is one whose path has no address any more.  *)
(* Between calls a session may be queued (mark_dirty), a broadcast session *)
(* may queue a sub-session open (it counts as ordinary until the open      *)
(* leaves), and the host may set or clear the broadcast flag of a session  *)
(* in FLIP (Command::SetGossip); an open and a cleared flag promote a      *)
(* waiting broadcast session at once (dirty_promote), a flag set while the *)
(* session waits in the ordinary queue takes effect at its next turn. The  *)
(* rejects of stateless.rs are not modelled: they go    *)
(* after the kept datagram and before the queues, each charged by          *)
(* stateless.rs; the trace check accepts one as a call's result.          *)
(*                                                                         *)
(* Checked, in every state reached (the module doc's invariants):          *)
(*  - QueueWF: each session waits at most once, in one queue, so the       *)
(*    queues hold at most K sessions;                                      *)
(*  - ClassOK: ordinary sessions (a broadcast one with an open still to    *)
(*    leave among them) wait in the first queue and broadcast sessions in  *)
(*    the second, so a broadcast session is served only when no ordinary   *)
(*    one waits (with no flag changes, FLIP = {});                         *)
(*  - ClassFlagOK: the broadcast queue holds broadcast sessions only, so   *)
(*    an ordinary session never waits behind a broadcast one; the ordinary *)
(*    queue holds ordinary sessions and those whose flag was set while     *)
(*    they waited there (late), until their turn;                          *)
(*  - Shape: a buffer goes to one destination and is a run of equal        *)
(*    datagrams of the first one's size, the last one possibly shorter;    *)
(*  - SegLimit, Fits: it never holds more than the configured number of    *)
(*    datagrams (L, max_gso) and fits the caller's buffer;                 *)
(*  - ChargedOK: no datagram enters it without passing the ledger, and the *)
(*    ledger was charged exactly its bytes plus OVH (the IP and UDP        *)
(*    headers) per datagram;                                               *)
(*  - StashFirst: the kept datagram is the only extra buffer and is dealt   *)
(*    with before anything else of a call.                                 *)
(* The connection's own run is at most L datagrams (pinc-transport         *)
(* send.rs batches up to max_gso), an assumption stated by ASSUME.         *)
(* Tx.cfg: 3 sessions (one broadcast), 2 destinations, L = 3, a buffer of  *)
(* 12 bytes, windows of at most 8 (MAX_DATAGRAM scaled), datagrams of 3    *)
(* bytes and 1 and 4 (another size), runs of two. Tx_flag.cfg: the same    *)
(* with the flag of the broadcast session changing. Witnesses: Tx_w_stash  *)
(* (a datagram is kept for the next call), Tx_w_full (a buffer of L        *)
(* datagrams leaves), Tx_w_late (ClassOK fails once flags change: a        *)
(* broadcast session waits in the ordinary queue until its turn).          *)
(* TraceTx.tla checks the recorded calls of the code against TxOps.tla.    *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS K, GOSSIP, FLIP, L, OUT, MD, OVH, F, ND

T == INSTANCE TxOps WITH OVH <- OVH

Shapes == {[d |-> x, len |-> s[1], seg |-> s[2]] :
             x \in 1..ND, s \in {<<F, F>>, <<1, 1>>, <<2 * F, F>>, <<F + 1, F>>, <<F + 1, F + 1>>}}
Gone == [d |-> 0, len |-> F, seg |-> F]
Avail(room) == {s \in Shapes \cup {Gone} : s.len <= room}

ASSUME /\ GOSSIP \subseteq 1..K /\ FLIP \subseteq 1..K /\ L >= 1 /\ F >= 2 /\ 2 * F + 2 <= MD /\ MD <= OUT
       /\ \A s \in Shapes : T!Segs(s.len, s.seg) <= L

(* gos: the sessions whose broadcast flag is set; late: the broadcast sessions whose flag was set while they waited in
   the ordinary queue (a ghost of ClassFlagOK) *)
VARIABLES qs, ctrl, stash, pc, buf, gos, late
vars == <<qs, ctrl, stash, pc, buf, gos, late>>

Class(i, c) == T!Cls(i \in gos, c)

Init == /\ qs = <<<<>>, <<>>>>
        /\ ctrl = [i \in 1..K |-> FALSE]
        /\ stash = <<>>
        /\ pc = "idle"
        /\ buf = T!NoBuf
        /\ gos = GOSSIP
        /\ late = {}

(* the host's other calls, between two poll_transmit calls *)
MarkDirty == /\ pc = "idle"
             /\ \E i \in 1..K : qs' = T!Enq(qs, i, Class(i, ctrl[i]))
             /\ UNCHANGED <<ctrl, stash, pc, buf, gos, late>>
(* queue_sub_open promotes the session (dirty_promote); the settle after it queues it if it was not waiting *)
QueueOpen == /\ pc = "idle"
             /\ \E i \in gos : /\ ctrl' = [ctrl EXCEPT ![i] = TRUE]
                               /\ qs' = T!Enq(T!Promote(qs, i, 1), i, 1)
                               /\ late' = late \ {i}
             /\ UNCHANGED <<stash, pc, buf, gos>>
(* Command::SetGossip: the flag changes, then dirty_promote *)
SetGossip == /\ pc = "idle"
             /\ \E i \in FLIP, g \in BOOLEAN :
                  /\ g # (i \in gos)
                  /\ gos' = IF g THEN gos \cup {i} ELSE gos \ {i}
                  /\ qs' = T!Promote(qs, i, T!Cls(g, ctrl[i]))
                  /\ late' = IF T!Cls(g, ctrl[i]) = 2 /\ T!InQ(qs[1], i) THEN late \cup {i} ELSE late \ {i}
             /\ UNCHANGED <<ctrl, stash, pc, buf>>

(* a call with nothing kept *)
Start == pc = "idle" /\ stash = <<>> /\ pc' = "loop" /\ UNCHANGED <<qs, ctrl, stash, buf, gos, late>>

(* send_stash: the kept datagram leaves alone, or is dropped (no address, a buffer too short, held by the ledger) *)
StashOut ==
    /\ pc = "idle" /\ stash # <<>>
    /\ stash' = <<>>
    /\ UNCHANGED <<qs, ctrl, gos, late>>
    /\ IF stash[1].d = 0 \/ stash[1].len > OUT
       THEN pc' = "loop" /\ UNCHANGED buf
       ELSE \E ok \in BOOLEAN : IF ok THEN pc' = "out" /\ buf' = T!NewBuf(stash[1])
                                ELSE pc' = "loop" /\ UNCHANGED buf

(* session i, first of queue qi, produced a datagram: note_sent clears its open, the session moves back *)
Served(qi, i) == /\ ctrl' = [ctrl EXCEPT ![i] = FALSE]
                 /\ qs' = T!Rotate(qs, qi, Class(i, FALSE))
                 /\ late' = late \ {i}
(* the first session of queue qi leaves it without sending (nothing to send, or its slot is gone) *)
Dropped(qi, i) == qs' = T!Pop(qs, qi) /\ late' = late \ {i}

Loop ==
    /\ pc = "loop"
    /\ UNCHANGED <<stash, gos>>
    /\ LET f == T!Front(qs)
       IN IF f = <<>> THEN pc' = "idle" /\ UNCHANGED <<qs, ctrl, buf, late>>
          ELSE \/ Dropped(f[1], f[2]) /\ UNCHANGED <<ctrl, pc, buf>>
               \/ \E r \in Avail(OUT) :
                    /\ Served(f[1], f[2])
                    /\ IF r.d = 0 THEN UNCHANGED <<pc, buf>>
                       ELSE \E ok \in BOOLEAN : IF ok THEN pc' = "batch" /\ buf' = T!NewBuf(r)
                                                ELSE UNCHANGED <<pc, buf>>

Batch ==
    /\ pc = "batch"
    /\ UNCHANGED gos
    /\ LET f == T!Front(qs)
           room == T!Room(buf, OUT, MD)
       IN IF ~T!Cont(buf, L, OUT) \/ f = <<>> THEN pc' = "out" /\ UNCHANGED <<qs, ctrl, stash, buf, late>>
          ELSE \/ room < MD /\ pc' = "out" /\ UNCHANGED <<qs, ctrl, stash, buf, late>>
               \/ Dropped(f[1], f[2]) /\ UNCHANGED <<ctrl, stash, pc, buf>>
               \/ \E r \in Avail(room) :
                    /\ Served(f[1], f[2])
                    /\ IF ~T!Joins(buf, r, L)
                       THEN stash' = <<r>> /\ pc' = "out" /\ UNCHANGED buf
                       ELSE /\ UNCHANGED stash
                            /\ \E ok \in BOOLEAN :
                                 IF ok THEN /\ buf' = T!Join(buf, r)
                                            /\ pc' = IF T!Full(buf, r) THEN "batch" ELSE "out"
                                 ELSE UNCHANGED <<buf, pc>>

Out == pc = "out" /\ pc' = "idle" /\ buf' = T!NoBuf /\ UNCHANGED <<qs, ctrl, stash, gos, late>>

Next == MarkDirty \/ QueueOpen \/ SetGossip \/ Start \/ StashOut \/ Loop \/ Batch \/ Out
Spec == Init /\ [][Next]_vars

TypeOK == /\ pc \in {"idle", "loop", "batch", "out"}
          /\ ctrl \in [1..K -> BOOLEAN]
          /\ stash \in {<<>>} \cup {<<s>> : s \in Shapes \cup {Gone}}
          /\ gos \subseteq 1..K /\ late \subseteq gos

QueueWF == /\ \A qi \in 1..2 : \A j, k \in 1..Len(qs[qi]) : qs[qi][j] = qs[qi][k] => j = k
           /\ \A i \in 1..K : ~(T!InQ(qs[1], i) /\ T!InQ(qs[2], i))
           /\ Len(qs[1]) + Len(qs[2]) <= K

ClassOK == \A qi \in 1..2 : \A k \in 1..Len(qs[qi]) : Class(qs[qi][k], ctrl[qs[qi][k]]) = qi
ClassFlagOK == /\ \A k \in 1..Len(qs[2]) : Class(qs[2][k], ctrl[qs[2][k]]) = 2
               /\ \A k \in 1..Len(qs[1]) : Class(qs[1][k], ctrl[qs[1][k]]) = 1 \/ qs[1][k] \in late

Built == pc \in {"batch", "out"}

Shape == Built => /\ Len(buf.segs) >= 1
                  /\ buf.d >= 1
                  /\ \A k \in 1..Len(buf.segs) : buf.segs[k].d = buf.d
                  /\ \A k \in 1..(Len(buf.segs) - 1) : buf.segs[k].n = buf.seg
                  /\ buf.segs[Len(buf.segs)].n \in 1..buf.seg
SegLimit == Built => Len(buf.segs) <= L
Fits == Built => T!BLen(buf) <= OUT
ChargedOK == Built => buf.charged = T!BLen(buf) + OVH * Len(buf.segs)
StashFirst == pc \in {"loop", "batch"} => stash = <<>>

(* reachability witnesses *)
NoStash == stash = <<>>
NotFull == ~(pc = "out" /\ Len(buf.segs) = L)
=============================================================================
