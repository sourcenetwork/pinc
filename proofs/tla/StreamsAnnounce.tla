--------------------------- MODULE StreamsAnnounce ---------------------------
(***************************************************************************)
(* The opener's announce (pinc-transport stream/send.rs `Send::announce`,  *)
(* `wants`, `next_frame`, `requeue`; stream/table.rs `announce_top`;       *)
(* conn/api.rs `opened`) against the receiver's table of StreamsOps.tla    *)
(* (rule A: a raise whenever the room grew).                               *)
(*                                                                         *)
(* The receiver cannot see a stream the opener opened and has not written  *)
(* on. An opener refused an open for the stream limit marks the newest     *)
(* stream of each kind it opened and sent nothing on (announce_top), once  *)
(* per stream; the stream then sends an empty STREAM frame (offset 0,      *)
(* length 0, no end), or its first data frame announces it when data was   *)
(* queued meanwhile; a lost empty frame of a stream still silent is sent   *)
(* again. The receiver's locate opens every stream below the one a frame   *)
(* names (ImplicitOpens in Streams.tla), so it counts every stream the     *)
(* opener had opened of that kind.                                         *)
(*                                                                         *)
(* State: T, the receiver's table (StreamsOps); the opener (a client, so   *)
(* its streams of kind c, 0 bidirectional and 1 unidirectional, are        *)
(* 4k + 2c): po[c] the streams of kind c it opened, plim the limit it was  *)
(* given (the handshake value, raised by every MAX_STREAMS that arrives),  *)
(* wrote the streams it wrote on (one byte and its end, which arrive at    *)
(* once), ann[id] the announce state ("no", "due", "sent"), fly the empty  *)
(* frames on the way, sends[id] and lost[id] how often the empty frame of  *)
(* id was sent and lost (a ghost), last what the last arrival of an empty  *)
(* frame did (a ghost: its id, the receiver's answer, the streams the      *)
(* receiver admitted after it and the credit it had advertised before).    *)
(* The receiver ends and reads a stream, finishes its half of a            *)
(* bidirectional one, and sends its control frames (a MAX_STREAMS frame    *)
(* arrives or is lost).                                                    *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - Exact: when the empty frame of the opener's newest stream of a kind  *)
(*    has arrived, the receiver counts exactly the streams of that kind    *)
(*    the opener opened (so it knows whether all credit is used); and      *)
(*    CountInOpened: it never counts more;                                 *)
(*  - AnnOnce: the empty frame of a stream is sent once, again only after  *)
(*    it was lost;                                                         *)
(*  - AnnInCredit: an empty frame that arrives is admitted (never held     *)
(*    back, never a stream limit error) and the receiver admits no stream  *)
(*    past the credit it had advertised: the announce adds no state the    *)
(*    receiver did not already allow. It is the frame Frame(T, id, 0, 0,   *)
(*    FALSE, FALSE), one of the frames Streams.tla's FrameOp makes, so the *)
(*    receiver's step is one the Streams configs already check;            *)
(*  - LimitInCredit: the opener's limit is a credit the receiver gave.     *)
(* Witness StreamsAnnounce_w: Exact's case is reached (NoAnnShown is       *)
(* violated).                                                              *)
(* Not modelled: a data frame lost (the opener's data arrives at once; a   *)
(* lost one is sent again, and a stream with data is not silent, so no     *)
(* announce depends on it); the opener's windows (one byte fits the first  *)
(* window); the opener's own stream table (the receiver's is the subject). *)
(* The other direction of the connection is the same with the roles        *)
(* swapped.                                                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, MAXOFF, RETRY, RemIds, LocIds, FIRSTK, RELEASE, PERSTREAM, SPR, ARENA, MOVEBACK, BOUND
\* the opener opens at most OPENS streams in all; an empty frame is lost at most LOSSES times
CONSTANTS OPENS, LOSSES
VARIABLES T, po, plim, wrote, ann, fly, sends, lost, last
vars == <<T, po, plim, wrote, ann, fly, sends, lost, last>>

INSTANCE StreamsOps

PId(c, k) == k * 4 + 2 * c
PIds == {PId(c, k) : c \in 0..1, k \in 0..(OPENS - 1)}
Opened(id) == Idx(id) < po[Class(id)]
Top(c) == PId(c, po[c] - 1)
NoLast == [id |-> -1, err |-> "", adm |-> 0, adv |-> 0]

Init == /\ T = Init0
        /\ po = [c \in 0..1 |-> 0]
        /\ plim = Init0.ad.adv
        /\ wrote = {}
        /\ ann = [id \in PIds |-> "no"]
        /\ fly = {}
        /\ sends = [id \in PIds |-> 0]
        /\ lost = [id \in PIds |-> 0]
        /\ last = NoLast

Refused == po[0] + po[1] >= plim

\* ---- the opener
\* open_stream inside the limit: nothing goes on the wire
Open(c) == /\ ~Refused /\ po[0] + po[1] < OPENS
           /\ po' = [po EXCEPT ![c] = @ + 1]
           /\ last' = NoLast
           /\ UNCHANGED <<T, plim, wrote, ann, fly, sends, lost>>
\* an open refused for the stream limit: announce_top marks the newest stream of each kind, when it is silent and was
\* never marked (Send::announce)
Mark(a, c) == IF po[c] > 0 /\ Top(c) \notin wrote /\ a[Top(c)] = "no" THEN [a EXCEPT ![Top(c)] = "due"] ELSE a
OpenRefused == /\ Refused
               /\ ann' = Mark(Mark(ann, 0), 1)
               /\ ann' # ann
               /\ last' = NoLast
               /\ UNCHANGED <<T, po, plim, wrote, fly, sends, lost>>
\* the opener writes one byte and its end on a stream it opened; a marked stream is announced by this frame
Write(id) == /\ Opened(id) /\ id \notin wrote
             /\ wrote' = wrote \cup {id}
             /\ ann' = IF ann[id] = "due" THEN [ann EXCEPT ![id] = "sent"] ELSE ann
             /\ T' = Frame(T, id, 0, 1, TRUE, FALSE).t
             /\ last' = NoLast
             /\ UNCHANGED <<po, plim, fly, sends, lost>>
\* next_frame of a marked stream with nothing queued: the empty frame leaves
SendAnn(id) == /\ ann[id] = "due" /\ id \notin wrote
               /\ ann' = [ann EXCEPT ![id] = "sent"]
               /\ fly' = fly \cup {id}
               /\ sends' = [sends EXCEPT ![id] = @ + 1]
               /\ last' = NoLast
               /\ UNCHANGED <<T, po, plim, wrote, lost>>
\* the empty frame arrives at the receiver
Arrive(id) == /\ id \in fly
              /\ LET R == Frame(T, id, 0, 0, FALSE, FALSE)
                 IN /\ T' = R.t
                    /\ last' = [id |-> id, err |-> R.err, adm |-> AdmittedN(R.t), adv |-> T.ad.adv]
              /\ fly' = fly \ {id}
              /\ UNCHANGED <<po, plim, wrote, ann, sends, lost>>
\* the empty frame is lost: requeue marks it again while the stream is still silent
Lose(id) == /\ id \in fly /\ lost[id] < LOSSES
            /\ fly' = fly \ {id}
            /\ lost' = [lost EXCEPT ![id] = @ + 1]
            /\ ann' = IF id \notin wrote THEN [ann EXCEPT ![id] = "due"] ELSE ann
            /\ last' = NoLast
            /\ UNCHANGED <<T, po, plim, wrote, sends>>

\* ---- the receiver
\* the application reads all of a stream
Read(id) == /\ FindSlot(T, id) # 0
            /\ T' = Consume(T, id, Readable(T.slots[FindSlot(T, id)]), 0, 1).t
            /\ last' = NoLast
            /\ UNCHANGED <<po, plim, wrote, ann, fly, sends, lost>>
\* our half of a bidirectional stream ends and is acknowledged
Done(id) == /\ FindSlot(T, id) # 0 /\ ~IsUni(id)
            /\ T' = Finish(T, id, T.ext, TRUE)
            /\ last' = NoLast
            /\ UNCHANGED <<po, plim, wrote, ann, fly, sends, lost>>
\* a control frame leaves; a MAX_STREAMS frame arrives at the opener or is lost (sent again)
Control(arrives) ==
    LET P == Pending(T)
    IN /\ P.kind # "none"
       /\ T' = IF P.kind = "msts" /\ ~arrives THEN CtlLostMsts(P.t, P.max) ELSE P.t
       /\ plim' = IF P.kind = "msts" /\ arrives THEN Max(plim, P.max) ELSE plim
       /\ last' = NoLast
       /\ UNCHANGED <<po, wrote, ann, fly, sends, lost>>

Next == \/ \E c \in 0..1 : Open(c)
        \/ OpenRefused
        \/ \E id \in PIds : Write(id) \/ SendAnn(id) \/ Arrive(id) \/ Lose(id) \/ Read(id) \/ Done(id)
        \/ \E a \in BOOLEAN : Control(a)
Spec == Init /\ [][Next]_vars

CountInOpened == \A c \in 0..1 : T.rn[c] <= po[c]
Exact == \A c \in 0..1 : (po[c] > 0 /\ ann[Top(c)] = "sent" /\ Top(c) \notin fly) => T.rn[c] = po[c]
AnnOnce == \A id \in PIds : sends[id] <= lost[id] + 1
AnnInCredit == last.id # -1 => (last.err = "ok" /\ last.adm <= last.adv)
LimitInCredit == plim <= T.ad.adv
Inv == CountInOpened /\ Exact /\ AnnOnce /\ AnnInCredit /\ LimitInCredit

\* witness (StreamsAnnounce_w.cfg must violate it): the empty frame of the opener's newest stream arrives
NoAnnShown == ~\E c \in 0..1 : po[c] > 0 /\ ann[Top(c)] = "sent" /\ Top(c) \notin fly /\ Top(c) \notin wrote
=============================================================================
