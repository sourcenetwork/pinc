------------------------------- MODULE StreamSend -------------------------------
(***************************************************************************)
(* The send half of a stream, pinc-transport stream/send.rs (Send<S, C>),  *)
(* over every interleaving of the calls the stream table makes on it, at   *)
(* small sizes (StreamSendOps.tla has the operators). Streams.tla models   *)
(* the table and the receive path and sees this half only as the pool      *)
(* chunks it holds and the state that frees a slot; this module is the     *)
(* half itself.                                                            *)
(*                                                                         *)
(* The environment: the application writes (WANTS bytes, ROOMS of the      *)
(* connection's send buffer cap), finishes, backs the stream with a        *)
(* source of SRCLENS bytes (whole, or one byte short), resets it; the peer *)
(* raises the window (LIMS) and asks the sender to stop (Streams::         *)
(* on_stop_sending resets the half: the same Reset); the packet builder    *)
(* takes frames of BUDGETS bytes, retransmission or fresh data, and copies *)
(* any frame below sent_max (a fresh one, a stale one built before an      *)
(* acknowledgement, or one the tail repair cut by clip); recovery declares *)
(* such frames lost or acknowledged, in any order and more than once (a    *)
(* late acknowledgement is the same call); the reset frame is taken, lost  *)
(* and acknowledged; other users take and give back pool chunks (EXTS).    *)
(* Frames are at most MAXB bytes, and a frame with the end marker ends at  *)
(* the final size the peer was told.                                       *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - send credit: credit is spent once per byte, within the peer's window *)
(*    (CreditSpent: written for a buffered stream, sent_max for a source-  *)
(*    backed one, never above the limit), nothing is sent past it          *)
(*    (SentInWindow, FramesInWindow: every frame next_frame can give ends  *)
(*    within the limit), retransmissions are free (RetxFree), and a reset  *)
(*    carries a final size the peer accepts (ResetInWindow);               *)
(*  - a retransmission never copies a released chunk: a retransmitted      *)
(*    frame starts at the acknowledged prefix (RetxAfterPrefix), from the  *)
(*    lowest lost range (LowestFirst), and any copy of any frame below     *)
(*    sent_max reads only slots that hold the chunk its offsets name and   *)
(*    no chunk ever released (CopyNeverReleased), so a stale frame whose   *)
(*    chunk's slot now holds a later chunk is refused, not copied; a write *)
(*    never writes into a slot of another chunk and never fails on the     *)
(*    pool once bounded by it (WriteSafe);                                 *)
(*  - the final size, once set, is fixed (FinalFixed), nothing is sent     *)
(*    past it (EndWithinFinal), and the peer is told one final size: every *)
(*    frame with the end marker and every reset frame carries the first    *)
(*    one told (OneFinalSize);                                             *)
(*  - the module invariants of send.rs: lost below sent_max (LostBelowSent),*)
(*    acked_prefix the end of the acknowledged prefix (ApIsPrefix), chunks *)
(*    held only from the one containing it (HeldFromPrefix), the bytes     *)
(*    written and not acknowledged held (BytesHeld), the pool within its   *)
(*    budget (Pool).                                                       *)
(* Underneath: a window of 0 at the start, the pool taken by other users,  *)
(* the ring and the range sets at capacity (LR = AR = 1: every second      *)
(* disjoint range overflows), a reset or a stop in every phase, a source   *)
(* that returns short, and the offset at MAXOFF (open_source past it is    *)
(* refused). Witnesses: StreamSend_wrap_w (a released chunk's slot holds a *)
(* later chunk: the case CopyNeverReleased guards), StreamSend_pool_w (a   *)
(* write the pool refuses), StreamSend_block_w (a source-backed stream     *)
(* blocked at the window), StreamSend_final_w (a reset after the end was   *)
(* sent).                                                                  *)
(*                                                                         *)
(* Assumption: the limits the peer gives are at most MAXOFF (a varint),    *)
(* which bounds what a buffered stream may write (write itself does not    *)
(* test MAX_OFFSET).                                                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CH, RING, B, LR, AR, MAXOFF
CONSTANTS LIM0, LIMS, WANTS, ROOMS, BUDGETS, MAXB, SRCLENS, EXTS, CODES

VARIABLE h

INSTANCE StreamSendOps

Init == \E l \in LIM0 : h = Open(New, l)

\* the frames recovery and the packet builder may name: below sent_max, at most MAXB bytes, the end marker only at
\* the final size told
Frames == {<<o, l, f>> \in (0..h.smax) \X (0..MAXB) \X BOOLEAN :
              /\ o + l <= h.smax
              /\ (l > 0 \/ f)
              /\ (f => (h.told # -1 /\ o + l = h.told))}

WriteOp == \E w \in WANTS, r \in ROOMS : h' = Write(h, w, r).s
FinishOp == h' = Finish(h).s
SourceOp == \E len \in SRCLENS, short \in 0..1 : h' = OpenSource(h, len, Max(len - short, 0)).s
ResetOp == \E c \in CODES : h' = Reset(h, c).s
RaiseOp == \E l \in LIMS : h' = RaiseLimit(h, l)
SendOp == \E retx \in BOOLEAN, b \in BUDGETS : h' = NextFrame(h, retx, b).s
CopyOp == \E f \in Frames : h' = CopyOut(h, f[1], f[2], f[3], TRUE).s
LostOp == \E f \in Frames : h' = OnLost(h, f[1], f[2], f[3]).s
AckOp == \E f \in Frames : h' = OnAcked(h, f[1], f[2], f[3]).s
TakeCtlOp == h' = TakeControl(h).s
CtlLostOp == h' = ControlLost(h, h.rcode, h.rfs)
CtlAckedOp == h' = ResetAcked(h)
ExtOp == \E n \in EXTS : h' = ExtTo(h, n)

Next == WriteOp \/ FinishOp \/ SourceOp \/ ResetOp \/ RaiseOp \/ SendOp \/ CopyOp \/ LostOp \/ AckOp
        \/ TakeCtlOp \/ CtlLostOp \/ CtlAckedOp \/ ExtOp
Spec == Init /\ [][Next]_h

(* ---- state invariants ---- *)
TypeOK == WellFormedOf(h)
Pool == PoolOf(h)
LostBelowSent == LostBelowSentOf(h)
ApIsPrefix == ApIsPrefixOf(h)
CreditSpent == CreditSpentOf(h)
SentInWindow == SentInWindowOf(h)
ResetInWindow == ResetInWindowOf(h)
EndWithinFinal == EndWithinFinalOf(h)
HeldFromPrefix == HeldFromPrefixOf(h)
BytesHeld == BytesHeldOf(h)
\* under the assumption on the limits, no offset passes MAXOFF
OffsetsInRange == Used(h) <= MAXOFF

(* ---- every call that could be made now ---- *)
FramesInWindow == \A retx \in BOOLEAN, b \in BUDGETS : LET R == NextFrame(h, retx, b) IN
    R.some => (R.off + R.len <= R.s.smax /\ R.s.smax <= h.limit)
RetxFree == \A b \in BUDGETS : LET R == NextFrame(h, TRUE, b) IN R.s.smax = h.smax /\ R.s.wr = h.wr
RetxAfterPrefix == \A b \in BUDGETS : LET R == NextFrame(h, TRUE, b) IN R.some => R.off >= h.ap
LowestFirst == \A b \in BUDGETS : LET R == NextFrame(h, TRUE, b) IN
    (R.some /\ R.len > 0) => \A k \in 1..Len(R.s.lost) : R.s.lost[k][1] >= R.off + R.len
CopyNeverReleased == \A o \in 0..h.smax : \A l \in 0..(h.smax - o) : ReadsOwnOf(h, CopyOut(h, o, l, FALSE, TRUE))
WriteSafe == \A w \in WANTS, r \in ROOMS : LET W == Write(h, w, r) IN W.err # "Exhausted" /\ ~W.alias
OneFinalSize ==
    /\ \A retx \in BOOLEAN, b \in BUDGETS : LET R == NextFrame(h, retx, b) IN
           R.fin => (R.off + R.len = h.fs /\ (h.told = -1 \/ h.told = h.fs))
    /\ LET C == TakeControl(h) IN C.some => (h.told = -1 \/ h.told = C.fs)

(* ---- transition property ---- *)
FinalFixed == [][h.fs # -1 => h'.fs = h.fs]_h

(* ---- reachability witnesses (the *_w configs must find a violation) ---- *)
\* a chunk below the one holding acked_prefix was released and its slot now holds another chunk
NoStaleReuse == ~\E k \in 0..((h.ap \div CH) - 1) : h.ring[Slot(k)] \notin {-1, k}
\* a writable stream with credit and ring room whose write the pool refuses
PoolNeverBinds == ~(Live(h) /\ ~h.src /\ h.fs = -1 /\ PoolRoom(h) = 0 /\ Credit(h) > 0 /\ RingRoom(h) > 0)
\* a source-backed stream with bytes waiting and no credit left
NeverAtWindow == ~(Live(h) /\ h.src /\ Unsent(h) > 0 /\ h.smax = h.limit)
\* the half was reset after its end marker was sent
NeverResetAfterFin == ~(h.rst # 0 /\ h.fin \in {"sent", "acked"})
=============================================================================
