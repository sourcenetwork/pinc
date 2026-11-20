----------------------------- MODULE WireCursor -----------------------------
(***************************************************************************)
(* The bounded cursors of pinc-wire, Reader (reader.rs) and Writer          *)
(* (writer.rs), against the invariants their module documentation states: *)
(*                                                                         *)
(* Reader: "every read checks bounds first and, on failure, consumes       *)
(* nothing and returns WireError::Truncated; returned slices borrow the    *)
(* original input". Checked as:                                            *)
(*   RCursor     pos + remaining = the input length, and the rest is the   *)
(*               input after pos (nothing is read past the end);           *)
(*   RShort      a call succeeds exactly when the input left holds what it *)
(*               asks (n bytes, N bytes, a whole varint, one byte to peek);*)
(*   RAdvance    on success the position advances by exactly the bytes    *)
(*               taken (0 for peek_u8), and the result is those bytes of   *)
(*               the input, their big-endian value, or the varint they     *)
(*               encode;                                                   *)
(*   RRefused    on failure the state is unchanged and the error is        *)
(*               Truncated with needed = what was asked minus what is left *)
(*               (1 for peek_u8 and a cut varint), or the varint's error.  *)
(* Writer: "a write that does not fit fails with BufferTooSmall and leaves *)
(* the written content and position unchanged". Checked as:                *)
(*   WBound      the buffer keeps its length, pos <= its length, and no    *)
(*               cell after pos was ever written;                          *)
(*   WFits       a write succeeds exactly when its bytes fit in what       *)
(*               remains (and a varint is below 2^63);                     *)
(*   WAdvance    on success pos advances by exactly the bytes of the call, *)
(*               which are the bytes given, the big-endian form of the     *)
(*               value or its canonical varint, and the content before is  *)
(*               kept;                                                     *)
(*   WRefused    on failure the buffer and pos are unchanged and the error *)
(*               is BufferTooSmall with needed = the shortfall, or         *)
(*               VarintOverflow exactly from 2^63; ensure answers the same *)
(*               fit question and changes nothing.                         *)
(*                                                                         *)
(* A cursor's next call depends only on its state, and every state a       *)
(* sequence of calls reaches is a state these cases start from (the reader *)
(* at any position of its input, the writer at any position of its         *)
(* buffer with the cells after it never written), so checking one call     *)
(* from each such state covers every sequence: a case is a seed state      *)
(* reached by a real call (read_bytes(p), put_slice of p bytes) and one    *)
(* call after it. The cases are the states of one machine whose root has   *)
(* one successor per input or buffer size.                                 *)
(*                                                                         *)
(* Bounds (WireCursor.cfg): the reader on every input of 0 to 3 bytes over *)
(* {0, 1, 128, 255} and eight inputs of 8 to 10 bytes (u64 reads, a        *)
(* 9-byte varint, the largest varint, too long, non-minimal, truncated);   *)
(* the writer on every buffer of 0 to 10 bytes (a 9-byte varint and a u64  *)
(* fit, 11 bytes never do).                                                *)
(***************************************************************************)
EXTENDS WireCursorOps

VARIABLE c

(* ---- the domain ---- *)

Alpha == {0, 1, 128, 255}
RShort == UNION {[1..n -> Alpha] : n \in 0..3}
RLong == {<<1, 2, 3, 4, 5, 6, 7, 8>>, <<1, 2, 3, 4, 5, 6, 7, 8, 9>>, [i \in 1..8 |-> 255],
          [i \in 1..8 |-> 128] \o <<1>>, [i \in 1..8 |-> 255] \o <<127>>, [i \in 1..9 |-> 255],
          [i \in 1..8 |-> 128] \o <<0>>, [i \in 1..10 |-> 128]}
RInputs == RShort \cup RLong

RNs == {U!W(k) : k \in {0, 1, 2, 3, 4, 8, 9, 10}} \cup {U!Max64}
RCalls == {[op |-> "peek"], [op |-> "varint"]} \cup {[op |-> "bytes", n |-> x] : x \in RNs}
          \cup {[op |-> "uN", k |-> k] : k \in {1, 2, 4, 8}}

WCap == 10
U64Val == U!Add(U!Shl(U!W(16909060), 32), U!W(84281096))   \* 0x0102030405060708
WCalls == {[op |-> "slice", b |-> [i \in 1..k |-> i]] : k \in {0, 1, 2, 3, 9, 10, 11}}
          \cup {[op |-> "uN", k |-> 1, v |-> U!W(171)], [op |-> "uN", k |-> 2, v |-> U!W(258)],
                [op |-> "uN", k |-> 4, v |-> U!W(16909060)], [op |-> "uN", k |-> 8, v |-> U64Val],
                [op |-> "uN", k |-> 8, v |-> U!Max64]}
          \cup {[op |-> "varint", v |-> x] :
                  x \in {U!W(0), U!W(127), U!W(128), U!Sub(U!Pw(63), U!One), U!Pw(63), U!Max64}}
          \cup {[op |-> "ensure", n |-> x] : x \in {U!W(0), U!W(1), U!W(10), U!W(11), U!Max64}}

(* ---- the machine of cases ---- *)

Init == c = [t |-> "root"]

Next ==
    \/ c.t = "root" /\ \E s \in RInputs : c' = [t |-> "rseed", in |-> s]
    \/ c.t = "root" /\ \E cap \in 0..WCap : c' = [t |-> "wseed", cap |-> cap]
    \/ c.t = "rseed" /\ \E p \in 0..Len(c.in), cl \in RCalls :
           LET pre == RReadBytes(RNew(c.in), U!W(p)).st
           IN c' = [t |-> "r", in |-> c.in, pre |-> pre, cl |-> cl, x |-> RCall(pre, cl)]
    \/ c.t = "wseed" /\ \E p \in 0..c.cap, cl \in WCalls :
           LET pre == WPutSlice(WNew(c.cap), [i \in 1..p |-> 9]).st
           IN c' = [t |-> "w", cap |-> c.cap, pre |-> pre, cl |-> cl, x |-> WCall(pre, cl)]

Spec == Init /\ [][Next]_c

(* ---- the properties, stated from the documentation ---- *)

RCursor(in, r) == r.pos + Len(r.rest) = Len(in) /\ r.rest = SubSeq(in, r.pos + 1, Len(in))

(* the bytes a call must take when the input left holds them, or -1 when it must be refused *)
RTake(r, cl) ==
    CASE cl.op = "peek" -> (IF Len(r.rest) >= 1 THEN 0 ELSE -1)
      [] cl.op = "bytes" -> (IF U!Le(cl.n, U!W(Len(r.rest))) THEN U!Val(cl.n) ELSE -1)
      [] cl.op = "uN" -> (IF cl.k <= Len(r.rest) THEN cl.k ELSE -1)
      [] cl.op = "varint" -> IF V!Decode(r.rest).kind = "ok" THEN V!Decode(r.rest).n ELSE -1

RStepOK(in, pre, cl, x) ==
    LET k == RTake(pre, cl)
        taken == SubSeq(in, pre.pos + 1, pre.pos + k)
    IN /\ RCursor(in, pre) /\ RCursor(in, x.st)                                         \* RCursor
       /\ (x.res.kind = "ok") <=> (k >= 0)                                              \* RShort
       /\ (k >= 0) =>                                                                   \* RAdvance
            /\ x.st.pos = pre.pos + k
            /\ (CASE cl.op = "peek" -> x.res.b = in[pre.pos + 1]
                  [] cl.op = "bytes" -> x.res.bytes = taken
                  [] cl.op = "uN" -> Len(taken) = cl.k /\ BeBytes(x.res.v, cl.k) = taken
                  [] cl.op = "varint" -> V!Encode(x.res.v, 16) = [kind |-> "ok", bytes |-> taken])
       /\ (k < 0) =>                                                                    \* RRefused
            /\ x.st = pre
            /\ (CASE cl.op = "peek" -> x.res = Trunc(U!One)
                  [] cl.op = "bytes" -> x.res = Trunc(U!Sub(cl.n, U!W(Len(pre.rest))))
                  [] cl.op = "uN" -> x.res = Trunc(U!W(cl.k - Len(pre.rest)))
                  [] cl.op = "varint" ->
                       IF V!Decode(pre.rest).kind = "truncated" THEN x.res = Trunc(U!One)
                       ELSE x.res = [kind |-> V!Decode(pre.rest).kind])

(* the bytes a write must append: the slice, the big-endian form of the value, the canonical varint *)
WBytes(cl) ==
    CASE cl.op = "slice" -> cl.b
      [] cl.op = "uN" -> BeBytes(cl.v, cl.k)
      [] cl.op = "varint" -> V!Encode(cl.v, 16).bytes

Untouched(w) == \A i \in (w.pos + 1)..Len(w.buf) : w.buf[i] = -1

WStepOK(cap, pre, cl, x) ==
    /\ Len(pre.buf) = cap /\ Len(x.st.buf) = cap /\ x.st.pos <= cap                     \* WBound
    /\ Untouched(pre) /\ Untouched(x.st)
    /\ SubSeq(x.st.buf, 1, pre.pos) = SubSeq(pre.buf, 1, pre.pos)
    /\ IF cl.op = "ensure"
       THEN /\ x.st = pre
            /\ (x.res.kind = "ok") <=> U!Le(cl.n, U!W(cap - pre.pos))
            /\ (x.res.kind # "ok") => x.res = Small(U!Sub(cl.n, U!W(cap - pre.pos)))
       ELSE IF cl.op = "varint" /\ ~U!Lt(cl.v, U!Pw(63))
       THEN x.res = [kind |-> "overflow"] /\ x.st = pre                                 \* WRefused
       ELSE LET bs == WBytes(cl)
            IN /\ (x.res.kind = "ok") <=> (pre.pos + Len(bs) <= cap)                    \* WFits
               /\ (x.res.kind = "ok") =>                                                \* WAdvance
                    /\ x.st.pos = pre.pos + Len(bs)
                    /\ SubSeq(x.st.buf, pre.pos + 1, x.st.pos) = bs
                    /\ (cl.op = "uN" => Len(bs) = cl.k /\ BeWord(bs) = cl.v)
               /\ (x.res.kind # "ok") =>                                                \* WRefused
                    /\ x.st = pre
                    /\ x.res = Small(U!W(pre.pos + Len(bs) - cap))

Inv ==
    CASE c.t = "r" -> RStepOK(c.in, c.pre, c.cl, c.x)
      [] c.t = "w" -> /\ WStepOK(c.cap, c.pre, c.cl, c.x)
                      /\ WWritten(c.x.st) = SubSeq(c.x.st.buf, 1, c.x.st.pos)
                      /\ WRemaining(c.x.st) = c.cap - c.x.st.pos
      [] OTHER -> TRUE

(* ---- witnesses: TLC must find these violated (the refusal paths are reached) ---- *)

(* a read refused while bytes are left: the case where a reader that took a prefix would be caught *)
NoShortWithBytesLeft == ~(c.t = "r" /\ c.x.res.kind = "truncated" /\ Len(c.pre.rest) > 0)

(* a write refused while some room is left: the case where a writer that wrote a prefix would be caught *)
NoPartialRefusal == ~(c.t = "w" /\ c.cl.op # "ensure" /\ c.x.res.kind = "small" /\ WRemaining(c.pre) > 0)
=============================================================================
