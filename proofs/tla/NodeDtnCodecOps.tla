-------------------------- MODULE NodeDtnCodecOps --------------------------
(***************************************************************************)
(* The byte formats of pinc-node's delay-tolerant layer, step for step.    *)
(*                                                                         *)
(* The resume records of dtn_save.rs: `version(1)=2 | kind(1) | ...` with  *)
(*  - RECEIVED (2): `expires(8)`, nothing after;                           *)
(*  - HELD (0): `copies(2) | custody(1) 0 or 1 | alg(1) | key(32) |        *)
(*    bytes(8) | head_len(2) | head`, nothing after;                       *)
(*  - PARTIAL (1): `head_len(2) | head | runs`, a run `a(8) | b(8) |       *)
(*    b - a bytes`, any number of them, appended over time.                *)
(* Read is the parse of `restore_one` (the `read_record` of the refactor   *)
(* the trace test specifies) up to the checks against the node's state;    *)
(* EncReceived, EncHeld, EncPartial and RunsBytes are the writers          *)
(* (`dtn_save_received`, `dtn_save_held`, `dtn_save_partial`, `put_head`). *)
(* CheckRuns is `check_runs` and TakeRuns `take_runs` (its held set refuses *)
(* a range that does not start and end on a slice, pinc-dtn held.rs).      *)
(*                                                                         *)
(* The frames of dtn_wire.rs: `type(1) | length(4, big endian) | body`.    *)
(* Finish is `start` then `finish` (the header of a frame whose body has   *)
(* blen bytes); NextFrame is `next` on an input of len bytes whose first   *)
(* bytes are h; TakeU64 and TakeU16 are `take_u64` and `take_u16`.         *)
(*                                                                         *)
(* A signed head is opaque here: its bytes decode and verify exactly when  *)
(* they are in HEADS (ideal signatures, and the canonical head codec that  *)
(* DtnCodec.tla checks). Numbers over 2^30 are Nanos words (Nanos.tla).    *)
(***************************************************************************)
EXTENDS Integers, Sequences, Nanos
CONSTANT HEADS

VERSION == 2
HELD == 0
PARTIAL == 1
RECEIVED == 2
\* IdentityAlg::from_tag
ALGS == 1..4
BODYMAX == U!Pw(20)

Drop(s, n) == SubSeq(s, n + 1, Len(s))
Be2(v) == <<v \div 256, v % 256>>
Be4(w) == <<w[2] \div 256, w[2] % 256, w[1] \div 256, w[1] % 256>>
Be8(w) == <<w[4] \div 256, w[4] % 256, w[3] \div 256, w[3] % 256, w[2] \div 256, w[2] % 256, w[1] \div 256, w[1] % 256>>
FromBe2(s) == s[1] * 256 + s[2]
FromBe4(s) == <<s[3] * 256 + s[4], s[1] * 256 + s[2], 0, 0, 0>>
FromBe8(s) == <<s[7] * 256 + s[8], s[5] * 256 + s[6], s[3] * 256 + s[4], s[1] * 256 + s[2], 0>>

(***************************************************************************)
(* Records                                                                 *)
(***************************************************************************)
\* a read record: ok, the kind, and the fields of that kind (the others at a default)
Err == [ok |-> FALSE, k |-> "err", expires |-> Zero, copies |-> 0, custody |-> FALSE, alg |-> 0, key |-> <<>>,
        bytes |-> Zero, head |-> <<>>, runs |-> <<>>]
Received(e) == [Err EXCEPT !.ok = TRUE, !.k = "received", !.expires = e]
Held(cp, cu, al, key, by, hd) ==
    [Err EXCEPT !.ok = TRUE, !.k = "held", !.copies = cp, !.custody = cu, !.alg = al, !.key = key, !.bytes = by,
                !.head = hd]
Partial(hd, runs) == [Err EXCEPT !.ok = TRUE, !.k = "partial", !.head = hd, !.runs = runs]

\* the bytes after version and kind of a held record
HeldOf(r) ==
    IF Len(r) < 46 THEN Err
    ELSE LET hl == FromBe2(SubSeq(r, 45, 46))
         IN IF r[3] \notin {0, 1} \/ r[4] \notin ALGS \/ Len(r) # 46 + hl \/ SubSeq(r, 47, 46 + hl) \notin HEADS
            THEN Err
            ELSE Held(FromBe2(SubSeq(r, 1, 2)), r[3] = 1, r[4], SubSeq(r, 5, 36), FromBe8(SubSeq(r, 37, 44)),
                      SubSeq(r, 47, 46 + hl))

\* the bytes after version and kind of a partial record: the head, then the runs unread
PartialOf(r) ==
    IF Len(r) < 2 THEN Err
    ELSE LET hl == FromBe2(SubSeq(r, 1, 2))
         IN IF Len(r) < 2 + hl \/ SubSeq(r, 3, 2 + hl) \notin HEADS THEN Err
            ELSE Partial(SubSeq(r, 3, 2 + hl), Drop(r, 2 + hl))

Read(rec) ==
    IF Len(rec) < 2 \/ rec[1] # VERSION THEN Err
    ELSE LET r == Drop(rec, 2)
         IN IF rec[2] = RECEIVED THEN (IF Len(r) = 8 THEN Received(FromBe8(r)) ELSE Err)
            ELSE IF rec[2] = HELD THEN HeldOf(r)
            ELSE IF rec[2] = PARTIAL THEN PartialOf(r)
            ELSE Err

EncReceived(e) == <<VERSION, RECEIVED>> \o Be8(e)
EncHeld(cp, cu, al, key, by, hd) ==
    <<VERSION, HELD>> \o Be2(cp) \o <<IF cu THEN 1 ELSE 0>> \o <<al>> \o key \o Be8(by) \o Be2(Len(hd)) \o hd
\* a run [a |-> word, b |-> word, data |-> bytes]
RunBytes(r) == Be8(r.a) \o Be8(r.b) \o r.data
RECURSIVE RunsBytes(_)
RunsBytes(rs) == IF rs = <<>> THEN <<>> ELSE RunBytes(Head(rs)) \o RunsBytes(Tail(rs))
EncPartial(hd, rs) == <<VERSION, PARTIAL>> \o Be2(Len(hd)) \o hd \o RunsBytes(rs)

\* the bytes of a read record, written again
EncOf(x) ==
    CASE x.k = "received" -> EncReceived(x.expires)
      [] x.k = "held" -> EncHeld(x.copies, x.custody, x.alg, x.key, x.bytes, x.head)
      [] x.k = "partial" -> <<VERSION, PARTIAL>> \o Be2(Len(x.head)) \o x.head \o x.runs
      [] OTHER -> <<>>

(***************************************************************************)
(* The runs of a partial record                                            *)
(***************************************************************************)
Aligned(w, sl) == U!IsMultipleOf(w, sl)

\* check_runs: a short header or short data ends the walk whole; a bad or unaligned header refuses
RECURSIVE CheckRuns(_, _, _)
CheckRuns(bs, total, sl) ==
    IF Len(bs) < 16 THEN TRUE
    ELSE LET a == FromBe8(SubSeq(bs, 1, 8))
             b == FromBe8(SubSeq(bs, 9, 16))
         IN IF Le(b, a) \/ Lt(total, b) \/ ~Aligned(a, sl) \/ ~Aligned(b, sl) THEN FALSE
            ELSE LET n == U!Val(U!Sub(b, a))
                 IN IF Len(bs) - 16 < n THEN TRUE ELSE CheckRuns(Drop(bs, 16 + n), total, sl)

\* take_runs: the runs taken and the torn tail left (rest), or ok FALSE; with fix N5 it reads each header with the
\* parser check_runs uses (`next_run`): a header off the slices refuses even when its data is cut
RECURSIVE TakeFrom(_, _, _, _)
TakeFrom(bs, total, sl, acc) ==
    IF Len(bs) < 16 THEN [ok |-> TRUE, runs |-> acc, rest |-> bs]
    ELSE LET a == FromBe8(SubSeq(bs, 1, 8))
             b == FromBe8(SubSeq(bs, 9, 16))
         IN IF Le(b, a) \/ Lt(total, b) \/ ~Aligned(a, sl) \/ ~Aligned(b, sl)
            THEN [ok |-> FALSE, runs |-> <<>>, rest |-> <<>>]
            ELSE LET n == U!Val(U!Sub(b, a))
                 IN IF Len(bs) - 16 < n THEN [ok |-> TRUE, runs |-> acc, rest |-> bs]
                    ELSE TakeFrom(Drop(bs, 16 + n), total, sl,
                                  Append(acc, [a |-> a, b |-> b, data |-> SubSeq(bs, 17, 16 + n)]))
TakeRuns(bs, total, sl) == TakeFrom(bs, total, sl, <<>>)

(***************************************************************************)
(* Frames                                                                  *)
(***************************************************************************)
Finish(ty, blen) == <<ty>> \o Be4(IF Lt(blen, U!Pw(32)) THEN blen ELSE U!Sub(U!Pw(32), One))

NoFrame == [k |-> "none", ty |-> 0, n |-> Zero]
NextFrame(h, len) ==
    IF Lt(len, W(5)) THEN NoFrame
    ELSE LET n == FromBe4(SubSeq(h, 2, 5))
         IN IF Lt(BODYMAX, n) THEN [NoFrame EXCEPT !.k = "err"]
            ELSE IF Le(U!Add(W(5), n), len) THEN [k |-> "ok", ty |-> h[1], n |-> U!Add(W(5), n)]
            ELSE NoFrame

TakeU64(s) == IF Len(s) < 8 THEN [ok |-> FALSE, v |-> Zero, rest |-> <<>>]
              ELSE [ok |-> TRUE, v |-> FromBe8(SubSeq(s, 1, 8)), rest |-> Drop(s, 8)]
TakeU16(s) == IF Len(s) < 2 THEN [ok |-> FALSE, v |-> 0, rest |-> <<>>]
              ELSE [ok |-> TRUE, v |-> FromBe2(SubSeq(s, 1, 2)), rest |-> Drop(s, 2)]
=============================================================================
