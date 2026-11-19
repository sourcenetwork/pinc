--------------------------- MODULE ReconcileWire ---------------------------
(***************************************************************************)
(* The message layer of pinc-reconcile (wire.rs), written step for step:   *)
(* the reader primitives (read_u8, read_bytes, `count`), the               *)
(* prefix-compressed bound (put_bound, read_bound with its canonical       *)
(* check), the part head (tag byte with the infinity bit, lower bound,     *)
(* upper bound), the frame (frame_body, frame_header), the count field     *)
(* (put_parts, read_parts) and the item list (Items). The varint is the    *)
(* model of pinc-wire (Varint.tla, machine words); a varint decoded here   *)
(* is the integer when it is below 2^30 and the saturated value SatV       *)
(* above, which every comparison of the code (lengths, counts, limits all  *)
(* below 2^30 in the model) treats as "larger than any limit", so a huge   *)
(* varint is refused exactly as the code refuses it.                       *)
(*                                                                         *)
(* A reader is the sequence of bytes still unread; every operation returns *)
(* its result and the rest, or the reason (an operation never changes the  *)
(* caller's `last`: it is returned only on success).                       *)
(*                                                                         *)
(* Checked by TLC (ReconcileWire*.cfg) over:                               *)
(*  - every bound against every previous bound over a small alphabet,      *)
(*    every limit, with and without a rest, every cut of the encoding,     *)
(*    with the cap of the shared prefix length at 255 and (a scaled        *)
(*    config) at 1; long bounds of 255, 256 and 300 bytes at the real cap; *)
(*  - every byte string up to a length, read as a bound, a head, a bound   *)
(*    sequence, a frame, a count field and an item list: an accepted       *)
(*    string is the encoding of what it yields, and a refusal has the      *)
(*    reason of the first failing check of the code;                       *)
(*  - every frame length 0..300 and the edges of the 3-byte length, every  *)
(*    count and `more` pair around 2^6, 2^7, 2^14, 2^21 and 2^28.          *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/ReconcileWireProofs.lean,           *)
(* ReconcileWireMsg.lean):                                                 *)
(*   BoundRoundTrip     readBound_putBound                                 *)
(*   BoundCanonical     readBound_canonical, readBound_err_reason,         *)
(*                      readBound_bound_err, readBound_short,              *)
(*                      readBound_noncanon, readBound_count_err            *)
(*   BoundSizes         putBound_length, putBound_length_le                *)
(*   HeadRoundTrip      readHead_putHead, HeadCanonical readHead_canonical *)
(*   SeqRoundTrip       readBounds_putBounds, readBounds_canonical         *)
(*   FrameOK            frameBody_frameHeader, frameBody_canonical,        *)
(*                      frameBody_short, frameBody_mismatch,               *)
(*                      frameHeader_none_iff                               *)
(*   PartsOK            readParts_putParts, readParts_canonical,           *)
(*                      readParts_zero_more, readParts_truncated           *)
(*   ItemsOK            readItems_putItems, readItems_canonical,           *)
(*                      next_item_err, next_short, putItems_length         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

V == INSTANCE Varint WITH SmallMax <- 0, c <- 0

CONSTANTS MaxCpl, Alpha, BLen, RAlpha, RLen, Mode

SatV == 2 ^ 30
FrameMax == 16777215

Take(s, n) == IF n >= Len(s) THEN s ELSE SubSeq(s, 1, n)
Drop(s, n) == IF n >= Len(s) THEN <<>> ELSE SubSeq(s, n + 1, Len(s))
Min(a, b) == IF a < b THEN a ELSE b
Err(r) == [ok |-> FALSE, r |-> r]

(* ---- the varint field ---- *)
IntOf(w) == IF w[3] # 0 \/ w[4] # 0 \/ w[5] # 0 \/ w[2] >= 16384 THEN SatV ELSE V!U!Val(w)
Venc(v) == V!Encode(V!U!W(v), 16).bytes
EncLen(v) == Len(Venc(v))
(* count: a varint as a usize; a varint failure is Truncated *)
Count(r) ==
    LET d == V!Decode(r)
    IN IF d.kind = "ok"
       THEN [ok |-> TRUE, v |-> IntOf(d.v), half |-> IntOf(V!U!Shr(d.v, 1)), odd |-> d.v[1] % 2 = 1,
             rest |-> Drop(r, d.n)]
       ELSE Err("truncated")

ReadU8(r) == IF r = <<>> THEN Err("truncated") ELSE [ok |-> TRUE, v |-> Head(r), rest |-> Tail(r)]
ReadBytes(n, r) == IF n <= Len(r) THEN [ok |-> TRUE, v |-> Take(r, n), rest |-> Drop(r, n)] ELSE Err("truncated")

(* ---- bounds ---- *)
RECURSIVE Cpl(_, _)
Cpl(a, b) == IF a = <<>> \/ b = <<>> THEN 0 ELSE IF Head(a) = Head(b) THEN Cpl(Tail(a), Tail(b)) + 1 ELSE 0

PutBound(last, b) ==
    LET c == Min(Cpl(last, b), MaxCpl)
    IN [bytes |-> <<c>> \o Venc(Len(b) - c) \o Drop(b, c), last |-> b]

ReadBound(last, r, mx) ==
    IF r = <<>> THEN Err("truncated")
    ELSE LET c == Head(r)
             cn == Count(Tail(r))
         IN IF ~cn.ok THEN Err("truncated")
            ELSE LET n == cn.v
                     r2 == cn.rest
                 IN IF c > Len(last) \/ c + n > mx THEN Err("bound")
                    ELSE IF n > Len(r2) THEN Err("truncated")
                    ELSE LET sfx == Take(r2, n)
                             noncanon == (c < MaxCpl /\ Len(Drop(last, c)) > 0 /\ Len(sfx) > 0
                                         /\ Head(Drop(last, c)) = Head(sfx))
                                         \/ c > MaxCpl    \* never above 255 in the code: a byte; matters only at a scaled cap
                         IN IF noncanon THEN Err("bound")
                            ELSE [ok |-> TRUE, b |-> Take(last, c) \o sfx, rest |-> Drop(r2, n)]

(* ---- heads: hi is [none |-> TRUE] (infinity) or [none |-> FALSE, v |-> bound] ---- *)
InfBit == 128
PutHead(last, kind, lo, hi) ==
    LET b1 == PutBound(last, lo)
    IN IF hi.none THEN [bytes |-> <<kind + InfBit>> \o b1.bytes, last |-> lo]
       ELSE LET b2 == PutBound(lo, hi.v) IN [bytes |-> <<kind>> \o b1.bytes \o b2.bytes, last |-> hi.v]

ReadHead(last, r, mx) ==
    LET t == ReadU8(r)
    IN IF ~t.ok THEN t
       ELSE LET b1 == ReadBound(last, t.rest, mx)
            IN IF ~b1.ok THEN b1
               ELSE IF t.v >= InfBit
                    THEN [ok |-> TRUE, kind |-> t.v % 128, lo |-> b1.b, hi |-> [none |-> TRUE], last |-> b1.b, rest |-> b1.rest]
                    ELSE LET b2 == ReadBound(b1.b, b1.rest, mx)
                         IN IF ~b2.ok THEN b2
                            ELSE [ok |-> TRUE, kind |-> t.v, lo |-> b1.b, hi |-> [none |-> FALSE, v |-> b2.b],
                                  last |-> b2.b, rest |-> b2.rest]

(* ---- sequences of bounds against the running previous bound ---- *)
RECURSIVE PutBounds(_, _)
PutBounds(last, bs) ==
    IF bs = <<>> THEN [bytes |-> <<>>, last |-> last]
    ELSE LET p == PutBound(last, Head(bs))
             q == PutBounds(Head(bs), Tail(bs))
         IN [bytes |-> p.bytes \o q.bytes, last |-> q.last]

RECURSIVE ReadBounds(_, _, _, _)
ReadBounds(mx, k, last, r) ==
    IF k = 0 THEN [ok |-> TRUE, bs |-> <<>>, last |-> last, rest |-> r]
    ELSE LET p == ReadBound(last, r, mx)
         IN IF ~p.ok THEN p
            ELSE LET q == ReadBounds(mx, k - 1, p.b, p.rest)
                 IN IF ~q.ok THEN q ELSE [ok |-> TRUE, bs |-> <<p.b>> \o q.bs, last |-> q.last, rest |-> q.rest]

(* ---- frames ---- *)
FrameCheck(hdr, blen) ==
    IF (hdr[1] * 256 + hdr[2]) * 256 + hdr[3] = blen THEN [ok |-> TRUE] ELSE Err("frame")
FrameBody(msg) ==
    IF Len(msg) < 3 THEN Err("truncated")
    ELSE LET f == FrameCheck(Take(msg, 3), Len(msg) - 3)
         IN IF f.ok THEN [ok |-> TRUE, body |-> Drop(msg, 3)] ELSE f
FrameHeader(len) ==
    IF len > FrameMax THEN [ok |-> FALSE] ELSE [ok |-> TRUE, bytes |-> <<len \div 65536, (len \div 256) % 256, len % 256>>]

(* ---- the count field ---- *)
PutParts(cnt, more) == Venc(cnt * 2 + (IF more THEN 1 ELSE 0))
ReadParts(r) ==
    LET c == Count(r)
    IN IF ~c.ok THEN c
       ELSE IF c.half = 0 /\ c.odd THEN Err("count")
       ELSE [ok |-> TRUE, cnt |-> c.half, more |-> c.odd, rest |-> c.rest]

(* ---- item lists ---- *)
RECURSIVE Flat(_)
Flat(xs) == IF xs = <<>> THEN <<>> ELSE Venc(Len(Head(xs))) \o Head(xs) \o Flat(Tail(xs))
PutItems(xs) == Venc(Len(xs)) \o Flat(xs)
RECURSIVE Collect(_, _, _)
Collect(mx, left, r) ==
    IF left = 0 THEN [ok |-> TRUE, xs |-> <<>>, rest |-> r]
    ELSE LET c == Count(r)
         IN IF ~c.ok THEN Err("truncated")
            ELSE IF c.v > mx THEN Err("item")
            ELSE IF c.v > Len(c.rest) THEN Err("truncated")
            ELSE LET q == Collect(mx, left - 1, Drop(c.rest, c.v))
                 IN IF ~q.ok THEN q ELSE [ok |-> TRUE, xs |-> <<Take(c.rest, c.v)>> \o q.xs, rest |-> q.rest]
ReadItems(mx, r) ==
    LET c == Count(r)
    IN IF ~c.ok THEN c ELSE Collect(mx, c.v, c.rest)
DataLen(xs) == IF xs = <<>> THEN 0 ELSE Len(Flat(xs)) 

(* the size the machine budgets for a bound of length n *)
BoundLen(n) == 1 + EncLen(n) + n

(* ---- the bounded domain ---- *)
Strs(A, L) == UNION {[1..k -> A] : k \in 0..L}
Opts == {[none |-> TRUE]} \cup {[none |-> FALSE, v |-> b] : b \in Strs(Alpha, BLen)}
Rests == {<<>>, <<0>>, <<1, 1>>}

VARIABLE c
Init == c = [t |-> "root"]

Zeros(n) == [i \in 1..n |-> 0]
OneAt(n, i, v) == [j \in 1..n |-> IF j = i THEN v ELSE 0]
BigVarints == {V!Encode(V!U!Pw(k), 16).bytes : k \in {30, 31, 40, 62}} \cup {<<128, 0>>, <<128>>, <<255, 255, 255, 255, 255, 255, 255, 255, 255, 1>>}

Seeds ==
    CASE Mode = "small" ->
            {[f |-> "bound", last |-> l] : l \in Strs(Alpha, BLen)}
              \cup {[f |-> "canon", last |-> l] : l \in Strs(Alpha, BLen)}
              \cup {[f |-> "head", last |-> l] : l \in Strs(Alpha, BLen)}
              \cup {[f |-> "seq", last |-> l] : l \in Strs(Alpha, 2)}
              \cup {[f |-> "headcanon", last |-> l] : l \in Strs(Alpha, 2)}
              \cup {[f |-> "big", last |-> l] : l \in Strs(Alpha, 2)}
              \cup {[f |-> "frame", k |-> k] : k \in 0..3}
              \cup {[f |-> "hdr", k |-> k] : k \in 0..2}
              \cup {[f |-> "parts", k |-> k] : k \in 0..2}
              \cup {[f |-> "pcanon"]}
              \cup {[f |-> "items", k |-> k] : k \in 0..2}
              \cup {[f |-> "icanon"]}
      [] Mode = "long" ->
            {[f |-> "long", n |-> n] : n \in {254, 255, 256, 257, 300}}

(* the cases of a seed *)
Expand(sd) ==
    CASE sd.f = "bound" ->
            {[t |-> "bound", last |-> sd.last, b |-> b, mx |-> mx, rest |-> rs] :
                 b \in Strs(Alpha, BLen), mx \in 0..BLen, rs \in Rests}
      [] sd.f = "canon" ->
            {[t |-> "canon", last |-> sd.last, r |-> r, mx |-> mx] : r \in Strs(RAlpha, RLen), mx \in 0..BLen}
      [] sd.f = "head" ->
            {[t |-> "head", last |-> sd.last, kind |-> kd, lo |-> lo, hi |-> hi, mx |-> BLen, rest |-> rs] :
                 kd \in {0, 1, 7, 127}, lo \in Strs(Alpha, BLen), hi \in Opts, rs \in Rests}
      [] sd.f = "headcanon" ->
            {[t |-> "headcanon", last |-> sd.last, r |-> r] : r \in Strs({0, 1, 2, 129}, 5)}
      [] sd.f = "seq" ->
            {[t |-> "seq", last |-> sd.last, bs |-> bs, rest |-> rs] :
                 bs \in Strs(Strs(Alpha, 2), 3), rs \in Rests}
      [] sd.f = "big" ->
            {[t |-> "big", last |-> sd.last, r |-> <<cb>> \o vb \o rs, mx |-> mx] :
                 cb \in {0, 1, 2}, vb \in BigVarints, rs \in {<<>>, <<0, 0>>}, mx \in {0, 3}}
      [] sd.f = "frame" ->
            {[t |-> "frame", msg |-> m] : m \in Strs({0, 1, 2, 255}, 4)}
              \cup {[t |-> "frame", msg |-> <<0, 0, k>> \o Zeros(k)] : k \in 0..8}
      [] sd.f = "hdr" ->
            {[t |-> "hdr", len |-> len] : len \in 0..300}
              \cup {[t |-> "hdr", len |-> len] : len \in {255, 256, 65535, 65536, 65537, FrameMax - 1, FrameMax, FrameMax + 1, FrameMax + 2, 2 ^ 30}}
      [] sd.f = "parts" ->
            {[t |-> "parts", cnt |-> cnt, more |-> m, rest |-> rs] :
                 cnt \in (0..300) \cup {2 ^ 6 - 1, 2 ^ 6, 2 ^ 7 - 1, 2 ^ 7, 2 ^ 14 - 1, 2 ^ 14, 2 ^ 21 - 1, 2 ^ 21, 2 ^ 28 - 1},
                 m \in BOOLEAN, rs \in Rests}
      [] sd.f = "pcanon" ->
            {[t |-> "pcanon", r |-> r] : r \in Strs({0, 1, 2, 128, 129, 255}, 3)}
      [] sd.f = "items" ->
            {[t |-> "items", xs |-> xs, mx |-> mx, rest |-> rs] :
                 xs \in Strs(Strs({0, 1}, 2), 3), mx \in 0..3, rs \in Rests}
      [] sd.f = "icanon" ->
            {[t |-> "icanon", r |-> r, mx |-> mx] : r \in Strs({0, 1, 2, 3}, 6), mx \in {1, 2}}
      [] sd.f = "long" ->
            LET n == sd.n
                last == Zeros(n)
                bs == {Zeros(n), Zeros(n) \o <<0>>, Zeros(n - 1), Zeros(n + 1), OneAt(n, n, 7), OneAt(n, 255, 7),
                       OneAt(n, 256, 7), OneAt(n, 254, 7), Zeros(255) \o <<5>>, Zeros(254) \o <<5>>, <<>>, <<1>>}
            IN {[t |-> "bound", last |-> last, b |-> b, mx |-> 400, rest |-> rs] : b \in bs, rs \in Rests}
               \cup {[t |-> "canonlong", last |-> last, r |-> <<k>> \o Venc(m) \o Zeros(m) \o <<9>>, mx |-> 400] :
                       k \in {0, 1, 253, 254, 255}, m \in {0, 1, 2}}

Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ \E x \in Expand(c.sd) : c' = x

Spec == Init /\ [][Next]_c

(* ---- the properties ---- *)

IsPrefix(p, s) == Len(p) <= Len(s) /\ Take(s, Len(p)) = p

(* a bound encoded against `last` reads back with the rest untouched; a limit below its length refuses it with
   Bound; every cut of the encoding is Truncated; the size is the formula and at most BoundLen *)
BoundOK(last, b, mx, rest) ==
    LET e == PutBound(last, b)
        cp == Min(Cpl(last, b), MaxCpl)
    IN /\ e.last = b
       /\ Len(e.bytes) = 1 + EncLen(Len(b) - cp) + (Len(b) - cp)                        \* BoundSizes
       /\ Len(e.bytes) <= BoundLen(Len(b))
       /\ IF mx >= Len(b)
          THEN /\ ReadBound(last, e.bytes \o rest, mx) = [ok |-> TRUE, b |-> b, rest |-> rest]   \* BoundRoundTrip
               /\ mx = Len(b) => \A m \in 0..(Len(e.bytes) - 1) : ReadBound(last, Take(e.bytes, m), mx) = Err("truncated")
          ELSE ReadBound(last, e.bytes \o rest, mx) = Err("bound")

(* an accepted string is the encoding of the bound it yields, so there is one encoding per bound; a refusal is
   Truncated or Bound *)
CanonOK(last, r, mx) ==
    LET d == ReadBound(last, r, mx)
    IN IF d.ok
       THEN /\ r = PutBound(last, d.b).bytes \o d.rest                                  \* BoundCanonical
            /\ Len(d.b) <= mx
            /\ Len(Take(last, Len(Take(last, Head(r))))) = Head(r)
       ELSE d.r \in {"truncated", "bound"}

HeadOK(last, kd, lo, hi, mx, rest) ==
    LET e == PutHead(last, kd, lo, hi)
        d == ReadHead(last, e.bytes \o rest, mx)
    IN /\ d = [ok |-> TRUE, kind |-> kd, lo |-> lo, hi |-> hi, last |-> e.last, rest |-> rest]    \* HeadRoundTrip
       /\ (hi.none => e.bytes[1] >= 128) /\ (~hi.none => e.bytes[1] < 128)                 \* the infinity bit
       /\ Len(e.bytes) <= 1 + BoundLen(Len(lo)) + (IF hi.none THEN 0 ELSE BoundLen(Len(hi.v)))

HeadCanonOK(last, r) ==
    LET d == ReadHead(last, r, BLen)
    IN IF d.ok
       THEN /\ d.kind < 128
            /\ LET e == PutHead(last, d.kind, d.lo, d.hi)
               IN /\ r = e.bytes \o d.rest                                              \* HeadCanonical
                  /\ d.last = e.last
       ELSE d.r \in {"truncated", "bound"}

SeqOK(last, bs, rest) ==
    LET e == PutBounds(last, bs)
        d == ReadBounds(BLen + 2, Len(bs), last, e.bytes \o rest)
    IN d = [ok |-> TRUE, bs |-> bs, last |-> e.last, rest |-> rest]                      \* SeqRoundTrip

BigOK(last, r, mx) ==
    LET d == ReadBound(last, r, mx) IN
    /\ d.ok => r = PutBound(last, d.b).bytes \o d.rest
    /\ ~d.ok => d.r \in {"truncated", "bound"}

FrameOK(msg) ==
    LET d == FrameBody(msg)
    IN /\ Len(msg) < 3 => d = Err("truncated")
       /\ d.ok =>
            /\ Len(d.body) = (msg[1] * 256 + msg[2]) * 256 + msg[3]
            /\ FrameHeader(Len(d.body)).bytes \o d.body = msg                           \* the header is the length
       /\ (Len(msg) >= 3 /\ ~d.ok) => d = Err("frame") /\ (msg[1] * 256 + msg[2]) * 256 + msg[3] # Len(msg) - 3

HdrOK(len) ==
    LET h == FrameHeader(len)
    IN /\ h.ok <=> len <= FrameMax                                                       \* frameHeader_none_iff
       /\ h.ok => /\ (h.bytes[1] * 256 + h.bytes[2]) * 256 + h.bytes[3] = len
                  /\ FrameCheck(h.bytes, len) = [ok |-> TRUE]
                  /\ FrameCheck(h.bytes, len + 1) = Err("frame")

PartsOK(cnt, m, rest) ==
    LET e == PutParts(cnt, m)
        d == ReadParts(e \o rest)
    IN /\ IF cnt = 0 /\ m THEN d = Err("count") ELSE d = [ok |-> TRUE, cnt |-> cnt, more |-> m, rest |-> rest]
       /\ Len(e) = EncLen(cnt * 2 + (IF m THEN 1 ELSE 0))

PartsCanonOK(r) ==
    LET d == ReadParts(r)
    IN IF d.ok
       THEN /\ r = PutParts(d.cnt, d.more) \o d.rest
            /\ ~(d.cnt = 0 /\ d.more)
       ELSE d.r \in {"truncated", "count"}

ItemsOK(xs, mx, rest) ==
    LET e == PutItems(xs)
        d == ReadItems(mx, e \o rest)
        longest == IF xs = <<>> THEN 0 ELSE CHOOSE n \in {Len(x) : x \in {xs[i] : i \in 1..Len(xs)}} : \A i \in 1..Len(xs) : Len(xs[i]) <= n
    IN /\ IF longest <= mx THEN d = [ok |-> TRUE, xs |-> xs, rest |-> rest]              \* ItemsRoundTrip
                           ELSE d = Err("item")                                         \* the first too long item
       /\ Len(e) = EncLen(Len(xs)) + DataLen(xs) - (IF xs = <<>> THEN 0 ELSE 0)

ItemsCanonOK(r, mx) ==
    LET d == ReadItems(mx, r)
    IN IF d.ok
       THEN /\ r = PutItems(d.xs) \o d.rest
            /\ \A i \in 1..Len(d.xs) : Len(d.xs[i]) <= mx
       ELSE d.r \in {"truncated", "item"}

Inv ==
    CASE c.t = "root" \/ c.t = "seed" -> TRUE
      [] c.t = "bound" -> BoundOK(c.last, c.b, c.mx, c.rest)
      [] c.t = "canon" -> CanonOK(c.last, c.r, c.mx)
      [] c.t = "canonlong" -> CanonOK(c.last, c.r, c.mx)
      [] c.t = "head" -> HeadOK(c.last, c.kind, c.lo, c.hi, c.mx, c.rest)
      [] c.t = "headcanon" -> HeadCanonOK(c.last, c.r)
      [] c.t = "seq" -> SeqOK(c.last, c.bs, c.rest)
      [] c.t = "big" -> BigOK(c.last, c.r, c.mx)
      [] c.t = "frame" -> FrameOK(c.msg)
      [] c.t = "hdr" -> HdrOK(c.len)
      [] c.t = "parts" -> PartsOK(c.cnt, c.more, c.rest)
      [] c.t = "pcanon" -> PartsCanonOK(c.r)
      [] c.t = "items" -> ItemsOK(c.xs, c.mx, c.rest)
      [] c.t = "icanon" -> ItemsCanonOK(c.r, c.mx)
=============================================================================
