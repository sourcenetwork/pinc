----------------------------- MODULE PortMapText -----------------------------
(***************************************************************************)
(* The byte-text helpers of the UPnP leg: pinc-portmap text.rs.            *)
(*                                                                         *)
(* The code, step for step on byte sequences (a byte is an integer 0..255, *)
(* a Rust position is 0-based, Slice(s, a, b) is s[a..b]): the writer Out  *)
(* (`new`, `put`, `dec`, `ip4`, `done`), `find`, `trim`, `parse_u32`,      *)
(* `parse_ip4`, `header`, `element` and `tag`. A u32 is a record           *)
(* [hi, lo] of value hi * 65536 + lo (TLC integers are 32 bits wide); the  *)
(* accumulator of parse_u32 is a u64 in the code and here hi runs past     *)
(* 65535 (at most 152587 for ten digits). The usize subtraction of `dec`   *)
(* (`i -= 1`) stops TLC with an error if it could underflow.               *)
(*                                                                         *)
(* What the documentation of text.rs claims, stated apart from the code:   *)
(*  - WriterOK: after a run of puts into a buffer of cap bytes, `done` is  *)
(*    the total length when every put fit and None otherwise (an overflow  *)
(*    is reported, never a silent cut); the buffer holds the bytes of the  *)
(*    puts before the first that did not fit, in order, and nothing at or  *)
(*    after the point that put would have started (nothing more is written *)
(*    after an overflow, a later put that would fit included); n <= cap.   *)
(*  - DecOK: `dec` writes the decimal form of v: digits only, one to ten,  *)
(*    no leading zero unless v = 0, of value v.                            *)
(*  - ParseOK: `parse_u32` takes exactly a string of one to ten ASCII      *)
(*    digits that is at most 4294967295 (by the digits, compared as        *)
(*    strings), and its value; RoundTrip: parse_u32 of what dec wrote is   *)
(*    v; the value's own decimal form is the input without leading zeros.  *)
(*  - Ip4OK: `parse_ip4` takes exactly four dot-separated parts of one to  *)
(*    three digits each of value at most 255; it reads back what `ip4`     *)
(*    wrote.                                                               *)
(*  - TrimOK, FindOK: `trim` removes exactly the leading and trailing      *)
(*    spaces and tabs; `find` is the first position of the needle.         *)
(* No operator reads outside its input: TLC stops on an index outside a    *)
(* sequence, so a finished check shows none is reached on the domain.      *)
(*                                                                         *)
(* Checked over: buffers of 0 to 6 bytes with every run of up to 4 puts of *)
(* 0 to 4 bytes (5467 runs); `dec` of 0..999 and of 2^j - 1, 2^j, 2^j + 1  *)
(* (j in 0..32 within u32) and 10^k - 1, 10^k, 10^k + 1 (k in 0..9), each *)
(* boundary value also into every buffer of 0 to 11 bytes; parse_u32 of   *)
(* every string of 0 to 3 bytes over / 0 1 5 9 : and space, of the decimal *)
(* forms of the boundary values with a leading zero and with a trailing    *)
(* colon, and of the eleven-digit strings; parse_ip4 of every address over *)
(* the octets 0, 9, 10, 255 and of twelve malformed forms; trim of every   *)
(* string of up to 4 bytes over space, tab, a, b; find of every haystack   *)
(* of up to 5 bytes over a, b with every needle of up to 2 bytes. About    *)
(* 9800 states.                                                            *)
(*                                                                         *)
(* PortMapText_full.cfg is a witness: a run whose first overflow is        *)
(* followed by a put that would have fit is reached (NoLaterFit).          *)
(*                                                                         *)
(* PortMapUpnp.tla takes Find, Trim, ParseU32, ParseIp4, Header, Element   *)
(* and the writer from here (INSTANCE PortMapText WITH c <- 0).            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLE c

(* ---- helpers ---- *)
PanicSeq(msg) == IF Assert(FALSE, msg) THEN <<>> ELSE <<>>
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y
MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x
\* Rust s[a..b] (0-based, end exclusive); the caller has 0 <= a <= b <= Len(s)
Slice(s, a, b) == SubSeq(s, a + 1, b)
\* Rust s.get(a..b): defined when a <= b <= len
GetOk(s, a, b) == 0 <= a /\ a <= b /\ b <= Len(s)
IsDigit(x) == x >= 48 /\ x <= 57
\* u8::is_ascii_whitespace: space, tab, newline, form feed, carriage return
IsWs(x) == x \in {32, 9, 10, 12, 13}
Lower(x) == IF x >= 65 /\ x <= 90 THEN x + 32 ELSE x
\* <[u8]>::eq_ignore_ascii_case
EqIC(a, b) == Len(a) = Len(b) /\ \A k \in 1..Len(a) : Lower(a[k]) = Lower(b[k])

(* ---- u32 values as [hi, lo] ---- *)
W32(n) == [hi |-> n \div 65536, lo |-> n % 65536]
IsZero(x) == x.hi = 0 /\ x.lo = 0
\* x / 10 and x % 10 by long division over the two limbs
DivMod10(x) ==
    LET cur == (x.hi % 10) * 65536 + x.lo
    IN [q |-> [hi |-> x.hi \div 10, lo |-> cur \div 10], r |-> cur % 10]
\* x * 10 + d (the accumulator of parse_u32, a u64 in the code)
MulAdd10(x, d) == LET l == x.lo * 10 + d IN [hi |-> x.hi * 10 + l \div 65536, lo |-> l % 65536]
AddSmall(x, d) == LET l == x.lo + d IN [hi |-> x.hi + l \div 65536, lo |-> l % 65536]
SubOne(x) == IF x.lo > 0 THEN [x EXCEPT !.lo = @ - 1] ELSE [hi |-> x.hi - 1, lo |-> 65535]
RECURSIVE HornerR(_, _, _)
HornerR(b, k, acc) == IF k > Len(b) THEN acc ELSE HornerR(b, k + 1, MulAdd10(acc, b[k] - 48))
\* the value of a string of digits
Horner(b) == HornerR(b, 1, [hi |-> 0, lo |-> 0])

(* ---- the code: the writer ---- *)
\* Out::new over a buffer of cap bytes that holds `fill`
NewOut(cap, fill) == [buf |-> [k \in 1..cap |-> fill], n |-> 0, ok |-> TRUE]
\* Out::put: end = n + len (saturating_add, which a buffer in memory never reaches); buf.get_mut(n..end) is Some iff
\* end <= len, and the bytes are copied only while ok
Put(w, b) ==
    LET e == w.n + Len(b)
    IN IF e <= Len(w.buf) /\ w.ok
       THEN [w EXCEPT !.buf = [k \in 1..Len(w.buf) |-> IF k > w.n /\ k <= e THEN b[k - w.n] ELSE w.buf[k]], !.n = e]
       ELSE [w EXCEPT !.ok = FALSE]
\* Out::dec: the loop over digits[0..10] from the end, then put(digits[i..])
RECURSIVE DecLoop(_, _, _)
DecLoop(v, i, acc) ==
    IF i = 0 THEN PanicSeq("usize subtraction underflows in Out::dec")
    ELSE LET dm == DivMod10(v)
             acc2 == <<48 + dm.r>> \o acc
         IN IF IsZero(dm.q) \/ i - 1 = 0 THEN acc2 ELSE DecLoop(dm.q, i - 1, acc2)
DecBytes(v) == DecLoop(v, 10, <<>>)
PutDec(w, v) == Put(w, DecBytes(v))
\* Out::ip4: dec(a) . dec(b) . dec(c) . dec(d)
PutIp4(w, o) ==
    LET w1 == PutDec(w, W32(o[1]))
        w2 == PutDec(Put(w1, <<46>>), W32(o[2]))
        w3 == PutDec(Put(w2, <<46>>), W32(o[3]))
    IN PutDec(Put(w3, <<46>>), W32(o[4]))
\* Out::done: the length written, or -1 for None
Done(w) == IF w.ok THEN w.n ELSE -1
\* the bytes of what was written (the caller's buf[..n])
Written(w) == SubSeq(w.buf, 1, w.n)
Ip4Bytes(o) == Written(PutIp4(NewOut(15, 0), o))

(* ---- the code: searching and parsing ---- *)
\* text::find: Some(0) for an empty needle, else the first window equal to it (-1 for None)
Find(h, n) ==
    IF Len(n) = 0 THEN 0
    ELSE LET P == {p \in 0..(Len(h) - Len(n)) : Slice(h, p, p + Len(n)) = n}
         IN IF P = {} THEN -1 ELSE MinOf(P)
\* text::trim: without leading and trailing spaces and tabs
Trim(b) ==
    LET keep == {k \in 0..(Len(b) - 1) : b[k + 1] # 32 /\ b[k + 1] # 9}
        start == IF keep = {} THEN Len(b) ELSE MinOf(keep)
        end == IF keep = {} THEN start ELSE MaxOf(keep) + 1
    IN Slice(b, start, end)
\* <[u8]>::split(|x| x == sep): the pieces between the separators (one empty piece for an empty input)
Split(b, sep) ==
    LET Q == {p \in 0..(Len(b) - 1) : b[p + 1] = sep}
        n == Cardinality(Q)
        at(k) == CHOOSE p \in Q : Cardinality({q \in Q : q < p}) = k - 1
        bound(j) == IF j = 0 THEN -1 ELSE IF j = n + 1 THEN Len(b) ELSE at(j)
    IN [j \in 1..(n + 1) |-> SubSeq(b, bound(j - 1) + 2, bound(j))]
\* text::parse_u32: [ok, v]
NoneU == [ok |-> FALSE, v |-> [hi |-> 0, lo |-> 0]]
ParseU32(b) ==
    IF Len(b) = 0 \/ Len(b) > 10 THEN NoneU
    ELSE IF \E k \in 1..Len(b) : ~IsDigit(b[k]) THEN NoneU
    ELSE LET v == Horner(b) IN IF v.hi < 65536 THEN [ok |-> TRUE, v |-> v] ELSE NoneU
\* text::parse_ip4: [ok, o]
NoneIp == [ok |-> FALSE, o |-> <<0, 0, 0, 0>>]
PartOk(p) == Len(p) <= 3 /\ ParseU32(p).ok /\ ParseU32(p).v.hi = 0 /\ ParseU32(p).v.lo <= 255
ParseIp4(b) ==
    LET P == Split(b, 46)
    IN IF Len(P) = 4 /\ \A j \in 1..4 : PartOk(P[j])
       THEN [ok |-> TRUE, o |-> <<ParseU32(P[1]).v.lo, ParseU32(P[2]).v.lo, ParseU32(P[3]).v.lo, ParseU32(P[4]).v.lo>>]
       ELSE NoneIp
\* text::header: the trimmed value of the first line (split on \n, a trailing \r cut) whose trimmed name before the
\* first colon equals `name` ignoring ASCII case; [ok, v]
StripCr(l) == IF Len(l) > 0 /\ l[Len(l)] = 13 THEN SubSeq(l, 1, Len(l) - 1) ELSE l
HeaderAt(l, name) ==
    LET line == StripCr(l)
        colon == Find(line, <<58>>)
    IN colon >= 0 /\ EqIC(Trim(Slice(line, 0, colon)), name)
Header(head, name) ==
    LET L == Split(head, 10)
        J == {j \in 1..Len(L) : HeaderAt(L[j], name)}
    IN IF J = {} THEN [ok |-> FALSE, v |-> <<>>]
       ELSE LET line == StripCr(L[MinOf(J)])
                colon == Find(line, <<58>>)
            IN [ok |-> TRUE, v |-> Trim(Slice(line, colon + 1, Len(line)))]
\* the name of a tag: inner up to its first whitespace, after its last colon
TagLocal(inner) ==
    LET ws == {k \in 0..(Len(inner) - 1) : IsWs(inner[k + 1])}
        word == IF ws = {} THEN inner ELSE Slice(inner, 0, MinOf(ws))
        cs == {k \in 0..(Len(word) - 1) : word[k + 1] = 58}
    IN IF cs = {} THEN word ELSE Slice(word, MaxOf(cs) + 1, Len(word))
\* text::tag: the loop from `at`; [ok, s, e] with e the position after '>'
NoTag == [ok |-> FALSE, s |-> 0, e |-> 0]
RECURSIVE TagFrom(_, _, _, _)
TagFrom(hay, name, closing, at) ==
    LET lts == {k \in at..(Len(hay) - 1) : hay[k + 1] = 60}
    IN IF lts = {} THEN NoTag
       ELSE LET s == MinOf(lts)
                gts == {k \in s..(Len(hay) - 1) : hay[k + 1] = 62}
            IN IF gts = {} THEN NoTag
               ELSE LET gt == MinOf(gts)
                        inner0 == Slice(hay, s + 1, gt)
                    IN IF closing /\ (Len(inner0) = 0 \/ inner0[1] # 47) THEN TagFrom(hay, name, closing, gt)
                       ELSE LET inner == IF closing THEN Slice(inner0, 1, Len(inner0)) ELSE inner0
                            IN IF TagLocal(inner) = name THEN [ok |-> TRUE, s |-> s, e |-> gt + 1]
                               ELSE TagFrom(hay, name, closing, gt)
Tag(hay, name, closing) == TagFrom(hay, name, closing, 0)
\* text::element: [ok, text, next]
NoEl == [ok |-> FALSE, text |-> <<>>, next |-> 0]
Element(body, from, name) ==
    IF ~GetOk(body, from, Len(body)) THEN NoEl
    ELSE LET hay == Slice(body, from, Len(body))
             open == Tag(hay, name, FALSE)
         IN IF ~open.ok THEN NoEl
            ELSE LET start == open.e
                     rest == Slice(hay, start, Len(hay))
                     close == Tag(rest, name, TRUE)
                 IN IF ~close.ok THEN NoEl
                    ELSE [ok |-> TRUE, text |-> Trim(Slice(rest, 0, close.s)), next |-> from + start + close.e]

(* ---- the specification, stated apart from the code ---- *)
\* sums of the put lengths ps[1..k]
RECURSIVE Sum(_, _)
Sum(ps, k) == IF k = 0 THEN 0 ELSE ps[k] + Sum(ps, k - 1)
\* the byte put j writes (every byte of put j is j)
PutBytes(ps, j) == [k \in 1..ps[j] |-> j]
RECURSIVE Concat(_, _)
Concat(ps, k) == IF k = 0 THEN <<>> ELSE Concat(ps, k - 1) \o PutBytes(ps, k)
\* the first put that does not fit (Len(ps) + 1 when all fit)
FirstOver(ps, cap) ==
    LET K == {k \in 1..Len(ps) : Sum(ps, k) > cap} IN IF K = {} THEN Len(ps) + 1 ELSE MinOf(K)
WriterOK(cap, ps, w) ==
    LET k == FirstOver(ps, cap)
        n == Sum(ps, k - 1)
    IN /\ w.n = n /\ n <= cap
       /\ Done(w) = IF k = Len(ps) + 1 THEN n ELSE -1
       /\ Written(w) = Concat(ps, k - 1)
       /\ \A x \in (n + 1)..cap : w.buf[x] = 0

AllDigits(b) == \A k \in 1..Len(b) : IsDigit(b[k])
DecOK(v) ==
    LET d == DecBytes(v)
    IN /\ Len(d) \in 1..10 /\ AllDigits(d) /\ (Len(d) = 1 \/ d[1] # 48) /\ Horner(d) = v

\* the digits of u32::MAX
U32Max == <<52, 50, 57, 52, 57, 54, 55, 50, 57, 53>>
\* a <= b for digit strings of one length, by the first byte that differs
LexLe(a, b) == a = b \/ \E k \in 1..Len(a) : a[k] < b[k] /\ \A j \in 1..(k - 1) : a[j] = b[j]
StripZeros(b) ==
    LET nz == {k \in 1..Len(b) : b[k] # 48}
    IN IF nz = {} THEN <<48>> ELSE SubSeq(b, MinOf(nz), Len(b))
ParseOK(b) ==
    LET r == ParseU32(b)
        form == Len(b) \in 1..10 /\ AllDigits(b) /\ (Len(b) < 10 \/ LexLe(b, U32Max))
    IN /\ r.ok = form
       /\ r.ok => DecBytes(r.v) = StripZeros(b)
RoundTrip(v) == ParseU32(DecBytes(v)) = [ok |-> TRUE, v |-> v]

Ip4Form(b) ==
    LET P == Split(b, 46)
    IN Len(P) = 4 /\ \A j \in 1..4 : Len(P[j]) \in 1..3 /\ AllDigits(P[j])
                                    /\ (Len(P[j]) < 3 \/ LexLe(P[j], <<50, 53, 53>>))
Ip4OK(b) == ParseIp4(b).ok = Ip4Form(b)
Ip4Trip(o) == ParseIp4(Ip4Bytes(o)) = [ok |-> TRUE, o |-> o]

IsTab(x) == x = 32 \/ x = 9
TrimOK(b) ==
    LET r == Trim(b)
    IN \E i \in 0..Len(b) : \E j \in 0..(Len(b) - i) :
           /\ r = SubSeq(b, i + 1, Len(b) - j)
           /\ \A k \in 1..i : IsTab(b[k])
           /\ \A k \in (Len(b) - j + 1)..Len(b) : IsTab(b[k])
           /\ (Len(r) = 0 \/ (~IsTab(r[1]) /\ ~IsTab(r[Len(r)])))
FindOK(h, n) ==
    LET p == Find(h, n)
        at(q) == q + Len(n) <= Len(h) /\ SubSeq(h, q + 1, q + Len(n)) = n
    IN IF p >= 0 THEN at(p) /\ \A q \in 0..(p - 1) : ~at(q) ELSE \A q \in 0..Len(h) : ~at(q)

(* ---- the domain ---- *)
\* 2^j as a u32 record (j <= 31), 10^k as the value of "1" and k zeros
Pow2(j) == IF j < 16 THEN [hi |-> 0, lo |-> 2 ^ j] ELSE [hi |-> 2 ^ (j - 16), lo |-> 0]
Pow10(k) == Horner(<<49>> \o [i \in 1..k |-> 48])
MaxU32 == [hi |-> 65535, lo |-> 65535]
Edges ==
    {Pow2(j) : j \in 0..31} \cup {SubOne(Pow2(j)) : j \in 1..31} \cup {AddSmall(Pow2(j), 1) : j \in 0..31}
    \cup {Pow10(k) : k \in 0..9} \cup {SubOne(Pow10(k)) : k \in 1..9} \cup {AddSmall(Pow10(k), 1) : k \in 0..9}
    \cup {MaxU32}
Small == {W32(n) : n \in 0..999}
\* parse_u32 inputs: short strings over / 0 1 5 9 : space; the boundary forms with a leading zero, a trailing colon;
\* eleven digits
Al == {47, 48, 49, 53, 57, 58, 32}
Short == UNION {[1..n -> Al] : n \in 0..3}
Forms == UNION {{DecBytes(v), <<48>> \o DecBytes(v), DecBytes(v) \o <<58>>} : v \in Edges}
         \cup {<<52, 50, 57, 52, 57, 54, 55, 50, 57, 54>>,             \* 4294967296
               <<57, 57, 57, 57, 57, 57, 57, 57, 57, 57>>,             \* 9999999999
               <<49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48>>,         \* 10000000000
               <<48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49>>}         \* 00000000001
\* parse_ip4 inputs
Oct == {0, 9, 10, 255}
BadIp == {<<>>, <<49, 46, 50, 46, 51>>,                                 \* 1.2.3
          <<49, 46, 50, 46, 51, 46, 52, 46>>,                           \* 1.2.3.4.
          <<49, 46, 50, 46, 51, 46, 52, 46, 53>>,                       \* 1.2.3.4.5
          <<50, 53, 54, 46, 49, 46, 49, 46, 49>>,                       \* 256.1.1.1
          <<49, 46, 46, 50, 46, 51>>,                                   \* 1..2.3
          <<48, 48, 48, 49, 46, 49, 46, 49, 46, 49>>,                   \* 0001.1.1.1
          <<48, 49, 46, 49, 46, 49, 46, 49>>,                           \* 01.1.1.1 (taken: two digits)
          <<46, 49, 46, 49, 46, 49>>,                                   \* .1.1.1
          <<49, 46, 49, 46, 49, 46, 49, 32>>,                           \* "1.1.1.1 "
          <<97, 46, 49, 46, 49, 46, 49>>,                               \* a.1.1.1
          <<57, 57, 57, 46, 49, 46, 49, 46, 49>>}                       \* 999.1.1.1
TrimIn == UNION {[1..n -> {32, 9, 97, 98}] : n \in 0..4}
Hays == UNION {[1..n -> {97, 98}] : n \in 0..5}
Needles == UNION {[1..n -> {97, 98}] : n \in 0..2}

(* the cases are the states of one machine; the writer runs grow one put at a time *)
Init == c = [t |-> "root"]
Seeds ==
    {[t |-> "w", cap |-> k, ps |-> <<>>, w |-> NewOut(k, 0)] : k \in 0..6}
    \cup {[t |-> "dec", v |-> v] : v \in Small \cup Edges}
    \cup {[t |-> "deccap", v |-> v, cap |-> k] : v \in Edges, k \in 0..11}
    \cup {[t |-> "pu", b |-> b] : b \in Short \cup Forms}
    \cup {[t |-> "ip", b |-> Ip4Bytes(<<a, y, x, d>>), o |-> <<a, y, x, d>>] : a, y, x, d \in Oct}
    \cup {[t |-> "pi", b |-> b] : b \in BadIp}
    \cup {[t |-> "trim", b |-> b] : b \in TrimIn}
    \cup {[t |-> "find", h |-> h, n |-> n] : h \in Hays, n \in Needles}
Next ==
    \/ c.t = "root" /\ \E x \in Seeds : c' = x
    \/ c.t = "w" /\ Len(c.ps) < 4 /\ \E l \in 0..4 :
           LET ps == Append(c.ps, l) IN c' = [c EXCEPT !.ps = ps, !.w = Put(c.w, PutBytes(ps, Len(ps)))]
Spec == Init /\ [][Next]_c

Inv ==
    CASE c.t = "w" -> WriterOK(c.cap, c.ps, c.w)
      [] c.t = "dec" -> DecOK(c.v) /\ RoundTrip(c.v)
      [] c.t = "deccap" -> (Done(PutDec(NewOut(c.cap, 0), c.v)) = (IF Len(DecBytes(c.v)) <= c.cap THEN Len(DecBytes(c.v)) ELSE -1))
      [] c.t = "pu" -> ParseOK(c.b)
      [] c.t = "ip" -> Ip4OK(c.b) /\ Ip4Trip(c.o)
      [] c.t = "pi" -> Ip4OK(c.b)
      [] c.t = "trim" -> TrimOK(c.b)
      [] c.t = "find" -> FindOK(c.h, c.n)
      [] OTHER -> TRUE

\* Witness (PortMapText_full.cfg, which TLC must violate): no run has a put that would fit after the first overflow.
NoLaterFit ==
    c.t = "w" =>
        LET k == FirstOver(c.ps, c.cap)
        IN ~\E j \in (k + 1)..Len(c.ps) : Sum(c.ps, k - 1) + c.ps[j] <= c.cap
=============================================================================
