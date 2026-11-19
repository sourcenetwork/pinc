------------------------------ MODULE WireCbor ------------------------------
(***************************************************************************)
(* The strict DAG-CBOR codec of pinc-wire (cbor/*.rs), the operators of    *)
(* WireCborOps.tla, against what the module documentation states: "the     *)
(* decoder accepts only the canonical DAG-CBOR subset (minimal arguments,  *)
(* definite lengths, valid UTF-8, 64-bit finite floats, only tag 42 over a *)
(* 0x00-prefixed byte string, text map keys unique and in length-then-     *)
(* bytewise order) and the encoder emits exactly that subset, so decode    *)
(* then encode is the identity"; map keys are checked by MapReader and by  *)
(* skip_value; nesting is bounded by MAX_DEPTH; every encoder method is    *)
(* atomic.                                                                 *)
(*                                                                         *)
(* The subset is stated here apart from the code: SpecFirst decides the    *)
(* first item of a byte string from the head rules (a width is minimal     *)
(* when no shorter form holds the argument), SpecValue is a recursive      *)
(* descent over one value (keys text and strictly increasing by KeyLess,   *)
(* shorter first then bytewise; the content of a tag a byte string         *)
(* starting with 0x00; at most MaxDepth arrays and maps open, as the       *)
(* documentation of skip_value and MAX_DEPTH counts them).                 *)
(*                                                                         *)
(*   KeysOK      check_key_order accepts exactly KeyLess, refuses an equal *)
(*               key as a duplicate and a smaller one as out of order;     *)
(*   DecOK       next_item on a fresh decoder decides as SpecFirst (the    *)
(*               same error kind, the same needed count, the same bytes    *)
(*               consumed), never reads past the input, and an accepted    *)
(*               item re-encodes with the encoder to exactly the bytes it  *)
(*               took (decode then encode is the identity, so there is one *)
(*               accepted encoding per value); the item after a tag is     *)
(*               accepted exactly when it is a byte string starting with   *)
(*               0x00, and the pair re-encodes with tag_cid;               *)
(*   EncOK       every encoder call fits exactly when the room is at least *)
(*               its encoding, writes that encoding whatever the room, and *)
(*               on a refusal writes nothing and names the shortfall (a    *)
(*               non-finite float is refused whatever the room); the       *)
(*               encoding is in the subset (SpecFirst) and decodes back to *)
(*               the same item followed by any rest (round trip);          *)
(*   SkipAgrees  skip_value on a fresh decoder decides as SpecValue (kind, *)
(*               bytes consumed, needed count), never past the input;      *)
(*   MapAgrees   walking a map with MapReader and skip_value of each value *)
(*               decides as skip_value of the whole map with one more      *)
(*               frame, and the keys it returns are strictly increasing;   *)
(*   MkOK        MapKeys::key accepts a key exactly when one is still      *)
(*               declared, it follows the previous key by KeyLess and it   *)
(*               fits, writes nothing on a refusal, and a completed map    *)
(*               (each key followed by null) is accepted whole by          *)
(*               skip_value and by MapReader with the same keys.           *)
(*                                                                         *)
(* The cases are the states of one machine; Parts picks the families:      *)
(*  "keys" every pair of keys of 0 to 3 bytes over {0, 97, 255};           *)
(*  "dec"  every first byte 0..255 followed by each of 37 tails (every     *)
(*         argument width minimal and not, float bits finite and not,      *)
(*         payloads, invalid UTF-8 of each kind, tag contents);            *)
(*  "enc"  80 encoder calls (12 boundary arguments for each of unsigned,   *)
(*         negative, array and map, byte and text strings of 0 to 256      *)
(*         bytes, CIDs of 0 to 255 bytes, booleans, null, 9 floats) into   *)
(*         buffers of 0, 1, L - 1, L and L + 1 bytes (L the encoding);     *)
(*  "skip" every sequence of up to MaxTok tokens (scalars, empty, one- and *)
(*         two-element arrays and maps, tag 42; keys "a", "b", "aa" and a  *)
(*         non-text key; tag contents good, empty and not starting with    *)
(*         0x00), grown while skip_value still answers Truncated;          *)
(*  "mk"   ordered_map of 0, 1 and 2 entries into a 7-byte buffer, then    *)
(*         key calls from {"", "a", "b", "aa"}, each accepted key followed *)
(*         by null.                                                        *)
(***************************************************************************)
EXTENDS WireCborOps

CONSTANT Parts

VARIABLE c

(* ---- the subset, stated apart from the code ---- *)

(* the DAG-CBOR key order: shorter first, then bytewise *)
KeyLess(p, k) ==
    \/ Len(p) < Len(k)
    \/ Len(p) = Len(k) /\ \E j \in 1..Len(p) : p[j] < k[j] /\ \A m \in 1..(j - 1) : p[m] = k[m]

(* the bytes of the argument for an additional information below 28 *)
ArgWidth(ai) == IF ai <= 23 THEN 0 ELSE IF ai = 24 THEN 1 ELSE IF ai = 25 THEN 2 ELSE IF ai = 26 THEN 4 ELSE 8

(* the form of additional information ai can carry the argument a *)
Holds(ai, a) == IF ai <= 23 THEN a = U!W(ai) ELSE U!Lt(a, U!Pw(8 * ArgWidth(ai)))

(* minimal: no shorter form carries the argument *)
Minimal(ai, a) == \A ai2 \in 0..27 : ArgWidth(ai2) < ArgWidth(ai) => ~Holds(ai2, a)

(* the decision on the first item of s: [kind |-> "ok", n (its bytes), hd (its head bytes), mj, a],
   [kind |-> "truncated", needed], or [kind |-> "noncanon"] *)
SpecFirst(s) ==
    IF Len(s) = 0 THEN [kind |-> "truncated", needed |-> U!One]
    ELSE LET mj == s[1] \div 32
             ai == s[1] % 32
             w == ArgWidth(ai)
             a == IF ai <= 23 THEN U!W(ai) ELSE BeWord(SubSeq(s, 2, 1 + w))
             avail == Len(s) - 1 - w
             p == SubSeq(s, 2 + w, 1 + w + U!Val(a))
         IN IF mj = 7
            THEN IF ai \in {20, 21, 22} THEN [kind |-> "ok", n |-> 1, hd |-> 1, mj |-> 7, a |-> U!Zero]
                 ELSE IF ai # 27 THEN [kind |-> "noncanon"]
                 ELSE IF Len(s) < 9 THEN [kind |-> "truncated", needed |-> U!W(9 - Len(s))]
                 ELSE IF Finite(a) THEN [kind |-> "ok", n |-> 9, hd |-> 9, mj |-> 7, a |-> U!Zero]
                 ELSE [kind |-> "noncanon"]
            ELSE IF ai >= 28 THEN [kind |-> "noncanon"]
            ELSE IF avail < 0 THEN [kind |-> "truncated", needed |-> U!W(0 - avail)]
            ELSE IF ~Minimal(ai, a) THEN [kind |-> "noncanon"]
            ELSE IF mj \in {2, 3} /\ U!Lt(U!W(avail), a) THEN [kind |-> "truncated", needed |-> U!Sub(a, U!W(avail))]
            ELSE IF mj = 3 /\ ~Utf8Ok(p) THEN [kind |-> "noncanon"]
            ELSE IF mj \in {2, 3} THEN [kind |-> "ok", n |-> 1 + w + U!Val(a), hd |-> 1 + w, mj |-> mj, a |-> a]
            ELSE IF mj = 6 /\ a # U!W(TagCid) THEN [kind |-> "noncanon"]
            ELSE [kind |-> "ok", n |-> 1 + w, hd |-> 1 + w, mj |-> mj, a |-> a]

Rest(s, j) == SubSeq(s, j + 1, Len(s))

(* the content of a tag at offset j: a byte string whose first byte is 0x00 *)
SpecCid(s, j) ==
    LET g == SpecFirst(Rest(s, j))
    IN IF g.kind # "ok" THEN g
       ELSE IF g.mj = 2 /\ g.n > g.hd /\ s[j + g.hd + 1] = 0 THEN [kind |-> "ok", end |-> j + g.n]
       ELSE [kind |-> "noncanon"]

(* one value at offset i inside `open` open arrays and maps: [kind |-> "ok", end] or the first error *)
RECURSIVE SpecValue(_, _, _, _), SpecArr(_, _, _, _, _), SpecMap(_, _, _, _, _, _)
SpecValue(s, i, open, md) ==
    LET f == SpecFirst(Rest(s, i))
        j == i + f.n
    IN IF f.kind # "ok" THEN f
       ELSE IF f.mj = 6 THEN SpecCid(s, j)
       ELSE IF f.mj \notin {4, 5} \/ f.a = U!Zero THEN [kind |-> "ok", end |-> j]
       ELSE IF f.mj = 5 /\ ~U!Lt(f.a, U!Pw(63)) THEN [kind |-> "truncated", needed |-> UsizeMax]
       ELSE IF open >= md THEN [kind |-> "depth"]
       ELSE IF f.mj = 4 THEN SpecArr(s, j, f.a, open + 1, md)
       ELSE SpecMap(s, j, f.a, open + 1, md, NoKey)

SpecArr(s, j, cnt, open, md) ==
    LET v == SpecValue(s, j, open, md)
    IN IF cnt = U!Zero THEN [kind |-> "ok", end |-> j]
       ELSE IF v.kind # "ok" THEN v
       ELSE SpecArr(s, v.end, U!Sub(cnt, U!One), open, md)

SpecMap(s, j, cnt, open, md, prev) ==
    LET kf == SpecFirst(Rest(s, j))
        key == SubSeq(s, j + kf.hd + 1, j + kf.n)
        v == SpecValue(s, j + kf.n, open, md)
    IN IF cnt = U!Zero THEN [kind |-> "ok", end |-> j]
       ELSE IF kf.kind # "ok" THEN kf
       ELSE IF kf.mj # 3 THEN [kind |-> "noncanon"]
       ELSE IF prev.some /\ ~KeyLess(prev.k, key) THEN [kind |-> "noncanon"]
       ELSE IF v.kind # "ok" THEN v
       ELSE SpecMap(s, v.end, U!Sub(cnt, U!One), open, md, SomeKey(key))

(* ---- the domain ---- *)

MaxTok == 5
MkCap == 7

KStrs == UNION {[1..n -> {0, 97, 255}] : n \in 0..3}

AS(n) == [i \in 1..n |-> 97]
Tails ==
    {<<>>, <<23>>, <<24>>, <<42>>, <<43>>, <<255>>, <<0, 42>>,
     <<0, 255>>, <<1, 0>>, <<0, 0, 255, 255>>, <<0, 1, 0, 0>>,
     <<0, 0, 0, 0, 255, 255, 255, 255>>, <<0, 0, 0, 1, 0, 0, 0, 0>>, [i \in 1..8 |-> 255],
     <<127, 240, 0, 0, 0, 0, 0, 0>>, <<63, 240, 0, 0, 0, 0, 0, 0>>, <<128, 0, 0, 0, 0, 0, 0, 0>>,
     <<127, 239, 255, 255, 255, 255, 255, 255>>,
     AS(23), <<24>> \o AS(24), <<24>> \o AS(23),
     <<42, 65, 0>>, <<42, 64>>, <<42, 65, 1>>, <<42, 1>>, <<42, 216, 42>>, <<42, 65>>,
     <<195, 169>>, <<192, 128>>, <<237, 160, 128>>, <<240, 159, 152, 128>>, <<244, 144, 128, 128>>,
     <<224, 128, 128>>, <<128>>, <<195>>, <<97, 0>>, <<0, 97>>}

Args == {U!W(0), U!W(1), U!W(23), U!W(24), U!W(42), U!W(255), U!W(256), U!W(65535), U!W(65536),
         U!Sub(U!Pw(32), U!One), U!Pw(32), U!Max64}
BPay(n) == [i \in 1..n |-> (i * 7) % 256]
(* 0.0, the least subnormal, -0.0, 1.0, the largest finite, +inf, -inf, a quiet NaN, a signalling NaN *)
Floats == {U!Zero, U!One, U!Pw(63), U!Shl(U!W(1023), 52), U!Sub(U!Shl(U!W(2047), 52), U!One),
           U!Shl(U!W(2047), 52), U!Shl(U!W(4095), 52), U!Shl(U!W(32760), 48), U!Add(U!Shl(U!W(2047), 52), U!One)}
EncCalls ==
    {[op |-> o, a |-> x] : o \in {"uns", "neg", "array", "map"}, x \in Args}
    \cup {[op |-> "bytes", b |-> BPay(n)] : n \in {0, 1, 23, 24, 255, 256}}
    \cup {[op |-> "text", b |-> t] : t \in {<<>>, <<97>>, <<195, 169>>, <<240, 159, 152, 128>>, AS(23), AS(24),
                                              AS(255), AS(256)}}
    \cup {[op |-> "cid", b |-> [i \in 1..n |-> i % 256]] : n \in {0, 1, 22, 23, 254, 255}}
    \cup {[op |-> "bool", v |-> x] : x \in BOOLEAN} \cup {[op |-> "null"]}
    \cup {[op |-> "float", a |-> f] : f \in Floats}

FullCap(cl) == IF cl.op \in {"bytes", "text", "cid"} THEN Len(cl.b) + 20 ELSE 20
Full(cl) == ECall(WNew(FullCap(cl)), cl)
EncCaps(cl) == LET l == Len(WWritten(Full(cl).st)) IN {0, 1, l - 1, l, l + 1} \ {-1}

Leaf(bs) == [b |-> bs, kids |-> 0, map |-> FALSE, tag |-> FALSE]
VT == {Leaf(<<1>>), Leaf(<<128>>), Leaf(<<97, 97>>),
       [b |-> <<129>>, kids |-> 1, map |-> FALSE, tag |-> FALSE],
       [b |-> <<130>>, kids |-> 2, map |-> FALSE, tag |-> FALSE],
       [b |-> <<161>>, kids |-> 2, map |-> TRUE, tag |-> FALSE],
       [b |-> <<162>>, kids |-> 4, map |-> TRUE, tag |-> FALSE],
       [b |-> <<216, 42>>, kids |-> 1, map |-> FALSE, tag |-> TRUE]}
KT == {Leaf(<<97, 97>>), Leaf(<<97, 98>>), Leaf(<<98, 97, 97>>), Leaf(<<1>>)}
CT == {Leaf(<<65, 0>>), Leaf(<<64>>), Leaf(<<65, 1>>)}

(* the generator's own stack of open containers, to offer keys, tag contents or values *)
Toks(g) ==
    IF g = <<>> THEN VT
    ELSE IF g[Len(g)].tag THEN CT
    ELSE IF g[Len(g)].map /\ g[Len(g)].left % 2 = 0 THEN KT
    ELSE VT

RECURSIVE GPop(_)
GPop(g) == IF g # <<>> /\ g[Len(g)].left = 0 THEN GPop(SubSeq(g, 1, Len(g) - 1)) ELSE g

GenStep(g, tk) ==
    LET g1 == IF g = <<>> THEN g ELSE [g EXCEPT ![Len(g)].left = @ - 1]
        g2 == IF tk.kids > 0 THEN Append(g1, [left |-> tk.kids, map |-> tk.map, tag |-> tk.tag]) ELSE g1
    IN GPop(g2)

EKeys == {<<>>, <<97>>, <<98>>, <<97, 97>>}

(* ---- the machine of cases ---- *)

Init == c = [t |-> "root"]

Next ==
    \/ c.t = "root" /\ \E p \in Parts : c' = [t |-> "part", p |-> p]
    \/ c.t = "part" /\ c.p = "keys" /\ c' = [t |-> "keys"]
    \/ c.t = "part" /\ c.p = "dec" /\ \E b \in 0..255 : c' = [t |-> "decb", b |-> b]
    \/ c.t = "decb" /\ \E tl \in Tails : c' = [t |-> "dec", s |-> <<c.b>> \o tl]
    \/ c.t = "part" /\ c.p = "enc" /\ \E cl \in EncCalls : c' = [t |-> "encv", cl |-> cl]
    \/ c.t = "encv" /\ \E cap \in EncCaps(c.cl) : c' = [t |-> "enc", cl |-> c.cl, cap |-> cap]
    \/ c.t = "part" /\ c.p = "skip" /\ c' = [t |-> "skip", s |-> <<>>, g |-> <<>>, nt |-> 0]
    \/ /\ c.t = "skip" /\ c.nt < MaxTok /\ (c.s = <<>> \/ c.g # <<>>)
       /\ SkipValue(Fresh(c.s)).res.kind = "truncated"
       /\ \E tk \in Toks(c.g) : c' = [t |-> "skip", s |-> c.s \o tk.b, g |-> GenStep(c.g, tk), nt |-> c.nt + 1]
    \/ c.t = "part" /\ c.p = "mk" /\ \E len \in 0..2 :
           LET h == EHeader(WNew(MkCap), 5, U!W(len))
           IN c' = [t |-> "mk", w |-> h.st, mk |-> [left |-> U!W(len), prev |-> NoKey], n |-> len, keys |-> <<>>,
                    ph |-> "key", last |-> [op |-> "omap", res |-> h.res]]
    \/ c.t = "mk" /\ c.ph = "key" /\ \E key \in EKeys :
           LET x == MKey(c.mk, c.w, key)
           IN c' = [c EXCEPT !.w = x.st, !.mk = x.mk,
                             !.keys = IF x.res.kind = "ok" THEN Append(@, key) ELSE @,
                             !.ph = IF x.res.kind = "ok" THEN "val" ELSE "key",
                             !.last = [op |-> "key", key |-> key, res |-> x.res, w0 |-> c.w, mk0 |-> c.mk]]
    \/ c.t = "mk" /\ c.ph = "val" /\
           LET x == ENull(c.w)
           IN c' = [c EXCEPT !.w = x.st, !.ph = IF x.res.kind = "ok" THEN "key" ELSE "stuck",
                             !.last = [op |-> "null", res |-> x.res]]

Spec == Init /\ [][Next]_c

(* ---- the properties ---- *)

KeysOK ==
    /\ \A k \in KStrs : KeyCheck(NoKey, k) = Ok
    /\ \A p, k \in KStrs :
         LET r == KeyCheck(SomeKey(p), k)
         IN /\ (r = Ok) <=> KeyLess(p, k)
            /\ (r = NC("duplicate map key")) <=> (p = k)
            /\ (r = NC("map keys out of order")) <=> KeyLess(k, p)

(* the encoder call that writes an item; a tag's head is the head tag_cid writes *)
ItemCall(it) ==
    CASE it.k \in {"uns", "neg", "array", "map", "float"} -> [op |-> it.k, a |-> it.a]
      [] it.k \in {"bytes", "text"} -> [op |-> it.k, b |-> it.b]
      [] it.k = "bool" -> [op |-> "bool", v |-> it.v]
      [] it.k = "null" -> [op |-> "null"]

TagHead == SubSeq(WWritten(ETagCid(WNew(4), <<>>).st), 1, 2)

(* the encoder, into a buffer of exactly Len(bytes), writes exactly bytes for the item *)
Canon(it, bytes) ==
    IF it.k = "tag" THEN bytes = TagHead
    ELSE LET e == ECall(WNew(Len(bytes)), ItemCall(it))
         IN e.res.kind = "ok" /\ WWritten(e.st) = bytes

SameDecision(res, sp) ==
    /\ res.kind = sp.kind
    /\ (sp.kind = "truncated" => res.needed = sp.needed)

DecOK(s) ==
    LET x == NextItem(Fresh(s))
        sp == SpecFirst(s)
        it == x.res.item
        n == x.d.r.pos
        rest == x.d.r.rest
        y == NextItem(x.d)
        sp2 == SpecFirst(rest)
        isCid == sp2.kind = "ok" /\ sp2.mj = 2 /\ sp2.n > sp2.hd /\ rest[sp2.hd + 1] = 0
    IN /\ SameDecision(x.res, sp)
       /\ x.res.kind = "ok" =>
            /\ n = sp.n /\ n <= Len(s) /\ rest = SubSeq(s, n + 1, Len(s))
            /\ Canon(it, SubSeq(s, 1, n))
            /\ (it.k = "text" => Utf8Ok(it.b))
            /\ rest # <<>> =>
                 IF it.k = "tag"
                 THEN /\ (y.res.kind = "ok") <=> isCid
                      /\ (sp2.kind # "ok" => SameDecision(y.res, sp2))
                      /\ (sp2.kind = "ok" /\ ~isCid =>
                            y.res = NC("tag 42 content must be a byte string starting with 0x00"))
                      /\ (y.res.kind = "ok" =>
                            LET t == ETagCid(WNew(y.d.r.pos), Tail(y.res.item.b))
                            IN t.res.kind = "ok" /\ WWritten(t.st) = SubSeq(s, 1, y.d.r.pos))
                 ELSE /\ SameDecision(y.res, sp2)
                      /\ (y.res.kind = "ok" => y.d.r.pos = n + sp2.n)

CallItem(cl) ==
    CASE cl.op \in {"uns", "neg", "array", "map", "float"} -> [k |-> cl.op, a |-> cl.a]
      [] cl.op \in {"bytes", "text"} -> [k |-> cl.op, b |-> cl.b]
      [] cl.op = "bool" -> [k |-> "bool", v |-> cl.v]
      [] cl.op = "null" -> [k |-> "null"]

Rests == {<<>>, <<0>>, <<255>>, <<216, 42>>}

RoundTrip(cl, fb, rest) ==
    LET x == NextItem(Fresh(fb \o rest))
        y == NextItem(x.d)
    IN IF cl.op = "cid"
       THEN /\ x.res = OkItem([k |-> "tag", a |-> U!W(TagCid)]) /\ x.d.r.pos = 2
            /\ y.res = OkItem([k |-> "bytes", b |-> <<0>> \o cl.b]) /\ y.d.r.pos = Len(fb)
       ELSE x.res = OkItem(CallItem(cl)) /\ x.d.r.pos = Len(fb)

InSubset(cl, fb) ==
    LET f == SpecFirst(fb)
        g == SpecFirst(Rest(fb, 2))
    IN IF cl.op = "cid"
       THEN /\ f.kind = "ok" /\ f.mj = 6 /\ f.n = 2
            /\ g.kind = "ok" /\ g.mj = 2 /\ 2 + g.n = Len(fb) /\ SubSeq(fb, 2 + g.hd + 1, Len(fb)) = <<0>> \o cl.b
       ELSE f.kind = "ok" /\ f.n = Len(fb)

EncOK(cl, cap) ==
    LET x == ECall(WNew(cap), cl)
        full == Full(cl)
        fb == WWritten(full.st)
    IN IF cl.op = "float" /\ ~Finite(cl.a)
       THEN x.res = NC("NaN and infinity are not allowed") /\ x.st = WNew(cap)
       ELSE /\ full.res.kind = "ok"
            /\ (x.res.kind = "ok") <=> (cap >= Len(fb))
            /\ (x.res.kind = "ok") =>
                 /\ WWritten(x.st) = fb
                 /\ \A i \in (Len(fb) + 1)..cap : x.st.buf[i] = -1
            /\ (x.res.kind # "ok") => (x.res = Small(U!W(Len(fb) - cap)) /\ x.st = WNew(cap))
            /\ InSubset(cl, fb)
            /\ \A rest \in Rests : RoundTrip(cl, fb, rest)

SkipAgrees(s) ==
    LET x == SkipValue(Fresh(s))
        sp == SpecValue(s, 0, 0, MaxDepth)
    IN /\ SameDecision(x.res, sp)
       /\ (sp.kind = "ok" => x.d.r.pos = sp.end)
       /\ x.d.r.pos <= Len(s)

(* a map whose count fits the frame (below 2^63) *)
IsMap(s) == Len(s) > 0 /\ s[1] \div 32 = 5 /\ (SpecFirst(s).kind # "ok" \/ U!Lt(SpecFirst(s).a, U!Pw(63)))

MapAgrees(s) ==
    LET m == MapRun(s)
        y == SkipWith(Fresh(s), MaxDepth + 1)
    IN /\ m.res.kind = y.res.kind
       /\ (m.res.kind = "ok" => m.d.r.pos = y.d.r.pos)
       /\ (m.res.kind = "truncated" => m.res.needed = y.res.needed)
       /\ (m.res.kind = "noncanon" => m.res.why = y.res.why)
       /\ \A i \in 1..(Len(m.keys) - 1) : KeyLess(m.keys[i], m.keys[i + 1])

MkOK ==
    LET l == c.last
        out == WWritten(c.w)
        sk == SkipValue(Fresh(out))
        m == MapRun(out)
    IN /\ (l.op = "key" =>
             LET accept == /\ l.mk0.left # U!Zero
                           /\ (~l.mk0.prev.some \/ KeyLess(l.mk0.prev.k, l.key))
                           /\ WRemaining(l.w0) >= 1 + Len(l.key)
             IN /\ (l.res.kind = "ok") <=> accept
                /\ (l.res.kind # "ok") => (c.w = l.w0 /\ c.mk = l.mk0)
                /\ (l.res.kind = "ok") =>
                     /\ WWritten(c.w) = WWritten(l.w0) \o <<96 + Len(l.key)>> \o l.key
                     /\ c.mk.left = U!Sub(l.mk0.left, U!One))
       /\ (c.ph = "key" /\ c.mk.left = U!Zero =>
             /\ sk.res.kind = "ok" /\ sk.d.r.pos = Len(out)
             /\ m.res.kind = "ok" /\ m.d.r.pos = Len(out) /\ m.keys = c.keys /\ Len(c.keys) = c.n)

Inv ==
    CASE c.t = "keys" -> KeysOK
      [] c.t = "dec" -> DecOK(c.s)
      [] c.t = "enc" -> EncOK(c.cl, c.cap)
      [] c.t = "skip" -> SkipAgrees(c.s) /\ (IsMap(c.s) => MapAgrees(c.s))
      [] c.t = "mk" -> MkOK
      [] OTHER -> TRUE

(* witness: TLC must find a skip case refused for depth (the bound is reached) *)
NoDepth == c.t = "skip" => SkipValue(Fresh(c.s)).res.kind # "depth"
=============================================================================
