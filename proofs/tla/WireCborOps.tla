----------------------------- MODULE WireCborOps -----------------------------
(***************************************************************************)
(* The strict DAG-CBOR codec of pinc-wire (cbor/mod.rs, cbor/decode.rs,    *)
(* cbor/encode.rs) as pure operators, written call for call on the cursors *)
(* of WireCursorOps.tla (the decoder reads through a Reader, the encoder   *)
(* writes through a Writer).                                               *)
(*                                                                         *)
(* Decoder: the state is [r, cid], the fields of the struct (the reader    *)
(* and cid_pending). ReadArg is `read_arg` (the minimal width per          *)
(* additional information 24..27, reserved 28..30, indefinite 31),         *)
(* ReadSimple `read_simple`, ReadItem `read_item`, NextItem `next_item`    *)
(* (the tag 42 content check through cid_pending, which mem::take clears), *)
(* SkipWith `skip_value` with the frame stack of MaxDepth frames (a        *)
(* sequence whose length is `depth`; `stack.get_mut(depth)` fails when it  *)
(* is MaxDepth), MapNew and NextKey `MapReader::new` and `next_key`,       *)
(* KeyCheck `check_key_order`.                                             *)
(*                                                                         *)
(* Encoder: HeadShape is `head_shape`, EHead `head` (put_u8 of the initial *)
(* byte, then the last `tail` bytes of to_be_bytes), EHeader `header`      *)
(* (ensure, then head), EString `string`, ETagCid `tag_cid`, EFloat        *)
(* `float`, EBool `bool`, ENull `null`, MKey `MapKeys::key`.               *)
(*                                                                         *)
(* An item is [k |-> kind, ...]: "uns", "neg", "array", "map", "tag" and   *)
(* "float" carry the argument a (a U64 word; a float its bits), "bytes"    *)
(* and "text" the bytes b, "bool" the value v, "null" nothing. An error is *)
(* [kind |-> "truncated", needed], [kind |-> "noncanon", why] (the reason  *)
(* string of WireError::NonCanonical, verbatim), [kind |-> "unexpected",   *)
(* why], [kind |-> "depth"], [kind |-> "small", needed].                   *)
(*                                                                         *)
(* Assumptions, not modelled: a 64-bit usize (`usize::try_from` of a       *)
(* payload length always succeeds, usize::MAX is u64::MAX), and the        *)
(* semantics of core: `str::from_utf8` accepts exactly the well-formed     *)
(* UTF-8 of the Unicode standard (Utf8Ok, its Table 3-7), `f64::is_finite` *)
(* is "the exponent field is not all ones" (Finite), and                   *)
(* `f64::from_bits` / `to_bits` round trip a finite value's bits.          *)
(***************************************************************************)
EXTENDS WireCursorOps

CONSTANT MaxDepth

NC(why) == [kind |-> "noncanon", why |-> why]
OkItem(it) == [kind |-> "ok", item |-> it]
TagCid == 42
UsizeMax == U!Max64

(* f64::is_finite of the bits *)
Finite(bits) == U!Val(U!Low(U!Shr(bits, 52), 11)) # 2047

(* well-formed UTF-8 (Unicode Table 3-7), from byte i on *)
RECURSIVE Utf8From(_, _)
Utf8From(s, i) ==
    IF i > Len(s) THEN TRUE
    ELSE LET b == s[i]
             In(k, lo, hi) == i + k <= Len(s) /\ s[i + k] >= lo /\ s[i + k] <= hi
         IN IF b <= 127 THEN Utf8From(s, i + 1)
            ELSE IF b >= 194 /\ b <= 223 THEN In(1, 128, 191) /\ Utf8From(s, i + 2)
            ELSE IF b = 224 THEN In(1, 160, 191) /\ In(2, 128, 191) /\ Utf8From(s, i + 3)
            ELSE IF (b >= 225 /\ b <= 236) \/ b = 238 \/ b = 239
                 THEN In(1, 128, 191) /\ In(2, 128, 191) /\ Utf8From(s, i + 3)
            ELSE IF b = 237 THEN In(1, 128, 159) /\ In(2, 128, 191) /\ Utf8From(s, i + 3)
            ELSE IF b = 240 THEN In(1, 144, 191) /\ In(2, 128, 191) /\ In(3, 128, 191) /\ Utf8From(s, i + 4)
            ELSE IF b >= 241 /\ b <= 243
                 THEN In(1, 128, 191) /\ In(2, 128, 191) /\ In(3, 128, 191) /\ Utf8From(s, i + 4)
            ELSE IF b = 244 THEN In(1, 128, 143) /\ In(2, 128, 191) /\ In(3, 128, 191) /\ Utf8From(s, i + 4)
            ELSE FALSE
Utf8Ok(s) == Utf8From(s, 1)

(* ---- the decoder ---- *)

(* Decoder::new *)
Fresh(s) == [r |-> RNew(s), cid |-> FALSE]

(* Decoder::read_arg: the argument of a header; a width wider than its value needs is refused *)
ReadArg(r, info) ==
    IF info <= 23 THEN [res |-> [kind |-> "ok", a |-> U!W(info)], st |-> r]
    ELSE IF info >= 28
    THEN [res |-> IF info <= 30 THEN NC("reserved additional information")
                  ELSE NC("indefinite lengths are not allowed"), st |-> r]
    ELSE LET n == (CASE info = 24 -> 1 [] info = 25 -> 2 [] info = 26 -> 4 [] info = 27 -> 8)
             min == (CASE info = 24 -> U!W(24) [] info = 25 -> U!W(256) [] info = 26 -> U!W(65536)
                       [] info = 27 -> U!Pw(32))
             x == RReadUN(r, n)
         IN IF x.res.kind # "ok" THEN x
            ELSE IF U!Lt(x.res.v, min) THEN [res |-> NC("argument is not minimally encoded"), st |-> x.st]
            ELSE [res |-> [kind |-> "ok", a |-> x.res.v], st |-> x.st]

(* Decoder::read_simple: major type 7 *)
ReadSimple(r, info) ==
    CASE info = 20 -> [res |-> OkItem([k |-> "bool", v |-> FALSE]), st |-> r]
      [] info = 21 -> [res |-> OkItem([k |-> "bool", v |-> TRUE]), st |-> r]
      [] info = 22 -> [res |-> OkItem([k |-> "null"]), st |-> r]
      [] info \in {25, 26} -> [res |-> NC("floats must be 64-bit"), st |-> r]
      [] info = 27 ->
           (LET x == RReadUN(r, 8)
            IN IF x.res.kind # "ok" THEN x
               ELSE IF Finite(x.res.v) THEN [res |-> OkItem([k |-> "float", a |-> x.res.v]), st |-> x.st]
               ELSE [res |-> NC("NaN and infinity are not allowed"), st |-> x.st])
      [] info >= 28 -> [res |-> NC("reserved or indefinite form"), st |-> r]
      [] OTHER -> [res |-> NC("undefined and other simple values are not allowed"), st |-> r]

(* Decoder::read_payload on a 64-bit usize: the try_from always succeeds *)
ReadPayload(r, len) == RReadBytes(r, len)

(* Decoder::read_item *)
ReadItem(r) ==
    LET x == RReadUN(r, 1)
        initial == U!Val(x.res.v)
        major == initial \div 32
        info == initial % 32
        g == ReadArg(x.st, info)
        arg == g.res.a
        p == ReadPayload(g.st, arg)
    IN IF x.res.kind # "ok" THEN x
       ELSE IF major = 7 THEN ReadSimple(x.st, info)
       ELSE IF g.res.kind # "ok" THEN g
       ELSE CASE major = 0 -> [res |-> OkItem([k |-> "uns", a |-> arg]), st |-> g.st]
              [] major = 1 -> [res |-> OkItem([k |-> "neg", a |-> arg]), st |-> g.st]
              [] major = 2 -> (IF p.res.kind # "ok" THEN p
                               ELSE [res |-> OkItem([k |-> "bytes", b |-> p.res.bytes]), st |-> p.st])
              [] major = 3 -> (IF p.res.kind # "ok" THEN p
                               ELSE IF Utf8Ok(p.res.bytes)
                                    THEN [res |-> OkItem([k |-> "text", b |-> p.res.bytes]), st |-> p.st]
                                    ELSE [res |-> NC("text is not valid UTF-8"), st |-> p.st])
              [] major = 4 -> [res |-> OkItem([k |-> "array", a |-> arg]), st |-> g.st]
              [] major = 5 -> [res |-> OkItem([k |-> "map", a |-> arg]), st |-> g.st]
              [] OTHER -> IF arg = U!W(TagCid) THEN [res |-> OkItem([k |-> "tag", a |-> arg]), st |-> g.st]
                          ELSE [res |-> NC("only tag 42 is allowed"), st |-> g.st]

(* Decoder::next_item: the item after a tag must be a byte string starting with 0x00; returns [res, d] *)
NextItem(d) ==
    LET x == ReadItem(d.r)
        it == x.res.item
        cidOK == it.k = "bytes" /\ Len(it.b) >= 1 /\ it.b[1] = 0
    IN IF x.res.kind # "ok" THEN [res |-> x.res, d |-> [r |-> x.st, cid |-> d.cid]]
       ELSE IF d.cid /\ ~cidOK
       THEN [res |-> NC("tag 42 content must be a byte string starting with 0x00"), d |-> [r |-> x.st, cid |-> FALSE]]
       ELSE [res |-> x.res, d |-> [r |-> x.st, cid |-> it.k = "tag"]]

NoKey == [some |-> FALSE, k |-> <<>>]
SomeKey(key) == [some |-> TRUE, k |-> key]

(* Rust's comparison of two byte slices: lexicographic, a proper prefix first *)
RECURSIVE LexCmp(_, _, _)
LexCmp(a, b, i) ==
    IF i > Len(a) /\ i > Len(b) THEN "equal"
    ELSE IF i > Len(a) THEN "less"
    ELSE IF i > Len(b) THEN "greater"
    ELSE IF a[i] < b[i] THEN "less"
    ELSE IF a[i] > b[i] THEN "greater"
    ELSE LexCmp(a, b, i + 1)

(* check_key_order(prev, key): (prev.len(), prev.as_bytes()).cmp(&(key.len(), key.as_bytes())) *)
KeyCheck(prev, key) ==
    IF ~prev.some THEN Ok
    ELSE LET o == IF Len(prev.k) < Len(key) THEN "less"
                  ELSE IF Len(prev.k) > Len(key) THEN "greater"
                  ELSE LexCmp(prev.k, key, 1)
         IN CASE o = "less" -> Ok
              [] o = "equal" -> NC("duplicate map key")
              [] o = "greater" -> NC("map keys out of order")

(* pop the frames with nothing left: the `while` of skip_value *)
RECURSIVE PopDone(_)
PopDone(stk) == IF Len(stk) > 0 /\ stk[Len(stk)].left = U!Zero THEN PopDone(SubSeq(stk, 1, Len(stk) - 1)) ELSE stk

(* the loop of skip_value with md frames; stk[i] is [left, map, prev] *)
RECURSIVE SkipLoop(_, _, _)
SkipLoop(d, stk, md) ==
    LET depth == Len(stk)
        keyTurn == depth > 0 /\ stk[depth].map /\ U!Low(stk[depth].left, 1) = U!Zero
        x == NextItem(d)
        it == x.res.item
        kc == KeyCheck(stk[depth].prev, it.b)
        stk1 == IF depth = 0 THEN stk
                ELSE [stk EXCEPT ![depth].prev = IF keyTurn THEN SomeKey(it.b) ELSE @,
                                 ![depth].left = SatSub(@, U!One)]
        lm == (CASE it.k = "array" -> [ok |-> TRUE, left |-> it.a, map |-> FALSE]
                 [] it.k = "map" -> (IF U!Lt(it.a, U!Pw(63)) THEN [ok |-> TRUE, left |-> U!Shl(it.a, 1), map |-> TRUE]
                                     ELSE [ok |-> FALSE])
                 [] it.k = "tag" -> [ok |-> TRUE, left |-> U!One, map |-> FALSE]
                 [] OTHER -> [ok |-> TRUE, left |-> U!Zero, map |-> FALSE])
        stk2 == IF lm.left # U!Zero THEN Append(stk1, [left |-> lm.left, map |-> lm.map, prev |-> NoKey]) ELSE stk1
        stk3 == PopDone(stk2)
    IN IF x.res.kind # "ok" THEN [res |-> x.res, d |-> x.d]
       ELSE IF keyTurn /\ it.k # "text" THEN [res |-> NC("map keys must be text strings"), d |-> x.d]
       ELSE IF keyTurn /\ kc.kind # "ok" THEN [res |-> kc, d |-> x.d]
       ELSE IF ~lm.ok THEN [res |-> Trunc(UsizeMax), d |-> x.d]
       ELSE IF lm.left # U!Zero /\ depth >= md THEN [res |-> [kind |-> "depth"], d |-> x.d]
       ELSE IF Len(stk3) = 0 THEN [res |-> Ok, d |-> x.d]
       ELSE SkipLoop(x.d, stk3, md)

(* Decoder::skip_value with md frames: a scalar is one next_item, a container walks the frame stack *)
SkipWith(d, md) ==
    LET p == RPeek(d.r)
        x == NextItem(d)
    IN IF p.kind # "ok" THEN [res |-> p, d |-> d]
       ELSE IF ~((p.b \div 32) \in 4..6)
            THEN [res |-> IF x.res.kind = "ok" THEN Ok ELSE x.res, d |-> x.d]
       ELSE SkipLoop(d, <<>>, md)

SkipValue(d) == SkipWith(d, MaxDepth)

(* MapReader::new: [res, mr, d]; mr is [left, prev] *)
MapNew(d) ==
    LET x == NextItem(d)
    IN IF x.res.kind # "ok" THEN [res |-> x.res, d |-> x.d]
       ELSE IF x.res.item.k = "map"
            THEN [res |-> Ok, mr |-> [left |-> x.res.item.a, prev |-> NoKey], d |-> x.d]
       ELSE [res |-> [kind |-> "unexpected", why |-> "expected a map"], d |-> x.d]

(* MapReader::next_key: [res, mr, d]; an ok res carries key, NoKey for None *)
NextKey(mr, d) ==
    LET x == NextItem(d)
        key == x.res.item.b
        kc == KeyCheck(mr.prev, key)
    IN IF mr.left = U!Zero THEN [res |-> [kind |-> "ok", key |-> NoKey], mr |-> mr, d |-> d]
       ELSE IF x.res.kind # "ok" THEN [res |-> x.res, mr |-> mr, d |-> x.d]
       ELSE IF x.res.item.k # "text" THEN [res |-> NC("map keys must be text strings"), mr |-> mr, d |-> x.d]
       ELSE IF kc.kind # "ok" THEN [res |-> kc, mr |-> mr, d |-> x.d]
       ELSE [res |-> [kind |-> "ok", key |-> SomeKey(key)],
             mr |-> [left |-> U!Sub(mr.left, U!One), prev |-> SomeKey(key)], d |-> x.d]

(* a caller walking one map: MapReader::new, then next_key and skip_value of each value until None or an error;
   returns the last result, the keys read and the decoder *)
RECURSIVE MapLoop(_, _, _)
MapLoop(mr, d, keys) ==
    LET k == NextKey(mr, d)
        v == SkipValue(k.d)
    IN IF k.res.kind # "ok" THEN [res |-> k.res, keys |-> keys, d |-> k.d]
       ELSE IF ~k.res.key.some THEN [res |-> Ok, keys |-> keys, d |-> k.d]
       ELSE IF v.res.kind # "ok" THEN [res |-> v.res, keys |-> Append(keys, k.res.key.k), d |-> v.d]
       ELSE MapLoop(k.mr, v.d, Append(keys, k.res.key.k))

MapRun(s) ==
    LET m == MapNew(Fresh(s))
    IN IF m.res.kind # "ok" THEN [res |-> m.res, keys |-> <<>>, d |-> m.d] ELSE MapLoop(m.mr, m.d, <<>>)

(* ---- the encoder ---- *)

(* head_shape: (initial-byte info, trailing argument bytes) of the minimal header *)
HeadShape(a) ==
    IF U!Lt(a, U!W(24)) THEN [info |-> U!Val(a), tail |-> 0]
    ELSE IF U!Le(a, U!W(255)) THEN [info |-> 24, tail |-> 1]
    ELSE IF U!Le(a, U!W(65535)) THEN [info |-> 25, tail |-> 2]
    ELSE IF U!Le(a, U!Sub(U!Pw(32), U!One)) THEN [info |-> 26, tail |-> 4]
    ELSE [info |-> 27, tail |-> 8]

HeadLen(a) == 1 + HeadShape(a).tail

(* Encoder::head: put_u8(major << 5 | info)?, then put_slice(&arg.to_be_bytes()[8 - tail..]) *)
EHead(w, major, a) ==
    LET hs == HeadShape(a)
        x == WPutU8(w, major * 32 + hs.info)
    IN IF x.res.kind # "ok" THEN x ELSE WPutSlice(x.st, SubSeq(BeBytes(a, 8), 9 - hs.tail, 8))

(* Encoder::header: ensure(head_len(arg))?, then head *)
EHeader(w, major, a) ==
    LET e == WEnsure(w, U!W(HeadLen(a)))
    IN IF e.kind # "ok" THEN [res |-> e, st |-> w] ELSE EHead(w, major, a)

(* Encoder::string: ensure(head_len(len) + len)?, head, put_slice(payload) *)
EString(w, major, p) ==
    LET len == U!W(Len(p))
        e == WEnsure(w, U!W(HeadLen(len) + Len(p)))
        h == EHead(w, major, len)
    IN IF e.kind # "ok" THEN [res |-> e, st |-> w]
       ELSE IF h.res.kind # "ok" THEN h
       ELSE WPutSlice(h.st, p)

(* Encoder::tag_cid: ensure the whole, head(6, 42), head(2, len + 1), put_u8(0), put_slice(cid) *)
ETagCid(w, cid) ==
    LET len == U!W(Len(cid) + 1)
        e == WEnsure(w, U!W(HeadLen(U!W(TagCid)) + HeadLen(len) + Len(cid) + 1))
        h1 == EHead(w, 6, U!W(TagCid))
        h2 == EHead(h1.st, 2, len)
        z == WPutU8(h2.st, 0)
    IN IF e.kind # "ok" THEN [res |-> e, st |-> w]
       ELSE IF h1.res.kind # "ok" THEN h1
       ELSE IF h2.res.kind # "ok" THEN h2
       ELSE IF z.res.kind # "ok" THEN z
       ELSE WPutSlice(z.st, cid)

(* Encoder::float: the finite check first, then ensure(9)?, put_u8(0xfb), put_u64(bits) *)
EFloat(w, bits) ==
    LET e == WEnsure(w, U!W(9))
        x == WPutU8(w, 251)
    IN IF ~Finite(bits) THEN [res |-> NC("NaN and infinity are not allowed"), st |-> w]
       ELSE IF e.kind # "ok" THEN [res |-> e, st |-> w]
       ELSE IF x.res.kind # "ok" THEN x
       ELSE WPutUN(x.st, bits, 8)

(* Encoder::bool: put_u8(0xf4 | v); Encoder::null: put_u8(0xf6) *)
EBool(w, v) == WPutU8(w, IF v THEN 245 ELSE 244)
ENull(w) == WPutU8(w, 246)

(* one encoder call: [op |-> "uns" | "neg" | "array" | "map" | "float", a], [op |-> "bytes" | "text" | "cid", b],
   [op |-> "bool", v], [op |-> "null"] *)
ECall(w, cl) ==
    CASE cl.op = "uns" -> EHeader(w, 0, cl.a)
      [] cl.op = "neg" -> EHeader(w, 1, cl.a)
      [] cl.op = "bytes" -> EString(w, 2, cl.b)
      [] cl.op = "text" -> EString(w, 3, cl.b)
      [] cl.op = "array" -> EHeader(w, 4, cl.a)
      [] cl.op = "map" -> EHeader(w, 5, cl.a)
      [] cl.op = "cid" -> ETagCid(w, cl.b)
      [] cl.op = "bool" -> EBool(w, cl.v)
      [] cl.op = "null" -> ENull(w)
      [] cl.op = "float" -> EFloat(w, cl.a)

(* MapKeys::key: [res, st, mk]; mk is [left, prev]; ordered_map(len) is map(len) and [left |-> len, prev |-> NoKey] *)
MKey(mk, w, key) ==
    LET kc == KeyCheck(mk.prev, key)
        x == EString(w, 3, key)
    IN IF mk.left = U!Zero THEN [res |-> NC("more keys than the declared map length"), st |-> w, mk |-> mk]
       ELSE IF kc.kind # "ok" THEN [res |-> kc, st |-> w, mk |-> mk]
       ELSE IF x.res.kind # "ok" THEN [res |-> x.res, st |-> x.st, mk |-> mk]
       ELSE [res |-> x.res, st |-> x.st, mk |-> [left |-> U!Sub(mk.left, U!One), prev |-> SomeKey(key)]]

=============================================================================
