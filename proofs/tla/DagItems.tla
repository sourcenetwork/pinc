------------------------------- MODULE DagItems -------------------------------
(***************************************************************************)
(* The DAG-CBOR item stream that pinc-dag reads blocks and CAR headers     *)
(* from, and the CID links in it: the operators DagBlock.tla and           *)
(* DagCar.tla share.                                                       *)
(*                                                                         *)
(* Abstraction: a CBOR input is the sequence of items the strict pull      *)
(* decoder of pinc-wire (Decoder::next_item) yields from it, in order,     *)
(* with `end` TRUE when the bytes end exactly after the last item and      *)
(* FALSE when the bytes after it are not a valid item (the decoder's       *)
(* refusal: non-minimal argument, bad UTF-8, a tag other than 42 and the   *)
(* rest, which the model of the pinc-wire codec covers). Every reader of   *)
(* pinc-dag consumes the same decoder item by item, so an error of the     *)
(* decoder surfaces exactly when the reader asks for that item; the        *)
(* abstraction keeps the order of every decision. A count or an integer    *)
(* is a natural: a trace records one above 2^20 as 2^20, which no reader   *)
(* can tell apart (a count larger than the items left fails at the end of  *)
(* the items whatever its value; an integer is only compared with 1).      *)
(*                                                                         *)
(* Modelled from the code: the rule of Decoder::next_item that a tag is    *)
(* followed by a byte string starting with 0x00 (NextItem),                *)
(* Decoder::skip_value with its stack of MAX_DEPTH frames and its key      *)
(* order check (Skip), check_key_order (KeyOK), CidRef::read_cbor          *)
(* (ReadCbor), CidList::read (CidList), and skip_null of block/parse.rs    *)
(* (SkipNull). The CIDs inside are parsed and ordered by DagCid.tla; the   *)
(* parse and the text of the CIDs in CidPool are computed once (a model    *)
(* that extends this module binds CidPool in its configuration with        *)
(* `CONSTANT CidPool <- Pool`; a trace instance binds it to {}).           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

U == INSTANCE U64
L == INSTANCE DagCborLen WITH SmallMax <- 0, c <- 0
C == INSTANCE DagCid WITH Parts <- {}, c <- 0

CONSTANT CidPool

MaxDepth == 64

(* ---- items ---- *)
Txt(b) == [k |-> "text", b |-> b]
Arr(n) == [k |-> "array", n |-> n]
MapI(n) == [k |-> "map", n |-> n]
Tag == [k |-> "tag", v |-> 42]
Null == [k |-> "null"]
UInt(v) == [k |-> "uint", v |-> v]
Bts(b) == [k |-> "bytes", b |-> b]
Bad == [k |-> "bad"]

(* the map keys pinc-dag reads and writes, as bytes *)
KDelta == <<100, 101, 108, 116, 97>>
KHeads == <<104, 101, 97, 100, 115>>
KLinks == <<108, 105, 110, 107, 115>>
KSig == <<115, 105, 103, 110, 97, 116, 117, 114, 101>>
KEnc == <<101, 110, 99, 114, 121, 112, 116, 105, 111, 110>>
KLink == <<108, 105, 110, 107>>
KName == <<110, 97, 109, 101>>
KRoots == <<114, 111, 111, 116, 115>>
KVersion == <<118, 101, 114, 115, 105, 111, 110>>

(* lexicographic order of byte strings: -1, 0, 1 *)
SeqCmp(a, b) == C!SeqCmp(a, b)

(* Encoder::tag_cid: tag 42 over a byte string of 0x00 and the CID *)
CidItems(raw) == <<Tag, Bts(<<0>> \o raw)>>

RECURSIVE CatCids(_)
CatCids(s) == IF s = <<>> THEN <<>> ELSE CidItems(Head(s)) \o CatCids(Tail(s))

(* ---- the CIDs: parse and text, computed once for the pool ---- *)
CidMemo == [b \in CidPool |-> C!Parse(b)]
TextMemo == [b \in CidPool |-> C!Chars(b)]
PCid(b) == IF b \in CidPool THEN CidMemo[b] ELSE C!Parse(b)
TextOf(b) == IF b \in CidPool THEN TextMemo[b] ELSE C!Chars(b)

(* cmp_text of two raw CIDs *)
CidCmp(a, b) == SeqCmp(TextOf(a), TextOf(b))

(* ---- the decoder ---- *)

(* Decoder::next_item at index i: past the items is an error (the decoder's Truncated, or the refused bytes when
   end is FALSE), and so is an item after a tag that is not a byte string starting with 0x00 (cid_pending) *)
NextItem(s, i) ==
    IF i > Len(s) THEN Bad
    ELSE IF i > 1 /\ s[i - 1].k = "tag" /\ ~(s[i].k = "bytes" /\ s[i].b # <<>> /\ s[i].b[1] = 0) THEN Bad
    ELSE s[i]

(* check_key_order: prev is <<>> (no key yet) or <<key>>; shorter keys first, then bytewise, no duplicate *)
KeyOK(prev, key) ==
    \/ prev = <<>>
    \/ Len(prev[1]) < Len(key)
    \/ Len(prev[1]) = Len(key) /\ SeqCmp(prev[1], key) = -1

(* Decoder::skip_value: a frame is [left, map, prev]; a map counts its keys and values *)
RECURSIVE PopDone(_)
PopDone(st) == IF st # <<>> /\ st[Len(st)].left = 0 THEN PopDone(SubSeq(st, 1, Len(st) - 1)) ELSE st

RECURSIVE SkipLoop(_, _, _)
SkipLoop(s, i, st) ==
    LET it == NextItem(s, i)
        top == Len(st)
        keyTurn == top > 0 /\ st[top].map /\ st[top].left % 2 = 0
    IN IF it.k = "bad" THEN [ok |-> FALSE]
       ELSE IF keyTurn /\ it.k # "text" THEN [ok |-> FALSE]
       ELSE IF keyTurn /\ ~KeyOK(st[top].prev, it.b) THEN [ok |-> FALSE]
       ELSE LET st1 == IF top = 0 THEN st
                       ELSE (LET f == st[top]
                             IN [st EXCEPT ![top] = [left |-> IF f.left > 0 THEN f.left - 1 ELSE 0, map |-> f.map,
                                                     prev |-> IF keyTurn THEN <<it.b>> ELSE f.prev]])
                left == CASE it.k = "array" -> it.n
                          [] it.k = "map" -> 2 * it.n
                          [] it.k = "tag" -> 1
                          [] OTHER -> 0
            IN IF left > 0 /\ Len(st1) >= MaxDepth THEN [ok |-> FALSE]
               ELSE LET st2 == PopDone(IF left > 0 THEN Append(st1, [left |-> left, map |-> (it.k = "map"), prev |-> <<>>])
                                       ELSE st1)
                    IN IF st2 = <<>> THEN [ok |-> TRUE, next |-> i + 1] ELSE SkipLoop(s, i + 1, st2)

(* a scalar is one next_item; a container walks the frames *)
Skip(s, i) ==
    IF i > Len(s) THEN [ok |-> FALSE]
    ELSE IF s[i].k \notin {"array", "map", "tag"}
         THEN IF NextItem(s, i).k = "bad" THEN [ok |-> FALSE] ELSE [ok |-> TRUE, next |-> i + 1]
    ELSE SkipLoop(s, i, <<>>)

(* ---- CID links ---- *)
WErr == [err |-> "wire", w |-> "cbor"]
CErr(kind) == [err |-> "cid", c |-> kind]

(* CidRef::read_cbor: a tag, then a byte string of 0x00 and the CID; a CidError *)
ReadCbor(s, i) ==
    LET t == NextItem(s, i) IN
    IF t.k # "tag" THEN CErr("wire")
    ELSE LET bi == NextItem(s, i + 1) IN
         IF bi.k # "bytes" THEN CErr("wire")
         ELSE LET p == PCid(Tail(bi.b)) IN
              IF p.err # "ok" THEN CErr(p.err) ELSE [err |-> "ok", cid |-> p.cid.raw, next |-> i + 2]

(* CidList::read: an array header, then every CID validated *)
RECURSIVE ReadCids(_, _, _, _)
ReadCids(s, i, n, acc) ==
    IF n = 0 THEN [err |-> "ok", cids |-> acc, next |-> i]
    ELSE LET r == ReadCbor(s, i) IN IF r.err # "ok" THEN r ELSE ReadCids(s, r.next, n - 1, Append(acc, r.cid))

CidList(s, i) == LET a == NextItem(s, i) IN IF a.k # "array" THEN CErr("wire") ELSE ReadCids(s, i + 1, a.n, <<>>)

(* skip_null of block/parse.rs: a probe of the next item *)
SkipNull(s, i) == LET it == NextItem(s, i) IN IF it.k = "bad" THEN WErr ELSE [err |-> "ok", null |-> it.k = "null"]
=============================================================================
