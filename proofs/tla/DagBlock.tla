------------------------------- MODULE DagBlock -------------------------------
(***************************************************************************)
(* The blocks of pinc-dag (block/parse.rs, block/encode.rs): BlockRef::    *)
(* parse (ParseBlock) with LinkList::read, read_link, skip_null,           *)
(* read_optional_cid and check_ascending, and encode_block (EncodeBlock)   *)
(* with BlockParts::encoded_len (EncodedLen) and entry_count. A block is   *)
(* the item stream of DagItems.tla; the CIDs are those of DagCid.tla.      *)
(*                                                                         *)
(* What the module documentation states, checked by TLC (DagBlock.cfg):    *)
(*   EncOK     encode_block refuses a delta that is not exactly one item   *)
(*             (Wire), then duplicate heads, then duplicate links          *)
(*             (Unordered), and accepts the rest; encoded_len equals the   *)
(*             bytes written, a buffer of exactly that size is enough and  *)
(*             one byte less is refused with BufferTooSmall needing 1;     *)
(*             the output is the canonical block: heads in text order of   *)
(*             their CIDs, links by CID text then name, empty fields and   *)
(*             absent options left out, and BlockRef::parse reads back     *)
(*             exactly the parts written (encode/parse round trip); bytes  *)
(*             after the block map are refused with TrailingBytes;         *)
(*   StrictOK  each documented refusal of BlockRef::parse is reached with  *)
(*             its own error: trailing bytes, no delta, unordered or       *)
(*             duplicate heads and links, an invalid CID, links that are   *)
(*             not an array, a link name that is not text, a link without  *)
(*             its link or name, a map that is not canonical, a nesting    *)
(*             deeper than 64; and the documented tolerances (an unknown   *)
(*             key, a null or empty heads or links, a null signature) are  *)
(*             accepted;                                                   *)
(*   MutOK     every single-item mutation of three canonical blocks (swap, *)
(*             drop, duplicate, replace by 7 filler items, count +-1,      *)
(*             append, bytes after the end) is refused with a documented   *)
(*             error or accepted, and an accepted block that uses no       *)
(*             tolerance re-encodes to exactly its input: the canonical    *)
(*             byte form of a block is unique.                             *)
(* Witness (DagBlock_loose.cfg): LooseRoundTrip is violated, so a block    *)
(* that uses a tolerance (an unknown key) parses but does not re-encode to *)
(* its input, as block/mod.rs says ("a block with unknown keys therefore   *)
(* parses but does not re-encode byte for byte").                          *)
(*                                                                         *)
(* The ghost field `loose` of a parse marks the use of a tolerance; the    *)
(* code has no such field.                                                 *)
(***************************************************************************)
EXTENDS DagItems, FiniteSets

(* ---- errors: BlockError ---- *)
Unord(what) == [err |-> "unordered", what |-> what]
Malformed(what) == [err |-> "malformed", what |-> what]
Small(needed) == [err |-> "wire", w |-> "small", needed |-> needed]

(* ---- the orders of check_ascending and of the sorts of encode_block ---- *)
LinkCmp(a, b) == LET x == CidCmp(a.cid, b.cid) IN IF x # 0 THEN x ELSE SeqCmp(a.name, b.name)

HeadsAsc(hs) == \A i \in 1..(Len(hs) - 1) : CidCmp(hs[i], hs[i + 1]) = -1
LinksAsc(ls) == \A i \in 1..(Len(ls) - 1) : LinkCmp(ls[i], ls[i + 1]) = -1

(* ---- BlockRef::parse ---- *)

(* read_link: the map of one link, keys "link" and "name" in canonical order, unknown keys skipped *)
RECURSIVE LinkLoop(_, _, _, _, _)
LinkLoop(s, i, left, prev, a) ==
    IF left = 0
    THEN IF a.hasCid /\ a.hasName
         THEN [err |-> "ok", link |-> [cid |-> a.cid, name |-> a.name], next |-> i, loose |-> a.loose]
         ELSE Malformed("link needs a link and a name")
    ELSE LET k == NextItem(s, i) IN
         IF k.k # "text" THEN WErr
         ELSE IF ~KeyOK(prev, k.b) THEN WErr
         ELSE IF k.b = KLink
              THEN LET r == ReadCbor(s, i + 1) IN
                   IF r.err # "ok" THEN r
                   ELSE LinkLoop(s, r.next, left - 1, <<k.b>>, [a EXCEPT !.hasCid = TRUE, !.cid = r.cid])
         ELSE IF k.b = KName
              THEN LET t == NextItem(s, i + 1) IN
                   IF t.k = "bad" THEN WErr
                   ELSE IF t.k # "text" THEN Malformed("link name is not text")
                   ELSE LinkLoop(s, i + 2, left - 1, <<k.b>>, [a EXCEPT !.hasName = TRUE, !.name = t.b])
         ELSE LET sk == Skip(s, i + 1) IN
              IF ~sk.ok THEN WErr
              ELSE LinkLoop(s, sk.next, left - 1, <<k.b>>, [a EXCEPT !.loose = TRUE])

ReadLink(s, i) ==
    LET m == NextItem(s, i) IN
    IF m.k # "map" THEN WErr
    ELSE LinkLoop(s, i + 1, m.n, <<>>, [hasCid |-> FALSE, cid |-> <<>>, hasName |-> FALSE, name |-> <<>>, loose |-> FALSE])

RECURSIVE ReadLinks(_, _, _, _, _)
ReadLinks(s, i, n, acc, loose) ==
    IF n = 0 THEN [err |-> "ok", links |-> acc, next |-> i, loose |-> loose]
    ELSE LET r == ReadLink(s, i) IN
         IF r.err # "ok" THEN r ELSE ReadLinks(s, r.next, n - 1, Append(acc, r.link), loose \/ r.loose)

(* LinkList::read: the decoder's error first, then an item that is not an array *)
LinkList(s, i) ==
    LET a == NextItem(s, i) IN
    IF a.k = "bad" THEN WErr
    ELSE IF a.k # "array" THEN Malformed("links is not an array")
    ELSE ReadLinks(s, i + 1, a.n, <<>>, FALSE)

(* read_optional_cid *)
OptCid(s, i) ==
    LET sn == SkipNull(s, i) IN
    IF sn.err # "ok" THEN sn
    ELSE IF sn.null THEN [err |-> "ok", cid |-> <<>>, next |-> i + 1, null |-> TRUE]
    ELSE LET r == ReadCbor(s, i) IN IF r.err # "ok" THEN r ELSE [err |-> "ok", cid |-> <<r.cid>>, next |-> r.next, null |-> FALSE]

(* the loop over the keys of the block map; a is the parts read so far *)
RECURSIVE BLoop(_, _, _, _, _, _)
BLoop(s, e, i, left, prev, a) ==
    IF left = 0
    THEN IF i <= Len(s) \/ ~e THEN [err |-> "trailing"]
         ELSE IF ~a.hasDelta THEN [err |-> "missingDelta"]
         ELSE [err |-> "ok", delta |-> a.delta, heads |-> a.heads, links |-> a.links, sig |-> a.sig, enc |-> a.enc,
               loose |-> a.loose]
    ELSE LET k == NextItem(s, i)
             j == i + 1
         IN IF k.k # "text" THEN WErr
            ELSE IF ~KeyOK(prev, k.b) THEN WErr
            ELSE IF k.b = KDelta
                 THEN LET sk == Skip(s, j) IN
                      IF ~sk.ok THEN WErr
                      ELSE BLoop(s, e, sk.next, left - 1, <<k.b>>, [a EXCEPT !.hasDelta = TRUE, !.delta = SubSeq(s, j, sk.next - 1)])
            ELSE IF k.b = KHeads
                 THEN LET sn == SkipNull(s, j) IN
                      IF sn.err # "ok" THEN sn
                      ELSE IF sn.null THEN BLoop(s, e, j + 1, left - 1, <<k.b>>, [a EXCEPT !.heads = <<>>, !.loose = TRUE])
                      ELSE LET cl == CidList(s, j) IN
                           IF cl.err # "ok" THEN cl
                           ELSE IF ~HeadsAsc(cl.cids) THEN Unord("heads")
                           ELSE BLoop(s, e, cl.next, left - 1, <<k.b>>,
                                      [a EXCEPT !.heads = cl.cids, !.loose = a.loose \/ cl.cids = <<>>])
            ELSE IF k.b = KLinks
                 THEN LET sn == SkipNull(s, j) IN
                      IF sn.err # "ok" THEN sn
                      ELSE IF sn.null THEN BLoop(s, e, j + 1, left - 1, <<k.b>>, [a EXCEPT !.links = <<>>, !.loose = TRUE])
                      ELSE LET ll == LinkList(s, j) IN
                           IF ll.err # "ok" THEN ll
                           ELSE IF ~LinksAsc(ll.links) THEN Unord("links")
                           ELSE BLoop(s, e, ll.next, left - 1, <<k.b>>,
                                      [a EXCEPT !.links = ll.links, !.loose = a.loose \/ ll.loose \/ ll.links = <<>>])
            ELSE IF k.b = KSig
                 THEN LET o == OptCid(s, j) IN
                      IF o.err # "ok" THEN o
                      ELSE BLoop(s, e, o.next, left - 1, <<k.b>>, [a EXCEPT !.sig = o.cid, !.loose = a.loose \/ o.null])
            ELSE IF k.b = KEnc
                 THEN LET o == OptCid(s, j) IN
                      IF o.err # "ok" THEN o
                      ELSE BLoop(s, e, o.next, left - 1, <<k.b>>, [a EXCEPT !.enc = o.cid, !.loose = a.loose \/ o.null])
            ELSE LET sk == Skip(s, j) IN
                 IF ~sk.ok THEN WErr ELSE BLoop(s, e, sk.next, left - 1, <<k.b>>, [a EXCEPT !.loose = TRUE])

(* s: the items of the block, e: the bytes end right after them *)
ParseBlock(s, e) ==
    LET m == NextItem(s, 1) IN
    IF m.k # "map" THEN WErr
    ELSE BLoop(s, e, 2, m.n, <<>>,
               [hasDelta |-> FALSE, delta |-> <<>>, heads |-> <<>>, links |-> <<>>, sig |-> <<>>, enc |-> <<>>, loose |-> FALSE])

(* ---- encode_block ---- *)

(* parts: [d (the delta items), dend (its bytes end after them), heads, links ([cid, name]), sig, enc (<<>> or
   <<cid>>)] *)

RECURSIVE InsH(_, _)
InsH(x, s) == IF s = <<>> THEN <<x>> ELSE IF CidCmp(x, Head(s)) <= 0 THEN <<x>> \o s ELSE <<Head(s)>> \o InsH(x, Tail(s))
RECURSIVE SortH(_)
SortH(s) == IF s = <<>> THEN <<>> ELSE InsH(Head(s), SortH(Tail(s)))

RECURSIVE InsL(_, _)
InsL(x, s) == IF s = <<>> THEN <<x>> ELSE IF LinkCmp(x, Head(s)) <= 0 THEN <<x>> \o s ELSE <<Head(s)>> \o InsL(x, Tail(s))
RECURSIVE SortL(_)
SortL(s) == IF s = <<>> THEN <<>> ELSE InsL(Head(s), SortL(Tail(s)))

(* windows(2).any(a == b) after the sort *)
HasDup(s) == \E i \in 1..(Len(s) - 1) : s[i] = s[i + 1]

(* the delta is exactly one item: skip_value, then is_empty *)
DeltaOK(d, e) == LET k == Skip(d, 1) IN k.ok /\ k.next = Len(d) + 1 /\ e

EntryCount(p) ==
    1 + (IF p.heads # <<>> THEN 1 ELSE 0) + (IF p.links # <<>> THEN 1 ELSE 0)
      + (IF p.sig # <<>> THEN 1 ELSE 0) + (IF p.enc # <<>> THEN 1 ELSE 0)

RECURSIVE SumCids(_)
SumCids(s) == IF s = <<>> THEN 0 ELSE L!CL(Len(Head(s))) + SumCids(Tail(s))

RECURSIVE SumLinks(_)
SumLinks(s) ==
    IF s = <<>> THEN 0
    ELSE 1 + L!TL(4) + L!CL(Len(Head(s).cid)) + L!TL(4) + L!TL(Len(Head(s).name)) + SumLinks(Tail(s))

(* BlockParts::encoded_len, term for term *)
EncodedLen(p) ==
    L!HL(EntryCount(p)) + L!TL(5) + L!ItemsWritten(p.d)
    + (IF p.heads = <<>> THEN 0 ELSE L!TL(5) + L!HL(Len(p.heads)) + SumCids(p.heads))
    + (IF p.links = <<>> THEN 0 ELSE L!TL(5) + L!HL(Len(p.links)) + SumLinks(p.links))
    + (IF p.sig = <<>> THEN 0 ELSE L!TL(9) + L!CL(Len(p.sig[1])))
    + (IF p.enc = <<>> THEN 0 ELSE L!TL(10) + L!CL(Len(p.enc[1])))

RECURSIVE CatLinks(_)
CatLinks(ls) ==
    IF ls = <<>> THEN <<>>
    ELSE <<MapI(2), Txt(KLink)>> \o CidItems(Head(ls).cid) \o <<Txt(KName), Txt(Head(ls).name)>> \o CatLinks(Tail(ls))

(* the items encode_block writes, in its order *)
EncItems(p, hs, ls) ==
    <<MapI(EntryCount(p)), Txt(KDelta)>> \o p.d
    \o (IF hs = <<>> THEN <<>> ELSE <<Txt(KHeads), Arr(Len(hs))>> \o CatCids(hs))
    \o (IF ls = <<>> THEN <<>> ELSE <<Txt(KLinks), Arr(Len(ls))>> \o CatLinks(ls))
    \o (IF p.sig = <<>> THEN <<>> ELSE <<Txt(KSig)>> \o CidItems(p.sig[1]))
    \o (IF p.enc = <<>> THEN <<>> ELSE <<Txt(KEnc)>> \o CidItems(p.enc[1]))

(* encode_block into a buffer of cap bytes; on success the sorted parts, the items and the length returned. An
   encoder that ran out after the length check (encoded_len below the bytes written) is the error with needed 0,
   which EncOK rules out. *)
EncodeBlock(p, cap) ==
    IF ~DeltaOK(p.d, p.dend) THEN WErr
    ELSE LET hs == SortH(p.heads)
             ls == SortL(p.links)
         IN IF HasDup(hs) THEN Unord("heads")
            ELSE IF HasDup(ls) THEN Unord("links")
            ELSE LET n == EncodedLen(p) IN
                 IF n > cap THEN Small(n - cap)
                 ELSE LET items == EncItems(p, hs, ls)
                          w == L!ItemsWritten(items)
                      IN IF w > cap THEN Small(0)
                         ELSE [err |-> "ok", len |-> w, items |-> items, heads |-> hs, links |-> ls]

(***************************************************************************)
(* The checked domain                                                      *)
(***************************************************************************)
CONSTANT Parts

(* CIDs: K1 and K2 differ in the last digit ('z' and '2'), so their byte order and text order disagree; K3 is the
   shortest CID; BadV2 has version 2; K3T has a trailing byte *)
K1 == <<1, 113, 0, 1, 25>>
K2 == <<1, 113, 0, 1, 26>>
K3 == <<1, 85, 0, 0>>
BadV2 == <<2, 113, 0, 0>>
K3T == K3 \o <<0>>
Pool == {K1, K2, K3, BadV2, K3T}

Lk(cid, name) == [cid |-> cid, name |-> name]
LA == Lk(K1, <<97>>)
LB == Lk(K1, <<98>>)
LAB == Lk(K1, <<97, 98>>)
LC == Lk(K2, <<97>>)
LE == Lk(K3, <<>>)

(* deltas: a scalar, a nested map and array, a CID link *)
D1 == <<UInt(0)>>
D2 == <<MapI(1), Txt(<<97>>), Arr(2), UInt(1), Null>>
D3 == CidItems(K3)
GoodDeltas == {D1, D2, D3}

HeadSeqs == {<<>>, <<K1>>, <<K1, K2>>, <<K2, K1>>, <<K1, K1>>, <<K3, K2, K1>>, <<K1, K3, K2>>}
LinkSeqs == {<<>>, <<LA>>, <<LB, LA>>, <<LC, LA>>, <<LA, LA>>, <<LB, LAB>>, <<LE, LC, LB>>}
Sigs == {<<>>, <<K1>>}
Encs == {<<>>, <<K2>>}

(* deltas that are not exactly one item: two items, an array short of an item, map keys out of order, no item,
   bytes after the item *)
BadDeltas ==
    {[d |-> <<UInt(0), UInt(1)>>, dend |-> TRUE], [d |-> <<Arr(2), UInt(0)>>, dend |-> TRUE],
     [d |-> <<MapI(2), Txt(<<98>>), Null, Txt(<<97>>), Null>>, dend |-> TRUE], [d |-> <<>>, dend |-> TRUE],
     [d |-> <<UInt(0)>>, dend |-> FALSE]}

EncCases ==
    {[t |-> "enc", d |-> d, dend |-> TRUE, heads |-> h, links |-> l, sig |-> s, enc |-> x] :
        d \in GoodDeltas, h \in HeadSeqs, l \in LinkSeqs, s \in Sigs, x \in Encs}
    \cup {[t |-> "enc", d |-> b.d, dend |-> b.dend, heads |-> <<K1>>, links |-> <<>>, sig |-> <<>>, enc |-> <<>>] : b \in BadDeltas}

(* pieces of hand-built blocks *)
DeltaE(d) == <<Txt(KDelta)>> \o d
HeadsE(hs) == <<Txt(KHeads), Arr(Len(hs))>> \o CatCids(hs)
LinksE(ls) == <<Txt(KLinks), Arr(Len(ls))>> \o CatLinks(ls)
SigE(cid) == <<Txt(KSig)>> \o CidItems(cid)
Blk(n, body) == <<MapI(n)>> \o body
Deep(n) == [i \in 1..n |-> Arr(1)] \o <<UInt(0)>>

OK(loose) == [err |-> "ok", loose |-> loose]
CidE(kind) == CErr(kind)
St(s, e, want) == [t |-> "strict", in |-> s, end |-> e, want |-> want]

StrictCases == {
    St(Blk(1, DeltaE(D1)), FALSE, [err |-> "trailing"]),
    St(Blk(1, DeltaE(D1)) \o <<UInt(0)>>, TRUE, [err |-> "trailing"]),
    St(Blk(1, HeadsE(<<K2>>)), TRUE, [err |-> "missingDelta"]),
    St(Blk(2, DeltaE(D1) \o HeadsE(<<K1, K2>>)), TRUE, Unord("heads")),
    St(Blk(2, DeltaE(D1) \o HeadsE(<<K1, K1>>)), TRUE, Unord("heads")),
    St(Blk(2, DeltaE(D1) \o LinksE(<<LB, LA>>)), TRUE, Unord("links")),
    St(Blk(2, DeltaE(D1) \o LinksE(<<LA, LA>>)), TRUE, Unord("links")),
    St(Blk(2, DeltaE(D1) \o HeadsE(<<BadV2>>)), TRUE, CidE("version")),
    St(Blk(2, DeltaE(D1) \o HeadsE(<<K3T>>)), TRUE, CidE("trailing")),
    St(Blk(2, DeltaE(D1) \o <<Txt(KHeads), UInt(0)>>), TRUE, CidE("wire")),
    St(Blk(2, DeltaE(D1) \o <<Txt(KLinks), UInt(0)>>), TRUE, Malformed("links is not an array")),
    St(Blk(2, DeltaE(D1) \o <<Txt(KLinks), Arr(1), MapI(2), Txt(KLink)>> \o CidItems(K1) \o <<Txt(KName), UInt(0)>>),
       TRUE, Malformed("link name is not text")),
    St(Blk(2, DeltaE(D1) \o <<Txt(KLinks), Arr(1), MapI(1), Txt(KLink)>> \o CidItems(K1)), TRUE,
       Malformed("link needs a link and a name")),
    St(Blk(2, DeltaE(D1) \o <<Txt(KLinks), Arr(1), MapI(2), Txt(KName), Txt(<<97>>), Txt(KLink)>> \o CidItems(K1)),
       TRUE, WErr),
    St(Blk(2, DeltaE(D1) \o <<Txt(KSig), Tag, Bts(<<1>> \o K1)>>), TRUE, CidE("wire")),
    St(Blk(2, DeltaE(D1) \o <<Txt(KSig), UInt(0)>>), TRUE, CidE("wire")),
    St(Blk(2, HeadsE(<<K1>>) \o DeltaE(D1)), TRUE, WErr),
    St(Blk(2, DeltaE(D1) \o DeltaE(D1)), TRUE, WErr),
    St(Blk(1, <<UInt(0), UInt(0)>>), TRUE, WErr),
    St(<<Arr(0)>>, TRUE, WErr),
    St(<<>>, TRUE, WErr),
    St(Blk(3, DeltaE(D1)), TRUE, WErr),
    St(Blk(1, DeltaE(<<MapI(2), Txt(<<98>>), Null, Txt(<<97>>), Null>>)), TRUE, WErr),
    St(Blk(1, DeltaE(Deep(64))), TRUE, OK(FALSE)),
    St(Blk(1, DeltaE(Deep(65))), TRUE, WErr),
    St(Blk(2, <<Txt(<<122>>), UInt(0)>> \o DeltaE(D1)), TRUE, OK(TRUE)),
    St(Blk(2, DeltaE(D1) \o <<Txt(KLinks), Arr(1), MapI(3), Txt(<<97>>), UInt(0), Txt(KLink)>> \o CidItems(K1)
                         \o <<Txt(KName), Txt(<<97>>)>>), TRUE, OK(TRUE)),
    St(Blk(2, DeltaE(D1) \o <<Txt(KHeads), Null>>), TRUE, OK(TRUE)),
    St(Blk(2, DeltaE(D1) \o <<Txt(KHeads), Arr(0)>>), TRUE, OK(TRUE)),
    St(Blk(2, DeltaE(D1) \o <<Txt(KLinks), Null>>), TRUE, OK(TRUE)),
    St(Blk(2, DeltaE(D1) \o <<Txt(KSig), Null>>), TRUE, OK(TRUE)),
    St(Blk(2, DeltaE(D1) \o SigE(K3)), TRUE, OK(FALSE))}

(* mutations of three canonical blocks *)
Swap(s, i) == [s EXCEPT ![i] = s[i + 1], ![i + 1] = s[i]]
DropAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
DupAt(s, i) == SubSeq(s, 1, i) \o SubSeq(s, i, Len(s))
Fillers == {UInt(0), Null, Txt(<<97>>), Arr(0), MapI(0), Tag, Txt(KName)}

Muts(s) ==
    {Swap(s, i) : i \in 1..(Len(s) - 1)} \cup {DropAt(s, i) : i \in 1..Len(s)} \cup {DupAt(s, i) : i \in 1..Len(s)}
    \cup {[s EXCEPT ![i] = f] : i \in 1..Len(s), f \in Fillers}
    \cup {[s EXCEPT ![i] = [s[i] EXCEPT !.n = s[i].n + dn]] : i \in {i \in 1..Len(s) : s[i].k \in {"array", "map"}}, dn \in {-1, 1}}
    \cup {s \o <<UInt(0)>>}

MutParts == {
    [d |-> D2, dend |-> TRUE, heads |-> <<K1, K2>>, links |-> <<LA>>, sig |-> <<K1>>, enc |-> <<K2>>],
    [d |-> D1, dend |-> TRUE, heads |-> <<>>, links |-> <<LB, LAB>>, sig |-> <<>>, enc |-> <<>>],
    [d |-> D3, dend |-> TRUE, heads |-> <<K3>>, links |-> <<LE, LC>>, sig |-> <<>>, enc |-> <<K2>>]}
MutBases == {EncodeBlock(p, 100000).items : p \in MutParts}

MutCases ==
    {[t |-> "mut", in |-> m, end |-> TRUE] : m \in UNION {Muts(b) : b \in MutBases}}
    \cup {[t |-> "mut", in |-> b, end |-> FALSE] : b \in MutBases}

Starts ==
    (IF "enc" \in Parts THEN EncCases ELSE {})
    \cup (IF "strict" \in Parts THEN StrictCases ELSE {})
    \cup (IF "mut" \in Parts THEN MutCases ELSE {})
    \cup (IF "loose" \in Parts THEN {x \in StrictCases : x.want.err = "ok" /\ x.want.loose} ELSE {})

VARIABLE c
Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E x \in Starts : c' = x
Spec == Init /\ [][Next]_c

(***************************************************************************)
(* The properties                                                          *)
(***************************************************************************)
ErrKinds == {"ok", "wire", "cid", "trailing", "missingDelta", "malformed", "unordered"}

Distinct(s) == Cardinality({s[i] : i \in 1..Len(s)}) = Len(s)
Perm(a, b) == Len(a) = Len(b) /\ {a[i] : i \in 1..Len(a)} = {b[i] : i \in 1..Len(b)}

PartsOf(r) == [d |-> r.delta, dend |-> TRUE, heads |-> r.heads, links |-> r.links, sig |-> r.sig, enc |-> r.enc]

EncOK(p) ==
    LET r == EncodeBlock(p, 100000)
        good == DeltaOK(p.d, p.dend)
    IN /\ ~good => r = WErr
       /\ good /\ ~Distinct(p.heads) => r = Unord("heads")
       /\ good /\ Distinct(p.heads) /\ ~Distinct(p.links) => r = Unord("links")
       /\ good /\ Distinct(p.heads) /\ Distinct(p.links) =>
            /\ r.err = "ok"
            /\ r.len = EncodedLen(p)
            /\ HeadsAsc(r.heads) /\ Perm(r.heads, p.heads)
            /\ LinksAsc(r.links) /\ Perm(r.links, p.links)
            /\ EncodeBlock(p, r.len) = r
            /\ EncodeBlock(p, r.len - 1) = Small(1)
            /\ EncodeBlock(p, 0) = Small(r.len)
            /\ ParseBlock(r.items, TRUE)
                 = [err |-> "ok", delta |-> p.d, heads |-> r.heads, links |-> r.links, sig |-> p.sig, enc |-> p.enc,
                    loose |-> FALSE]
            /\ ParseBlock(r.items, FALSE) = [err |-> "trailing"]
            /\ ParseBlock(r.items \o <<Null>>, TRUE) = [err |-> "trailing"]

StrictOK(x) ==
    LET r == ParseBlock(x.in, x.end) IN
    /\ r.err = x.want.err
    /\ r.err \in {"malformed", "unordered"} => r.what = x.want.what
    /\ r.err = "cid" => r.c = x.want.c
    /\ r.err = "ok" => r.loose = x.want.loose

MutOK(x) ==
    LET r == ParseBlock(x.in, x.end) IN
    /\ r.err \in ErrKinds
    /\ r.err = "ok" /\ ~r.loose =>
         LET q == EncodeBlock(PartsOf(r), 100000) IN q.err = "ok" /\ q.items = x.in /\ x.end

Inv ==
    CASE c.t = "enc" -> EncOK(c)
      [] c.t = "strict" -> StrictOK(c)
      [] c.t = "mut" -> MutOK(c)
      [] OTHER -> TRUE

(* Not a law: an accepted block re-encodes to its input even when it uses a tolerance. TLC finds the violation
   (DagBlock_loose.cfg). *)
LooseRoundTrip ==
    c.t = "strict" =>
        LET r == ParseBlock(c.in, c.end) IN
        r.err = "ok" => LET q == EncodeBlock(PartsOf(r), 100000) IN q.err = "ok" /\ q.items = c.in
=============================================================================
