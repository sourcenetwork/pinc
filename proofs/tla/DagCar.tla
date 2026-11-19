-------------------------------- MODULE DagCar --------------------------------
(***************************************************************************)
(* The CAR v1 archives of pinc-dag (car/mod.rs, reader.rs, stream.rs,      *)
(* writer.rs): frame (Frame), split_section (SplitSection), parse_header   *)
(* (ParseHeader), CarReader::new (ReaderNew) with Sections (Secs),         *)
(* CarDecoder::decode (DecodeStream), CarWriter::header_len, section_len,  *)
(* new and section (HeaderLen, SectionLen, WriterNew, WriterSection). The  *)
(* frames and the CIDs are bytes (varints of Varint.tla, CIDs of           *)
(* DagCid.tla); a header body is the item stream of DagItems.tla, given by *)
(* its tokenization `tok` = [items, end] (the model looks it up in a table *)
(* of the header bodies it builds, a trace records it).                    *)
(*                                                                         *)
(* What the module documentation states, checked by TLC (DagCar.cfg):      *)
(*   CarOK     the writer writes `varint(len) header` and `varint(len) cid *)
(*             block` sections, header_len and section_len are the bytes   *)
(*             written (the "header length disagrees" refusal is never     *)
(*             reached), a buffer of exactly that size is enough and one   *)
(*             byte less is refused with BufferTooSmall needing 1; the     *)
(*             reader returns the roots and every section written (round   *)
(*             trip), a header or section over the maximum is refused with *)
(*             TooLarge, with verify a block that does not match its CID   *)
(*             and an unknown hash are refused and end the sections; a cut *)
(*             CAR is Truncated with the exact bytes needed, except a cut  *)
(*             between two sections, which is a complete shorter CAR; the  *)
(*             stream decoder, fed the bytes it asks for (exactly, or 7    *)
(*             more), yields the same header, sections and errors as the   *)
(*             reader and never asks the caller to hold more than one      *)
(*             frame of max_section plus a 9 byte prefix; on a cut CAR it  *)
(*             yields the complete frames and ends cleanly only between    *)
(*             two frames after the header;                                *)
(*   HdrOK     a header that is not {"roots": [CID...], "version": 1}      *)
(*             is refused with the documented reason (version not 1, an    *)
(*             unknown key, a missing key, bytes after the map, a bad root *)
(*             CID, a non-canonical map), by the reader and the decoder;   *)
(*   FrameOK   a non-minimal or too long length varint is a Wire error,    *)
(*             and a length of 2^62 is refused with TooLarge before any    *)
(*             byte of the body is required (or, with no maximum, asks for *)
(*             exactly the missing bytes).                                 *)
(* Witness (DagCar_cut.cfg): CutRefused is violated, so a CAR cut at a     *)
(* section boundary reads as a complete CAR, as reader.rs says ("Input     *)
(* that stops exactly between two sections is a complete, shorter CAR").   *)
(* The hash is the ideal one of DagCid.tla (Genuine); a trace records the  *)
(* genuine digests as triples <<code, block, digest>> (GenOf).             *)
(***************************************************************************)
EXTENDS DagItems

V == INSTANCE Varint WITH SmallMax <- 0, c <- 0

(* ---- errors: CarError ---- *)
TooLarge(len, max) == [err |-> "toolarge", len |-> len, max |-> max]
Trunc(n) == [err |-> "truncated", needed |-> n]
BadHeader(why) == [err |-> "badheader", why |-> why]
WireK(kind) == [err |-> "wire", w |-> kind]
Small(n) == [err |-> "wire", w |-> "small", needed |-> n]

Drop(s, n) == SubSeq(s, n + 1, Len(s))
Pfx(n) == V!Encode(U!W(n), 16).bytes

(* the genuine digest of blk under the hash code, from triples <<code, blk, digest>>; <<>> if not recorded *)
GenOf(g, code, blk) ==
    LET m == {t \in g : t[1] = code /\ t[2] = blk} IN IF m = {} THEN <<>> ELSE (CHOOSE t \in m : TRUE)[3]

(* ---- car/mod.rs ---- *)

(* frame: Need(n), an error, or Ready; max is a usize word, n and the length u64 words *)
Frame(input, max) ==
    LET d == V!Decode(input) IN
    IF d.kind = "truncated" THEN [t |-> "need", n |-> U!One]
    ELSE IF d.kind # "ok" THEN [t |-> "err", e |-> WireK(d.kind)]
    ELSE IF ~U!Le(d.v, max) THEN [t |-> "err", e |-> TooLarge(d.v, max)]
    ELSE LET total == U!Add(U!W(d.n), d.v) IN
         IF U!Le(total, U!W(Len(input)))
         THEN [t |-> "ready", consumed |-> U!Val(total), body |-> SubSeq(input, d.n + 1, U!Val(total))]
         ELSE [t |-> "need", n |-> U!Sub(total, U!W(Len(input)))]

(* split_section: parse_prefix, then verify on request; a CidError *)
SplitSection(body, verify, g) ==
    LET p == C!ParsePrefix(body) IN
    IF p.err # "ok" THEN CErr(p.err)
    ELSE IF ~verify THEN [err |-> "ok", cid |-> p.cid.raw, blk |-> p.rest]
    ELSE LET v == C!Verify(p.cid, GenOf(g, p.cid.hash, p.rest)) IN
         IF v.err # "ok" THEN CErr(v.err) ELSE [err |-> "ok", cid |-> p.cid.raw, blk |-> p.rest]

(* ---- reader.rs ---- *)

RECURSIVE HLoop(_, _, _, _, _, _, _)
HLoop(s, e, i, left, prev, roots, version) ==
    IF left = 0
    THEN IF i <= Len(s) \/ ~e THEN BadHeader("bytes follow the header map")
         ELSE IF roots = <<>> \/ ~version THEN BadHeader("roots and version are required")
         ELSE [err |-> "ok", roots |-> roots[1]]
    ELSE LET k == NextItem(s, i) IN
         IF k.k # "text" THEN WErr
         ELSE IF ~KeyOK(prev, k.b) THEN WErr
         ELSE IF k.b = KRoots
              THEN LET cl == CidList(s, i + 1) IN
                   IF cl.err # "ok" THEN cl ELSE HLoop(s, e, cl.next, left - 1, <<k.b>>, <<cl.cids>>, version)
         ELSE IF k.b = KVersion
              THEN LET v == NextItem(s, i + 1) IN
                   IF v.k = "bad" THEN WErr
                   ELSE IF ~(v.k = "uint" /\ v.v = 1) THEN BadHeader("version is not 1")
                   ELSE HLoop(s, e, i + 2, left - 1, <<k.b>>, roots, TRUE)
         ELSE BadHeader("unknown key")

ParseHeader(tok) ==
    LET m == NextItem(tok.items, 1) IN
    IF m.k # "map" THEN WErr ELSE HLoop(tok.items, tok.end, 2, m.n, <<>>, <<>>, FALSE)

(* CarReader::new: tok is the tokenization of the header body, used only when its frame is complete *)
ReaderNew(buf, max, tok) ==
    LET f == Frame(buf, max) IN
    IF f.t = "err" THEN f.e
    ELSE IF f.t = "need" THEN Trunc(f.n)
    ELSE LET h == ParseHeader(tok) IN
         IF h.err # "ok" THEN h ELSE [err |-> "ok", roots |-> h.roots, rest |-> Drop(buf, f.consumed)]

(* Sections: every section, an error ending the iteration *)
RECURSIVE Secs(_, _, _, _)
Secs(rest, max, verify, g) ==
    IF rest = <<>> THEN <<>>
    ELSE LET f == Frame(rest, max) IN
         IF f.t = "err" THEN <<f.e>>
         ELSE IF f.t = "need" THEN <<Trunc(f.n)>>
         ELSE LET s == SplitSection(f.body, verify, g) IN
              IF s.err # "ok" THEN <<s>> ELSE <<s>> \o Secs(Drop(rest, f.consumed), max, verify, g)

Read(buf, max, verify, tok, g) ==
    LET r == ReaderNew(buf, max, tok) IN
    IF r.err # "ok" THEN r ELSE [err |-> "ok", roots |-> r.roots, secs |-> Secs(r.rest, max, verify, g)]

(* ---- stream.rs: CarDecoder::decode with header_done = done ---- *)
DecodeStream(done, input, max, verify, tok, g) ==
    LET f == Frame(input, max) IN
    IF f.t = "err" THEN [t |-> "err", e |-> f.e]
    ELSE IF f.t = "need" THEN [t |-> "need", n |-> f.n]
    ELSE IF done
         THEN LET s == SplitSection(f.body, verify, g) IN
              IF s.err # "ok" THEN [t |-> "err", e |-> s]
              ELSE [t |-> "ok", consumed |-> f.consumed, entry |-> [t |-> "sec", cid |-> s.cid, blk |-> s.blk]]
         ELSE LET h == ParseHeader(tok) IN
              IF h.err # "ok" THEN [t |-> "err", e |-> h]
              ELSE [t |-> "ok", consumed |-> f.consumed, entry |-> [t |-> "hdr", roots |-> h.roots]]

(* ---- writer.rs ---- *)
HeaderItems(roots) == <<MapI(2), Txt(KRoots), Arr(Len(roots))>> \o CatCids(roots) \o <<Txt(KVersion), UInt(1)>>

RECURSIVE CidsLen(_)
CidsLen(s) == IF s = <<>> THEN 0 ELSE L!CL(Len(Head(s))) + CidsLen(Tail(s))

(* header_body_len, term for term *)
HeaderBodyLen(roots) == 1 + L!TL(5) + L!HL(Len(roots)) + CidsLen(roots) + L!TL(7) + 1
HeaderLen(roots) == LET b == HeaderBodyLen(roots) IN V!EncodedLen(U!W(b)) + b
SectionLen(cid, blk) == LET b == Len(cid) + Len(blk) IN V!EncodedLen(U!W(b)) + b

(* CarWriter::new into a buffer of cap bytes: the bytes written and pos *)
WriterNew(roots, cap) ==
    LET body == HeaderBodyLen(roots)
        total == V!EncodedLen(U!W(body)) + body
    IN IF total > cap THEN Small(total - cap)
       ELSE LET hb == L!ItemsBytes(HeaderItems(roots)) IN
            IF Len(hb) # body THEN BadHeader("header length disagrees with its encoding")
            ELSE [err |-> "ok", bytes |-> Pfx(body) \o hb, pos |-> total]

(* CarWriter::section at pos in a buffer of cap bytes: the bytes appended and the new pos; on an error pos stays *)
WriterSection(pos, cap, cid, blk) ==
    LET total == SectionLen(cid, blk)
        rest == cap - pos
    IN IF total > rest THEN Small(total - rest)
       ELSE [err |-> "ok", app |-> Pfx(Len(cid) + Len(blk)) \o cid \o blk, pos |-> pos + total]

(***************************************************************************)
(* The checked domain                                                      *)
(***************************************************************************)
CONSTANT Parts

Big == 100000
Blk1 == <<1, 2, 3>>
Blk2 == <<9>>
BlkBig == [i \in 1..100 |-> (37 * i + 11) % 256]

(* G1: BLAKE3 of Blk1; G2: SHA2-256 of BlkBig (a 136 byte section body, a two byte prefix); X: an unknown hash;
   BadV2: version 2 *)
G1 == C!NewCid(U!W(113), C!Blake3, C!Genuine(C!Blake3, Blk1)).cid.raw
G2 == C!NewCid(U!W(85), C!Sha256, C!Genuine(C!Sha256, BlkBig)).cid.raw
X == <<1, 113, 0, 1, 7>>
BadV2 == <<2, 113, 0, 0>>
Pool == {G1, G2, X, BadV2}

GenSet == {<<h, b, C!Genuine(h, b)>> : h \in {C!Sha256, C!Blake3}, b \in {Blk1, Blk2, BlkBig}}

(* a section: its CID, its block and whether the CID is the genuine one of the block under a known hash *)
Sec(cid, blk, genuine) == [cid |-> cid, blk |-> blk, genuine |-> genuine, known |-> cid # X]
S1 == Sec(G1, Blk1, TRUE)
S2 == Sec(G1, Blk2, FALSE)
S3 == Sec(G2, BlkBig, TRUE)
S4 == Sec(X, Blk2, FALSE)

RootSets == {<<>>, <<X>>, <<G1, X>>}
SecSeqs == {<<>>, <<S1>>, <<S3>>, <<S1, S2>>, <<S4, S1>>, <<S3, S1>>}

SecBody(s) == Len(s.cid) + Len(s.blk)
SecBytes(s) == Pfx(SecBody(s)) \o s.cid \o s.blk
RECURSIVE CatSecs(_)
CatSecs(ss) == IF ss = <<>> THEN <<>> ELSE SecBytes(Head(ss)) \o CatSecs(Tail(ss))

(* the CAR the documentation describes, apart from the writer *)
CarSpec(roots, ss) ==
    LET hb == L!ItemsBytes(HeaderItems(roots)) IN Pfx(Len(hb)) \o hb \o CatSecs(ss)

(* header bodies and their tokenization: [items, end]; end FALSE puts a 0xff byte after the items *)
Hdr(items, end, want) == [items |-> items, end |-> end, want |-> want]
HdrBytes(h) == L!ItemsBytes(h.items) \o (IF h.end THEN <<>> ELSE <<255>>)
NoRoots == <<Txt(KRoots), Arr(0)>>
Ver(v) == <<Txt(KVersion), v>>

BadHdrs == {
    Hdr(<<MapI(2)>> \o NoRoots \o Ver(UInt(2)), TRUE, BadHeader("version is not 1")),
    Hdr(<<MapI(2)>> \o NoRoots \o Ver(Txt(<<49>>)), TRUE, BadHeader("version is not 1")),
    Hdr(<<MapI(3), Txt(<<122, 122>>), UInt(0)>> \o NoRoots \o Ver(UInt(1)), TRUE, BadHeader("unknown key")),
    Hdr(<<MapI(1)>> \o NoRoots, TRUE, BadHeader("roots and version are required")),
    Hdr(<<MapI(1)>> \o Ver(UInt(1)), TRUE, BadHeader("roots and version are required")),
    Hdr(<<MapI(0)>>, TRUE, BadHeader("roots and version are required")),
    Hdr(HeaderItems(<<>>) \o <<UInt(0)>>, TRUE, BadHeader("bytes follow the header map")),
    Hdr(HeaderItems(<<>>), FALSE, BadHeader("bytes follow the header map")),
    Hdr(HeaderItems(<<BadV2>>), TRUE, CErr("version")),
    Hdr(<<MapI(2), Txt(KRoots), UInt(0)>> \o Ver(UInt(1)), TRUE, CErr("wire")),
    Hdr(<<Arr(0)>>, TRUE, WErr),
    Hdr(<<MapI(2)>> \o NoRoots \o <<Txt(KVersion)>>, TRUE, WErr),
    Hdr(<<MapI(2)>> \o Ver(UInt(1)) \o NoRoots, TRUE, WErr)}

GoodHdrs == {Hdr(HeaderItems(r), TRUE, [err |-> "ok", roots |-> r]) : r \in RootSets}

(* the tokenizer of the model: a table from header body bytes to [items, end], computed once *)
HdrTable == [b \in {HdrBytes(h) : h \in BadHdrs \cup GoodHdrs} |->
                LET h == CHOOSE h \in BadHdrs \cup GoodHdrs : HdrBytes(h) = b IN [items |-> h.items, end |-> h.end]]
NoTok == [items |-> <<>>, end |-> FALSE]
TokOf(buf, max) ==
    LET f == Frame(buf, max) IN
    IF f.t = "ready" /\ f.body \in DOMAIN HdrTable THEN HdrTable[f.body] ELSE NoTok

ReadM(buf, max, verify) == Read(buf, max, verify, TokOf(buf, max), GenSet)

(* the stream driver: decode on the buffer; on NeedMore(n) append n bytes ("min") or n + 7 ("more") from the
   CAR, or end when the CAR is spent; on a header or section drop `consumed` bytes. bound: every NeedMore(n) has
   the buffer plus n within max + 9. *)
RECURSIVE Drive(_, _, _, _, _, _, _, _, _)
Drive(car, max, verify, pol, buf, k, done, out, bound) ==
    LET d == DecodeStream(done, buf, max, verify, TokOf(buf, max), GenSet) IN
    IF d.t = "err" THEN [out |-> Append(out, d.e), bound |-> bound]
    ELSE IF d.t = "need"
         THEN LET b2 == bound /\ U!Le(U!Add(U!W(Len(buf)), d.n), U!Add(max, U!W(9))) IN
              IF k >= Len(car) THEN [out |-> Append(out, [t |-> "end", clean |-> buf = <<>> /\ done]), bound |-> b2]
              ELSE LET want == U!Val(d.n) + (IF pol = "more" THEN 7 ELSE 0)
                       take == IF k + want > Len(car) THEN Len(car) - k ELSE want
                   IN Drive(car, max, verify, pol, buf \o SubSeq(car, k + 1, k + take), k + take, done, out, b2)
    ELSE Drive(car, max, verify, pol, Drop(buf, d.consumed), k, TRUE, Append(out, d.entry), bound)

Stream(car, max, verify, pol) == Drive(car, max, verify, pol, <<>>, 0, FALSE, <<>>, TRUE)

(* the reader's result as the decoder's sequence *)
AsStream(r) ==
    IF r.err # "ok" THEN <<r>>
    ELSE <<[t |-> "hdr", roots |-> r.roots]>>
         \o [i \in 1..Len(r.secs) |-> IF r.secs[i].err = "ok" THEN [t |-> "sec", cid |-> r.secs[i].cid, blk |-> r.secs[i].blk]
                                       ELSE r.secs[i]]
         \o (IF r.secs # <<>> /\ r.secs[Len(r.secs)].err # "ok" THEN <<>> ELSE <<[t |-> "end", clean |-> TRUE]>>)

MaxBody(x) ==
    LET bodies == {HeaderBodyLen(x.roots)} \cup {SecBody(x.secs[i]) : i \in 1..Len(x.secs)}
    IN CHOOSE m \in bodies : \A o \in bodies : o <= m
MaxOf(x) == CASE x.mc = "exact" -> U!W(MaxBody(x)) [] x.mc = "less" -> U!W(MaxBody(x) - 1) [] x.mc = "huge" -> U!Max64

CarCases == {[t |-> "car", roots |-> r, secs |-> s, mc |-> m, verify |-> v] :
                r \in RootSets, s \in SecSeqs, m \in {"exact", "less", "huge"}, v \in BOOLEAN}
HdrCases == {[t |-> "hdr", h |-> h] : h \in BadHdrs}

(* length prefixes: non-minimal, ten bytes, 2^62 under the exact maximum and under none *)
GoodBody == L!ItemsBytes(HeaderItems(<<>>))
FrameCases == {
    [t |-> "frame", in |-> <<Len(GoodBody) + 128, 0>> \o GoodBody, max |-> U!Max64, want |-> WireK("nonminimal")],
    [t |-> "frame", in |-> [i \in 1..9 |-> 128] \o <<0>>, max |-> U!Max64, want |-> WireK("toolong")],
    [t |-> "frame", in |-> V!Encode(U!Pw(62), 16).bytes, max |-> U!W(Len(GoodBody)), want |-> TooLarge(U!Pw(62), U!W(Len(GoodBody)))],
    [t |-> "frame", in |-> V!Encode(U!Pw(62), 16).bytes, max |-> U!Max64, want |-> Trunc(U!Pw(62))],
    [t |-> "frame", in |-> <<>>, max |-> U!Max64, want |-> Trunc(U!One)],
    [t |-> "frame", in |-> <<Len(GoodBody)>> \o GoodBody, max |-> U!W(Len(GoodBody)), want |-> [err |-> "ok", roots |-> <<>>, secs |-> <<>>]],
    [t |-> "frame", in |-> <<Len(GoodBody)>> \o GoodBody, max |-> U!W(Len(GoodBody) - 1), want |-> TooLarge(U!W(Len(GoodBody)), U!W(Len(GoodBody) - 1))]}

Starts ==
    (IF "car" \in Parts THEN CarCases ELSE {})
    \cup (IF "hdr" \in Parts THEN HdrCases ELSE {})
    \cup (IF "frame" \in Parts THEN FrameCases ELSE {})

VARIABLE c
Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E x \in Starts : c' = x
Spec == Init /\ [][Next]_c

(***************************************************************************)
(* The properties                                                          *)
(***************************************************************************)

(* the reader's result the documentation states *)
RECURSIVE WantSecs(_, _, _)
WantSecs(ss, max, verify) ==
    IF ss = <<>> THEN <<>>
    ELSE LET s == Head(ss) IN
         IF ~U!Le(U!W(SecBody(s)), max) THEN <<TooLarge(U!W(SecBody(s)), max)>>
         ELSE IF verify /\ ~s.known THEN <<CErr("unsupported")>>
         ELSE IF verify /\ ~s.genuine THEN <<CErr("digest")>>
         ELSE <<[err |-> "ok", cid |-> s.cid, blk |-> s.blk]>> \o WantSecs(Tail(ss), max, verify)

Want(x) ==
    LET max == MaxOf(x)
        hb == HeaderBodyLen(x.roots)
    IN IF ~U!Le(U!W(hb), max) THEN TooLarge(U!W(hb), max)
       ELSE [err |-> "ok", roots |-> x.roots, secs |-> WantSecs(x.secs, max, x.verify)]

(* a cut after j bytes, with no maximum and no verify *)
RECURSIVE CutSecs(_, _, _)
CutSecs(ss, start, j) ==
    IF ss = <<>> \/ start = j THEN <<>>
    ELSE LET s == Head(ss)
             sl == SectionLen(s.cid, s.blk)
             pl == sl - SecBody(s)
         IN IF start + sl <= j THEN <<[err |-> "ok", cid |-> s.cid, blk |-> s.blk]>> \o CutSecs(Tail(ss), start + sl, j)
            ELSE <<Trunc(IF j - start < pl THEN U!One ELSE U!W(start + sl - j))>>

WantCut(x, j) ==
    LET hl == HeaderLen(x.roots)
        pl == hl - HeaderBodyLen(x.roots)
    IN IF j < hl THEN Trunc(IF j < pl THEN U!One ELSE U!W(hl - j))
       ELSE [err |-> "ok", roots |-> x.roots, secs |-> CutSecs(x.secs, hl, j)]

(* the decoder on a cut CAR: the frames it holds, then the end of the stream, clean only between two frames after
   the header ("end of stream between frames is a complete CAR", stream.rs) *)
StreamCut(w) ==
    IF w.err # "ok" THEN <<[t |-> "end", clean |-> FALSE]>>
    ELSE LET done == SelectSeq(w.secs, LAMBDA e : e.err = "ok") IN
         <<[t |-> "hdr", roots |-> w.roots]>>
         \o [i \in 1..Len(done) |-> [t |-> "sec", cid |-> done[i].cid, blk |-> done[i].blk]]
         \o <<[t |-> "end", clean |-> Len(done) = Len(w.secs)]>>

RECURSIVE Ends(_, _)
Ends(ss, start) == IF ss = <<>> THEN {} ELSE LET e == start + SectionLen(Head(ss).cid, Head(ss).blk) IN {e} \cup Ends(Tail(ss), e)

(* the cuts: every position in the header and up to 2 past it, and up to 2 around every section end *)
CutPos(x, car) ==
    LET hl == HeaderLen(x.roots) IN
    {j \in 0..(Len(car) - 1) : j <= hl + 2 \/ \E e \in Ends(x.secs, hl) : j >= e - 2 /\ j <= e + 2}

RECURSIVE WriteSecs(_, _)
WriteSecs(acc, ss) == IF ss = <<>> THEN acc ELSE WriteSecs(acc \o WriterSection(Len(acc), Big, Head(ss).cid, Head(ss).blk).app, Tail(ss))

WriterOK(x) ==
    LET hl == HeaderLen(x.roots)
        w == WriterNew(x.roots, Big)
    IN /\ Len(L!ItemsBytes(HeaderItems(x.roots))) = HeaderBodyLen(x.roots)
       /\ w.err = "ok" /\ w.pos = hl
       /\ WriterNew(x.roots, hl) = w
       /\ WriterNew(x.roots, hl - 1) = Small(1)
       /\ WriterNew(x.roots, 0) = Small(hl)
       /\ WriteSecs(w.bytes, x.secs) = CarSpec(x.roots, x.secs)
       /\ \A i \in 1..Len(x.secs) :
            LET s == x.secs[i]
                sl == SectionLen(s.cid, s.blk)
            IN /\ WriterSection(hl, hl + sl, s.cid, s.blk) = [err |-> "ok", app |-> SecBytes(s), pos |-> hl + sl]
               /\ WriterSection(hl, hl + sl - 1, s.cid, s.blk) = Small(1)
               /\ WriterSection(hl, hl, s.cid, s.blk) = Small(sl)

CarOK(x) ==
    LET car == CarSpec(x.roots, x.secs)
        max == MaxOf(x)
        r == ReadM(car, max, x.verify)
    IN /\ r = Want(x)
       /\ WriterOK(x)
       /\ \A pol \in {"min", "more"} :
            LET st == Stream(car, max, x.verify, pol) IN st.out = AsStream(r) /\ st.bound
       /\ (x.mc = "huge" /\ ~x.verify) =>
            \A j \in CutPos(x, car) :
                /\ ReadM(SubSeq(car, 1, j), max, FALSE) = WantCut(x, j)
                /\ Stream(SubSeq(car, 1, j), max, FALSE, "min").out = StreamCut(WantCut(x, j))

HdrOK(h) ==
    LET body == HdrBytes(h)
        car == Pfx(Len(body)) \o body
    IN /\ ReadM(car, U!Max64, FALSE) = h.want
       /\ DecodeStream(FALSE, car, U!Max64, FALSE, TokOf(car, U!Max64), GenSet) = [t |-> "err", e |-> h.want]

FrameOK(x) == ReadM(x.in, x.max, FALSE) = x.want

Inv ==
    CASE c.t = "car" -> CarOK(c)
      [] c.t = "hdr" -> HdrOK(c.h)
      [] c.t = "frame" -> FrameOK(c)
      [] OTHER -> TRUE

(* Not a law: every proper cut of a CAR is refused. TLC finds the violation (DagCar_cut.cfg). *)
CutRefused ==
    (c.t = "car" /\ c.mc = "huge" /\ ~c.verify) =>
        \A j \in CutPos(c, CarSpec(c.roots, c.secs)) :
            LET r == ReadM(SubSeq(CarSpec(c.roots, c.secs), 1, j), U!Max64, FALSE)
            IN r.err # "ok" \/ (r.secs # <<>> /\ r.secs[Len(r.secs)].err # "ok")
=============================================================================
