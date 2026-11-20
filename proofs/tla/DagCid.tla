------------------------------- MODULE DagCid -------------------------------
(***************************************************************************)
(* The CIDs of pinc-dag (cid/mod.rs, owned.rs, text.rs, hash.rs), byte     *)
(* for byte: CidRef::parse_prefix (ParsePrefix), CidRef::parse (Parse),    *)
(* Cid::new (NewCid), Cid::for_block (ForBlock), CidRef::verify (Verify),  *)
(* CidRef::digest (Digest), text::chars (Chars), text::encode              *)
(* (EncodeText), text::decode and Cid::parse_text (DecodeText, ParseText)  *)
(* and cmp_text (CmpText). The varints are those of Varint.tla (the model  *)
(* of pinc-wire varint.rs, on the 64-bit words of U64.tla).                *)
(*                                                                         *)
(* What the module documentation states, checked by TLC (DagCid.cfg):      *)
(*   CidOK      Cid::new accepts exactly a digest of at most 64 bytes, a   *)
(*              codec and hash code below 2^63 and, for SHA2-256 and       *)
(*              BLAKE3, a 32-byte digest, refusing the rest with the       *)
(*              documented error in the code's order; the bytes are        *)
(*              varint(1) varint(codec) varint(hash) varint(len) digest    *)
(*              (CidBytes, stated apart from the parser), at most MAX_LEN  *)
(*              (84) long, and parse back to the same parts;               *)
(*   (CidOK)    parse_prefix returns the CID and exactly the bytes after   *)
(*              it; parse refuses a trailing byte; every proper cut is a   *)
(*              truncation;                                                *)
(*   BytesOK    every accepted single-byte mutation of the header and the  *)
(*              last byte, and every accepted input of up to 4 bytes over  *)
(*              a class alphabet, is the CidBytes of its own parts: the    *)
(*              byte form of a CID is unique (CidOK checks the mutations); *)
(*   (Classes)  CIDv0, a version other than 1, a non-minimal or too long   *)
(*              varint, a digest over 64 bytes, a known hash with a        *)
(*              digest that is not 32 bytes and a short digest are each    *)
(*              refused with their own error;                              *)
(*   TextOKFor  chars is the RFC 4648 base32 lower text with the b prefix  *)
(*              (TextSpec, stated apart from the code), at most            *)
(*              MAX_TEXT_LEN (136) long, encode_text fits exactly when the *)
(*              buffer holds it, parse_text inverts it, every accepted     *)
(*              text is the text of its bytes (one text per CID), and the  *)
(*              missing prefix, a character outside the alphabet, a text   *)
(*              whose length no CID has (5 or more bits left over: not a   *)
(*              whole number of bytes), nonzero padding and a text longer  *)
(*              than any CID are refused, each with its own reason (TextOK *)
(*              checks every short text);                                  *)
(*   PairOK     cmp_text is the order of the texts, antisymmetric, and 0   *)
(*              exactly for equal CIDs;                                    *)
(*   HashOK     for_block of a known hash builds the CID of the digest,    *)
(*              verify accepts the block it was built from and refuses     *)
(*              another, and an unknown hash code is refused by both.      *)
(* The hash function is an ideal one: Genuine is an injective stand-in on  *)
(* the checked domain, and the trace records the genuine SHA2-256 and      *)
(* BLAKE3 digests.                                                         *)
(* Witness (DagCid_order.cfg): ByteOrderIsTextOrder is violated, so the    *)
(* text order differs from the byte order (the module documentation says   *)
(* so) on the checked pairs.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

U == INSTANCE U64
V == INSTANCE Varint WITH SmallMax <- 0, c <- 0

MaxDigestLen == 64
DigestLen == 32
MaxLen == 1 + 9 + 9 + 1 + MaxDigestLen
NDigits(n) == (8 * n + 4) \div 5
MaxTextLen == 1 + NDigits(MaxLen)
Sha256 == U!W(18)
Blake3 == U!W(30)
Known(h) == h = Sha256 \/ h = Blake3
Limit == U!Pw(63)

Drop(s, n) == SubSeq(s, n + 1, Len(s))
Same(n, x) == [i \in 1..n |-> x]

(* ---- errors: CidError, and the WireError kinds of Varint.tla ---- *)
WireErr(kind, needed) == [err |-> "wire", w |-> kind, needed |-> needed]
VarErr(d) == WireErr(d.kind, IF d.kind = "truncated" THEN 1 ELSE 0)
TErr(why) == [err |-> "text", why |-> why]

(* ---- CidRef::parse_prefix and CidRef::parse ---- *)
ParsePrefix(input) ==
    IF Len(input) >= 2 /\ input[1] = 18 /\ input[2] = 32 THEN [err |-> "v0"]
    ELSE LET dv == V!Decode(input) IN
    IF dv.kind # "ok" THEN VarErr(dv)
    ELSE IF dv.v # U!One THEN [err |-> "version", v |-> dv.v]
    ELSE LET p1 == dv.n
             dc == V!Decode(Drop(input, p1)) IN
    IF dc.kind # "ok" THEN VarErr(dc)
    ELSE LET p2 == p1 + dc.n
             dh == V!Decode(Drop(input, p2)) IN
    IF dh.kind # "ok" THEN VarErr(dh)
    ELSE LET p3 == p2 + dh.n
             dl == V!Decode(Drop(input, p3)) IN
    IF dl.kind # "ok" THEN VarErr(dl)
    \* u8::try_from(len).filter(<= 64)
    ELSE IF ~U!Lt(dl.v, U!W(MaxDigestLen + 1)) THEN [err |-> "toolong", len |-> dl.v]
    ELSE IF Known(dh.v) /\ dl.v # U!W(DigestLen) THEN [err |-> "mismatch", hash |-> dh.v, len |-> dl.v]
    ELSE LET p4 == p3 + dl.n
             n == U!Val(dl.v) IN
    \* Reader::read_bytes: Truncated { needed: n - remaining }
    IF Len(input) - p4 < n THEN WireErr("truncated", n - (Len(input) - p4))
    ELSE [err |-> "ok", cid |-> [raw |-> SubSeq(input, 1, p4 + n), codec |-> dc.v, hash |-> dh.v, dlen |-> n],
          rest |-> Drop(input, p4 + n)]

Parse(input) ==
    LET r == ParsePrefix(input) IN
    IF r.err # "ok" THEN r
    ELSE IF r.rest # <<>> THEN [err |-> "trailing"]
    ELSE [err |-> "ok", cid |-> r.cid]

(* CidRef::digest: the last dlen bytes of the raw CID *)
Digest(cid) == SubSeq(cid.raw, Len(cid.raw) - cid.dlen + 1, Len(cid.raw))

(* ---- Cid::new: four put_varint and a put_slice into a MAX_LEN buffer, then a re-parse ---- *)
PutErr(e) == WireErr(e.kind, IF e.kind = "small" THEN e.needed ELSE 0)

NewCid(codec, hash, d) ==
    IF Len(d) > MaxDigestLen THEN [err |-> "toolong", len |-> U!W(Len(d))]
    ELSE LET e1 == V!Encode(U!One, MaxLen) IN
    IF e1.kind # "ok" THEN PutErr(e1)
    ELSE LET e2 == V!Encode(codec, MaxLen - Len(e1.bytes)) IN
    IF e2.kind # "ok" THEN PutErr(e2)
    ELSE LET e3 == V!Encode(hash, MaxLen - Len(e1.bytes) - Len(e2.bytes)) IN
    IF e3.kind # "ok" THEN PutErr(e3)
    ELSE LET e4 == V!Encode(U!W(Len(d)), MaxLen - Len(e1.bytes) - Len(e2.bytes) - Len(e3.bytes)) IN
    IF e4.kind # "ok" THEN PutErr(e4)
    ELSE LET room == MaxLen - Len(e1.bytes) - Len(e2.bytes) - Len(e3.bytes) - Len(e4.bytes) IN
    IF room < Len(d) THEN WireErr("small", Len(d) - room)
    ELSE LET bytes == e1.bytes \o e2.bytes \o e3.bytes \o e4.bytes \o d IN
    \* u8::try_from(written.len()).map_err(|_| too_long)
    IF Len(bytes) > 255 THEN [err |-> "toolong", len |-> U!W(Len(d))]
    ELSE Parse(bytes)

(* ---- hash.rs, Cid::for_block and CidRef::verify; g is the genuine digest of the block (ideal hash) ---- *)
ForBlock(codec, hash, g) == IF ~Known(hash) THEN [err |-> "unsupported", hash |-> hash] ELSE NewCid(codec, hash, g)

Verify(cid, g) ==
    IF ~Known(cid.hash) THEN [err |-> "unsupported", hash |-> cid.hash]
    ELSE IF g = Digest(cid) THEN [err |-> "ok"]
    ELSE [err |-> "digest"]

(* ---- text.rs ---- *)

(* ALPHABET: a..z then 2..7, as ASCII codes *)
B32(v) == IF v < 26 THEN 97 + v ELSE 50 + (v - 26)

(* chars: the lazy iterator, step for step: pull a byte while fewer than 5 bits are held, emit the top 5 bits, and
   at the end the remaining bits shifted up; acc is a u16 *)
RECURSIVE CharsFrom(_, _, _, _)
CharsFrom(bs, k, acc, bits) ==
    IF bits < 5 /\ k <= Len(bs) THEN CharsFrom(bs, k + 1, (acc * 256 + bs[k]) % 65536, bits + 8)
    ELSE IF bits >= 5
         THEN LET nb == bits - 5
              IN <<B32((acc \div (2 ^ nb)) % 32)>> \o CharsFrom(bs, k, acc % (2 ^ nb), nb)
    ELSE IF bits > 0 THEN <<B32((acc * (2 ^ (5 - bits))) % 32)>> \o CharsFrom(bs, k, 0, 0)
    ELSE <<>>

Chars(bs) == <<98>> \o CharsFrom(bs, 1, 0, 0)

(* the specification of the text, apart from the code: digit j holds bits 5j .. 5j + 4 of the bytes, most
   significant first, the bits past the end being zero *)
DigitAt(bs, j) ==
    LET o == 5 * j
        q == o \div 8
        r == o % 8
        b1 == IF q + 2 <= Len(bs) THEN bs[q + 2] ELSE 0
    IN ((bs[q + 1] * 256 + b1) \div (2 ^ (11 - r))) % 32

TextSpec(bs) == <<98>> \o [j \in 1..NDigits(Len(bs)) |-> B32(DigitAt(bs, j - 1))]

(* text::encode into a buffer of cap bytes *)
EncodeText(bs, cap) ==
    LET n == 1 + NDigits(Len(bs)) IN
    IF n > cap THEN [err |-> "small", needed |-> n - cap] ELSE [err |-> "ok", text |-> Chars(bs)]

(* text::decode over the digits after the prefix: acc is a u16, out the [u8; MAX_LEN] buffer *)
RECURSIVE DecFrom(_, _, _, _, _)
DecFrom(ds, i, acc, bits, out) ==
    IF i > Len(ds)
    THEN IF bits >= 5 THEN TErr("the text is not a whole number of bytes")
         ELSE IF acc # 0 THEN TErr("padding bits are not zero") ELSE [err |-> "ok", bytes |-> out]
    ELSE LET ch == ds[i] IN
         IF ~((ch >= 97 /\ ch <= 122) \/ (ch >= 50 /\ ch <= 55))
         THEN TErr("character outside the base32 lower alphabet")
         ELSE LET v == IF ch >= 97 THEN ch - 97 ELSE ch - 50 + 26
                  acc1 == ((acc * 32) % 65536) + v
                  bits1 == bits + 5
              IN IF bits1 >= 8
                 THEN LET nb == bits1 - 8
                          byte == acc1 \div (2 ^ nb)
                      IN IF byte > 255 THEN TErr("bad digit")
                         ELSE IF Len(out) >= MaxLen THEN TErr("longer than any CID")
                         ELSE DecFrom(ds, i + 1, acc1 % (2 ^ nb), nb, Append(out, byte))
                 ELSE DecFrom(ds, i + 1, acc1, bits1, out)

DecodeText(s) ==
    IF Len(s) = 0 \/ s[1] # 98 THEN TErr("missing the b prefix") ELSE DecFrom(Tail(s), 1, 0, 0, <<>>)

(* Cid::parse_text *)
ParseText(s) == LET d == DecodeText(s) IN IF d.err # "ok" THEN d ELSE Parse(d.bytes)

(* Iterator::cmp: lexicographic, a proper prefix first; -1, 0, 1 *)
RECURSIVE SeqCmpAt(_, _, _)
SeqCmpAt(a, b, i) ==
    IF i > Len(a) /\ i > Len(b) THEN 0
    ELSE IF i > Len(a) THEN -1
    ELSE IF i > Len(b) THEN 1
    ELSE IF a[i] < b[i] THEN -1
    ELSE IF a[i] > b[i] THEN 1
    ELSE SeqCmpAt(a, b, i + 1)
SeqCmp(a, b) == SeqCmpAt(a, b, 1)

(* cmp_text over the raw bytes of two CIDs *)
CmpText(a, b) == SeqCmp(Chars(a), Chars(b))

(***************************************************************************)
(* The checked domain                                                      *)
(***************************************************************************)
CONSTANT Parts

Max63 == U!Sub(Limit, U!One)
(* one value per class: a one-byte and a two-byte varint, the largest encodable value, the first refused one;
   the two known hash codes and an unknown one *)
Codecs == {U!W(113), U!W(128), Max63, Limit}
Hashes == {Sha256, Blake3, U!Zero, Max63, Limit}
DLens == {0, 1, 31, 32, 33, 64, 65}
Ramp(n) == [i \in 1..n |-> (37 * i + 11) % 256]

(* the CIDs of every codec, hash code and digest length class, with a ramp digest; zero and 0xff digests of a
   BLAKE3 CID and of the longest CID (84 bytes) *)
CidCases ==
    {[t |-> "cid", codec |-> co, hash |-> h, d |-> Ramp(n)] : co \in Codecs, h \in Hashes, n \in DLens}
    \cup {[t |-> "cid", codec |-> p[1], hash |-> p[2], d |-> Same(p[3], x)] :
            p \in {<<U!W(113), Blake3, 32>>, <<Max63, Max63, 64>>}, x \in {0, 255}}

(* pairs for the text order: two CIDs whose last digits are '2' and 'z' (byte order and text order disagree), a
   shorter and a longer CID and a BLAKE3 CID *)
ShortPool == {<<1, 113, 0, 1, 25>>, <<1, 113, 0, 1, 26>>, <<1, 85, 0, 0>>}
PairPool == ShortPool \cup {<<1, 113, 0, 2, 25, 0>>, NewCid(U!W(113), Blake3, Ramp(32)).cid.raw}
PairCases == {[t |-> "pair", a |-> a, b |-> b] : a \in PairPool, b \in PairPool}

(* the pairs of the short CIDs only, for the witness (no deep recursion: it runs on the default stack) *)
OrderCases == {[t |-> "pair", a |-> a, b |-> b] : a \in ShortPool, b \in ShortPool}

(* the ideal hash: an injective stand-in for blocks of up to 30 bytes *)
Genuine(code, blk) ==
    [i \in 1..32 |-> IF i = 1 THEN code[1] % 256 ELSE IF i = 2 THEN Len(blk) ELSE IF i - 2 <= Len(blk) THEN blk[i - 2] ELSE 0]
Blocks == {<<>>, <<1, 2, 3>>}
HashCases == {[t |-> "hash", codec |-> U!W(113), hash |-> h, blk |-> b] : h \in {Sha256, Blake3, U!Zero}, b \in Blocks}

(* the input alphabets: binary strings of up to 4 bytes over byte classes (zero, small, the CIDv0 bytes, the BLAKE3
   code, continuation bytes); texts of "b" and up to 3 characters over digits, an uppercase letter and a character
   outside the alphabet *)
JAlpha == {0, 1, 2, 18, 30, 32, 128, 255}
TAlpha == {97, 122, 50, 55, 65, 49}

Starts ==
    (IF "cid" \in Parts THEN CidCases ELSE {})
    \cup (IF "pair" \in Parts THEN PairCases ELSE {})
    \cup (IF "order" \in Parts THEN OrderCases ELSE {})
    \cup (IF "hash" \in Parts THEN HashCases ELSE {})
    \cup (IF "bytes" \in Parts THEN {[t |-> "bytes", in |-> <<>>]} ELSE {})
    \cup (IF "text" \in Parts THEN {[t |-> "text", in |-> s] : s \in {<<>>, <<66>>, <<98>>}} ELSE {})

VARIABLE c
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E x \in Starts : c' = x
    \/ c.t = "bytes" /\ Len(c.in) < 4 /\ \E b \in JAlpha : c' = [c EXCEPT !.in = Append(c.in, b)]
    \/ c.t = "text" /\ Len(c.in) >= 1 /\ c.in[1] = 98 /\ Len(c.in) < 4 /\ \E ch \in TAlpha : c' = [c EXCEPT !.in = Append(c.in, ch)]
Spec == Init /\ [][Next]_c

(***************************************************************************)
(* The properties                                                          *)
(***************************************************************************)

(* the bytes of a CID, apart from the parser: the minimal varints of Varint.tla and the digest *)
CidBytes(codec, hash, d) == <<1>> \o V!Encode(codec, 16).bytes \o V!Encode(hash, 16).bytes \o <<Len(d)>> \o d

(* the index of the digest length byte *)
LenAt(x) == 1 + Len(V!Encode(x.codec, 16).bytes) + Len(V!Encode(x.hash, 16).bytes) + 1

(* the result of Cid::new the documentation states, in the order of the code's checks *)
Expected(x) ==
    IF Len(x.d) > MaxDigestLen THEN [err |-> "toolong", len |-> U!W(Len(x.d))]
    ELSE IF ~U!Lt(x.codec, Limit) \/ ~U!Lt(x.hash, Limit) THEN WireErr("overflow", 0)
    ELSE IF Known(x.hash) /\ Len(x.d) # DigestLen THEN [err |-> "mismatch", hash |-> x.hash, len |-> U!W(Len(x.d))]
    ELSE [err |-> "ok", cid |-> [raw |-> CidBytes(x.codec, x.hash, x.d), codec |-> x.codec, hash |-> x.hash, dlen |-> Len(x.d)]]

Rests == {<<>>, <<0>>, <<1, 113>>, <<18, 32>>, <<255>>}
CutPos(b) == {j \in 0..(Len(b) - 1) : j <= 24 \/ j >= Len(b) - 2}
Muts(b, h) == {[b EXCEPT ![j] = v] : j \in {j \in 1..Len(b) : j <= h + 1 \/ j = Len(b)}, v \in {0, 1, 18, 128, 255}} \ {b}
Reenc(m) == LET p == Parse(m) IN p.err = "ok" => CidBytes(p.cid.codec, p.cid.hash, Digest(p.cid)) = m

Classes(x, b) ==
    LET h == LenAt(x) IN
    /\ Parse(<<18, 32>> \o b) = [err |-> "v0"]
    /\ \A v \in {0, 2, 3, 127} : Parse([b EXCEPT ![1] = v]) = [err |-> "version", v |-> U!W(v)]
    /\ Parse(<<129, 0>> \o Tail(b)) = WireErr("nonminimal", 0)
    /\ Parse(Same(9, 128) \o b) = WireErr("toolong", 0)
    /\ \A n \in {65, 100, 127} : Parse([b EXCEPT ![h] = n]) = [err |-> "toolong", len |-> U!W(n)]
    /\ Known(x.hash) => \A n \in {0, 31, 33, 64} : Parse([b EXCEPT ![h] = n]) = [err |-> "mismatch", hash |-> x.hash, len |-> U!W(n)]
    /\ (~Known(x.hash) /\ Len(x.d) < MaxDigestLen) => Parse([b EXCEPT ![h] = Len(x.d) + 1]) = WireErr("truncated", 1)

TextMuts(t) ==
    ({[t EXCEPT ![j] = ch] : j \in {2, 3, Len(t) - 1, Len(t)}, ch \in {97, 98, 55, 50, 122}}
     \cup {SubSeq(t, 1, Len(t) - 1), SubSeq(t, 1, Len(t) - 2), t \o <<97>>, t \o <<97, 97>>}) \ {t}
TextReenc(m) == LET p == ParseText(m) IN p.err = "ok" => Chars(p.cid.raw) = m

TextOKFor(r, b) ==
    LET t == Chars(b)
        n == Len(t)
    IN /\ t = TextSpec(b)
       /\ n = 1 + NDigits(Len(b)) /\ n <= MaxTextLen
       /\ EncodeText(b, MaxTextLen) = [err |-> "ok", text |-> t]
       /\ EncodeText(b, n) = [err |-> "ok", text |-> t]
       /\ EncodeText(b, n - 1) = [err |-> "small", needed |-> 1]
       /\ EncodeText(b, 0) = [err |-> "small", needed |-> n]
       /\ ParseText(t) = r
       /\ ParseText(Tail(t)) = TErr("missing the b prefix")
       /\ ParseText([t EXCEPT ![2] = t[2] - 32]) = TErr("character outside the base32 lower alphabet")
       /\ \A m \in TextMuts(t) : TextReenc(m)
       /\ Len(b) = MaxLen => ParseText(t \o <<97, 97>>) = TErr("longer than any CID")

CidOK(x) ==
    LET r == NewCid(x.codec, x.hash, x.d) IN
    /\ r = Expected(x)
    /\ r.err = "ok" =>
         LET b == r.cid.raw IN
         /\ Len(b) <= MaxLen
         /\ Digest(r.cid) = x.d
         /\ Parse(b) = r
         /\ \A rest \in Rests : ParsePrefix(b \o rest) = [err |-> "ok", cid |-> r.cid, rest |-> rest]
         /\ \A z \in {0, 1, 255} : Parse(b \o <<z>>) = [err |-> "trailing"]
         /\ \A j \in CutPos(b) : LET p == Parse(SubSeq(b, 1, j)) IN p.err = "wire" /\ p.w = "truncated"
         /\ \A m \in Muts(b, LenAt(x)) : Reenc(m)
         /\ Classes(x, b)
         /\ TextOKFor(r, b)

PairOK(a, b) ==
    /\ CmpText(a, b) = SeqCmp(TextSpec(a), TextSpec(b))
    /\ CmpText(a, b) = -CmpText(b, a)
    /\ (CmpText(a, b) = 0) <=> (a = b)

HashOK(x) ==
    LET g == Genuine(x.hash, x.blk)
        r == ForBlock(x.codec, x.hash, g)
    IN IF ~Known(x.hash)
       THEN /\ r = [err |-> "unsupported", hash |-> x.hash]
            /\ Verify(NewCid(x.codec, x.hash, g).cid, g) = [err |-> "unsupported", hash |-> x.hash]
       ELSE /\ r.err = "ok"
            /\ Digest(r.cid) = g
            /\ Verify(r.cid, g) = [err |-> "ok"]
            /\ \A o \in Blocks \ {x.blk} : Verify(r.cid, Genuine(x.hash, o)) = [err |-> "digest"]

(* every short input: the error kinds are CidError's, an accepted input is the CidBytes of its parts (unique byte
   form), parse_prefix splits the input, and the text of the input parses to the same result *)
BytesOK(s) ==
    LET p == Parse(s)
        pp == ParsePrefix(s)
    IN /\ p.err \in {"ok", "v0", "version", "toolong", "mismatch", "trailing", "wire"}
       /\ p.err = "ok" => /\ CidBytes(p.cid.codec, p.cid.hash, Digest(p.cid)) = s
                          /\ NewCid(p.cid.codec, p.cid.hash, Digest(p.cid)) = p
       /\ pp.err = "ok" => pp.cid.raw \o pp.rest = s
       /\ ParseText(TextSpec(s)) = p

(* every short text: an accepted text is the text of its bytes; the "bad digit" branch is never taken *)
TextOK(s) ==
    LET d == DecodeText(s) IN
    /\ d.err \in {"ok", "text"}
    /\ d.err = "ok" => TextSpec(d.bytes) = s
    /\ d.err = "text" => d.why # "bad digit"

Inv ==
    CASE c.t = "cid" -> CidOK(c)
      [] c.t = "pair" -> PairOK(c.a, c.b)
      [] c.t = "hash" -> HashOK(c)
      [] c.t = "bytes" -> BytesOK(c.in)
      [] c.t = "text" -> TextOK(c.in)
      [] OTHER -> TRUE

(* Not a law: the module documentation says the text order differs from the byte order. TLC finds the violation
   (DagCid_order.cfg). *)
ByteOrderIsTextOrder == c.t = "pair" => CmpText(c.a, c.b) = SeqCmp(c.a, c.b)
=============================================================================
