------------------------------ MODULE Varint ------------------------------
(***************************************************************************)
(* The unsigned varint of vinc-wire (varint.rs), written step for step on  *)
(* the machine integers of U64.tla: `encoded_len` (u64::bit_width, usize   *)
(* div_ceil), `encode` (the overflow test, the saturating_sub of the       *)
(* missing bytes, the shift by 7 * i and the mask of each group) and       *)
(* `decode` (the loop over the first 9 bytes, `value |= (b & 0x7f) << 7i`, *)
(* the trailing-zero test). A shift by 64 or more, an overflow or an       *)
(* underflow stops TLC with an error, so a finished model check shows     *)
(* that no such operation is reachable in the checked domain.              *)
(*                                                                         *)
(* The specification of a varint is stated apart from the code: an         *)
(* encoding is a byte string of 1 to 9 bytes whose last byte is below 128, *)
(* whose others are at least 128 and which does not end in a zero byte     *)
(* unless it is one byte long (IsEnc); its value is the sum of the low 7   *)
(* bits of each byte times 2^(7 * position) (ValueOf).                     *)
(*                                                                         *)
(* Checked by TLC (Varint.cfg) over:                                       *)
(*  - every value below SmallMax and, for every j in 0..64, the values     *)
(*    2^j - 1, 2^j, 2^j + 1 (the boundaries of every byte length, 2^63 and *)
(*    u64::MAX among them), with every buffer size 0..10 and the rests     *)
(*    {}, {0}, {128}, {255}, {0, 0}, {128, 128};                           *)
(*  - every byte string of 0 to 2 bytes, every string of 0 to 4 bytes over *)
(*    a class alphabet (0, 1, 2, 64, 127, 128, 129, 192, 255), and the     *)
(*    strings of 5 to 10 bytes that are a run of continuation bytes        *)
(*    followed by a terminator or by nothing, with and without a trailing  *)
(*    byte (the too long, truncated and non-minimal inputs).               *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Vinc/Varint.lean):                       *)
(*   RoundTrip              Varint.decode_encode                           *)
(*   Canonical, Unique      Varint.decode_canonical, Varint.unique_encoding *)
(*   EncodeLength           Varint.encode_length                           *)
(*   DecodeBounds           Varint.decode_bounds                           *)
(*   EncodeInto             Varint.encodeInto_ok_iff, encodeInto_decode    *)
(*   the boundary sets      Vinc.Link (Varint boundary theorems)           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

CONSTANT SmallMax

MaxLen == 9
Limit == U!Pw(63)

(* ---- the code ---- *)

(* varint::encoded_len; the value must be below 2^63 to be encodable *)
EncodedLen(v) ==
    LET bits == U!BitLen(v)
    IN IF bits = 0 THEN 1 ELSE IF bits % 7 > 0 THEN bits \div 7 + 1 ELSE bits \div 7

(* byte i (0-based) of the encoding of v, which has n bytes *)
EncByte(v, i, n) ==
    LET group == U!Val(U!Low(U!Shr64(v, 7 * i), 7))
    IN IF i + 1 < n THEN group + 128 ELSE group

(* varint::encode into a buffer of cap bytes: the error kinds and, on success, the bytes written *)
Encode(v, cap) ==
    IF ~U!Lt(v, Limit) THEN [kind |-> "overflow"]
    ELSE LET n == EncodedLen(v)
             short == IF n > cap THEN n - cap ELSE 0
         IN IF n > cap THEN [kind |-> "small", needed |-> short]
            ELSE [kind |-> "ok", bytes |-> [i \in 1..n |-> EncByte(v, i - 1, n)]]

(* varint::decode: the loop over the first MaxLen bytes; i is the 0-based index, value the accumulator *)
RECURSIVE DecodeFrom(_, _, _)
DecodeFrom(input, i, value) ==
    IF i >= (IF Len(input) < MaxLen THEN Len(input) ELSE MaxLen)
    THEN IF Len(input) >= MaxLen THEN [kind |-> "toolong"] ELSE [kind |-> "truncated"]
    ELSE LET b == input[i + 1]
             value2 == U!Or(value, U!Shl64(U!W(b % 128), 7 * i))
         IN IF b < 128
            THEN IF b = 0 /\ i > 0 THEN [kind |-> "nonminimal"]
                 ELSE [kind |-> "ok", v |-> value2, n |-> i + 1]
            ELSE DecodeFrom(input, i + 1, value2)

Decode(input) == DecodeFrom(input, 0, U!Zero)

(* ---- the specification, apart from the code ---- *)

Prefix(s, n) == SubSeq(s, 1, n)

(* an encoding: 1 to 9 bytes, continuation bytes then a last byte below 128 that is not zero unless alone *)
IsEnc(p) ==
    /\ Len(p) >= 1 /\ Len(p) <= MaxLen
    /\ \A k \in 1..(Len(p) - 1) : p[k] >= 128
    /\ p[Len(p)] < 128
    /\ (Len(p) = 1 \/ p[Len(p)] # 0)

(* the value of an encoding, as an exact word *)
RECURSIVE ValueOf(_, _)
ValueOf(p, k) == IF k > Len(p) THEN U!Zero ELSE U!Add(U!Shl(U!W(p[k] % 128), 7 * (k - 1)), ValueOf(p, k + 1))

(* ---- the bounded domain ---- *)

(* the boundary values: for j in 0..64, 2^j - 1, 2^j and 2^j + 1 (2^64 itself is not a u64) *)
EdgeVal(j, d) ==
    IF d = -1 THEN U!Sub(U!Pw(j), U!One) ELSE IF d = 0 THEN U!Pw(j) ELSE U!Add(U!Pw(j), U!One)
EdgeOK(j, d) == (j >= 1 \/ d >= 0) /\ (j < 64 \/ d = -1)

Rests == {<<>>, <<0>>, <<128>>, <<255>>, <<0, 0>>, <<128, 128>>}

(* the byte alphabets of the input generators: all bytes, a class alphabet (zero, small, 127, continuation
   bytes of every kind), and the run alphabet of the long inputs *)
Alpha == {0, 1, 2, 64, 127, 128, 129, 192, 255}

(* The cases are the states of one machine, so TLC enumerates them without building a set of all of them:
   the initial states are the values, the inputs grow one byte at a time.
   mode 1: strings of 0..4 bytes over Alpha;  mode 2: strings of 0..2 bytes over all 256 bytes;
   mode 3: runs of 0..10 continuation bytes (128 or 255), each also ended by a terminator (mode 4) and
   followed by a trailing byte (mode 5), the too long, truncated and non-minimal inputs. *)
VARIABLE c
Init == c = [t |-> "root"]

(* the root state has one successor per seed; a seed has one successor per value or the empty input of a mode *)
Seeds ==
    {[f |-> "blk", b |-> b] : b \in 0..((SmallMax - 1) \div 64)}
    \cup {[f |-> "edge", j |-> j, d |-> d] : j \in 0..64, d \in -1..1}
    \cup {[f |-> "dec", a |-> a] : a \in 1..3}

Expand(sd) ==
    CASE sd.f = "blk" -> {[t |-> "enc", v |-> U!W(k)] : k \in (64 * sd.b)..(IF 64 * sd.b + 63 < SmallMax THEN 64 * sd.b + 63 ELSE SmallMax - 1)}
      [] sd.f = "edge" -> IF EdgeOK(sd.j, sd.d) THEN {[t |-> "enc", v |-> EdgeVal(sd.j, sd.d)]} ELSE {}
      [] sd.f = "dec" -> {[t |-> "dec", in |-> <<>>, a |-> sd.a]}

Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ \E x \in Expand(c.sd) : c' = x
    \/ c.t = "dec" /\ (
       \/ c.a = 1 /\ Len(c.in) < 4 /\ \E b \in Alpha : c' = [c EXCEPT !.in = Append(c.in, b)]
       \/ c.a = 2 /\ Len(c.in) < 2 /\ \E b \in 0..255 : c' = [c EXCEPT !.in = Append(c.in, b)]
       \/ c.a = 3 /\ Len(c.in) < 10 /\ \E b \in {128, 255} : c' = [c EXCEPT !.in = Append(c.in, b)]
       \/ c.a = 3 /\ Len(c.in) >= 5 /\ \E b \in {0, 1, 127} : c' = [c EXCEPT !.a = 4, !.in = Append(c.in, b)]
       \/ c.a = 4 /\ \E b \in {0, 255} : c' = [c EXCEPT !.a = 5, !.in = Append(c.in, b)])

Spec == Init /\ [][Next]_c

(* ---- the properties ---- *)

(* the encoding of v: the code agrees with the specification, has EncodedLen bytes (at most 9), decodes back to v
   with any rest after it, and every buffer size gives the right result *)
EncodeOK(v) ==
    LET e == Encode(v, 16)
    IN IF ~U!Lt(v, Limit)
       THEN /\ e.kind = "overflow"
            /\ \A cap \in 0..10 : Encode(v, cap).kind = "overflow"
       ELSE /\ e.kind = "ok"
            /\ Len(e.bytes) = EncodedLen(v) /\ Len(e.bytes) <= MaxLen                       \* EncodeLength
            /\ IsEnc(e.bytes) /\ ValueOf(e.bytes, 1) = v                                    \* Canonical
            /\ \A rest \in Rests : Decode(e.bytes \o rest) = [kind |-> "ok", v |-> v, n |-> Len(e.bytes)]
                                                                                            \* RoundTrip
            /\ \A cap \in 0..10 :                                                           \* EncodeInto
                 IF cap >= Len(e.bytes) THEN Encode(v, cap) = e
                 ELSE Encode(v, cap) = [kind |-> "small", needed |-> Len(e.bytes) - cap]
            /\ \A m \in 1..(Len(e.bytes) - 1) :                                             \* a cut encoding
                 Decode(Prefix(e.bytes, m)).kind = "truncated"

(* the decode of an input: an accepted prefix is exactly the encoding of the value, the value is below 2^63 and at
   most 9 bytes are used, and the error kinds are exactly the inputs that have no encoding as a prefix *)
DecodeOK(s) ==
    LET d == Decode(s)
        hasEnc == \E n \in 1..(IF Len(s) < MaxLen THEN Len(s) ELSE MaxLen) : IsEnc(Prefix(s, n))
        allCont == \A k \in 1..(IF Len(s) < MaxLen THEN Len(s) ELSE MaxLen) : s[k] >= 128
        nonMin == \E n \in 2..(IF Len(s) < MaxLen THEN Len(s) ELSE MaxLen) :
                      (\A k \in 1..(n - 1) : s[k] >= 128) /\ s[n] = 0
    IN /\ (d.kind = "ok") <=> hasEnc
       /\ d.kind = "ok" =>
            /\ U!Lt(d.v, Limit) /\ d.n <= MaxLen /\ d.n <= Len(s)                           \* DecodeBounds
            /\ IsEnc(Prefix(s, d.n)) /\ ValueOf(Prefix(s, d.n), 1) = d.v
            /\ Encode(d.v, 16) = [kind |-> "ok", bytes |-> Prefix(s, d.n)]                 \* Unique
       /\ (d.kind = "toolong") <=> (Len(s) >= MaxLen /\ allCont)
       /\ (d.kind = "truncated") <=> (Len(s) < MaxLen /\ allCont)
       /\ (d.kind = "nonminimal") <=> (~hasEnc /\ ~allCont /\ nonMin)
       /\ d.kind \in {"ok", "toolong", "truncated", "nonminimal"}

Inv == IF c.t \in {"root", "seed"} THEN TRUE ELSE IF c.t = "enc" THEN EncodeOK(c.v) ELSE DecodeOK(c.in)
=============================================================================
