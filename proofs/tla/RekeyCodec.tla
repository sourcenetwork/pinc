---------------------------- MODULE RekeyCodec ----------------------------
(***************************************************************************)
(* The REKEY body of vinc-security keyroll.rs (Rekey::write, encode and    *)
(* decode): kind(1) (0 request, 1 answer), share(32), and for an answer a  *)
(* varint switch_pn. The varint is the Encode and Decode of Varint.tla on  *)
(* the machine words of U64.tla.                                           *)
(*                                                                         *)
(* RkEncode refuses a switch number of 2^63 or more (VarintOverflow);      *)
(* RkDecode is strict: an unknown kind, a short body and a trailing byte   *)
(* are refused, as is a bad varint (reported "varint", which the trace     *)
(* folds with "short" into one class). A request is 33 bytes and an        *)
(* answer 34 to 42.                                                        *)
(*                                                                         *)
(* Checked (RekeyCodec.cfg) for every switch number boundary of every      *)
(* width (2^j - 1, 2^j, 2^j + 1 for j in 0..64), three shares, both kinds: *)
(*   RoundTrip   decode (encode r) = r, and the lengths are 33 and 34..42; *)
(*   Unique      an accepted body re-encodes to itself, so each message    *)
(*               has exactly one accepted body;                            *)
(*   Strict      every cut of the body, a trailing byte, an unknown kind   *)
(*               and a kind changed to the other are refused.              *)
(* Lean counterpart: Vinc/KeyRoll.lean (decode_encode, encode_decode,      *)
(* encode_injective, the refusal theorems).                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

V == INSTANCE Varint WITH SmallMax <- 0, c <- 0
U == INSTANCE U64

RkEncode(r) ==
    IF r.ans /\ ~U!Lt(r.spn, V!Limit) THEN [err |-> "overflow"]
    ELSE [err |-> "ok",
          bytes |-> <<IF r.ans THEN 1 ELSE 0>> \o r.sh \o (IF r.ans THEN V!Encode(r.spn, 16).bytes ELSE <<>>)]

RkDecode(buf) ==
    IF Len(buf) = 0 THEN [err |-> "short"]
    ELSE IF buf[1] > 1 THEN [err |-> "kind"]
    ELSE IF Len(buf) - 1 < 32 THEN [err |-> "short"]
    ELSE LET sh == SubSeq(buf, 2, 33)
             after == SubSeq(buf, 34, Len(buf))
         IN IF buf[1] = 1
            THEN LET d == V!Decode(after)
                 IN IF d.kind # "ok" THEN [err |-> "varint"]
                    ELSE IF d.n # Len(after) THEN [err |-> "trailing"]
                    ELSE [err |-> "ok", ans |-> TRUE, sh |-> sh, spn |-> d.v]
            ELSE IF Len(after) # 0 THEN [err |-> "trailing"]
            ELSE [err |-> "ok", ans |-> FALSE, sh |-> sh, spn |-> U!Zero]

(* ---- the checked domain ---- *)
Shares == {[i \in 1..32 |-> 0], [i \in 1..32 |-> 255], [i \in 1..32 |-> i]}
(* the widths around every varint length boundary (2^(7k) - 1, 2^(7k), 2^(7k) + 1), 2^63 and 2^64 included *)
Widths == {0, 1, 2, 6, 7, 8, 13, 14, 15, 20, 21, 22, 27, 28, 29, 34, 35, 36, 41, 42, 43, 48, 49, 50, 55, 56, 57, 62, 63, 64}
Edges == UNION {{V!EdgeVal(j, d) : d \in {x \in -1..1 : V!EdgeOK(j, x)}} : j \in Widths}

VARIABLES ans, sh, spn
vars == <<ans, sh, spn>>

Init == ans \in BOOLEAN /\ sh \in Shares /\ spn \in Edges
Spec == Init /\ [][UNCHANGED vars]_vars

Msg == [ans |-> ans, sh |-> sh, spn |-> IF ans THEN spn ELSE U!Zero]

Cut(b) == {SubSeq(b, 1, k) : k \in 0..(Len(b) - 1)}
Extras(b) == {b \o <<x>> : x \in {0, 1, 128, 255}}
Kinds(b) == {<<k>> \o SubSeq(b, 2, Len(b)) : k \in {2, 3, 255}}
Flip(b) == <<1 - b[1]>> \o SubSeq(b, 2, Len(b))

RoundTrip ==
    LET e == RkEncode(Msg)
    IN IF ans /\ ~U!Lt(spn, V!Limit) THEN e.err = "overflow"
       ELSE /\ e.err = "ok"
            /\ Len(e.bytes) = (IF ans THEN 33 + V!EncodedLen(spn) ELSE 33)
            /\ ans => (Len(e.bytes) >= 34 /\ Len(e.bytes) <= 42)
            /\ RkDecode(e.bytes) = [err |-> "ok", ans |-> ans, sh |-> sh, spn |-> Msg.spn]

Unique ==
    LET e == RkEncode(Msg)
        cands == IF e.err = "ok" THEN Cut(e.bytes) \cup Extras(e.bytes) \cup Kinds(e.bytes) \cup {Flip(e.bytes), e.bytes}
                 ELSE {}
    IN \A b \in cands :
         LET d == RkDecode(b)
         IN d.err = "ok" => RkEncode([ans |-> d.ans, sh |-> d.sh, spn |-> d.spn]) = [err |-> "ok", bytes |-> b]

Strict ==
    LET e == RkEncode(Msg)
    IN e.err = "ok" =>
        /\ \A b \in Cut(e.bytes) : RkDecode(b).err \in {"short", "varint"}
        /\ \A b \in Extras(e.bytes) : RkDecode(b).err = "trailing"
        /\ \A b \in Kinds(e.bytes) : RkDecode(b).err = "kind"
        /\ RkDecode(Flip(e.bytes)).err = (IF ans THEN "trailing" ELSE "varint")
=============================================================================
