----------------------------- MODULE FacadeAddrOps -----------------------------
(***************************************************************************)
(* Node ids as text and a node's address as a ticket, as the code computes *)
(* them: crates/pinc/src/addr.rs `node_to_string`, `is_lower_hex`,         *)
(* `node_from_str`, `NodeAddr::with_direct`, `with_relay`, `ticket`,       *)
(* `parse`. Text is a sequence of byte codes. A node id is [alg |-> tag    *)
(* 1..4, bytes |-> NB bytes]; pinc-crypto identity.rs `from_tag` knows     *)
(* tags 1..4 and 1 is Ed25519, which prints without a tag and is refused   *)
(* with one (one text per id). A socket address is                         *)
(* [txt |-> its Display text, flow |-> its IPv6 flowinfo] (0 for IPv4).    *)
(* The core library's `SocketAddr` parse is an argument: a function cp     *)
(* from the texts it accepts to the address it gives; any other text is    *)
(* refused. NB is 1 in the model check and 32 in the trace check.          *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANT NB

Dot == 46
At == 64
Comma == 44
Sep == <<58, 47, 47>>   \* "://"

\* lowercase hex digits and their values
HexChar(d) == IF d < 10 THEN 48 + d ELSE 87 + d
IsLowerHexChar(c) == c \in 48..57 \/ c \in 97..102
HexVal(c) == IF c \in 48..57 THEN c - 48 ELSE c - 87
Hex2(v) == <<HexChar(v \div 16), HexChar(v % 16)>>
IsLowerHex(s, n) == Len(s) = n /\ \A k \in 1..Len(s) : IsLowerHexChar(s[k])

\* the first position of c in s, 0 when none (`split_once`)
First(s, c) == IF \E k \in 1..Len(s) : s[k] = c
               THEN CHOOSE k \in 1..Len(s) : s[k] = c /\ \A j \in 1..(k - 1) : s[j] # c
               ELSE 0
Before(s, k) == SubSeq(s, 1, k - 1)
After(s, k) == SubSeq(s, k + 1, Len(s))
Has(s, c) == First(s, c) > 0
Contains(s, t) == Len(t) <= Len(s) /\ \E k \in 0..(Len(s) - Len(t)) : SubSeq(s, k + 1, k + Len(t)) = t

\* str::split(c): every piece, an empty one included
RECURSIVE Split(_, _)
Split(s, c) == IF First(s, c) = 0 THEN <<s>> ELSE <<Before(s, First(s, c))>> \o Split(After(s, First(s, c)), c)
\* [a, b, ...].join(c)
RECURSIVE Join(_, _)
Join(xs, c) == IF xs = <<>> THEN <<>>
               ELSE IF Len(xs) = 1 THEN xs[1]
               ELSE xs[1] \o <<c>> \o Join(Tail(xs), c)

\* node_to_string
RECURSIVE HexBytes(_)
HexBytes(bs) == IF bs = <<>> THEN <<>> ELSE Hex2(Head(bs)) \o HexBytes(Tail(bs))
NodeToString(id) == (IF id.alg = 1 THEN <<>> ELSE Hex2(id.alg) \o <<Dot>>) \o HexBytes(id.bytes)

\* node_from_str: [ok, v]
Err == [ok |-> FALSE, v |-> [alg |-> 0, bytes |-> <<>>]]
Bytes(hex) == [k \in 1..NB |-> 16 * HexVal(hex[2 * k - 1]) + HexVal(hex[2 * k])]
Id(alg, hex) == IF IsLowerHex(hex, 2 * NB) THEN [ok |-> TRUE, v |-> [alg |-> alg, bytes |-> Bytes(hex)]] ELSE Err
NodeFromStr(s) ==
    LET k == First(s, Dot)
    IN IF k > 0
       THEN LET tag == Before(s, k)
            IN IF ~IsLowerHex(tag, 2) THEN Err
               ELSE LET t == 16 * HexVal(tag[1]) + HexVal(tag[2])
                    \* a known tag other than Ed25519's: "01." is refused (an Ed25519 id is written without a tag)
                    IN IF t \in 2..4 THEN Id(t, After(s, k)) ELSE Err
       ELSE Id(1, s)

\* NodeAddr::with_direct(addr): an IPv6 flow label is dropped (the text form has none)
WithDirect(a) == [a EXCEPT !.flow = 0]

\* NodeAddr::with_relay(url) accepts the url exactly when it is non-empty, has "://" and no ','
RelayOK(u) == u # <<>> /\ Contains(u, Sep) /\ ~Has(u, Comma)

\* NodeAddr::ticket of [node, direct, relays]
Items(v) == [k \in 1..Len(v.direct) |-> v.direct[k].txt] \o v.relays
Ticket(v) == NodeToString(v.node) \o (IF Items(v) = <<>> THEN <<>> ELSE <<At>> \o Join(Items(v), Comma))

\* NodeAddr::parse with the core library's parse cp
PErr == [ok |-> FALSE, v |-> [node |-> [alg |-> 0, bytes |-> <<>>], direct |-> <<>>, relays |-> <<>>]]
RECURSIVE Fill(_, _, _)
Fill(r, items, cp) ==
    IF items = <<>> \/ ~r.ok THEN r
    ELSE LET it == Head(items)
         IN IF it = <<>> THEN Fill(r, Tail(items), cp)
            ELSE IF Contains(it, Sep) THEN Fill([r EXCEPT !.v.relays = Append(@, it)], Tail(items), cp)
            ELSE IF it \in DOMAIN cp THEN Fill([r EXCEPT !.v.direct = Append(@, cp[it])], Tail(items), cp)
            ELSE PErr
Parse(s, cp) ==
    LET k == First(s, At)
        id == IF k > 0 THEN Before(s, k) ELSE s
        rest == IF k > 0 THEN After(s, k) ELSE <<>>
        n == NodeFromStr(id)
    IN IF ~n.ok THEN PErr
       ELSE Fill([ok |-> TRUE, v |-> [node |-> n.v, direct |-> <<>>, relays |-> <<>>]], Split(rest, Comma), cp)
=============================================================================
