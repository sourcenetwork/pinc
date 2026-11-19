----------------------------- MODULE PortMapAddr -----------------------------
(***************************************************************************)
(* Which addresses the port-mapping client trusts: pinc-portmap addr.rs    *)
(* (`is_shared`, `is_private`, `usable_host`, `external_ok`).              *)
(*                                                                         *)
(* The code is written on octets and 16-bit segments as the Rust code      *)
(* does: its own masks (`o[1] & 0xc0 == 64`, `s & 0xffc0 == 0xfe80`,       *)
(* `s & 0xfe00 == 0xfc00`), `to_canonical` (an IPv4-mapped IPv6 address,   *)
(* ::ffff:a.b.c.d, is the IPv4 address it maps) and the predicates of the  *)
(* core library (`is_private`, `is_loopback`, `is_multicast`,              *)
(* `is_broadcast`, `is_link_local`, `is_unspecified`), each as the core    *)
(* library defines it (a stated assumption).                               *)
(*                                                                         *)
(* The rule is stated apart from the code, as the documentation of         *)
(* addr.rs and client.rs gives it, by network prefix (InNet4, InNet6       *)
(* compare the leading bits by division, never by a mask):                 *)
(*   shared          100.64.0.0/10                                         *)
(*   private         10/8, 172.16/12, 192.168/16 (RFC 1918), 100.64/10     *)
(*   usable host     none of 0.0.0.0/32, 127/8, 224/4, 255.255.255.255/32, *)
(*                   169.254/16                                            *)
(*   external        a usable host that is not private; for IPv6 none of   *)
(*                   ::/128, ::1/128, ff00::/8, fe80::/10, fc00::/7, and   *)
(*                   an IPv4-mapped address judged as its IPv4 address     *)
(* (external_ok's list in its documentation omits broadcast, which the     *)
(* code refuses through usable_host and no internet peer can send to; the  *)
(* rule follows the code's composition and the report states the gap).    *)
(*                                                                         *)
(* Properties (Inv): SharedRule, PrivateRule, HostRule, ExternalRule, and  *)
(* MappedSame (a mapped address is judged exactly as its IPv4 address).    *)
(*                                                                         *)
(* Checked over the boundary sets of every class: first octets on both     *)
(* sides of each first-octet boundary (0, 1, 9 to 11, 99 to 101, 126 to    *)
(* 128, 168 to 173, 191 to 193, 223 to 225, 239, 240, 254, 255), second    *)
(* octets on both sides of each second-octet boundary (15, 16, 31, 32, 63, *)
(* 64, 127, 128, 167 to 169, 253 to 255, and 0), last octets 0, 1 and 255; *)
(* every one of these also as an IPv4-mapped IPv6 address; and IPv6        *)
(* addresses whose first segment is on both sides of each IPv6 boundary    *)
(* (fbff, fc00, fdff, fe00, fe7f, fe80, febf, fec0, feff, ff00, ffff, 0,   *)
(* 1, 2001) with five tails (all zero, ::1, the mapped prefix, all ones,   *)
(* the deprecated compatible form ::10.0.0.1, which is not mapped).        *)
(* 4929 distinct addresses; no TLC integer reaches 2^17.                   *)
(*                                                                         *)
(* PortMapAddr_mapped.cfg is a witness: a mapped address that the IPv6     *)
(* rules alone would accept is refused because its IPv4 address is         *)
(* private, so the canonical step decides cases of the domain.             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLE c

(* ---- arithmetic helpers ---- *)
\* x & y, bit by bit (TLA+ has no bitwise operator)
RECURSIVE BitAnd(_, _)
BitAnd(x, y) == IF x = 0 \/ y = 0 THEN 0 ELSE 2 * BitAnd(x \div 2, y \div 2) + (IF x % 2 = 1 /\ y % 2 = 1 THEN 1 ELSE 0)
MinI(a, b) == IF a <= b THEN a ELSE b
MaxI(a, b) == IF a >= b THEN a ELSE b

\* an address: [v |-> 4, o |-> <<4 octets>>] or [v |-> 6, s |-> <<8 segments>>]
V4(o) == [v |-> 4, o |-> o]
V6(s) == [v |-> 6, s |-> s]
\* Ipv4Addr::to_ipv6_mapped
Mapped(o) == V6(<<0, 0, 0, 0, 0, 65535, o[1] * 256 + o[2], o[3] * 256 + o[4]>>)

(* ---- the code ---- *)

\* the core library's Ipv4Addr predicates (a stated assumption: their definitions in core::net)
StdUnspecified4(o) == o = <<0, 0, 0, 0>>
StdLoopback4(o) == o[1] = 127
StdMulticast4(o) == o[1] >= 224 /\ o[1] <= 239
StdBroadcast4(o) == o = <<255, 255, 255, 255>>
StdLinkLocal4(o) == o[1] = 169 /\ o[2] = 254
StdPrivate4(o) == o[1] = 10 \/ (o[1] = 172 /\ o[2] >= 16 /\ o[2] <= 31) \/ (o[1] = 192 /\ o[2] = 168)

\* addr::is_shared: o[0] == 100 && o[1] & 0xc0 == 64
IsShared(o) == o[1] = 100 /\ BitAnd(o[2], 192) = 64
\* addr::is_private
IsPrivate(o) == StdPrivate4(o) \/ IsShared(o)
\* addr::usable_host
UsableHost(o) == ~(StdUnspecified4(o) \/ StdLoopback4(o) \/ StdMulticast4(o) \/ StdBroadcast4(o) \/ StdLinkLocal4(o))

\* Ipv6Addr::to_ipv4_mapped: ::ffff:a.b.c.d
IsMappedSegs(s) == s[1] = 0 /\ s[2] = 0 /\ s[3] = 0 /\ s[4] = 0 /\ s[5] = 0 /\ s[6] = 65535
\* IpAddr::to_canonical
Canonical(a) ==
    IF a.v = 6 /\ IsMappedSegs(a.s)
    THEN V4(<<a.s[7] \div 256, a.s[7] % 256, a.s[8] \div 256, a.s[8] % 256>>)
    ELSE a
\* the IPv6 arm of addr::external_ok, after to_canonical
V6Code(s) ==
    ~(s = <<0, 0, 0, 0, 0, 0, 0, 0>>                       \* is_unspecified
      \/ s = <<0, 0, 0, 0, 0, 0, 0, 1>>                    \* is_loopback
      \/ BitAnd(s[1], 65280) = 65280                       \* is_multicast: segment 0 & 0xff00 == 0xff00
      \/ BitAnd(s[1], 65472) = 65152                       \* s & 0xffc0 == 0xfe80
      \/ BitAnd(s[1], 65024) = 64512)                      \* s & 0xfe00 == 0xfc00
\* addr::external_ok
ExternalOk(a) ==
    LET k == Canonical(a)
    IN IF k.v = 4 THEN UsableHost(k.o) /\ ~IsPrivate(k.o) ELSE V6Code(k.s)

(* ---- the rule, by prefix ---- *)

\* the first len bits of o equal those of net (octets)
InNet4(o, net, len) ==
    \A i \in 1..4 : LET b == MinI(8, MaxI(0, len - 8 * (i - 1))) IN o[i] \div 2 ^ (8 - b) = net[i] \div 2 ^ (8 - b)
\* the same on 16-bit segments
InNet6(s, net, len) ==
    \A i \in 1..8 : LET b == MinI(16, MaxI(0, len - 16 * (i - 1))) IN s[i] \div 2 ^ (16 - b) = net[i] \div 2 ^ (16 - b)

RuleShared(o) == InNet4(o, <<100, 64, 0, 0>>, 10)
RulePrivate(o) ==
    \/ InNet4(o, <<10, 0, 0, 0>>, 8) \/ InNet4(o, <<172, 16, 0, 0>>, 12) \/ InNet4(o, <<192, 168, 0, 0>>, 16)
    \/ RuleShared(o)
RuleHost(o) ==
    ~(\/ InNet4(o, <<0, 0, 0, 0>>, 32) \/ InNet4(o, <<127, 0, 0, 0>>, 8) \/ InNet4(o, <<224, 0, 0, 0>>, 4)
      \/ InNet4(o, <<255, 255, 255, 255>>, 32) \/ InNet4(o, <<169, 254, 0, 0>>, 16))
Z6 == <<0, 0, 0, 0, 0, 0, 0, 0>>
RuleV6(s) ==
    ~(\/ InNet6(s, Z6, 128) \/ InNet6(s, <<0, 0, 0, 0, 0, 0, 0, 1>>, 128)
      \/ InNet6(s, <<65280, 0, 0, 0, 0, 0, 0, 0>>, 8)       \* ff00::/8
      \/ InNet6(s, <<65152, 0, 0, 0, 0, 0, 0, 0>>, 10)      \* fe80::/10
      \/ InNet6(s, <<64512, 0, 0, 0, 0, 0, 0, 0>>, 7))      \* fc00::/7
RuleMapped(s) == InNet6(s, <<0, 0, 0, 0, 0, 65535, 0, 0>>, 96)
RuleExternal(a) ==
    IF a.v = 4 THEN RuleHost(a.o) /\ ~RulePrivate(a.o)
    ELSE IF RuleMapped(a.s)
         THEN LET o == <<a.s[7] \div 256, a.s[7] % 256, a.s[8] \div 256, a.s[8] % 256>>
              IN RuleHost(o) /\ ~RulePrivate(o)
         ELSE RuleV6(a.s)

(* ---- the domain ---- *)
O1 == {0, 1, 9, 10, 11, 99, 100, 101, 126, 127, 128, 168, 169, 170, 171, 172, 173, 191, 192, 193, 223, 224, 225,
       239, 240, 254, 255}
O2 == {0, 15, 16, 31, 32, 63, 64, 127, 128, 167, 168, 169, 253, 254, 255}
O3 == {0, 255}
O4 == {0, 1, 255}
S1 == {0, 1, 8193, 64511, 64512, 65023, 65024, 65151, 65152, 65215, 65216, 65279, 65280, 65535}
Tails == {<<0, 0, 0, 0, 0, 0, 0>>, <<0, 0, 0, 0, 0, 0, 1>>, <<0, 0, 0, 0, 65535, 0, 0>>,
          <<65535, 65535, 65535, 65535, 65535, 65535, 65535>>, <<0, 0, 0, 0, 0, 2560, 1>>}

Quads == {<<a, b, x, d>> : a \in O1, b \in O2, x \in O3, d \in O4}
Addrs == {V4(o) : o \in Quads} \cup {Mapped(o) : o \in Quads} \cup {V6(<<h>> \o t) : h \in S1, t \in Tails}

(* the root state has one successor per address *)
Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E a \in Addrs : c' = [t |-> "case", a |-> a]
Spec == Init /\ [][Next]_c

(* ---- the properties ---- *)
SharedRule(a) == a.v = 4 => IsShared(a.o) = RuleShared(a.o)
PrivateRule(a) == a.v = 4 => IsPrivate(a.o) = RulePrivate(a.o)
HostRule(a) == a.v = 4 => UsableHost(a.o) = RuleHost(a.o)
ExternalRule(a) == ExternalOk(a) = RuleExternal(a)
MappedSame(a) == (a.v = 6 /\ IsMappedSegs(a.s)) => ExternalOk(a) = ExternalOk(Canonical(a))

Inv == c.t = "case" => (SharedRule(c.a) /\ PrivateRule(c.a) /\ HostRule(c.a) /\ ExternalRule(c.a) /\ MappedSame(c.a))

\* Witness (PortMapAddr_mapped.cfg, which TLC must violate): no mapped address the IPv6 rules alone accept is refused.
NoMappedRefused == c.t = "case" => ~(c.a.v = 6 /\ IsMappedSegs(c.a.s) /\ V6Code(c.a.s) /\ ~ExternalOk(c.a))
=============================================================================
