----------------------------- MODULE CryptoKdf -----------------------------
(***************************************************************************)
(* The key derivation of vinc-crypto (kdf.rs) and every call site of the   *)
(* BLAKE3 derive_key primitive.                                            *)
(*                                                                         *)
(* The primitive receives a Call: the mode, the label (context string) and *)
(* the material. expand(prk, label, ctx) feeds prk || ctx under label;     *)
(* NodeId::from_public feeds tag || public key under NODE_ID; the hybrid   *)
(* digest feeds the message under HYBRID_SIGNATURE; a labelled Transcript  *)
(* feeds its length-prefixed fields under its label. extract(salt, ikm) is *)
(* keyed_hash, the other mode of the primitive.                            *)
(*                                                                         *)
(* Checked, exhaustively over the declared small domains (prk of 2 bytes   *)
(* of a 2-letter alphabet stands for 32 bytes: only the common length of   *)
(* all secrets matters):                                                   *)
(*   RegistryOK        the 31 labels that reach the primitive (23 of       *)
(*                     vinc-security, 2 of vinc-crypto, 6 of vinc-dtn) are *)
(*                     pairwise distinct, start with the prefix, are ASCII *)
(*                     and are longer than it                              *)
(*   ExpandInjective   the call of expand determines secret, label, ctx    *)
(*   AmbiguousWithoutLength  the same without the common length is false   *)
(*   ExtractInjective, NodeIdInjective, HybridInjective                    *)
(*   SitesSeparated    calls of different sites differ                     *)
(*   TicketRoles       the one label with two roles (ticket) gives         *)
(*                     materials of 24 and 64 bytes                        *)
(*   OutLength, OutPrefix  the output has the length asked for and a       *)
(*                     shorter output is a prefix of a longer one          *)
(*   ChainInjective    a chain of derivations is injective in its start    *)
(*                     secret (with a perfect primitive: a derived secret  *)
(*                     is the term of its call)                            *)
(* TraceCrypto.tla checks the recorded calls of the code against these     *)
(* operators. Lean counterpart: proofs/lean/Vinc/CryptoKdf.lean            *)
(* (expandCall_injective, registry_bytes_nodup, sites_separated,           *)
(* ticket_roles_separate, out_prefix, chain_injective).                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

L == INSTANCE Labels

NodeIdLabel == "VINC 2026 v1 node id"
HybridLabel == "VINC 2026 v1 hybrid signature"
CryptoLabels == <<NodeIdLabel, HybridLabel>>
DtnLabels == <<"VINC 2026 v1 dtn chain", "VINC 2026 v1 dtn transcript", "VINC 2026 v1 dtn slice key",
               "VINC 2026 v1 dtn bundle id", "VINC 2026 v1 dtn head", "VINC 2026 v1 dtn custody ack">>
Registry == L!AllLabels \o CryptoLabels \o DtnLabels
RIdx == 1..Len(Registry)

Call(mode, label, material) == [mode |-> mode, label |-> label, material |-> material]
ExpandCall(prk, label, ctx) == Call("derive", label, prk \o ctx)
ExtractCall(salt, ikm) == Call("keyed", salt, ikm)
NodeIdCall(tag, pk) == Call("derive", NodeIdLabel, <<tag>> \o pk)
HybridCall(msg) == Call("derive", HybridLabel, msg)
TranscriptCall(label, enc) == Call("derive", label, enc)

(* the extendable output: byte i of the output of a call is a function of the call and i (a perfect primitive) *)
Out(c, n) == [i \in 1..n |-> <<c, i>>]

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

Bits == {0, 1}
Prks == {<<a, b>> : a \in Bits, b \in Bits}
Strs(n) == UNION {[1..k -> Bits] : k \in 0..n}
Ctxs == Strs(2)
SecLabels == {L!AllLabels[i] : i \in 1..Len(L!AllLabels)}
Lbls == {NodeIdLabel, HybridLabel, "VINC 2026 v1 packet key", "VINC 2026 v1 dtn slice key", "VINC 2026 v1 ticket"}

Starts(s, p) == Len(s) > Len(p) /\ SubSeq(s, 1, Len(p)) = p

RegistryOK ==
    /\ Len(Registry) = 31
    /\ \A i, j \in RIdx : Registry[i] = Registry[j] => i = j
    /\ \A i \in RIdx : Starts(Registry[i], L!Prefix)
    /\ \A i \in RIdx : \A k \in 1..Len(Registry[i]) : SubSeq(Registry[i], k, k) \in L!Chars

ExpandInjective ==
    \A p, q \in Prks : \A l, m \in Lbls : \A c, d \in Ctxs :
        ExpandCall(p, l, c) = ExpandCall(q, m, d) => (p = q /\ l = m /\ c = d)

AmbiguousWithoutLength ==
    ExpandCall(<<1>>, "VINC 2026 v1 packet key", <<0, 1>>) = ExpandCall(<<1, 0>>, "VINC 2026 v1 packet key", <<1>>)

ExtractInjective ==
    \A p, q \in Prks : \A c, d \in Ctxs : ExtractCall(p, c) = ExtractCall(q, d) => (p = q /\ c = d)

Pks == Strs(2)
NodeIdInjective ==
    \A t, u \in 1..4 : \A p, q \in Pks : NodeIdCall(t, p) = NodeIdCall(u, q) => (t = u /\ p = q)

HybridInjective == \A m, n \in Strs(3) : HybridCall(m) = HybridCall(n) => m = n

(* one call of each site, with every other site's labels excluded from the label set of the site *)
ExpandLabels == {l \in Lbls : l # NodeIdLabel /\ l # HybridLabel}
SitesSeparated ==
    /\ \A t \in 1..4 : \A p \in Pks : \A m \in Strs(3) : NodeIdCall(t, p) # HybridCall(m)
    /\ \A t \in 1..4 : \A p \in Pks : \A q \in Prks : \A l \in ExpandLabels : \A c \in Ctxs :
           NodeIdCall(t, p) # ExpandCall(q, l, c) /\ HybridCall(p) # ExpandCall(q, l, c)
    /\ \A p \in Prks : \A c \in Ctxs : \A m \in Strs(3) : ExpandCall(p, NodeIdLabel, c) # HybridCall(m)
    /\ \A p \in Prks : \A c \in Ctxs : \A d \in Ctxs : \A l \in ExpandLabels : \A m \in ExpandLabels :
           l # m => ExpandCall(p, l, c) # ExpandCall(p, m, d)

(* the roles of the labels, read from the call sites: only the ticket label is used both as the label of a
   transcript (the ticket context: a 16-byte id and a 6-byte credit record, each with a 1-byte length) and as the
   label of an expand (a 32-byte secret and a 32-byte context hash) *)
TicketTranscriptLen == (1 + 16) + (1 + 6)
TicketExpandLen == 32 + 32
TicketRoles == TicketTranscriptLen # TicketExpandLen

OutLength == \A c \in {ExpandCall(p, "VINC 2026 v1 packet key", <<>>) : p \in Prks} : \A n \in 0..4 : Len(Out(c, n)) = n
OutPrefix == \A c \in {ExpandCall(p, "VINC 2026 v1 packet key", <<>>) : p \in Prks} : \A n, m \in 0..4 :
    n <= m => Out(c, m) = Out(c, n) \o [i \in 1..(m - n) |-> <<c, n + i>>]

(* a derived secret, as the term of its call (a perfect primitive); the chain applies a list of (label, ctx) *)
Derive(s, l, c) == [call |-> ExpandCall(<<s>>, l, c)]
Steps == {<<l, c>> : l \in {"VINC 2026 v1 packet key", "VINC 2026 v1 ticket"}, c \in Strs(1)}
ChainOf(s, a, b) == Derive(Derive(s, a[1], a[2]), b[1], b[2])
ChainInjective ==
    \A s, t \in {"s0", "s1", "s2"} : \A a, b \in Steps :
        ChainOf(s, a, b) = ChainOf(t, a, b) => s = t
=============================================================================
