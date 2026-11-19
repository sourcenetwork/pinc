------------------------------ MODULE FacadeState ------------------------------
(***************************************************************************)
(* What survives a restart, as the facade frames it: crates/pinc/src/      *)
(* engine/state.rs around the core's own state (pinc-core state.rs), with  *)
(* the operators of FacadeStateOps.tla at scaled widths (node 1 byte, IPv4 *)
(* 1, IPv6 2, port 1, core_len 1, count 1, record_seq 1; BOOK_MAX 2,       *)
(* ADDRS_MAX 2; the real ones are 32, 4, 16, 2, 4, 2, 8, 4096 and 8).      *)
(*                                                                         *)
(* Composition: the core's part is CoreStateOps.tla itself, not a stand-in: *)
(* the core bytes a live state exports are CS!Enc of its tables, and the   *)
(* core's restore is CS!Restore. CoreState.tla checks that the core's      *)
(* restore accepts exactly what its parse reads and that a refusal leaves  *)
(* its tables as they were (AtomicInv, Strict); here the facade's layer is *)
(* checked on top of it.                                                   *)
(*                                                                         *)
(* Cases (a machine whose root has one successor per input and live        *)
(* state): sources (an empty one, one with a core round trip, a full book, *)
(* core bytes the core refuses, a node twice, an address twice, an entry   *)
(* with no address, a new node, and two past the bounds: 3 nodes, 3        *)
(* addresses of one node) encoded in versions 1 and 2; every cut; one byte *)
(* appended; every byte changed to 0, 255 and its successor; the first     *)
(* entry's algorithm and family tags set to 0, 5 and 255; each restored    *)
(* into three live states (empty, one node with a core round trip, a full  *)
(* book with a node at ADDRS_MAX).                                         *)
(*                                                                         *)
(* Properties (the module doc, lines 9-15, and `restore_state`'s doc):     *)
(*   RT        the export of a live state parses back as it               *)
(*   Strict    a cut, an appended byte, a count past BOOK_MAX, an n past   *)
(*             ADDRS_MAX, an unknown algorithm or family tag is refused,   *)
(*             and a well-formed source is accepted                       *)
(*   Canon     accepted bytes are the encoding of what they read          *)
(*   Atomic    restore accepts exactly when the framing parses and the    *)
(*             core accepts its bytes, and a refusal changes nothing      *)
(*   V1        a version-1 state leaves the record number as it is       *)
(*   SeqRises  the record number never falls, and is the larger of the    *)
(*             two after a version-2 restore                              *)
(*   Bounded   the book never holds more than BOOK_MAX nodes, ADDRS_MAX   *)
(*             addresses of one, an address twice or an empty entry       *)
(*   Keep      a restore never drops what the book held, and adds only    *)
(*             what the input holds                                       *)
(*   Merge     restoring a canonical state into an empty endpoint gives   *)
(*             exactly the book and record number written                 *)
(* FacadeState_count.cfg checks AddrDoc, the doc of `Restored::addresses`  *)
(* (state.rs 47: "Nodes whose addresses went into the address book"): it   *)
(* FAILS on today's code, which counts every node of the input (line 168): *)
(* an entry with no address, a node twice, a node the full book refused    *)
(* (finding F4). FacadeState_full.cfg is a witness that a full book        *)
(* refuses an input's address (NoneRefused fails).                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

F == INSTANCE FacadeStateOps WITH NB <- 1, IP4 <- 1, IP6 <- 2, PORT <- 1, CLEN <- 1, CNT <- 1, SEQ <- 1,
                                  BOOKMAX <- 2, ADDRSMAX <- 2
CS == INSTANCE CoreStateOps WITH CT <- 2, KR <- 2, EK <- 2, LAZY <- FALSE, LAXTAIL <- FALSE

NOW == 100
CoreE(c) == CS!Enc(c)
CoreR(c, b) == CS!Restore(c, b, NOW)

\* the core's tables: empty, and one round trip
CEmpty == [tk |-> <<>>, kr |-> <<>>, ek |-> <<>>]
CKr == [tk |-> <<>>, kr |-> <<[alg |-> 1, node |-> [j \in 1..32 |-> j], rtt |-> CS!BEr(5, 8)]>>, ek |-> <<>>]
CB == CS!Enc(CEmpty)

N1 == [alg |-> 1, bytes |-> <<7>>]
N2 == [alg |-> 2, bytes |-> <<8>>]
N3 == [alg |-> 4, bytes |-> <<9>>]
A4 == <<4, 10, 20>>
A6 == <<6, 1, 2, 30>>
B4 == <<4, 11, 21>>

L0 == [core |-> CEmpty, book |-> <<>>, seq |-> <<0>>]
L1 == [core |-> CKr, book |-> <<<<N1, <<A4>>>>>>, seq |-> <<5>>]
L2 == [core |-> CEmpty, book |-> <<<<N1, <<A4, A6>>>>, <<N2, <<A6>>>>>>, seq |-> <<9>>]
Lives == {L0, L1, L2}

\* sources: the core's bytes, a book, a record number; ok: within the bounds, so the framing must accept it
S(core, book, seq, ok) == [core |-> core, book |-> book, seq |-> <<seq>>, ok |-> ok]
Src == {S(CB, <<>>, 0, TRUE),
        S(CS!Enc(CKr), <<<<N1, <<A4>>>>>>, 5, TRUE),
        S(CB, <<<<N1, <<A4, A6>>>>, <<N2, <<A6>>>>>>, 9, TRUE),
        S(SubSeq(CB, 1, Len(CB) - 1), <<<<N1, <<B4>>>>>>, 3, TRUE),
        S(CB, <<<<N1, <<A4>>>>, <<N1, <<B4>>>>>>, 1, TRUE),
        S(CB, <<<<N2, <<A4, A4>>>>>>, 200, TRUE),
        S(CB, <<<<N3, <<>>>>, <<N1, <<B4>>>>>>, 7, TRUE),
        S(CB, <<<<N3, <<B4>>>>>>, 2, TRUE),
        S(CB, <<<<N1, <<A4>>>>, <<N2, <<A6>>>>, <<N3, <<B4>>>>>>, 1, FALSE),
        S(CB, <<<<N1, <<A4, A6, B4>>>>>>, 1, FALSE)}

Encs == {[bs |-> F!Enc(v, s.core, s.book, s.seq), src |-> s, ver |-> v] : s \in Src, v \in {1, 2}}
Mut(bs, p, v) == [bs EXCEPT ![p] = v]
Vals(c) == {0, 255, (c + 1) % 256} \ {c}
\* the first entry's algorithm tag and first address's family tag
AlgAt(e) == 1 + 1 + Len(e.src.core) + 1 + 1
FamAt(e) == AlgAt(e) + 1 + 1 + 1
Tagged == {e \in Encs : e.src.ok /\ e.src.book # <<>> /\ e.src.book[1][2] # <<>>}

In(e, bs, want, enc) == [bs |-> bs, want |-> want, src |-> e.src, ver |-> e.ver, enc |-> enc]
Inputs ==
    {In(e, e.bs, IF e.src.ok THEN "yes" ELSE "no", TRUE) : e \in Encs}
    \cup UNION {{In(e, SubSeq(e.bs, 1, k), "no", FALSE) : k \in 0..(Len(e.bs) - 1)} : e \in Encs}
    \cup {In(e, e.bs \o <<0>>, "no", FALSE) : e \in Encs}
    \cup UNION {UNION {{In(e, Mut(e.bs, p, v), "any", FALSE) : v \in Vals(e.bs[p])} : p \in 1..Len(e.bs)} : e \in Encs}
    \cup {In(e, Mut(e.bs, AlgAt(e), v), "no", FALSE) : e \in Tagged, v \in {0, 5, 255}}
    \cup {In(e, Mut(e.bs, FamAt(e), v), "no", FALSE) : e \in Tagged, v \in {0, 5, 255}}

VARIABLE cs
Init == cs = [k |-> "root"]
Next == cs.k = "root" /\ \E i \in Inputs, L \in Lives : cs' = [k |-> "case", in |-> i, live |-> L]
Spec == Init /\ [][Next]_cs

P == F!Parse(cs.in.bs)
R == F!Restore(cs.live, cs.in.bs, CoreR)

RT == cs.k = "root" =>
    \A L \in Lives : F!Parse(F!Export(L, CoreE)) = [ok |-> TRUE, ver |-> 2, core |-> CS!Enc(L.core), book |-> L.book,
                                                     seq |-> L.seq]
Strict == cs.k = "case" /\ cs.in.want # "any" => P.ok = (cs.in.want = "yes")
Canon == cs.k = "case" => (P.ok => F!Enc(P.ver, P.core, P.book, P.seq) = cs.in.bs)
Atomic == cs.k = "case" =>
    /\ R.ok = (P.ok /\ CS!Parse(P.core).ok)
    /\ ~R.ok => R.live = cs.live
V1 == cs.k = "case" /\ R.ok /\ P.ver = 1 => R.live.seq = cs.live.seq
SeqRises == cs.k = "case" =>
    /\ F!LexLe(cs.live.seq, R.live.seq)
    /\ R.ok /\ P.ver = 2 => F!LexLe(P.seq, R.live.seq) /\ R.live.seq \in {cs.live.seq, P.seq}
Bounded == cs.k = "case" =>
    LET b == R.live.book
    IN /\ Len(b) <= 2
       /\ \A j, k \in 1..Len(b) : j # k => b[j][1] # b[k][1]
       /\ \A k \in 1..Len(b) : /\ 1 <= Len(b[k][2]) /\ Len(b[k][2]) <= 2
                               /\ \A x, y \in 1..Len(b[k][2]) : x # y => b[k][2][x] # b[k][2][y]
Keep == cs.k = "case" /\ R.ok =>
    /\ F!Pairs(cs.live.book) \subseteq F!Pairs(R.live.book)
    /\ F!Pairs(R.live.book) \subseteq F!Pairs(cs.live.book) \cup F!Pairs(P.book)
Canonical(b) == /\ Len(b) <= 2
                /\ \A j, k \in 1..Len(b) : j # k => b[j][1] # b[k][1]
                /\ \A k \in 1..Len(b) : /\ 1 <= Len(b[k][2]) /\ Len(b[k][2]) <= 2
                                        /\ \A x, y \in 1..Len(b[k][2]) : x # y => b[k][2][x] # b[k][2][y]
Merge == cs.k = "case" /\ cs.in.enc /\ cs.live = L0 /\ R.ok /\ Canonical(cs.in.src.book) =>
    /\ R.live.book = cs.in.src.book
    /\ R.live.seq = (IF cs.in.ver = 2 THEN cs.in.src.seq ELSE L0.seq)
    /\ R.live.core = CS!Restore(CEmpty, cs.in.src.core, NOW).live

\* finding F4: the documented count, nodes of the input with an address in the book after
AddrDoc == cs.k = "case" /\ R.ok =>
    R.res[4] = Cardinality({e[1] : e \in {x \in F!Range(P.book) : \E j \in 1..Len(x[2]) :
                                                              <<x[1], x[2][j]>> \in F!Pairs(R.live.book)}})
\* witness: some input's address is refused by the bounds
NoneRefused == cs.k = "case" /\ R.ok => F!Pairs(P.book) \subseteq F!Pairs(R.live.book)
=============================================================================
