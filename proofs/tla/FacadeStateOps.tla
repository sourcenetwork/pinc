---------------------------- MODULE FacadeStateOps ----------------------------
(***************************************************************************)
(* The framing of the endpoint's saved state as the facade writes and      *)
(* reads it: crates/pinc/src/engine/state.rs `export_state` (131-158),     *)
(* `parse` (98-127), `restore_state` (161-180), and the address book's     *)
(* `add_address` (engine/ops.rs 464-478). Bytes are sequences of byte      *)
(* codes.                                                                  *)
(*                                                                         *)
(* Format: version(1) core_len(CLEN) core count(CNT) { alg(1) node(NB)     *)
(* n(1) { tag(1) ip(IP4 or IP6) port(PORT) } } record_seq(SEQ), version 1  *)
(* without record_seq. The widths are constants: the real ones (4, 2, 32,  *)
(* 4, 16, 2, 8) in the trace check, scaled ones in the model check.        *)
(*                                                                         *)
(* A node is [alg, bytes]; an address is its bytes as written (tag, ip,    *)
(* port); the book is a sequence of <<node, addresses>> in the order the   *)
(* code iterates it; record_seq stays a byte string (big-endian, compared  *)
(* by LexLe) and so never passes TLC's integers. The core's own bytes are  *)
(* handed to operator arguments: CE(core) is what the core exports and     *)
(* CR(core, bytes) is the core's restore ([ok, live, res]), so the core is *)
(* whatever model the caller composes (FacadeState.tla: CoreStateOps).     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS NB, IP4, IP6, PORT, CLEN, CNT, SEQ, BOOKMAX, ADDRSMAX

Drop(s, n) == SubSeq(s, n + 1, Len(s))
Cap(s, n) == IF Len(s) <= n THEN s ELSE SubSeq(s, 1, n)
RECURSIVE Cat(_)
Cat(s) == IF s = <<>> THEN <<>> ELSE Head(s) \o Cat(Tail(s))
RECURSIVE BEr(_, _)
BEr(v, w) == IF w = 0 THEN <<>> ELSE BEr(v \div 256, w - 1) \o <<v % 256>>
\* what of v lies above its low w bytes
RECURSIVE Hi(_, _)
Hi(v, w) == IF w = 0 THEN v ELSE Hi(v \div 256, w - 1)
RECURSIVE BEs(_)
BEs(b) == IF b = <<>> THEN 0 ELSE BEs(SubSeq(b, 1, Len(b) - 1)) * 256 + b[Len(b)]
\* big-endian a <= b, both of one width
RECURSIVE LexLe(_, _)
LexLe(a, b) == a = <<>> \/ Head(a) < Head(b) \/ (Head(a) = Head(b) /\ LexLe(Tail(a), Tail(b)))
MaxBE(a, b) == IF LexLe(a, b) THEN b ELSE a
\* a big-endian claim b is at most r, without computing b (a u32 claim may pass TLC's integers); r is a length
ClaimLe(b, r) == Hi(r, Len(b)) > 0 \/ LexLe(b, BEr(r, Len(b)))

Width(tag) == IF tag = 4 THEN IP4 ELSE IF tag = 6 THEN IP6 ELSE -1

(* ---- parse ---- *)
AFail == [ok |-> FALSE, l |-> <<>>, rest |-> <<>>]
\* Cursor::addr, n times
RECURSIVE Addrs(_, _, _)
Addrs(r, n, acc) ==
    IF n = 0 THEN [ok |-> TRUE, l |-> acc, rest |-> r]
    ELSE IF r = <<>> \/ Width(r[1]) < 0 \/ Len(r) < 1 + Width(r[1]) + PORT THEN AFail
    ELSE Addrs(Drop(r, 1 + Width(r[1]) + PORT), n - 1, Append(acc, SubSeq(r, 1, 1 + Width(r[1]) + PORT)))
\* the k entries of the book: a known algorithm tag (from_tag: 1..4), the node, n <= ADDRSMAX, the addresses
RECURSIVE Entries(_, _, _)
Entries(r, k, acc) ==
    IF k = 0 THEN [ok |-> TRUE, l |-> acc, rest |-> r]
    ELSE IF Len(r) < 2 + NB \/ r[1] \notin 1..4 \/ r[2 + NB] > ADDRSMAX THEN AFail
    ELSE LET a == Addrs(Drop(r, 2 + NB), r[2 + NB], <<>>)
         IN IF ~a.ok THEN AFail
            ELSE Entries(a.rest, k - 1, Append(acc, <<[alg |-> r[1], bytes |-> SubSeq(r, 2, 1 + NB)], a.l>>))

PFail == [ok |-> FALSE, ver |-> 0, core |-> <<>>, book |-> <<>>, seq |-> <<>>]
\* parse: seq is SEQ bytes in version 2 and <<>> (None) in version 1; no byte may follow
Parse(bs) ==
    IF bs = <<>> \/ bs[1] \notin {1, 2} \/ Len(bs) < 1 + CLEN THEN PFail
    ELSE LET lb == SubSeq(bs, 2, 1 + CLEN)
             r2 == Drop(bs, 1 + CLEN)
         IN IF ~ClaimLe(lb, Len(r2)) THEN PFail
            ELSE LET r3 == Drop(r2, BEs(lb))
                 IN IF Len(r3) < CNT \/ BEs(SubSeq(r3, 1, CNT)) > BOOKMAX THEN PFail
                    ELSE LET e == Entries(Drop(r3, CNT), BEs(SubSeq(r3, 1, CNT)), <<>>)
                         IN IF ~e.ok \/ Len(e.rest) # (IF bs[1] = 2 THEN SEQ ELSE 0) THEN PFail
                            ELSE [ok |-> TRUE, ver |-> bs[1], core |-> SubSeq(r2, 1, BEs(lb)), book |-> e.l,
                                  seq |-> e.rest]

(* ---- the encoding, and export_state ---- *)
EncEntry(e) == <<e[1].alg>> \o e[1].bytes \o <<Len(e[2])>> \o Cat(e[2])
Enc(ver, core, book, seq) ==
    <<ver>> \o BEr(Len(core), CLEN) \o core \o BEr(Len(book), CNT)
    \o Cat([k \in 1..Len(book) |-> EncEntry(book[k])]) \o (IF ver = 2 THEN seq ELSE <<>>)
\* a live state is [core, book, seq]; export takes BOOK_MAX nodes and ADDRS_MAX addresses of each
Export(live, CE(_)) ==
    LET b == Cap(live.book, BOOKMAX)
    IN Enc(2, CE(live.core), [k \in 1..Len(b) |-> <<b[k][1], Cap(b[k][2], ADDRSMAX)>>], live.seq)

(* ---- the address book ---- *)
\* the <<node, address>> pairs a book holds
Pairs(b) == UNION {{<<b[k][1], b[k][2][j]>> : j \in 1..Len(b[k][2])} : k \in 1..Len(b)}
Range(s) == {s[k] : k \in 1..Len(s)}
Pos(book, node) == {k \in 1..Len(book) : book[k][1] = node}
\* add_address: a new node only below BOOKMAX, an address kept once, at most ADDRSMAX of one node
AddAddr(book, node, a) ==
    IF Pos(book, node) = {}
    THEN IF Len(book) >= BOOKMAX THEN book ELSE Append(book, <<node, <<a>>>>)
    ELSE LET k == CHOOSE k \in Pos(book, node) : TRUE
             v == book[k][2]
         IN IF \E j \in 1..Len(v) : v[j] = a THEN book
            ELSE IF Len(v) >= ADDRSMAX THEN book
            ELSE [book EXCEPT ![k] = <<node, Append(v, a)>>]
\* every address of one entry offered in turn (the code's `|` does not short-circuit); kept: add_address answered
\* true for one of them, that is the address is in the book after the call
RECURSIVE AddAll(_, _, _, _)
AddAll(book, node, as, kept) ==
    IF as = <<>> THEN [book |-> book, kept |-> kept]
    ELSE LET b == AddAddr(book, node, Head(as))
         IN AddAll(b, node, Tail(as), kept \/ <<node, Head(as)>> \in Pairs(b))
\* the entries merged in order; ns is the set of nodes with an address kept, n counts them: a node named by several
\* entries counts once (state.rs restore_state, fix F14 and the count of nodes)
RECURSIVE MergeS(_, _, _)
MergeS(book, es, ns) ==
    IF es = <<>> THEN [book |-> book, ns |-> ns]
    ELSE LET r == AddAll(book, Head(es)[1], Head(es)[2], FALSE)
         IN MergeS(r.book, Tail(es), IF r.kept THEN ns \cup {Head(es)[1]} ELSE ns)
MergeN(book, es) == LET m == MergeS(book, es, {}) IN [book |-> m.book, n |-> Cardinality(m.ns)]
Merge(book, es) == MergeN(book, es).book

(* ---- restore_state ---- *)
\* every check that can refuse (parse, then the core) comes before the first write
RFail(live) == [ok |-> FALSE, live |-> live, res |-> <<0, 0, 0, 0>>]
Restore(live, bs, CR(_, _)) ==
    LET p == Parse(bs) IN
    IF ~p.ok THEN RFail(live)
    ELSE LET c == CR(live.core, p.core) IN
         IF ~c.ok THEN RFail(live)
         ELSE LET m == MergeN(live.book, p.book)
              IN [ok |-> TRUE,
                  live |-> [core |-> c.live, book |-> m.book,
                            seq |-> IF p.ver = 2 THEN MaxBE(live.seq, p.seq) ELSE live.seq],
                  \* Restored { tickets, peers, prekeys } of the core, then addresses: the nodes the book kept an address of
                  res |-> c.res \o <<m.n>>]
=============================================================================
