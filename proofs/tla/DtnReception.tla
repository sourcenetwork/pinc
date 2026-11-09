------------------------------ MODULE DtnReception ------------------------------
(***************************************************************************)
(* The receiving side of a bundle, vinc-dtn/src/bundle.rs `Reception`:     *)
(* `feed`, `holds`, `next_missing`, `is_complete`, `is_decodable`,         *)
(* `finish` (with its scratch) and `resume`, over the verified-range set   *)
(* of VerifiedRanges                                                       *)
(* (RangeOps.tla: the same `insert` and `contains_range`).                 *)
(*                                                                         *)
(* The tree verifier is imported as its contract: a group of a proof       *)
(* stream is delivered only if it hashes to the signed root, so it equals  *)
(* the sender's symbol (collisions are assumed away, as in the verifier    *)
(* model); a stream may carry a wrong group, stop short or carry trailing  *)
(* bytes, and the groups verified before the fault stay delivered. Bytes   *)
(* are scaled to symbols of G bytes, so offsets are s * G, the only way    *)
(* the code uses the symbol size. The erasure code is a real small         *)
(* Reed-Solomon code over GF(5) (parity j of a block is the sum over data  *)
(* i of (i + 1)^j * d_i, for j = 0, 1: a Vandermonde parity, MDS for up to *)
(* four data symbols), and `Rs::reconstruct` is its specification: it      *)
(* keeps the present data symbols, solves the missing data from the first  *)
(* as many present parity rows, and re-encodes every parity symbol of the  *)
(* block (the code of rs.rs does exactly this); the solution is unique,    *)
(* which TLC checks in every state (ReconUniqueOK). The layout is k = 2,  *)
(* m = 2 and three                                                         *)
(* data symbols: block 0 has data 0, 1 and parity 2, 3; block 1 (the      *)
(* short last block, one data symbol) has data 4 and parity 5, 6.          *)
(* The sender's content is either a code word in every block (honest) or   *)
(* has one parity symbol changed (a sender whose parity is not a code      *)
(* word, which the signed root still commits to).                          *)
(*                                                                         *)
(* Checked by TLC (DtnReception.cfg for W = 2, DtnReception_w3.cfg for     *)
(* W = 3, a held set of at most W disjoint intervals; the same rules):     *)
(* the set only grows; a feed writes only the sender's symbols into the    *)
(* buffer and records exactly the verified ones that fit; ReceptionFull    *)
(* keeps the earlier symbols; an empty feed changes nothing; `finish`      *)
(* works per block in order on a COPY of the block (the scratch), copies   *)
(* back only the symbols that are not held, and so never writes a held     *)
(* symbol: HeldAlways, every held symbol's buffer bytes are the sender's,  *)
(* always, including after a finish that fails. `finish` reports           *)
(* Incomplete exactly when a block holds fewer than k symbols (the blocks  *)
(* before it already completed, the blocks from it on untouched),          *)
(* Inconsistent only for a sender whose parity is not a code word (an      *)
(* honest sender never), and Ok exactly when the blocks are decodable and  *)
(* every block that is not fully held is rebuilt, symbol by symbol where   *)
(* it is not held, to the sender's bytes; Ok leaves the buffer equal to    *)
(* the sender's content and everything held, any other verdict leaves the  *)
(* held set alone and the held symbols' bytes as they were. A fully held   *)
(* block is skipped, as in the code, and a wrong-sized outboard or scratch *)
(* is `Buffer` with nothing changed. The helpers is_complete,              *)
(* is_decodable and next_missing agree with their definitions; `resume`    *)
(* keeps the buffer and the held set and refuses a bad signature, an       *)
(* expired head and a wrong-sized buffer.                                  *)
(*                                                                         *)
(* The symbols that are not held hold whatever the reconstruction wrote:   *)
(* after a failed finish they can differ from the sender's, which is       *)
(* harmless because they are not held and a later feed or finish rewrites  *)
(* them from verified symbols only.                                        *)
(*                                                                         *)
(* Lean counterpart (proofs/lean/Vinc/DtnReception.lean, unbounded in the *)
(* number of symbols, blocks and in the symbol size): feedGo_buf (only     *)
(* verified bytes enter the buffer), feedGo_verified (held means verified),*)
(* feedGo_mono and feedGo_reach (the held set only grows and stays within  *)
(* capacity, also when a record fails), feedGo_new, feedGo_cover and       *)
(* feed_ok_holds, feed_empty, feed_ok_iff, holds_iff, isComplete_iff,      *)
(* isDecodable, resume_spec; and for finish: finish_held_untouched (a held *)
(* symbol is never written, for every block, symbol and size),             *)
(* block_ok_iff and honest_block_ok (the verdict of one block),            *)
(* finish_complete_iff and finish_stops (the block order: the first block  *)
(* short of k symbols stops it, the blocks after it untouched),            *)
(* finish_exact (an honest sender succeeds) and blocksOf_ordered (the      *)
(* blocks of a layout are ascending and disjoint).                         *)
(***************************************************************************)
EXTENDS RangeOps, FiniteSets, TLC

CONSTANTS G, W

K == 2
M == 2
Total == 7
Syms == 0..(Total - 1)
Blocks == 0..1
BStart(b) == 4 * b
BK(b) == IF b = 0 THEN 2 ELSE 1
BN(b) == BK(b) + M
BSyms(b) == BStart(b)..(BStart(b) + BN(b) - 1)
IsParity(s) == s \in {2, 3, 5, 6}

Pow(x, j) == x ^ j
(* parity j of a block with data function d over 0..kk-1 *)
ParityOf(kk, d, j) == LET RECURSIVE S(_) S(i) == IF i = kk THEN 0 ELSE Pow(i + 1, j) * d[i] + S(i + 1) IN S(0) % 5
(* the code word of a block: the data, then the two parity symbols *)
Codeword(b, d) == [i \in 0..(BN(b) - 1) |-> IF i < BK(b) THEN d[i] ELSE ParityOf(BK(b), d, i - BK(b))]

(* contents: honest from three data symbols, or with the parity symbol f changed *)
Honest(d3) == [s \in Syms |->
    IF s \in 0..3 THEN Codeword(0, [i \in 0..1 |-> d3[i + 1]])[s] ELSE Codeword(1, [i \in 0..0 |-> d3[3]])[s - 4]]
Faulty(d3, f) == [Honest(d3) EXCEPT ![f] = (Honest(d3)[f] + 1) % 5]
Contents == {Honest(<<1, 2, 3>>)} \cup {Faulty(<<1, 2, 3>>, f) : f \in {2, 5}}

(* does the block's region of `v` hold a code word *)
BlockSlice(v, b) == [i \in 0..(BN(b) - 1) |-> v[BStart(b) + i]]
IsCW(v, b) == BlockSlice(v, b) = Codeword(b, [i \in 0..(BK(b) - 1) |-> v[BStart(b) + i]])

(* ---- the code ---- *)
Holds(h, s) == s < Total /\ ContainsRange(h, s * G, (s + 1) * G)
HeldSet(h) == {s \in Syms : Holds(h, s)}
IsComplete(h) == ContainsRange(h, 0, Total * G)
IsDecodable(h) == \A b \in Blocks : Cardinality({s \in BSyms(b) : Holds(h, s)}) >= BK(b)

(* next_missing(from): the first run of unheld symbols at or after `from` (a symbol index), by the loop of the code *)
RECURSIVE NMGo(_, _, _)
NMGo(h, i, at) ==
    IF i > Len(h) THEN IF at < Total * G THEN [some |-> TRUE, a |-> at \div G, b |-> Total] ELSE [some |-> FALSE]
    ELSE IF h[i][2] <= at THEN NMGo(h, i + 1, at)
    ELSE IF h[i][1] > at THEN [some |-> TRUE, a |-> at \div G, b |-> Min(h[i][1], Total * G) \div G]
    ELSE NMGo(h, i + 1, h[i][2])
NextMissing(h, from) == NMGo(h, 1, from * G)

(* the groups of a stream a verifier delivers: the longest prefix whose groups equal the sender's symbols *)
RECURSIVE Verified(_, _, _)
Verified(ct, a, vals) ==
    IF vals = <<>> \/ vals[1] # ct[a] THEN <<>> ELSE <<vals[1]>> \o Verified(ct, a + 1, Tail(vals))

(* the sink: copy each delivered group into the buffer, then try to record its interval; a full set records
   nothing but the copy has happened and the loop goes on *)
RECURSIVE Sink(_, _, _, _, _)
Sink(buf, h, full, a, vals) ==
    IF vals = <<>> THEN [buf |-> buf, h |-> h, full |-> full]
    ELSE LET r == InsertResult(h, <<a * G, (a + 1) * G>>, W)
         IN Sink([buf EXCEPT ![a] = vals[1]], r.items, full \/ ~r.ok, a + 1, Tail(vals))

(* feed of symbols [a, b) with the stream `st` (the groups, and whether bytes trail the proof) *)
FeedResult(ct, buf, h, a, b, st) ==
    IF a = b THEN [buf |-> buf, h |-> h, res |-> "ok"]
    ELSE LET ver == Verified(ct, a, st.vals)
             out == Sink(buf, h, FALSE, a, ver)
             cut == Len(ver) < b - a \/ Len(st.vals) < b - a \/ st.extra
         IN [buf |-> out.buf, h |-> out.h, res |-> IF cut THEN "tree" ELSE IF out.full THEN "full" ELSE "ok"]

(* the reconstruction of one block of `buf`: the present data kept, the missing data solved from the first as many
   present parity rows, every parity symbol recomputed *)
Recon(buf, h, b) ==
    LET kk == BK(b)
        pres(i) == Holds(h, BStart(b) + i)
        missing == {i \in 0..(kk - 1) : ~pres(i)}
        e == Cardinality(missing)
        prows == {j \in 0..(M - 1) : pres(kk + j)}
        \* the first e present parity rows
        used == {j \in prows : Cardinality({x \in prows : x < j}) < e}
        sols == {d \in [0..(kk - 1) -> 0..4] :
                   /\ \A i \in 0..(kk - 1) : pres(i) => d[i] = buf[BStart(b) + i]
                   /\ \A j \in used : ParityOf(kk, d, j) = buf[BStart(b) + kk + j]}
    IN CHOOSE d \in sols : TRUE
ReconUnique(buf, h, b) ==
    LET kk == BK(b)
        pres(i) == Holds(h, BStart(b) + i)
        e == Cardinality({i \in 0..(kk - 1) : ~pres(i)})
        prows == {j \in 0..(M - 1) : pres(kk + j)}
        used == {j \in prows : Cardinality({x \in prows : x < j}) < e}
    IN Cardinality({d \in [0..(kk - 1) -> 0..4] :
                   /\ \A i \in 0..(kk - 1) : pres(i) => d[i] = buf[BStart(b) + i]
                   /\ \A j \in used : ParityOf(kk, d, j) = buf[BStart(b) + kk + j]}) = 1

FullyHeld(h, b) == \A s \in BSyms(b) : Holds(h, s)
Decodable(h, b) == Cardinality({s \in BSyms(b) : Holds(h, s)}) >= BK(b)

(* finish: blocks in order; a fully held block is skipped; the first block short of k symbols stops it (earlier blocks
   already completed). A block is reconstructed in the scratch, a copy of its region, and only the symbols that are
   not held are copied back, so a held symbol is never written. *)
RECURSIVE FinishGo(_, _, _)
FinishGo(buf, h, b) ==
    IF b > 1 THEN [buf |-> buf, res |-> "done"]
    ELSE IF FullyHeld(h, b) THEN FinishGo(buf, h, b + 1)
    ELSE IF ~Decodable(h, b) THEN [buf |-> buf, res |-> "incomplete"]
    ELSE LET d == Recon(buf, h, b)
             nb == [s \in Syms |-> IF s \in BSyms(b) /\ ~Holds(h, s) THEN Codeword(b, d)[s - BStart(b)] ELSE buf[s]]
         IN FinishGo(nb, h, b + 1)

(* block b of the content c is rebuilt right: every symbol of it that is not held gets the sender's bytes *)
BlockMatches(c, bf, h, b) ==
    LET d == Recon(bf, h, b)
    IN \A s \in BSyms(b) : ~Holds(h, s) => Codeword(b, d)[s - BStart(b)] = c[s]

VARIABLES ct, have, buf, res
vars == <<ct, have, buf, res>>

Init == /\ ct \in Contents
        /\ have = <<>>
        /\ buf = [s \in Syms |-> 9]
        /\ res = "init"

GoodVals(a, b) == [i \in 1..(b - a) |-> ct[a + i - 1]]
Streams(a, b) ==
    {[vals |-> GoodVals(a, b), extra |-> FALSE], [vals |-> GoodVals(a, b), extra |-> TRUE]}
    \cup {[vals |-> SubSeq(GoodVals(a, b), 1, j), extra |-> FALSE] : j \in 0..(b - a - 1)}
    \cup {[vals |-> [GoodVals(a, b) EXCEPT ![p] = (GoodVals(a, b)[p] + 1) % 5], extra |-> FALSE] : p \in {1, b - a}}

\* the ranges a peer asks for: every symbol, the two blocks, the whole bundle, and an empty range
Ranges == {<<a, a + 1>> : a \in Syms} \cup {<<0, 4>>, <<4, 7>>, <<0, 7>>, <<3, 3>>}

Feed ==
    \E rg \in Ranges : \E a \in {rg[1]}, b \in {rg[2]} : \E st \in Streams(a, b) :
        LET r == FeedResult(ct, buf, have, a, b, st)
        IN /\ buf' = r.buf /\ have' = r.h /\ res' = r.res
           /\ UNCHANGED ct

Finish ==
    /\ LET r == FinishGo(buf, have, 0)
       IN IF r.res = "incomplete"
          THEN /\ buf' = r.buf /\ res' = "fin_incomplete" /\ have' = have
          ELSE IF r.buf = ct
               THEN /\ buf' = r.buf /\ res' = "fin_ok" /\ have' = <<<<0, Total * G>>>>
               ELSE /\ buf' = r.buf /\ res' = "fin_inconsistent" /\ have' = have
    /\ UNCHANGED ct

\* Reception::finish with an outboard or scratch of the wrong size: refused before anything is read or written
FinishBuffer == res' = "fin_buffer" /\ UNCHANGED <<ct, have, buf>>

\* Reception::resume: the signature, then the lifetime, then the buffer size; the state is the one passed in
Resume ==
    \E badSig \in BOOLEAN, expired \in BOOLEAN, wrongSize \in BOOLEAN :
        /\ res' = IF badSig THEN "r_crypto" ELSE IF expired THEN "r_expired" ELSE IF wrongSize THEN "r_buffer" ELSE "r_ok"
        /\ UNCHANGED <<ct, have, buf>>

Next == Feed \/ Finish \/ FinishBuffer \/ Resume
Spec == Init /\ [][Next]_vars

(* ---- the properties ---- *)
TypeOK == /\ ct \in Contents /\ buf \in [Syms -> 0..9] /\ Canonical(have) /\ Len(have) <= W

\* what a held symbol's buffer bytes are: the verified ones, always, also after a finish that fails
HeldAlways == \A s \in HeldSet(have) : buf[s] = ct[s]

\* the reconstruction of a block that is not fully held has a unique solution in every state
ReconUniqueOK == \A b \in Blocks : ~FullyHeld(have, b) /\ Decodable(have, b) => ReconUnique(buf, have, b)

HeldGrows == [][HeldSet(have) \subseteq HeldSet(have')]_vars

FeedCorrect ==
    [][ (res' \in {"ok", "tree", "full"}) =>
         /\ \A s \in Syms : buf'[s] # buf[s] => buf'[s] = ct[s]
         /\ \A s \in Syms : (Holds(have', s) /\ ~Holds(have, s)) => buf'[s] = ct[s] ]_vars

\* the groups a feed delivers are kept in the buffer even when the held set is full, and the intervals recorded
\* before the fault stay
FullKeepsEarlier == [][res' = "full" => HeldSet(have) \subseteq HeldSet(have')]_vars

FinishCorrect ==
    [][ (res' \in {"fin_incomplete", "fin_inconsistent", "fin_ok"}) =>
         /\ (res' = "fin_incomplete") = ~(\A b \in Blocks : Decodable(have, b))
         \* Ok exactly when the blocks are decodable and every block that is not fully held is rebuilt to the sender's bytes
         /\ (res' = "fin_ok") = ((\A b \in Blocks : Decodable(have, b))
                                 /\ \A b \in Blocks : ~FullyHeld(have, b) => BlockMatches(ct, buf, have, b))
         \* an honest sender is never reported inconsistent
         /\ (res' = "fin_inconsistent") => (\E b \in Blocks : ~FullyHeld(have, b) /\ ~IsCW(ct, b))
         /\ (res' = "fin_ok") => (buf' = ct /\ IsComplete(have') /\ HeldSet(have') = Syms)
         /\ (res' # "fin_ok") => have' = have
         \* a held symbol is never written, whatever the verdict
         /\ \A s \in HeldSet(have) : buf'[s] = buf[s]
         \* a block short of k symbols stops finish: it and every later block are untouched
         /\ \A b, b2 \in Blocks : (b <= b2 /\ ~Decodable(have, b)) => \A s \in BSyms(b2) : buf'[s] = buf[s] ]_vars

FinishBufferCorrect == [][res' = "fin_buffer" => (have' = have /\ buf' = buf)]_vars

ResumeCorrect == [][(res' \in {"r_crypto", "r_expired", "r_buffer", "r_ok"}) => (have' = have /\ buf' = buf)]_vars

HelpersOK ==
    /\ IsComplete(have) = (HeldSet(have) = Syms)
    /\ IsDecodable(have) = (\A b \in Blocks : Decodable(have, b))
    /\ \A from \in Syms \cup {Total} :
         LET r == NextMissing(have, from)
         IN IF r.some
            THEN /\ r.a >= from /\ r.a < r.b /\ r.b <= Total
                 /\ ~Holds(have, r.a) /\ \A s \in from..(r.a - 1) : Holds(have, s)
                 /\ \A s \in r.a..(r.b - 1) : ~Holds(have, s)
                 /\ (r.b < Total => Holds(have, r.b))
            ELSE \A s \in from..(Total - 1) : Holds(have, s)
=============================================================================
