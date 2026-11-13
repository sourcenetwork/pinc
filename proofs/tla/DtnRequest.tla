------------------------------ MODULE DtnRequest ------------------------------
(***************************************************************************)
(* What a receiver asks its holders for, and when it may finish: the       *)
(* request side of a delay-tolerant transfer, vinc-node/src/dtn.rs         *)
(* `Dtn::want` (the next run, data before parity, at most what each block  *)
(* is short, never a symbol this transfer lost) and vinc-node/src/dtn_rx.rs *)
(* `dtn_offered` (a transfer starts with nothing lost), `dtn_advance`      *)
(* (ask, finish, or refuse a stuck block) and `dtn_data` (a symbol that    *)
(* fails its proof is lost from this transfer, kept in `RxCtx::lost`).     *)
(*                                                                         *)
(* The story. A bundle is two erasure blocks of K = 2 data symbols and     *)
(* M = 1 parity symbol: block 0 is symbols 0, 1 (data) and 2 (parity),     *)
(* block 1 is 3, 4 (data) and 5 (parity). Any K symbols of a block rebuild *)
(* it (DtnRs and DtnReception prove that `finish` does). Several holders   *)
(* may feed the same partial bundle at the same time, each on its own      *)
(* transfer. A holder's copy may be corrupt in some symbols (Bad), and a   *)
(* corrupt symbol fails its proof, as do the symbols after it in the same  *)
(* answer (the verifier stops at the fault). A holder may also vanish      *)
(* mid-transfer, at most MaxDrops times in all. The receiver keeps every   *)
(* symbol that verified, whoever sent it (the partial bundle).             *)
(*                                                                         *)
(* What must never happen: parity asked for while every data symbol of    *)
(* its block can still come from that holder (no loss, no parity); a       *)
(* block asked for more symbols than it was short of K; a symbol asked for *)
(* that was already held or that this transfer lost; a transfer going on   *)
(* with a block that can no longer reach K from its holder (junk); more    *)
(* than M + 1 symbols of one block lost on one transfer; a holder whose    *)
(* copy is whole refused; a finish with a block short of K. What must      *)
(* happen: when some holder can prove K symbols of every block and keeps   *)
(* offering, the bundle is finished.                                       *)
(*                                                                         *)
(* The guards, each a constant so a RED configuration can remove one:      *)
(* MarkLost (a symbol that fails its proof is not asked of this transfer   *)
(* again), DataFirst (a block's symbols are taken in symbol order, data    *)
(* first), NeedCap (a block asks for no more than it is short), PerTransfer *)
(* (each transfer has its own lost symbols; without it there is one set    *)
(* for the partial, emptied at every offer, as the code once had), and     *)
(* StopStuck (a block that cannot reach K from this holder ends the        *)
(* transfer).                                                              *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/DtnHeld.lean, the per-block count    *)
(* the receiver decides with (`count b` is the number of held symbols of   *)
(* block b, at most K + M), which this model reads as Cardinality.         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences, TLC

\* NH holders; Case picks which symbols each holder's copy has corrupt; MaxRun is the longest run one request asks
\* for (CHUNK_BYTES in symbols); MaxDrops bounds how often holders vanish mid-transfer; the rest are the guards.
CONSTANTS NH, Case, MaxRun, MaxDrops, MarkLost, DataFirst, NeedCap, PerTransfer, StopStuck

K == 2                                   \* data symbols a block
M == 1                                   \* parity symbols a block
NB == 2                                  \* blocks
Per == K + M                             \* symbols a block
Syms == 0..(NB * Per - 1)                \* every symbol of the bundle
Holders == 1..NH                         \* the holders, numbered
BStart(b) == b * Per                     \* the first symbol of block b
BEnd(b) == BStart(b) + Per               \* one past the last symbol of block b
BSyms(b) == BStart(b)..(BEnd(b) - 1)     \* the symbols of block b
Blk(s) == s \div Per                     \* the block of symbol s
IsParity(s) == s % Per >= K              \* the last M symbols of a block are its parity
DataOf(b) == {s \in BSyms(b) : ~IsParity(s)}  \* the data symbols of block b

\* The corrupt symbols of each holder's copy, by case: "none" no loss; "one" every holder has one corrupt data symbol
\* in each block; "two" holder 1 cannot prove two symbols of block 1 (so it cannot finish it) and holder 2 is honest;
\* "allbad" holder 1's copy is corrupt everywhere and holder 2 has one corrupt data symbol.
Bad == CASE Case = "none"   -> [h \in Holders |-> {}]
         [] Case = "one"    -> [h \in Holders |-> {1, 3}]
         [] Case = "two"    -> [h \in Holders |-> IF h = 1 THEN {3, 5} ELSE {}]
         [] Case = "allbad" -> [h \in Holders |-> IF h = 1 THEN Syms ELSE {4}]

Min(a, b) == IF a < b THEN a ELSE b      \* the smaller of two numbers

\* The symbols of block b in symbol order, as a sequence.
InOrder(b) == [i \in 1..Per |-> BStart(b) + i - 1]
\* The same sequence reversed: parity first, the order a broken DataFirst guard uses.
Reversed(sq) == [i \in 1..Len(sq) |-> sq[Len(sq) - i + 1]]
\* The symbols of block b that are neither held (h) nor lost (l), in the order the guard picks.
Open(h, l, b) ==
    LET o == SelectSeq(InOrder(b), LAMBDA s : s \notin h /\ s \notin l)
    IN IF DataFirst THEN o ELSE Reversed(o)
\* The symbols a block short of `need` takes from its open ones: the first `need`, or all of them without NeedCap.
Pick(o, need) == IF NeedCap THEN SubSeq(o, 1, Min(need, Len(o))) ELSE o
\* How many symbols block b is short of K.
Need(h, b) == K - Cardinality(h \cap BSyms(b))

\* Grow the run r = <<first, end>> (end exclusive; <<>> for none) with the symbols of sq while each is the next one
\* and the run is shorter than MaxRun; stop at the first that is not, as the code returns the run there.
RECURSIVE Ext(_, _)
Ext(r, sq) ==
    IF sq = <<>> THEN [run |-> r, stop |-> FALSE]
    ELSE LET s == Head(sq)
         IN IF r = <<>> THEN Ext(<<s, s + 1>>, Tail(sq))
            ELSE IF r[2] = s /\ r[2] - r[1] < MaxRun THEN Ext(<<r[1], s + 1>>, Tail(sq))
            ELSE [run |-> r, stop |-> TRUE]

\* `Dtn::want`, block by block from block b with the run r so far: a block that holds K symbols adds nothing (and
\* ends a run already started); a block short of K symbols with fewer open symbols than it needs is Stuck; otherwise
\* it adds its picks to the run, which goes on into the next block only if it ends on this block's last symbol.
RECURSIVE WantGo(_, _, _, _)
WantGo(h, l, b, r) ==
    IF b >= NB THEN IF r = <<>> THEN [kind |-> "decodable"] ELSE [kind |-> "ask", run |-> r]
    ELSE LET need == Need(h, b)
         IN IF need <= 0
            THEN IF r # <<>> THEN [kind |-> "ask", run |-> r] ELSE WantGo(h, l, b + 1, r)
            ELSE LET o == Open(h, l, b)
                 IN IF StopStuck /\ Len(o) < need THEN [kind |-> "stuck"]
                    ELSE LET x == Ext(r, Pick(o, need))
                         IN IF x.stop THEN [kind |-> "ask", run |-> x.run]
                            ELSE IF x.run # <<>> /\ x.run[2] < BEnd(b) THEN [kind |-> "ask", run |-> x.run]
                            ELSE WantGo(h, l, b + 1, x.run)
Want(h, l) == WantGo(h, l, 0, <<>>)
\* The symbols of a run, as a set.
RunSet(r) == r[1]..(r[2] - 1)
\* Every block holds K symbols: `finish` rebuilds the rest (Ok), as DtnReception's FinishCorrect states.
Decodable(h) == \A b \in 0..(NB - 1) : Need(h, b) <= 0

VARIABLES have, lost, shared, st, ask, base, refused, done, drops
vars == <<have, lost, shared, st, ask, base, refused, done, drops>>

\* have: the symbols held, whoever sent them; lost[x]: the symbols holder x's transfer could not prove (its
\* `RxCtx::lost`); shared: the one lost set of the partial that a broken PerTransfer guard uses instead; st[x]: whether
\* x has a transfer with a request out ("asking") or not ("idle"); ask[x]: the symbols asked of x and not yet
\* answered; base[x]: the held symbols when that request was made, which it was computed from; refused: the holders
\* refused as stuck; done: the bundle was finished Ok; drops: how often a holder vanished.
Init == /\ have = {} /\ lost = [x \in Holders |-> {}] /\ shared = {}
        /\ st = [x \in Holders |-> "idle"] /\ ask = [x \in Holders |-> {}] /\ base = [x \in Holders |-> {}]
        /\ refused = {} /\ done = FALSE /\ drops = 0

\* The lost symbols holder x's transfer decides with: its own, or the partial's one set without PerTransfer.
LostOf(x) == IF PerTransfer THEN lost[x] ELSE shared

\* After an offer from holder x is taken or its request answered, with held set h and x's lost set l: ask x for the
\* next run, finish, or refuse a stuck block and end x's transfer (the partial stays). A finish of a bundle that is
\* not decodable is refused (finish reports Incomplete) and the transfer ends. Other transfers are left as they are.
Next1(x, h, l) ==
    LET w == Want(h, l)
    IN /\ have' = h
       /\ IF PerTransfer THEN lost' = [lost EXCEPT ![x] = l] /\ UNCHANGED shared
                         ELSE shared' = l /\ UNCHANGED lost
       /\ IF w.kind = "ask"
          THEN /\ st' = [st EXCEPT ![x] = "asking"] /\ ask' = [ask EXCEPT ![x] = RunSet(w.run)]
               /\ base' = [base EXCEPT ![x] = h] /\ UNCHANGED <<refused, done>>
          ELSE /\ st' = [st EXCEPT ![x] = "idle"] /\ ask' = [ask EXCEPT ![x] = {}] /\ UNCHANGED base
               /\ done' = (w.kind = "decodable" /\ Decodable(h))
               /\ refused' = IF w.kind = "stuck" THEN refused \cup {x} ELSE refused

\* Holder x offers the bundle while it has no transfer: the transfer starts with nothing lost (without PerTransfer
\* the partial's one set is emptied, under any other transfer's feet), and the receiver asks.
Offer(x) ==
    /\ ~done /\ st[x] = "idle"
    /\ Next1(x, have, {})
    /\ UNCHANGED drops

\* Holder x answers its request: the symbols before its first corrupt one verify and are held; that one fails and,
\* with MarkLost, is lost from x's transfer; the receiver then asks x again (or finishes, or refuses x).
Serve(x) ==
    /\ ~done /\ st[x] = "asking"
    /\ LET bad == ask[x] \cap Bad[x]
           f == IF bad = {} THEN -1 ELSE CHOOSE s \in bad : \A t \in bad : s <= t
           ok == IF f = -1 THEN ask[x] ELSE {s \in ask[x] : s < f}
       IN /\ UNCHANGED drops
          /\ Next1(x, have \cup ok, IF f # -1 /\ MarkLost THEN LostOf(x) \cup {f} ELSE LostOf(x))

\* Holder x vanishes mid-transfer: its transfer ends, the verified symbols stay.
Drop(x) ==
    /\ ~done /\ st[x] = "asking" /\ drops < MaxDrops
    /\ st' = [st EXCEPT ![x] = "idle"] /\ ask' = [ask EXCEPT ![x] = {}] /\ drops' = drops + 1
    /\ UNCHANGED <<have, lost, shared, base, refused, done>>

Next == \E x \in Holders : Offer(x) \/ Serve(x) \/ Drop(x)
\* Requests are answered, and every holder keeps offering while it has no transfer (strong fairness: an offer that
\* is possible again and again is taken).
Spec == Init /\ [][Next]_vars /\ \A x \in Holders : WF_vars(Serve(x)) /\ SF_vars(Offer(x))

(* ---- the properties ---- *)

TypeOK == /\ have \subseteq Syms /\ shared \subseteq Syms /\ refused \subseteq Holders /\ done \in BOOLEAN
          /\ \A x \in Holders : /\ lost[x] \subseteq Syms /\ ask[x] \subseteq Syms /\ base[x] \subseteq Syms
                                /\ st[x] \in {"idle", "asking"}
          /\ drops \in 0..MaxDrops

\* Parity is asked of a holder only in place of a data symbol of its block that this transfer lost: with no loss,
\* only data is fetched.
NoParityWithoutLoss == \A x \in Holders : \A s \in ask[x] : IsParity(s) => \E d \in DataOf(Blk(s)) : d \in LostOf(x)

\* A request asks no block for more symbols than it was short of K when it was made.
AskWithinNeed == \A x \in Holders : \A b \in 0..(NB - 1) : Cardinality(ask[x] \cap BSyms(b)) <= Need(base[x], b)

\* A request asks for no symbol held when it was made, and none this transfer lost.
AskFresh == \A x \in Holders : ask[x] \cap (base[x] \cup LostOf(x)) = {}

\* While a request is out, every block can still reach K symbols from that holder: no junk is fetched for a bundle
\* this holder cannot complete.
ActiveReachable ==
    \A x \in Holders : st[x] = "asking" =>
        \A b \in 0..(NB - 1) : Cardinality(BSyms(b) \ (have \cup LostOf(x))) >= Need(have, b)

\* One transfer has lost at most M + 1 of a block's symbols that are still missing: each loss came while the block
\* had at least as many open symbols as it needed, so the M + 1st leaves it stuck and the holder is refused before
\* it can fail another. Alone on the partial, that is at most M + 1 failed asks per block; symbols another holder
\* brings in meanwhile lower what the block needs, and so may let this transfer ask (and lose) more.
LostBounded == \A x \in Holders : \A b \in 0..(NB - 1) : Cardinality((lost[x] \cap BSyms(b)) \ have) <= M + 1

\* A holder whose copy is whole is never refused.
HonestNotRefused == \A x \in refused : Bad[x] # {}

\* A finished bundle holds K symbols in every block, so the rebuild succeeded.
FinishDecodable == done => Decodable(have)

\* The bundle is finished, eventually.
Progress == <>done
=============================================================================
