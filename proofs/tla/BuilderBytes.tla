---------------------------- MODULE BuilderBytes ----------------------------
(***************************************************************************)
(* The outboard builder of pinc-dag (tree/builder.rs) at the byte level,   *)
(* written step for step on the machine integers of U64.tla: `update`      *)
(* (the size checks, the loop that takes min(room, bytes left) bytes, the  *)
(* hasher offset `consumed / group * group`, `in_group`, `consumed`),      *)
(* `complete_group` (the stack push, `div_ceil`, the merge loop with       *)
(* `done - 2 * rs`, `2 * rs`), `parent` (the slot `preorder_index * 64`,   *)
(* narrowed to a usize of 32 or 64 bits, the range checked against the     *)
(* buffer, the root test) and `finish` (`ls + rs`, `n - size`). A step     *)
(* that overflows, underflows, shifts by 64 or more, narrows to a usize    *)
(* that does not fit, finds no slot or pushes onto a full stack stops TLC  *)
(* with an error: a finished model check shows that none is reachable in   *)
(* the checked domain.                                                     *)
(*                                                                         *)
(* The hash is symbolic (mode "sym": a hash is the term of its arguments,  *)
(* so equal hashes mean equal inputs, which is collision resistance), a    *)
(* table of recorded calls (mode of the trace check), or an opaque node    *)
(* name (mode "arith", for the arithmetic of trees of 2^54 groups). The     *)
(* hasher is modelled by the offset it was set to and the number of bytes  *)
(* it took; every `update` of the hasher must extend the bytes it has (the *)
(* assumption that hashing a group in several calls equals hashing the     *)
(* concatenation is that of BLAKE3, stated in the README).                 *)
(*                                                                         *)
(* The specification is stated apart from the code (SpecRoot, SpecWrites): *)
(* the genuine chaining value of a node is the hash of its children's, a   *)
(* leaf the hash of its group; the genuine outboard has, for every parent, *)
(* the pair of its children's values at the slot given by its position    *)
(* among the parents (counted from the definition).                        *)
(*                                                                         *)
(* Checked by TLC (BuilderBytes.cfg) as a state machine that feeds pieces: *)
(*  - split: every value length up to 4 groups + 1 byte of group sizes 1,  *)
(*    2 and 4 bytes (the model is parametric in the group length, which    *)
(*    the code uses only through `group_len()`), fed in every sequence of  *)
(*    pieces of every size (empty pieces, pieces past the declared length, *)
(*    outboard buffers of the wrong size); and the real group sizes 1 KiB, *)
(*    2 KiB and 1 GiB with the pieces that end at the byte counts within   *)
(*    two bytes of a group edge or at the end of the value (every          *)
(*    distance between two such counts is a piece size: 1, 2, g - 1, g,    *)
(*    g + 1, ...), the empty piece and one byte too many, on a 32-bit and  *)
(*    a 64-bit usize. At every state `StateDet` holds: the state equals    *)
(*    the group-level reference (the value fed group by group) for the bytes *)
(*    consumed, whatever the pieces were; `finish` on a copy returns the   *)
(*    genuine root and has written exactly the genuine pairs once the      *)
(*    value is complete;                                                   *)
(*  - arith: for every number of complete groups d up to 2^54 (the         *)
(*    boundary set 2^j - 1, 2^j, 2^j + 1 and the numbers around them) and  *)
(*    every tree size n >= d, the group that completes the d-th group      *)
(*    merges the stack exactly as the binary representation of d says,     *)
(*    writing parents at the slots of the definition; and `finish` of a    *)
(*    full stack of n groups merges the right spine into the genuine       *)
(*    nodes.                                                               *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/BuilderBytes.lean, Builder.lean):   *)
(*   StateDet         BuilderBytes.builder_split_invariance, updLoop_inv,  *)
(*                    updStep_inv                                          *)
(*   FinishOK         BuilderBytes.builder_split_root, Builder.builder_correct, *)
(*                    Builder.builder_outboard, builder_correct_one         *)
(*   ErrorsOK         BuilderBytes.update_errors, finish_errors, builder_empty *)
(*   ArithOK          BuilderBytes.builder_arith, mergeTopM_eq,            *)
(*                    finishTopM_eq, merge_safe, finish_safe, slotM_eq     *)
(*   StackOK          Builder.mainPhase_stack_le                           *)
(*   the boundary sets  Pinc.Link (Builder boundary theorems)              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

StackCap == 64
Sixty4 == U!W(64)
Two == U!W(2)

(* ---- the hash ---- *)

(* a hash is a record whose mode names how a call is evaluated *)
Sym == [mode |-> "sym"]
ArithH == [mode |-> "arith"]

LeafHash(H, root, idx, ln) ==
    IF H.mode = "sym" THEN <<"L", root, idx, ln>>
    ELSE IF H.mode = "arith" THEN <<"cv", idx, U!Add(idx, U!One)>>
    ELSE (CHOOSE r \in H.leaf : r[1] = root /\ r[2] = U!Val(idx) /\ r[3] = U!Val(ln))[4]

ParHash(H, root, l, r) ==
    IF H.mode = "sym" THEN <<"P", root, l, r>>
    ELSE IF H.mode = "arith" THEN <<"cv", l[2], r[3]>>
    ELSE (CHOOSE x \in H.par : x[1] = root /\ x[2] = l /\ x[3] = r)[4]

EmptyHash(H) == IF H.mode \in {"sym", "arith"} THEN <<"E">> ELSE H.e0

(* ---- the code ---- *)

(* the layout of a builder: the value length, the group length g (a power of two), the number of groups, the size
   of the outboard buffer, and the width of usize *)
MkLay(len, g, bits) == [k |-> "run", len |-> len, g |-> g, n |-> L!GroupsG(len, g), ob |-> L!OutboardSizeG(len, g), bits |-> bits]

InitState(H, lay) ==
    [ing |-> U!Zero, con |-> U!Zero, h |-> [off |-> U!Zero, n |-> U!Zero], stack |-> <<>>, wr |-> <<>>,
     root |-> IF lay.len = U!Zero THEN EmptyHash(H) ELSE <<"unset">>]

(* OutboardBuilder::parent: write the pair of the node [lo, hi) at its slot and return its chaining value *)
ParentOp(H, lay, st, lo, hi, l, r) ==
    LET idx == L!PreorderIndex(lay.n, lo, hi)
        at == U!Mul64(idx, Sixty4)
        t == U!TryFrom(at, lay.bits)
        e == U!CAddU(t.v, Sixty4, lay.bits)
        found == t.ok /\ e.ok /\ U!Le(e.v, lay.ob)
        isRoot == lo = U!Zero /\ hi = lay.n
        cv == ParHash(H, isRoot, l, r)
    IN IF ~found THEN [cv |-> cv, st |-> st, err |-> "outboard"]
       ELSE [cv |-> cv, err |-> "none",
             st |-> [st EXCEPT !.wr = Append(st.wr, [slot |-> idx, l |-> l, r |-> r]),
                               !.root = IF isRoot THEN cv ELSE st.root]]

(* the merge loop of complete_group: while the two top sizes are equal, merge them into the node ending at `done` *)
RECURSIVE MergeLoop(_, _, _, _)
MergeLoop(H, lay, st, done) ==
    IF Len(st.stack) >= 2 /\ st.stack[1].size = st.stack[2].size
    THEN LET rs == st.stack[1].size
             lo == U!Sub64(done, U!Mul64(rs, Two))
             p == ParentOp(H, lay, st, lo, done, st.stack[2].cv, st.stack[1].cv)
             st2 == p.st
         IN IF p.err # "none" THEN [st2 EXCEPT !.root = <<"outboard error">>]
            ELSE MergeLoop(H, lay,
                           [st2 EXCEPT !.stack = <<[cv |-> p.cv, size |-> U!Mul64(rs, Two)]>>
                                                 \o SubSeq(st2.stack, 3, Len(st2.stack))], done)
    ELSE st

(* OutboardBuilder::complete_group, after in_group was reset *)
CompleteGroup(H, lay, st) ==
    LET idx == U!Div64(st.h.off, lay.g)
    IN IF lay.n = U!One
       THEN [st EXCEPT !.root = LeafHash(H, TRUE, idx, st.h.n)]
       ELSE IF Len(st.stack) >= StackCap THEN [st EXCEPT !.root = <<"stack overflow">>]
       ELSE MergeLoop(H, lay,
                      [st EXCEPT !.stack = <<[cv |-> LeafHash(H, FALSE, idx, st.h.n), size |-> U!One]>> \o st.stack],
                      U!DivCeil(st.con, lay.g))

(* the loop of update over `rem` more bytes *)
RECURSIVE UpdLoop(_, _, _, _)
UpdLoop(H, lay, st, rem) ==
    IF rem = U!Zero THEN st
    ELSE LET st0 == IF st.ing = U!Zero
                    THEN [st EXCEPT !.h = [off |-> U!Mul64(U!Div64(st.con, lay.g), lay.g), n |-> U!Zero]]
                    ELSE st
             tf == U!TryFrom(U!Sub64(lay.g, st0.ing), lay.bits)
             room == IF tf.ok THEN tf.v ELSE U!Sub(U!Pw(lay.bits), U!One)
             take == U!Min(room, rem)
             st1 == [st0 EXCEPT !.h = [off |-> st0.h.off, n |-> U!Add64(st0.h.n, take)],
                                !.ing = U!Add64(st0.ing, take), !.con = U!Add64(st0.con, take)]
         IN IF U!Add(st0.h.off, st0.h.n) # st0.con
            THEN [st0 EXCEPT !.root = <<"hasher content is not the bytes consumed">>]
            ELSE UpdLoop(H, lay,
                         IF st1.ing = lay.g \/ st1.con = lay.len
                         THEN CompleteGroup(H, lay, [st1 EXCEPT !.ing = U!Zero]) ELSE st1,
                         U!Sub(rem, take))

(* OutboardBuilder::update with a piece of k bytes and an outboard buffer of obLen bytes *)
UpdateCall(H, lay, st, k, obLen) ==
    IF obLen # lay.ob THEN [res |-> "outsize", st |-> st]
    ELSE IF U!Lt(U!Sub64(lay.len, st.con), k) THEN [res |-> "toomuch", st |-> st]
    ELSE [res |-> "ok", st |-> UpdLoop(H, lay, st, k)]

(* the loop of finish: merge the two top entries into the node that ends at the last group *)
RECURSIVE FinLoop(_, _, _)
FinLoop(H, lay, st) ==
    IF Len(st.stack) >= 2
    THEN LET rs == st.stack[1].size
             ls == st.stack[2].size
             size == U!Add64(ls, rs)
             p == ParentOp(H, lay, st, U!Sub64(lay.n, size), lay.n, st.stack[2].cv, st.stack[1].cv)
         IN IF p.err # "none" THEN [p.st EXCEPT !.root = <<"outboard error">>]
            ELSE FinLoop(H, lay, [p.st EXCEPT !.stack = <<[cv |-> p.cv, size |-> size]>>
                                                         \o SubSeq(p.st.stack, 3, Len(p.st.stack))])
    ELSE st

(* OutboardBuilder::finish on a copy of the builder state *)
FinishCall(H, lay, st, obLen) ==
    IF obLen # lay.ob THEN [res |-> "outsize"]
    ELSE IF st.con # lay.len THEN [res |-> "incomplete"]
    ELSE LET fin == FinLoop(H, lay, st) IN [res |-> "ok", root |-> fin.root, wr |-> fin.wr]

(* ---- the specification, apart from the code ---- *)

(* the genuine chaining value of the node [a, b) *)
RECURSIVE GenCv(_, _, _)
GenCv(lay, a, b) ==
    LET isRoot == a = U!Zero /\ b = lay.n
    IN IF U!Sub(b, a) = U!One THEN LeafHash(Sym, isRoot, a, L!GroupSizeG(lay.len, lay.g, a))
       ELSE LET m == U!Add(a, L!SpecLeft(U!Sub(b, a)))
            IN ParHash(Sym, isRoot, GenCv(lay, a, m), GenCv(lay, m, b))

SpecRoot(lay) == IF lay.len = U!Zero THEN EmptyHash(Sym) ELSE GenCv(lay, U!Zero, lay.n)

(* the genuine outboard: for each parent [a, b) at position idx, the pair of its children's values *)
RECURSIVE SpecW(_, _, _, _)
SpecW(lay, a, b, idx) ==
    IF U!Sub(b, a) = U!One THEN {}
    ELSE LET m == U!Add(a, L!SpecLeft(U!Sub(b, a)))
         IN {[slot |-> idx, l |-> GenCv(lay, a, m), r |-> GenCv(lay, m, b)]}
            \cup SpecW(lay, a, m, U!Add(idx, U!One))
            \cup SpecW(lay, m, b, U!Add(U!Add(idx, U!One), L!SpecParents(U!Sub(m, a))))

SpecWrites(lay) == IF lay.n = U!Zero THEN {} ELSE SpecW(lay, U!Zero, lay.n, U!Zero)

SeqSet(s) == {s[i] : i \in 1..Len(s)}

(* the group-level reference: the value fed group by group, to `con` bytes *)
RECURSIVE RefState(_, _, _, _)
RefState(H, lay, st, k) ==
    IF st.con = k THEN st
    ELSE LET piece == U!Min(lay.g, U!Sub(k, st.con))
         IN RefState(H, lay, UpdLoop(H, lay, st, piece), k)

(* ---- the properties ---- *)

StateDet(H, lay, st) == st = RefState(H, lay, InitState(H, lay), st.con)

WritesGenuine(lay, st) ==
    /\ SeqSet(st.wr) \subseteq SpecWrites(lay)
    /\ \A a, b \in 1..Len(st.wr) : a # b => st.wr[a].slot # st.wr[b].slot

FinishOK(H, lay, st) ==
    LET f == FinishCall(H, lay, st, lay.ob)
    IN IF st.con # lay.len THEN f.res = "incomplete"
       ELSE /\ f.res = "ok"
            /\ f.root = SpecRoot(lay)
            /\ SeqSet(f.wr) = SpecWrites(lay)
            /\ Len(f.wr) = IF lay.n = U!Zero THEN 0 ELSE U!Val(L!SpecParents(lay.n))
            /\ lay.len = U!Zero => f.wr = <<>>

ErrorsOK(H, lay, st) ==
    /\ UpdateCall(H, lay, st, U!Zero, U!Add(lay.ob, U!One)) = [res |-> "outsize", st |-> st]
    /\ UpdateCall(H, lay, st, U!Add(U!Sub(lay.len, st.con), U!One), lay.ob) = [res |-> "toomuch", st |-> st]
    /\ FinishCall(H, lay, st, U!Add(lay.ob, U!One)) = [res |-> "outsize"]
    /\ UpdateCall(H, lay, st, U!Zero, lay.ob) = [res |-> "ok", st |-> st]

Shape(st, lay) ==
    /\ Len(st.stack) <= 55
    /\ U!Lt(st.ing, lay.g) /\ U!Le(st.con, lay.len)

(* ---- the bounded domain ---- *)

(* the byte counts a feed may stop at: around every group edge (two bytes each side), the last bytes of the value *)
Targets(lay) ==
    LET k2 == U!Log2(lay.g)
        edges == {U!Shl(U!W(k), k2) : k \in 0..6}
        around == UNION {{U!Add(e, U!W(d)), IF U!Le(U!W(d), e) THEN U!Sub(e, U!W(d)) ELSE e} : e \in edges, d \in 0..2}
    IN {t \in around \cup {lay.len, IF U!Lt(U!Zero, lay.len) THEN U!Sub(lay.len, U!One) ELSE lay.len} : U!Le(t, lay.len)}

(* the piece sizes tried from a state: every size up to one past the bytes left for the small group sizes; for
   the real ones the pieces that end at a target (every distance between two targets, so the pieces include
   one byte, two bytes, g - 1, g, g + 1 and the like), the empty piece and one byte too many *)
Pieces(lay, st) ==
    LET left == U!Sub(lay.len, st.con)
    IN IF U!Le(lay.g, U!W(4))
       THEN {U!W(k) : k \in 0..(U!Val(left) + 1)}
       ELSE {x \in {U!Sub(t, st.con) : t \in {t \in Targets(lay) : U!Le(st.con, t)}} \cup {U!Zero, U!Add(left, U!One)} :
               U!Lt(x, U!Pw(lay.bits))}

EdgeVal(j, d) == L!EdgeVal(j, d)
EdgeOK(j, d) == L!EdgeOK(j, d)

(* The cases are the states of one machine: the root state has one successor per seed, a seed one per layout (or
   arithmetic case), so the cases are generated and checked by all the workers at once. *)
Seeds ==
    (UNION {{[f |-> "small", g |-> g, len |-> len] : len \in 0..(4 * g + 1)} : g \in {1, 2, 4}})
    \cup {[f |-> "kib", g |-> g, bits |-> bits] : g \in {1024, 2048}, bits \in {32, 64}}
    \cup {[f |-> "gib", i |-> i, bits |-> bits] : i \in 1..5, bits \in {32, 64}}
    \cup {[f |-> "arith", j |-> j, d |-> d] : j \in 0..54, d \in -1..1}
\* the quick profile (proofs/tla/quick): group sizes 1 and 2 bytes up to 3 groups + 1 byte, 1 KiB on both usizes, every
\* GiB case, and the arithmetic at the low powers, around 2^32 and at the top
SeedsQuick ==
    (UNION {{[f |-> "small", g |-> g, len |-> len] : len \in 0..(3 * g + 1)} : g \in {1, 2}})
    \cup {[f |-> "kib", g |-> 1024, bits |-> bits] : bits \in {32, 64}}
    \cup {[f |-> "gib", i |-> i, bits |-> bits] : i \in 1..5, bits \in {32, 64}}
    \cup {[f |-> "arith", j |-> j, d |-> d] : j \in {0, 1, 2, 31, 32, 53, 54}, d \in -1..1}

Expand(sd) ==
    CASE sd.f = "small" -> {MkLay(U!W(sd.len), U!W(sd.g), 64)}
      [] sd.f = "kib" ->
            {MkLay(U!W(len), U!W(sd.g), sd.bits) :
               len \in {0, 1, sd.g - 1, sd.g, sd.g + 1, 2 * sd.g, 2 * sd.g + 1, 3 * sd.g, 3 * sd.g + 1, 5 * sd.g + 7}}
      [] sd.f = "gib" ->
            {MkLay(<<U!W(1), U!Pw(30), U!Add(U!Pw(30), U!One), U!Add(U!Shl(U!Pw(30), 1), U!W(5)),
                     U!Shl(U!Pw(30), 2)>>[sd.i], U!Pw(30), sd.bits)}
      [] sd.f = "arith" ->
            IF EdgeOK(sd.j, sd.d) /\ U!Le(U!One, EdgeVal(sd.j, sd.d)) /\ U!Le(EdgeVal(sd.j, sd.d), U!Pw(54))
            THEN {[k |-> "arith", d |-> EdgeVal(sd.j, sd.d), n |-> n] :
                    n \in {m \in {EdgeVal(sd.j, sd.d), U!Add(EdgeVal(sd.j, sd.d), U!One), U!Pw(54),
                                   U!Sub(U!Pw(54), U!One)} : U!Le(EdgeVal(sd.j, sd.d), m) /\ U!Le(m, U!Pw(54))}}
            ELSE {}

VARIABLES lay, st

Init == lay = [k |-> "root"] /\ st = <<>>

Next ==
    \/ lay.k = "root" /\ \E sd \in Seeds : lay' = [k |-> "seed", sd |-> sd] /\ st' = <<>>
    \/ lay.k = "seed" /\ \E x \in Expand(lay.sd) :
           /\ lay' = x
           /\ st' = IF x.k = "run" THEN InitState(Sym, x) ELSE <<>>
    \/ lay.k = "run" /\ \E k \in Pieces(lay, st), ob \in {lay.ob, U!Add(lay.ob, U!One)} :
           LET r == UpdateCall(Sym, lay, st, k, ob)
           IN /\ r.res \in {"ok", "outsize", "toomuch"}
              /\ st' = r.st
              /\ UNCHANGED lay

Spec == Init /\ [][Next]_<<lay, st>>

(* ---- arithmetic of trees of up to 2^54 groups ---- *)

(* the stack of a builder after d complete groups, top first: the set bits of d from the lowest to the highest *)
BitSet(d, j) == U!Low(U!Shr(d, j), 1) = U!One
RECURSIVE BinFrom(_, _)
BinFrom(d, j) ==
    IF j > 63 THEN <<>>
    ELSE (IF BitSet(d, j)
          THEN LET lo == U!Shl(U!Shr(d, j + 1), j + 1)
               IN <<[cv |-> <<"cv", lo, U!Add(lo, U!Pw(j))>>, size |-> U!Pw(j)]>>
          ELSE <<>>) \o BinFrom(d, j + 1)
BinStack(d) == BinFrom(d, 0)

ArithLay(n) == MkLay(n, U!One, 64)

(* the state after d - 1 complete groups of a value of n >= d groups of one byte, about to complete group d *)
ArithBefore(d, n) ==
    [ing |-> U!Zero, con |-> d, h |-> [off |-> U!Sub(d, U!One), n |-> U!One], stack |-> BinStack(U!Sub(d, U!One)),
     wr |-> <<>>, root |-> <<"unset">>]

(* completing group d merges as many equal tops as d - 1 has trailing one bits, to the stack of d, and every
   parent written is a node of the tree of n groups at its slot *)
ArithOK(d, n) ==
    LET ly == ArithLay(n)
        after == CompleteGroup(ArithH, ly, ArithBefore(d, n))
    IN IF n = U!One THEN TRUE
       ELSE /\ after.stack = BinStack(d)
            /\ \A i \in 1..Len(after.wr) :
                 LET w == after.wr[i]
                     lo == w.l[2]
                     mid == w.l[3]
                     hi == w.r[3]
                 IN /\ w.r[2] = mid
                    /\ U!Sub(mid, lo) = U!Sub(hi, mid)
                    /\ hi = d \/ U!Le(hi, d)
                    /\ w.slot = L!SpecPos(U!Zero, n, lo, hi)

(* finish merges the right spine: the entry pairs are the children of the node, and the pair lands at its slot *)
ArithFinishOK(n) ==
    LET ly == ArithLay(n)
        sb == [ing |-> U!Zero, con |-> n, h |-> [off |-> U!Zero, n |-> U!Zero], stack |-> BinStack(n), wr |-> <<>>,
               root |-> <<"unset">>]
        f == FinishCall(ArithH, ly, sb, ly.ob)
    IN /\ f.res = "ok"
       /\ \A i \in 1..Len(f.wr) :
            LET w == f.wr[i]
                lo == w.l[2]
                mid == w.l[3]
                hi == w.r[3]
            IN /\ w.r[2] = mid /\ hi = n
               /\ mid = U!Add(lo, L!SpecLeft(U!Sub(hi, lo)))
               /\ w.slot = L!SpecPos(U!Zero, n, lo, hi)
       /\ IF Len(BinStack(n)) < 2 THEN TRUE ELSE f.root = <<"cv", U!Zero, n>>

Inv ==
    CASE lay.k \in {"root", "seed"} -> TRUE
      [] lay.k = "arith" -> ArithOK(lay.d, lay.n) /\ ArithFinishOK(lay.d) /\ ArithFinishOK(lay.n)
      [] lay.k = "run" ->
            /\ Shape(st, lay)
            /\ StateDet(Sym, lay, st)
            /\ WritesGenuine(lay, st)
            /\ FinishOK(Sym, lay, st)
            /\ ErrorsOK(Sym, lay, st)
            /\ st.root \notin {<<"outboard error">>, <<"stack overflow">>, <<"hasher content is not the bytes consumed">>}
=============================================================================
