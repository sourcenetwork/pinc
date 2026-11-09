------------------------------ MODULE Encoder ------------------------------
(***************************************************************************)
(* The range encoder of vinc-dag (tree/encode.rs), written step for step   *)
(* on the machine integers of U64.tla: `RangeEncoder::new` and `step` (the *)
(* stack of nodes with the pre-order index, `node.hi - node.lo`,           *)
(* `left_groups`, `node.lo + left`, `node.idx + left`, `node.idx * 64`,    *)
(* `node.lo * group_len`, the capacity of the stack), `encoded_len` (the   *)
(* fold with `checked_add`) and `encode_range` (the conversions of the     *)
(* offsets and lengths to usize on a 32-bit and on a 64-bit target,        *)
(* `slice_at`, `at.checked_add`, the output buffer). Any overflow,         *)
(* underflow, shift by 64 or more or division by zero stops TLC with an    *)
(* error.                                                                  *)
(*                                                                         *)
(* The stream is specified apart from the code (SpecWalk): the pre-order   *)
(* walk of the nodes that intersect the requested group range, a parent    *)
(* node giving its 64-byte pair at 64 times its position among the         *)
(* parents (counted from the definition: the node first, the parents of    *)
(* its left subtree, then those of its right subtree) and a group giving   *)
(* its bytes, the last group the remainder of the value.                   *)
(*                                                                         *)
(* Checked by TLC (Encoder.cfg) over:                                      *)
(*  - walk: every length k * group_len + d (k <= WalkK, d in -1..1) for    *)
(*    the logs 0, 1 and 20 with every byte range between the group edges   *)
(*    and the ends of the value; the steps equal SpecWalk, the stack never *)
(*    holds more than 55 nodes, and the exact stream length is the         *)
(*    closed form len + 64 * (groups - 1) for the whole value;             *)
(*  - big: the boundary lengths 2^j - 1, 2^j, 2^j + 1 (u64::MAX among      *)
(*    them) for the logs 0, 10 and 20 with the ranges at the start, the    *)
(*    end and the middle of the value (a path of up to 110 steps, since    *)
(*    the whole stream of a layout of 2^54 groups has 2^55 steps);         *)
(*  - fold: every list of up to 3 addends from the boundary addends: the   *)
(*    checked fold fails exactly when the exact sum reaches 2^64;          *)
(*  - toolong: whether encoded_len of the whole value is EncodedTooLong,   *)
(*    from the closed form (proved against the walk above), for every      *)
(*    boundary length and every log, including the layout of u64::MAX      *)
(*    bytes with groups of 1 GiB;                                          *)
(*  - encode: encode_range into output buffers of every size around the    *)
(*    stream length, with outboard buffers of the right size and one off,  *)
(*    on a 32-bit and a 64-bit usize: OutputTooSmall exactly when the      *)
(*    buffer is smaller than the stream, the stream length otherwise, no   *)
(*    failed conversion, never RangeOutOfBounds.                           *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Vinc/Encode.lean, MachineEnc.lean,       *)
(* Bounds.lean):                                                           *)
(*   StepsOK         Encode.encRun, Encode.lockstep, Encode.encStep_size,  *)
(*                   MachineEnc.encStepM_eq, MachineEnc.encRunM_eq         *)
(*   StackOK         Bounds.encoder_stack_le                               *)
(*   TotalOK         Layout.groups_le (the closed form, with Layout.pre_length) *)
(*   FoldOK          MachineEnc.foldAdd_eq                                 *)
(*   TooLongOK       MachineEnc.encodedLen_overflows_iff                   *)
(*   EncodeOK        MachineEnc.copyLoop_eq, MachineEnc.encodeRange_exact  *)
(*   the boundary sets  Vinc.Link (Encoder boundary theorems)              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

CONSTANT WalkK

StackCap == 64
Parent == U!W(64)

(* ---- the code ---- *)

(* RangeEncoder::new: the group range and the initial stack (top first); first, last the group interval *)
NewEnc(len, log, s, e) ==
    LET r == L!GroupRange(len, log, s, e)
    IN IF "err" \in DOMAIN r THEN [err |-> "range"]
       ELSE [first |-> r.a, last |-> r.b,
             stack |-> IF U!Lt(r.a, r.b)
                       THEN <<[lo |-> U!Zero, hi |-> L!Groups(len, log), idx |-> U!Zero]>>
                       ELSE <<>>]

(* RangeEncoder::step on the node popped: the step emitted and the nodes pushed (top first) *)
StepOf(len, log, first, last, node) ==
    LET count == U!Sub64(node.hi, node.lo)
    IN IF count = U!One
       THEN [step |-> [k |-> "g", off |-> U!Mul64(node.lo, L!GroupLen(log)),
                       len |-> L!GroupSize(len, log, node.lo)],
             push |-> <<>>]
       ELSE LET left == L!LeftGroups(count)
                mid == U!Add64(node.lo, left)
                right == [lo |-> mid, hi |-> node.hi, idx |-> U!Add64(node.idx, left)]
                lft == [lo |-> node.lo, hi |-> mid, idx |-> U!Add64(node.idx, U!One)]
            IN [step |-> [k |-> "p", off |-> U!Mul64(node.idx, Parent)],
                push |-> (IF U!Lt(mid, first) \/ mid = first THEN <<>> ELSE <<lft>>)
                         \o (IF U!Lt(mid, last) THEN <<right>> ELSE <<>>)]

(* the iterator to exhaustion: the steps in order and the greatest stack depth reached; the stack has
   StackCap slots, a push beyond them is the error StackOverflow *)
RECURSIVE RunFrom(_, _, _, _, _, _, _)
RunFrom(len, log, first, last, stack, acc, mx) ==
    IF stack = <<>> THEN [steps |-> acc, max |-> mx]
    ELSE LET r == StepOf(len, log, first, last, Head(stack))
             st == r.push \o Tail(stack)
         IN IF Len(st) > StackCap THEN [steps |-> <<"stack overflow">>, max |-> 99]
            ELSE RunFrom(len, log, first, last, st, Append(acc, r.step), IF Len(st) > mx THEN Len(st) ELSE mx)

Run(len, log, s, e) ==
    LET n == NewEnc(len, log, s, e)
    IN IF "err" \in DOMAIN n THEN [err |-> "range"]
       ELSE RunFrom(len, log, n.first, n.last, n.stack, <<>>, Len(n.stack))

(* the size in bytes of a step *)
StepBytes(st) == IF st.k = "p" THEN Parent ELSE st.len

(* encoded_len: the fold with checked_add; a result or EncodedTooLong *)
RECURSIVE FoldAdd(_, _)
FoldAdd(acc, xs) ==
    IF xs = <<>> THEN [ok |-> TRUE, v |-> acc]
    ELSE LET r == U!CAdd(acc, Head(xs))
         IN IF r.ok THEN FoldAdd(r.v, Tail(xs)) ELSE [ok |-> FALSE, v |-> U!Zero]

EncodedLenOf(steps) == FoldAdd(U!Zero, [i \in 1..Len(steps) |-> StepBytes(steps[i])])

(* slice_at(data, offset, len) with a data slice of dlen bytes on a usize of `bits` bits: the conversions, the
   checked end and the bounds test; TRUE when the slice exists *)
SliceAt(dlen, offset, ln, bits) ==
    LET so == U!TryFrom(offset, bits)
        sl == U!TryFrom(ln, bits)
    IN so.ok /\ sl.ok /\ LET en == U!CAddU(so.v, sl.v, bits)
                         IN en.ok /\ U!Le(en.v, dlen)

(* the copy loop of encode_range over the steps from k on: `at` bytes written so far; the result is the bytes
   written, or the error of the first step that has no source or does not fit *)
RECURSIVE EncGo(_, _, _, _, _, _, _)
EncGo(steps, k, at, len, obLen, outLen, bits) ==
    IF k > Len(steps) THEN [ok |-> at]
    ELSE LET st == steps[k]
             src == IF st.k = "p" THEN SliceAt(obLen, st.off, Parent, bits) ELSE SliceAt(len, st.off, st.len, bits)
             en == U!CAddU(at, StepBytes(st), bits)
         IN IF ~src THEN [err |-> "range"]
            ELSE IF ~en.ok \/ U!Lt(outLen, en.v) THEN [err |-> "small"]
            ELSE EncGo(steps, k + 1, en.v, len, obLen, outLen, bits)

(* encode_range into an output of outLen bytes, with a value of len bytes and an outboard of obLen bytes
   (both lengths of slices, so below 2^bits): the result *)
EncodeRange(len, log, s, e, obLen, outLen, bits) ==
    IF ~L!NewOK(log) THEN [err |-> "group"]
    ELSE IF obLen # L!OutboardSize(len, log) THEN [err |-> "outboard"]
    ELSE LET r == Run(len, log, s, e)
         IN IF "err" \in DOMAIN r THEN [err |-> "range"]
            ELSE EncGo(r.steps, 1, U!Zero, len, obLen, outLen, bits)

(* ---- the specification, apart from the code ---- *)

(* the nodes [a, b) that intersect the group interval [first, last) *)
Inter(a, b, first, last) == U!Lt(a, last) /\ U!Lt(first, b)

(* the stream of the node [a, b) of a tree of n groups with idx the position of the node among the parents:
   the node's pair, then the stream of the left child, then that of the right child, restricted to the
   children that intersect the interval *)
RECURSIVE SpecWalk(_, _, _, _, _, _, _, _)
SpecWalk(len, log, n, a, b, idx, first, last) ==
    IF U!Sub(b, a) = U!One
    THEN <<[k |-> "g", off |-> U!Shl(a, 10 + log),
            len |-> IF U!Add(a, U!One) = n THEN U!Sub(len, U!Shl(a, 10 + log)) ELSE U!Pw(10 + log)]>>
    ELSE LET m == U!Add(a, L!SpecLeft(U!Sub(b, a)))
         IN <<[k |-> "p", off |-> U!Shl(idx, 6)]>>
            \o (IF Inter(a, m, first, last)
                THEN SpecWalk(len, log, n, a, m, U!Add(idx, U!One), first, last) ELSE <<>>)
            \o (IF Inter(m, b, first, last)
                THEN SpecWalk(len, log, n, m, b, U!Add(U!Add(idx, U!One), L!SpecParents(U!Sub(m, a))),
                              first, last) ELSE <<>>)

SpecSteps(len, log, s, e) ==
    LET r == L!GroupRange(len, log, s, e)
        n == L!Groups(len, log)
    IN IF U!Lt(r.a, r.b) THEN SpecWalk(len, log, n, U!Zero, n, U!Zero, r.a, r.b) ELSE <<>>

(* the exact sum of a list of addends from k on, and the exact length in bytes of a list of steps *)
RECURSIVE SumList(_, _)
SumList(xs, k) == IF k > Len(xs) THEN U!Zero ELSE U!Add(xs[k], SumList(xs, k + 1))
SumExact(steps) == SumList([i \in 1..Len(steps) |-> StepBytes(steps[i])], 1)

(* the whole value: the stream is the value and one pair per parent *)
FullTotal(len, log) == U!Add(len, U!Shl(L!SpecParents(L!Groups(len, log)), 6))

(* ---- the properties ---- *)

WalkOK(len, log, s, e) ==
    LET r == Run(len, log, s, e)
        range == L!GroupRange(len, log, s, e)
    IN IF "err" \in DOMAIN range THEN r = [err |-> "range"]
       ELSE /\ r.steps = SpecSteps(len, log, s, e)                                      \* StepsOK
            /\ r.max <= 55                                                              \* StackOK
            /\ LET fold == EncodedLenOf(r.steps)
                   total == SumExact(r.steps)
               IN /\ (fold.ok <=> U!Fits(total)) /\ (fold.ok => fold.v = total)         \* FoldOK
                  /\ (s = U!Zero /\ e = len) => total = FullTotal(len, log)             \* TotalOK

FoldOK(xs) ==
    LET r == FoldAdd(U!Zero, xs)
        total == SumList(xs, 1)
    IN /\ (r.ok <=> U!Fits(total)) /\ (r.ok => r.v = total)

(* encoded_len of the whole value: the stream is the value and one pair per parent, and the checked fold over the
   stream fails exactly when that exact total reaches 2^64 (FoldOK); the total itself is the sum of the steps of
   the walk for every layout the walk can run (WalkOK) *)
TooLongOK(len, log) ==
    LET n == L!Groups(len, log)
        r == FoldAdd(U!Zero, <<len, U!Shl(L!SpecParents(n), 6)>>)
    IN /\ U!Le(n, U!Pw(54))
       /\ (r.ok <=> U!Lt(FullTotal(len, log), U!Pw(64)))
       /\ (len = U!Max64 /\ log = 20 => ~r.ok)

EncodeOK(len, log, s, e, bits) ==
    LET r == Run(len, log, s, e)
        ob == L!OutboardSize(len, log)
    IN IF "err" \in DOMAIN r THEN EncodeRange(len, log, s, e, ob, U!Zero, bits) = [err |-> "range"]
       ELSE LET total == SumExact(r.steps)
                cand == {U!Zero, U!Shl(total, 1), U!Add(total, U!One), total}
                        \cup (IF total # U!Zero THEN {U!Sub(total, U!One)} ELSE {})
            IN \A out \in {o \in cand : U!Lt(o, U!Pw(bits))} :
                 /\ IF U!Lt(out, total) THEN EncodeRange(len, log, s, e, ob, out, bits) = [err |-> "small"]
                    ELSE EncodeRange(len, log, s, e, ob, out, bits) = [ok |-> total]
                 /\ EncodeRange(len, log, s, e, U!Add(ob, U!One), out, bits) = [err |-> "outboard"]

(* ---- the bounded domain ---- *)

EdgeVal(j, d) == L!EdgeVal(j, d)
EdgeOK(j, d) == L!EdgeOK(j, d)
MultVal(k, d, log) == L!MultVal(k, d, log)

(* byte offsets of interest: the group edges (a group boundary and one byte on each side), the ends and the middle *)
Offs(len, log) == L!Offsets(len, log)

(* the narrow ranges of a big layout: one byte at the start, at the end and in the middle, the empty range *)
Narrow(len) ==
    {<<U!Zero, U!One>>, <<U!Zero, U!Zero>>, <<U!Sub(len, U!One), len>>,
     <<U!Shr(len, 1), U!Add(U!Shr(len, 1), U!One)>>}

Addends == {U!Zero, U!One, Parent, U!Pw(63), U!Sub(U!Pw(63), U!One), U!Max64, U!Pw(32), U!Sub(U!Pw(64), Parent)}

RECURSIVE Lists(_)
Lists(k) == IF k = 0 THEN {<<>>} ELSE {<<a>> \o l : a \in Addends, l \in Lists(k - 1)}

(* The cases are the states of one machine, so TLC enumerates them without building a set of all of them: the
   root state has one successor per seed, and a seed has one successor per case, so the cases are generated and
   checked by all the workers at once. *)
Seeds ==
    {[f |-> "walk", k |-> k, d |-> d, log |-> log] : k \in 0..WalkK, d \in -1..1, log \in {0, 1, 20}}
    \cup {[f |-> "big", j |-> j, d |-> d, log |-> log] :
           j \in 0..64, d \in -1..1, log \in {0, 10, 20}}
    \cup {[f |-> "fold", a |-> a] : a \in Addends}
    \cup {[f |-> "toolong", j |-> j, d |-> d] : j \in 0..64, d \in -1..1}
    \cup {[f |-> "toolongk", k |-> k, d |-> d] : k \in 0..30, d \in -1..1}
    \cup {[f |-> "encode", k |-> k, d |-> d, log |-> log, bits |-> bits] :
           k \in 0..4, d \in -1..1, log \in {0, 1}, bits \in {32, 64}}
    \cup {[f |-> "encbig", j |-> j, d |-> d, log |-> log, bits |-> bits] :
           j \in 0..64, d \in -1..1, log \in {0, 20}, bits \in {32, 64}}

Expand(sd) ==
    CASE sd.f = "walk" ->
            LET len == MultVal(sd.k, sd.d, sd.log)
            IN {[t |-> "walk", len |-> len, log |-> sd.log, s |-> s, e |-> e] : s \in Offs(len, sd.log), e \in Offs(len, sd.log)}
      [] sd.f = "big" ->
            IF EdgeOK(sd.j, sd.d)
            THEN LET len == EdgeVal(sd.j, sd.d)
                 IN {[t |-> "walk", len |-> len, log |-> sd.log, s |-> r[1], e |-> r[2]] : r \in Narrow(len)}
            ELSE {}
      [] sd.f = "fold" ->
            {[t |-> "fold", xs |-> <<sd.a>> \o l] : l \in Lists(0) \cup Lists(1) \cup Lists(2)}
            \cup (IF sd.a = U!Zero THEN {[t |-> "fold", xs |-> <<>>]} ELSE {})
      [] sd.f = "toolong" ->
            IF EdgeOK(sd.j, sd.d)
            THEN {[t |-> "toolong", len |-> EdgeVal(sd.j, sd.d), log |-> log] : log \in 0..20}
            ELSE {}
      [] sd.f = "toolongk" -> {[t |-> "toolong", len |-> MultVal(sd.k, sd.d, log), log |-> log] : log \in 0..20}
      [] sd.f = "encode" ->
            LET len == MultVal(sd.k, sd.d, sd.log)
            IN {[t |-> "encode", len |-> len, log |-> sd.log, s |-> s, e |-> e, bits |-> sd.bits] :
                  s \in Offs(len, sd.log), e \in Offs(len, sd.log)}
      [] sd.f = "encbig" ->
            IF EdgeOK(sd.j, sd.d) /\ U!Lt(EdgeVal(sd.j, sd.d), U!Pw(sd.bits))
            THEN LET len == EdgeVal(sd.j, sd.d)
                 IN {[t |-> "encode", len |-> len, log |-> sd.log, s |-> r[1], e |-> r[2], bits |-> sd.bits] : r \in Narrow(len)}
            ELSE {}

VARIABLE c
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ \E x \in Expand(c.sd) : c' = x
Spec == Init /\ [][Next]_c

Inv ==
    CASE c.t \in {"root", "seed"} -> TRUE
      [] c.t = "walk" -> WalkOK(c.len, c.log, c.s, c.e)
      [] c.t = "fold" -> FoldOK(c.xs)
      [] c.t = "toolong" -> TooLongOK(c.len, c.log)
      [] c.t = "encode" -> EncodeOK(c.len, c.log, c.s, c.e, c.bits)
=============================================================================
