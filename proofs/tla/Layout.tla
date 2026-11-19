------------------------------ MODULE Layout ------------------------------
(***************************************************************************)
(* The tree layout arithmetic of pinc-dag (tree/layout.rs), written step   *)
(* for step on the machine integers of U64.tla: `Layout::new`,             *)
(* `for_group_bytes` (on a usize of 32 or 64 bits), `groups`, `depth`,     *)
(* `outboard_size`, `group_size` (the saturating multiply), `group_range`, *)
(* `left_groups` and the loop of `preorder_index`. Every `+`, `-`, `*`,    *)
(* `<<` and `/` of the code that overflows, underflows, shifts by 64 or    *)
(* more or divides by zero stops TLC with an error, so a finished model    *)
(* check shows that none is reachable in the checked domain.               *)
(*                                                                         *)
(* The specification is stated apart from the code, with exact arithmetic  *)
(* (no division, no saturation): a number of groups n is right when        *)
(* (n - 1) * group_len < len <= n * group_len; the depth d is the least    *)
(* with n <= 2^d; a node of c >= 2 groups splits at the power of two p     *)
(* with p < c <= 2p; the position of a parent among the parents is counted *)
(* from the definition (the node first, then the parents of the left       *)
(* subtree, then those of the right one) and, for small trees, by listing  *)
(* the parents in pre-order.                                               *)
(*                                                                         *)
(* Checked by TLC (Layout.cfg) over:                                       *)
(*  - every length 0..SmallLen with the group logs 0 and 1, and the        *)
(*    lengths k * group_len + d (k <= 40, d in -1..1) for every log 0..20, *)
(*    and for every j in 0..64 the lengths 2^j - 1, 2^j, 2^j + 1 (u64::MAX *)
(*    among them) with every log 0..20; group_size at the indices         *)
(*    0, 1, n - 2, n - 1, n, n + 1 and u64::MAX;                           *)
(*  - group_range over the byte offsets 0, 1, g - 1, g, g + 1, len - 1,    *)
(*    len, len + 1, len / 2 of the same layouts (every pair);              *)
(*  - left_groups of every count below 300 and of the boundary counts;     *)
(*  - preorder_index of every pair (lo, hi) of every tree of up to PreN    *)
(*    groups (the parents against the pre-order list, the other pairs for  *)
(*    termination without overflow), of every pair with hi <= 9 on trees   *)
(*    of up to 8 groups, and                                               *)
(*    of the nodes on the paths of fixed shapes (left spine, right spine,  *)
(*    alternating, and every path of up to 4 turns) of the trees of the    *)
(*    boundary sizes, whose depth reaches 54;                              *)
(*  - for_group_bytes on both usize widths, new for every log 0..70.       *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/Layout.lean, Machine.lean):         *)
(*   GroupsOK        Layout.groups_le, Machine.groupsM_eq                  *)
(*   DepthOK         Layout.depth_eq, Layout.ht_eq, Machine.depthM_eq      *)
(*   OutboardOK      Layout.outboardSize_eq, outboardSize_lt,              *)
(*                   Machine.outboardSizeM_eq                              *)
(*   GroupSizeOK     Layout.groupSize_spec, groupSize_eq,                  *)
(*                   Machine.groupSizeM_eq                                 *)
(*   GroupRangeOK    Layout.groupRange_spec, lt_groups_iff,                *)
(*                   Machine.groupRangeM_eq                                *)
(*   LeftOK          Layout.leftGroups_pos, leftGroups_lt,                 *)
(*                   le_two_leftGroups, leftGroups_max,                    *)
(*                   Machine.leftGroupsM_eq                                *)
(*   PreorderOK      Layout.preorderIndex_correct, right_child_index,      *)
(*                   left_child_index, pre_length,                         *)
(*                   Machine.preorderIndexM_eq, preorderOffset_lt          *)
(*   ForGroupBytesOK Machine.forGroupBytesM_iff                            *)
(*   NewOK           Layout.new (InvalidGroupSize above log 20)            *)
(*   the boundary sets  Pinc.Link (Layout boundary theorems)               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

CONSTANTS SmallLen, PreN

MaxLog == 20
Chunk == U!W(1024)
Sixty4 == U!W(64)
Two == U!W(2)

(* ---- the code ---- *)

(* Layout::new accepts exactly the logs up to MAX_GROUP_LOG *)
NewOK(log) == log <= MaxLog

(* Layout::group_len: CHUNK_LEN << log *)
GroupLen(log) == U!Shl64(Chunk, log)

(* Layout::groups: len / g + (0 if len is a multiple of g else 1), for the group length g (a power of two); the
   operators with a G suffix take g itself, so the builder and verifier models, which use only the group length,
   share them *)
GroupsG(len, g) == U!Add64(U!Div64(len, g), IF U!IsMultipleOf(len, g) THEN U!Zero ELSE U!One)
Groups(len, log) == GroupsG(len, GroupLen(log))

(* Layout::depth: 0 for at most one group, else 64 - (n - 1).leading_zeros() *)
Depth(len, log) ==
    LET n == Groups(len, log)
    IN IF U!Le(n, U!One) THEN 0 ELSE 64 - U!LeadingZeros(U!Sub64(n, U!One))

(* Layout::outboard_size: groups.checked_sub(1) is None for no group, else parents * 64 *)
OutboardSizeG(len, g) ==
    LET n == GroupsG(len, g)
    IN IF U!Lt(n, U!One) THEN U!Zero ELSE U!Mul64(U!Sub64(n, U!One), Sixty4)
OutboardSize(len, log) == OutboardSizeG(len, GroupLen(log))

(* Layout::group_size *)
GroupSizeG(len, g, index) ==
    LET start == U!SatMul64(index, g)
    IN IF U!Le(len, start) THEN U!Zero
       ELSE LET rest == U!Sub64(len, start) IN IF U!Lt(rest, g) THEN rest ELSE g
GroupSize(len, log, index) == GroupSizeG(len, GroupLen(log), index)

(* Layout::group_range: an error, or the pair of group indices *)
GroupRange(len, log, s, e) ==
    IF U!Lt(e, s) \/ U!Lt(len, e) THEN [err |-> "range"]
    ELSE IF s = e THEN [a |-> U!Zero, b |-> U!Zero]
    ELSE LET g == GroupLen(log)
         IN [a |-> U!Div64(s, g), b |-> U!Add64(U!Div64(U!Sub64(e, U!One), g), U!One)]

(* Layout::for_group_bytes (gb is a usize, of 32 or 64 bits in the domain): gb / 1024, the multiple and
   power-of-two tests, then chunks.trailing_zeros() into Layout::new *)
ForGroupBytes(gb) ==
    LET chunks == U!Div64(gb, Chunk)
    IN IF ~U!IsMultipleOf(gb, Chunk) \/ ~U!IsPow2(chunks) THEN [err |-> "group"]
       ELSE IF ~NewOK(U!Log2(chunks)) THEN [err |-> "group"] ELSE [log |-> U!Log2(chunks)]

(* left_groups: match count.checked_sub(1) { Some(m) if m > 0 => 1 << m.ilog2(), _ => 0 } *)
LeftGroups(count) ==
    IF U!Lt(count, U!One) THEN U!Zero
    ELSE LET m == U!Sub(count, U!One)
         IN IF m # U!Zero THEN U!Shl64(U!One, U!Ilog2(m)) ELSE U!Zero

(* preorder_index: the loop, with nlo, nhi the running node and idx the index *)
RECURSIVE PreorderGo(_, _, _, _, _, _)
PreorderGo(groups, lo, hi, nlo, nhi, idx) ==
    IF ~(nlo = lo /\ nhi = hi) /\ U!Le(Two, IF U!Lt(nhi, nlo) THEN U!Zero ELSE U!Sub(nhi, nlo))
    THEN LET left == LeftGroups(U!Sub64(nhi, nlo))
             mid == U!Add64(nlo, left)
         IN IF U!Le(hi, mid)
            THEN PreorderGo(groups, lo, hi, nlo, mid, U!Add64(idx, U!One))
            ELSE PreorderGo(groups, lo, hi, mid, nhi, U!Add64(idx, left))
    ELSE idx

PreorderIndex(groups, lo, hi) == PreorderGo(groups, lo, hi, U!Zero, groups, U!Zero)

(* ---- the specification, apart from the code ---- *)

(* the split of a node of c >= 2 groups: the p = 2^k with p < c <= 2p (unique), taken among the two powers of two
   below the bit length of c, which is where it lies, and checked against the definition *)
SpecLeft(c) ==
    LET bl == U!BitLen(c)
        q == IF U!Lt(U!Pw(bl - 1), c) THEN U!Pw(bl - 1) ELSE U!Pw(bl - 2)
    IN IF U!Lt(q, c) /\ U!Le(c, U!Shl(q, 1)) THEN q ELSE U!Panic("no power of two splits the node")

(* the number of parents of a tree of c groups *)
SpecParents(c) == IF U!Le(Two, c) THEN U!Sub(c, U!One) ELSE U!Zero

(* the position of the parent [lo, hi) among the parents of the tree [a, b), counted from the definition: the
   node itself first, then every parent of the left subtree, then those of the right one *)
RECURSIVE SpecPos(_, _, _, _)
SpecPos(a, b, lo, hi) ==
    IF a = lo /\ b = hi THEN U!Zero
    ELSE LET m == U!Add(a, SpecLeft(U!Sub(b, a)))
         IN IF U!Le(hi, m) THEN U!Add(U!One, SpecPos(a, m, lo, hi))
            ELSE U!Add(U!Add(U!One, SpecParents(U!Sub(m, a))), SpecPos(m, b, lo, hi))

(* the parents of the tree [a, b) in pre-order, as a sequence of <<lo, hi>> pairs of small native numbers *)
RECURSIVE SpecList(_, _)
SpecList(a, b) ==
    IF b - a < 2 THEN <<>>
    ELSE LET m == a + CHOOSE p \in 1..(b - a) : \E k \in 0..8 : p = 2 ^ k /\ p < b - a /\ b - a <= 2 * p
         IN <<<<a, b>>>> \o SpecList(a, m) \o SpecList(m, b)

(* ---- the properties ---- *)

GroupsOK(len, log) ==
    LET n == Groups(len, log)
        k == 10 + log
    IN /\ IF len = U!Zero THEN n = U!Zero
          ELSE /\ U!Lt(U!Shl(U!Sub(n, U!One), k), len)
               /\ U!Le(len, U!Shl(n, k))
       /\ U!Le(n, U!Pw(54))

DepthOK(len, log) ==
    LET n == Groups(len, log)
        d == Depth(len, log)
    IN IF U!Le(n, U!One) THEN d = 0
       ELSE /\ U!Le(n, U!Pw(d)) /\ U!Lt(U!Pw(d - 1), n)

OutboardOK(len, log) ==
    LET n == Groups(len, log)
        ob == OutboardSize(len, log)
    IN /\ IF n = U!Zero THEN ob = U!Zero ELSE ob = U!Shl(U!Sub(n, U!One), 6)
       /\ U!Fits(ob)

GroupSizeOK(len, log, i) ==
    LET n == Groups(len, log)
        k == 10 + log
        sz == GroupSize(len, log, i)
    IN IF U!Le(n, i) THEN sz = U!Zero
       ELSE IF U!Lt(i, U!Sub(n, U!One)) THEN sz = U!Shl(U!One, k)
       ELSE sz = U!Sub(len, U!Shl(U!Sub(n, U!One), k))

GroupRangeOK(len, log, s, e) ==
    LET r == GroupRange(len, log, s, e)
        k == 10 + log
        n == Groups(len, log)
    IN IF U!Lt(e, s) \/ U!Lt(len, e) THEN r.err = "range"
       ELSE IF s = e THEN r = [a |-> U!Zero, b |-> U!Zero]
       ELSE /\ U!Le(U!Shl(r.a, k), s) /\ U!Lt(s, U!Shl(U!Add(r.a, U!One), k))
            /\ U!Lt(U!Shl(U!Sub(r.b, U!One), k), e) /\ U!Le(e, U!Shl(r.b, k))
            /\ U!Lt(r.a, r.b) /\ U!Le(r.b, n)

LeftOK(c) ==
    LET p == LeftGroups(c)
    IN IF U!Lt(c, Two) THEN p = U!Zero
       ELSE /\ U!IsPow2(p) /\ U!Lt(p, c) /\ U!Le(c, U!Shl(p, 1))

(* the index of the parent [lo, hi) in a tree of n groups, for a node of the tree *)
PreorderNodeOK(n, lo, hi) ==
    LET idx == PreorderIndex(n, lo, hi)
    IN /\ idx = SpecPos(U!Zero, n, lo, hi)
       /\ U!Lt(idx, SpecParents(n))
       /\ U!Fits(U!Mul64(idx, Sixty4))
       /\ U!Le(U!Shl(U!Add(idx, U!One), 6), U!Shl(SpecParents(n), 6))

ForGroupBytesOK(gb) ==
    LET r == ForGroupBytes(gb)
        want == \E log \in 0..MaxLog : gb = U!Shl(Chunk, log)
    IN IF want THEN /\ "log" \in DOMAIN r /\ GroupLen(r.log) = gb
                    ELSE r.err = "group"

(* ---- the bounded domain ---- *)

EdgeVal(j, d) ==
    IF d = -1 THEN U!Sub(U!Pw(j), U!One) ELSE IF d = 0 THEN U!Pw(j) ELSE U!Add(U!Pw(j), U!One)
EdgeOK(j, d) == (j >= 1 \/ d >= 0) /\ (j < 64 \/ d = -1)

(* the lengths around k groups of size 2^(10 + log) *)
MultVal(k, d, log) ==
    IF d = -1 THEN (IF k = 0 THEN U!Zero ELSE U!Sub(U!Shl(U!W(k), 10 + log), U!One))
    ELSE IF d = 0 THEN U!Shl(U!W(k), 10 + log)
    ELSE U!Add(U!Shl(U!W(k), 10 + log), U!One)

(* group indices of interest for a layout: 0, 1, n - 2, n - 1, n, n + 1 and u64::MAX *)
Indices(len, log) ==
    LET n == Groups(len, log)
    IN {U!Zero, U!One, U!Max64, n, U!Add(n, U!One)}
       \cup (IF U!Le(U!One, n) THEN {U!Sub(n, U!One)} ELSE {})
       \cup (IF U!Le(Two, n) THEN {U!Sub(n, Two)} ELSE {})

(* byte offsets of interest for a layout: the group edges, the ends and the middle of the value *)
Offsets(len, log) ==
    LET g == GroupLen(log)
    IN {U!Zero, U!One, len, U!Shr(len, 1)}
       \cup (IF U!Le(U!One, len) THEN {U!Sub(len, U!One)} ELSE {})
       \cup (IF U!Lt(len, U!Max64) THEN {U!Add(len, U!One)} ELSE {})
       \cup {U!Sub(g, U!One), g, U!Add(g, U!One)}

(* the sizes of the trees of the boundary checks *)
BigN(j, d) == EdgeVal(j, d)
BigOK(j, d) == EdgeOK(j, d) /\ j >= 1 /\ j <= 54 /\ U!Le(EdgeVal(j, d), U!Pw(54))

(* the node reached from the root [0, n) by the turns ts (a sequence of "L" and "R"), stopping at a leaf *)
RECURSIVE WalkNode(_, _, _)
WalkNode(a, b, ts) ==
    IF ts = <<>> \/ U!Lt(U!Sub(b, a), Two) THEN <<a, b>>
    ELSE LET m == U!Add(a, SpecLeft(U!Sub(b, a)))
         IN IF Head(ts) = "L" THEN WalkNode(a, m, Tail(ts)) ELSE WalkNode(m, b, Tail(ts))

RECURSIVE Rep(_, _)
Rep(x, k) == IF k = 0 THEN <<>> ELSE <<x>> \o Rep(x, k - 1)
RECURSIVE Alt(_, _)
Alt(x, k) == IF k = 0 THEN <<>> ELSE <<x>> \o Alt(IF x = "L" THEN "R" ELSE "L", k - 1)

RECURSIVE TurnStrings(_)
TurnStrings(k) == IF k = 0 THEN {<<>>} ELSE {<<t>> \o s : t \in {"L", "R"}, s \in TurnStrings(k - 1)}

Shapes == {Rep("L", 60), Rep("R", 60), Alt("L", 60), Alt("R", 60)}
Paths == Shapes \cup UNION {TurnStrings(k) : k \in 1..4}

GbSet ==
    {U!Zero, U!One, U!W(1023), U!W(1025), U!W(3072), U!W(2047), U!W(2048), U!W(5120), U!Pw(40), U!Pw(63)}
    \cup UNION {{U!Shl(Chunk, k), U!Sub(U!Shl(Chunk, k), U!One), U!Add(U!Shl(Chunk, k), U!One),
                 U!Shl(U!W(3), 10 + k)} : k \in 0..22}

(* The cases are the states of one machine, so TLC enumerates them without building a set of all of them. *)
Seeds ==
    {[f |-> "small", k |-> k] : k \in 0..SmallLen}
    \cup {[f |-> "mult", k |-> k, d |-> d] : k \in 0..40, d \in -1..1}
    \cup {[f |-> "edge", j |-> j, d |-> d] : j \in 0..64, d \in -1..1}
    \cup {[f |-> "rmult", k |-> k, d |-> d, log |-> log] : k \in 0..8, d \in -1..1, log \in {0, 10, MaxLog}}
    \cup {[f |-> "redge", j |-> j, d |-> d, log |-> log] : j \in 0..64, d \in -1..1, log \in {0, 10, MaxLog}}
    \cup {[f |-> "left", k |-> k] : k \in 0..299}
    \cup {[f |-> "ledge", j |-> j, d |-> d] : j \in 0..64, d \in -1..1}
    \cup {[f |-> "pre", n |-> n] : n \in 1..PreN}
    \cup {[f |-> "pre8", n |-> n] : n \in 1..8}
    \cup {[f |-> "path", j |-> j, d |-> d] : j \in 1..54, d \in -1..1}
    \cup {[f |-> "fgb"]}
    \cup {[f |-> "new"]}

(* The quick profile (quick/Layout.cfg substitutes it for Seeds): every family of Seeds over fewer values, the
   boundary ones kept (the multiples 0..3 and 40, the powers of two around 1, 10, 31, 54, 63 and 64, the logs 0 and
   MaxLog for the ranges, the counts below 70, the trees of up to 8 groups with hi <= 9 at 1, 2, 5 and 8, the paths
   of the trees of 2, 3, 2^53 and 2^54 groups). *)
SeedsQuick ==
    {[f |-> "small", k |-> k] : k \in 0..SmallLen}
    \cup {[f |-> "mult", k |-> k, d |-> d] : k \in {0, 1, 2, 3, 40}, d \in -1..1}
    \cup {[f |-> "edge", j |-> j, d |-> d] : j \in {0, 1, 10, 11, 31, 54, 63, 64}, d \in -1..1}
    \cup {[f |-> "rmult", k |-> k, d |-> d, log |-> log] : k \in {0, 1, 3}, d \in -1..1, log \in {0, MaxLog}}
    \cup {[f |-> "redge", j |-> j, d |-> d, log |-> log] : j \in {0, 1, 11, 31, 63, 64}, d \in -1..1, log \in {0, MaxLog}}
    \cup {[f |-> "left", k |-> k] : k \in 0..70}
    \cup {[f |-> "ledge", j |-> j, d |-> d] : j \in {0, 1, 2, 31, 32, 62, 63, 64}, d \in -1..1}
    \cup {[f |-> "pre", n |-> n] : n \in 1..PreN}
    \cup {[f |-> "pre8", n |-> n] : n \in {1, 2, 5, 8}}
    \cup {[f |-> "path", j |-> j, d |-> d] : j \in {1, 2, 53, 54}, d \in -1..1}
    \cup {[f |-> "fgb"]}
    \cup {[f |-> "new"]}

Expand(sd) ==
    CASE sd.f = "small" -> {[t |-> "lay", len |-> U!W(sd.k), log |-> log] : log \in 0..1}
      [] sd.f = "mult" -> {[t |-> "lay", len |-> MultVal(sd.k, sd.d, log), log |-> log] : log \in 0..MaxLog}
      [] sd.f = "edge" ->
            IF EdgeOK(sd.j, sd.d)
            THEN {[t |-> "lay", len |-> EdgeVal(sd.j, sd.d), log |-> log] : log \in 0..MaxLog}
            ELSE {}
      [] sd.f = "rmult" ->
            LET len == MultVal(sd.k, sd.d, sd.log)
            IN {[t |-> "range", len |-> len, log |-> sd.log, s |-> s, e |-> e] :
                  s \in Offsets(len, sd.log), e \in Offsets(len, sd.log)}
      [] sd.f = "redge" ->
            IF EdgeOK(sd.j, sd.d)
            THEN LET len == EdgeVal(sd.j, sd.d)
                 IN {[t |-> "range", len |-> len, log |-> sd.log, s |-> s, e |-> e] :
                       s \in Offsets(len, sd.log), e \in Offsets(len, sd.log)}
            ELSE {}
      [] sd.f = "left" -> {[t |-> "left", n |-> U!W(sd.k)]}
      [] sd.f = "ledge" -> IF EdgeOK(sd.j, sd.d) THEN {[t |-> "left", n |-> EdgeVal(sd.j, sd.d)]} ELSE {}
      [] sd.f = "pre" ->
            {[t |-> "pre", n |-> U!W(sd.n), lo |-> U!W(lo), hi |-> U!W(hi)] : lo \in 0..sd.n, hi \in 0..sd.n}
      [] sd.f = "pre8" ->
            {[t |-> "pre", n |-> U!W(sd.n), lo |-> U!W(lo), hi |-> U!W(hi)] : lo \in 0..9, hi \in 0..9}
      [] sd.f = "path" ->
            IF BigOK(sd.j, sd.d)
            THEN {[t |-> "path", n |-> EdgeVal(sd.j, sd.d), ts |-> ts] : ts \in Paths}
            ELSE {}
      [] sd.f = "fgb" -> {[t |-> "fgb", gb |-> gb] : gb \in GbSet}
      [] sd.f = "new" -> {[t |-> "new", log |-> log] : log \in 0..70}

VARIABLE c
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ \E x \in Expand(c.sd) : c' = x
Spec == Init /\ [][Next]_c

Inv ==
    CASE c.t \in {"root", "seed"} -> TRUE
      [] c.t = "lay" ->
            /\ GroupsOK(c.len, c.log) /\ DepthOK(c.len, c.log) /\ OutboardOK(c.len, c.log)
            /\ \A i \in Indices(c.len, c.log) : GroupSizeOK(c.len, c.log, i)
      [] c.t = "range" -> GroupRangeOK(c.len, c.log, c.s, c.e)
      [] c.t = "left" -> LeftOK(c.n)
      [] c.t = "pre" ->
            LET lis == SpecList(0, U!Val(c.n))
                pair == <<U!Val(c.lo), U!Val(c.hi)>>
                idx == PreorderIndex(c.n, c.lo, c.hi)
            IN /\ U!Le(idx, c.n)
               /\ (\E k \in 1..Len(lis) : lis[k] = pair) =>
                    (\E k \in 1..Len(lis) : lis[k] = pair /\ idx = U!W(k - 1) /\ PreorderNodeOK(c.n, c.lo, c.hi))
      [] c.t = "path" ->
            LET nd == WalkNode(U!Zero, c.n, c.ts)
            IN IF U!Le(Two, U!Sub(nd[2], nd[1])) THEN PreorderNodeOK(c.n, nd[1], nd[2]) ELSE TRUE
      [] c.t = "fgb" -> ForGroupBytesOK(c.gb)
      [] c.t = "new" -> NewOK(c.log) = (c.log <= MaxLog)
=============================================================================
