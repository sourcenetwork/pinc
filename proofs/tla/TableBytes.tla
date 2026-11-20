------------------------------ MODULE TableBytes ------------------------------
(***************************************************************************)
(* The block sizes of pinc-table, written step for step on the machine     *)
(* integers of U64.tla, on a usize of 32 and of 64 bits: `Array::bytes`,   *)
(* `Ring::bytes`, `Pool::bytes`, `SortedSlab::bytes` (with `width`), the   *)
(* refusals of `Array::new`, `Ring::new`, `Pool::new`, `SortedSlab::new`   *)
(* and `storage::fit` (storage.rs, `no_block_holds`), `Storage::zeroed`,   *)
(* and the plain `+` and `*` the tables compute on their sizes after they  *)
(* are made (a plain operation that overflows stops TLC with an error).    *)
(*                                                                         *)
(* The specification is stated apart from the code, with exact arithmetic *)
(* (no saturation): the need of a table is capacity * (record + the bytes  *)
(* each entry costs beside it), as each `bytes` documents: 3 for the array *)
(* (2 of order, 1 of presence), 0 for the ring, 12 for the pool (stack,    *)
(* generation, written length), the index entry for the slab (2 bytes up   *)
(* to 65,535 records, 4 above; the record is key + value).                 *)
(*                                                                         *)
(* Checked by TLC (TableBytes.cfg), for each table, each width and every   *)
(* capacity and record size of the boundary sets below, in every case:     *)
(*  - BytesOK: `bytes` is the exact need when it is below 2^bits, and      *)
(*    saturates at usize::MAX otherwise ("Saturates at usize::MAX");       *)
(*  - NewOK: `new` accepts exactly when the capacity is one the table can  *)
(*    number (array: at most 65,535 places; pool: slots and slot size at   *)
(*    most u32::MAX; slab: capacity at most u32::MAX and key + value below *)
(*    2^bits), the exact need is at most isize::MAX, and the block holds   *)
(*    it; Capacity for the first two, Storage with the exact need for the  *)
(*    third, so the need a refusal reports is never a saturated one; for   *)
(*    blocks of 0, need - 1, need, need + 1 and isize::MAX bytes;          *)
(*  - LayoutOK: in an accepted table the regions each `bytes` documents    *)
(*    tile the first `bytes` bytes of the block exactly, the offsets the   *)
(*    code computes with a plain `+` or `*` (`places * 3`,                 *)
(*    `2 * slots + i`, `slots * OVERHEAD`, `cap * rsize`, `klen + vlen`)   *)
(*    do not overflow, and every slot or place number fits the entry that  *)
(*    stores it (u16 order, u32 stack, 2- or 4-byte slab index);           *)
(*  - ZeroedOK: `Storage::zeroed` refuses exactly the lengths above        *)
(*    isize::MAX.                                                          *)
(* TableBytes_sat is a reachability witness: a table whose capacity the    *)
(* index can number but whose size does not fit saturates `bytes`.         *)
(*                                                                         *)
(* Boundary sets: capacities 2^j - 1, 2^j, 2^j + 1 for j in CapJ (with     *)
(* 65,535 and 65,536, u32::MAX and 2^32, isize::MAX and usize::MAX);       *)
(* record sizes 2^j - 1, 2^j, 2^j + 1 for j in RecJ and the sizes that     *)
(* make record + overhead exactly 2^j for j in TightJ (so the need lands   *)
(* exactly on 2^(bits-1) and 2^bits); slab key and value lengths from KVs  *)
(* and the tight ones; all below 2^bits.                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

MaxU(bits) == U!Sub(U!Pw(bits), U!One)
IsizeMax(bits) == U!Sub(U!Pw(bits - 1), U!One)

(* a.saturating_add(b) on a usize *)
SatAddU(a, b, bits) == LET x == U!Add(a, b) IN IF U!Lt(x, U!Pw(bits)) THEN x ELSE MaxU(bits)

(* a * n for a native n below 2^15, limb by limb (a limb times n plus the carry stays below 2^31); exact while the
   product is below 2^80 *)
RECURSIVE MulSmallAt(_, _, _, _)
MulSmallAt(a, n, k, cy) ==
    IF k > 5 THEN <<>>
    ELSE <<(a[k] * n + cy) % U!B>> \o MulSmallAt(a, n, k + 1, (a[k] * n + cy) \div U!B)

(* bits 15k .. 15k + 14 of b, as a native integer *)
Chunk(b, k) == U!Val(U!Low(U!Shr(b, 15 * k), 15))

(* the exact product a * b, for a product below 2^79 and b below 2^75: the sum of a times each 15-bit chunk of b *)
MulW(a, b) ==
    LET t(k) == U!Shl(MulSmallAt(a, Chunk(b, k), 1, 0), 15 * k)
    IN U!Add(t(0), U!Add(t(1), U!Add(t(2), U!Add(t(3), t(4)))))

(* the exact product, or `big` when it is at least 2^77 (then above every usize) *)
Prod(a, b) ==
    IF a = U!Zero \/ b = U!Zero THEN [big |-> FALSE, v |-> U!Zero]
    ELSE IF U!BitLen(a) + U!BitLen(b) > 79 THEN [big |-> TRUE, v |-> U!Zero]
    ELSE [big |-> FALSE, v |-> MulW(a, b)]

(* the product is below 2^w *)
Below2(p, w) == ~p.big /\ U!Lt(p.v, U!Pw(w))

(* a.saturating_mul(b) and a plain a * b on a usize *)
SatMulU(a, b, bits) == LET p == Prod(a, b) IN IF Below2(p, bits) THEN p.v ELSE MaxU(bits)
MulU(a, b, bits) == LET p == Prod(a, b) IN IF Below2(p, bits) THEN p.v ELSE U!Panic("usize multiplication overflows")

(* ---- the code ---- *)

(* SortedSlab::width *)
Width(n) == IF U!Le(n, U!W(65535)) THEN 2 ELSE 4

(* a case: the table, its capacity n, its record size r (key length k and value length v for the slab) *)
Bytes(x, bits) ==
    CASE x.kind = "array" -> SatMulU(x.n, SatAddU(x.r, U!W(3), bits), bits)
      [] x.kind = "ring" -> SatMulU(x.n, x.r, bits)
      [] x.kind = "pool" -> SatMulU(x.n, SatAddU(x.r, U!W(12), bits), bits)
      [] x.kind = "slab" -> SatMulU(x.n, SatAddU(SatAddU(x.k, x.v, bits), U!W(Width(x.n)), bits), bits)

Cap == [e |-> "capacity", need |-> U!Zero]

(* storage::fit: a need above isize::MAX is Capacity, a block shorter than the need is Storage *)
Fit(need, len, bits) ==
    IF ~U!Lt(need, U!Pw(bits - 1)) THEN Cap
    ELSE IF U!Lt(len, need) THEN [e |-> "storage", need |-> need]
    ELSE [e |-> "ok", need |-> U!Zero]

(* the refusals of each `new`, in the code's order, with the table's bytes b *)
NewB(x, b, len, bits) ==
    CASE x.kind = "array" -> IF ~U!TryFrom(x.n, 16).ok THEN Cap ELSE Fit(b, len, bits)
      [] x.kind = "ring" -> Fit(b, len, bits)
      [] x.kind = "pool" -> IF ~U!TryFrom(x.n, 32).ok \/ ~U!TryFrom(x.r, 32).ok THEN Cap ELSE Fit(b, len, bits)
      [] x.kind = "slab" -> IF ~U!TryFrom(x.n, 32).ok \/ ~U!CAddU(x.k, x.v, bits).ok THEN Cap ELSE Fit(b, len, bits)
New(x, len, bits) == NewB(x, Bytes(x, bits), len, bits)

(* Storage::zeroed *)
Zeroed(len, bits) == IF ~U!Lt(len, U!Pw(bits - 1)) THEN "capacity" ELSE "ok"

(* ---- the specification ---- *)

Ovh(x) == CASE x.kind = "array" -> 3 [] x.kind = "ring" -> 0 [] x.kind = "pool" -> 12 [] x.kind = "slab" -> Width(x.n)
RecLen(x) == IF x.kind = "slab" THEN U!Add(x.k, x.v) ELSE x.r
Exact(x) == Prod(x.n, U!Add(RecLen(x), U!W(Ovh(x))))

(* the capacity is one the table can number *)
Bound(x, bits) ==
    CASE x.kind = "array" -> U!Le(x.n, U!W(65535))
      [] x.kind = "ring" -> TRUE
      [] x.kind = "pool" -> U!Lt(x.n, U!Pw(32)) /\ U!Lt(x.r, U!Pw(32))
      [] x.kind = "slab" -> U!Lt(x.n, U!Pw(32)) /\ U!Lt(RecLen(x), U!Pw(bits))

SpecNewE(x, ex, len, bits) ==
    IF ~Bound(x, bits) \/ ~Below2(ex, bits - 1) THEN Cap
    ELSE IF U!Lt(len, ex.v) THEN [e |-> "storage", need |-> ex.v]
    ELSE [e |-> "ok", need |-> U!Zero]
SpecNew(x, len, bits) == SpecNewE(x, Exact(x), len, bits)

(* the block lengths a case is checked with: 0, need - 1, need, need + 1 and isize::MAX, as long as a slice can
   have that length *)
Lens(need, bits) ==
    {l \in {U!Zero, need, U!Add(need, U!One), IsizeMax(bits)} \cup (IF need = U!Zero THEN {} ELSE {U!Sub(need, U!One)}) :
        U!Le(l, IsizeMax(bits))}

(* the layout of an accepted table, with its bytes b *)
LayoutOK(x, b, bits) ==
    CASE x.kind = "array" ->
            LET two == MulU(x.n, U!W(2), bits)
                three == MulU(x.n, U!W(3), bits)
            IN /\ U!Add2(three, MulU(x.n, x.r, bits), bits) = b
               /\ x.n # U!Zero => /\ U!Lt(U!Add2(two, U!Sub(x.n, U!One), bits), three)
                                  /\ U!Lt(U!Sub(x.n, U!One), U!Pw(16))
      [] x.kind = "ring" -> MulU(x.n, x.r, bits) = b
      [] x.kind = "pool" ->
            /\ U!Add2(MulU(x.n, U!W(12), bits), MulU(x.n, x.r, bits), bits) = b
            /\ x.n # U!Zero => /\ U!Lt(U!Add2(MulU(U!W(2), x.n, bits), U!Sub(x.n, U!One), bits),
                                       MulU(x.n, U!W(3), bits))
                               /\ U!Lt(U!Sub(x.n, U!One), U!Pw(32))
            /\ U!Lt(x.r, U!Pw(32))
      [] x.kind = "slab" ->
            LET rs == U!Add2(x.k, x.v, bits)
            IN /\ U!Add2(MulU(x.n, rs, bits), MulU(x.n, U!W(Width(x.n)), bits), bits) = b
               /\ x.n # U!Zero => U!Lt(U!Sub(x.n, U!One), U!Pw(8 * Width(x.n)))

CaseOK(x, bits) ==
    LET b == Bytes(x, bits)
        ex == Exact(x)
    IN /\ b = IF Below2(ex, bits) THEN ex.v ELSE MaxU(bits)
       /\ \A l \in Lens(b, bits) : NewB(x, b, l, bits) = SpecNewE(x, ex, l, bits)
       /\ (Bound(x, bits) /\ Below2(ex, bits - 1)) => LayoutOK(x, b, bits)

(* ---- the cases ---- *)

Edge(j, d) == CASE d = -1 -> U!Sub(U!Pw(j), U!One) [] d = 0 -> U!Pw(j) [] d = 1 -> U!Add(U!Pw(j), U!One)
Below(xs, bits) == {y \in xs : U!Lt(y, U!Pw(bits))}

CapJ == {0, 1, 2, 15, 16, 17, 30, 31, 32, 33, 62, 63, 64}
RecJ == {0, 1, 4, 16, 31, 32, 63, 64}
TightJ == {4, 29, 30, 31, 60, 61, 62, 63, 64}

Caps(bits) == Below({Edge(j, d) : j \in CapJ, d \in -1..1}, bits)
Recs(ovh, bits) == Below({Edge(j, d) : j \in RecJ, d \in -1..1} \cup {U!Sub(U!Pw(j), U!W(ovh)) : j \in TightJ}, bits)
KVs(bits) == Below({U!Zero, U!One, U!W(4), U!Pw(31), U!Sub(U!Pw(32), U!One), U!Sub(U!Pw(63), U!One), U!Pw(63),
                    U!Max64}, bits)
SlabKV(bits) ==
    {<<ka, va>> : ka \in KVs(bits), va \in KVs(bits)}
    \cup {<<ka, U!Zero>> : ka \in Below({U!Sub(U!Pw(j), U!W(w)) : j \in TightJ, w \in {2, 4}}, bits)}
ZLens(bits) == {U!Zero, U!One, IsizeMax(bits), U!Pw(bits - 1), U!Add(U!Pw(bits - 1), U!One), MaxU(bits)}

Ovh0(kd) == CASE kd = "array" -> 3 [] kd = "ring" -> 0 [] kd = "pool" -> 12

(* The cases are the states of one machine, so TLC enumerates them without building a set of all of them. *)
Seeds ==
    (UNION {{[f |-> "new", kind |-> kd, bits |-> bits, n |-> n] : n \in Caps(bits)} :
              kd \in {"array", "ring", "pool", "slab"}, bits \in {32, 64}})
    \cup {[f |-> "zeroed", kind |-> "none", bits |-> bits, n |-> U!Zero] : bits \in {32, 64}}

Expand(sd) ==
    CASE sd.f = "new" /\ sd.kind = "slab" ->
            {[t |-> "case", bits |-> sd.bits, x |-> [kind |-> "slab", n |-> sd.n, r |-> U!Zero, k |-> kv[1], v |-> kv[2]]] :
               kv \in SlabKV(sd.bits)}
      [] sd.f = "new" /\ sd.kind # "slab" ->
            {[t |-> "case", bits |-> sd.bits, x |-> [kind |-> sd.kind, n |-> sd.n, r |-> r, k |-> U!Zero, v |-> U!Zero]] :
               r \in Recs(Ovh0(sd.kind), sd.bits)}
      [] sd.f = "zeroed" -> {[t |-> "zeroed", bits |-> sd.bits, len |-> l] : l \in ZLens(sd.bits)}

VARIABLE c
Init == c = [t |-> "root"]
Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ \E y \in Expand(c.sd) : c' = y
Spec == Init /\ [][Next]_c

Inv ==
    CASE c.t \in {"root", "seed"} -> TRUE
      [] c.t = "case" -> CaseOK(c.x, c.bits)
      [] c.t = "zeroed" -> (Zeroed(c.len, c.bits) = "ok") = U!Le(c.len, IsizeMax(c.bits))

\* a reachability witness: a capacity the table can number whose size does not fit saturates `bytes`
NoSaturation == c.t = "case" => (~Bound(c.x, c.bits) \/ Bytes(c.x, c.bits) # MaxU(c.bits))
=============================================================================
