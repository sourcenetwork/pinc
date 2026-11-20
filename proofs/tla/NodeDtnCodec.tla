----------------------------- MODULE NodeDtnCodec -----------------------------
(***************************************************************************)
(* The byte formats of pinc-node's delay-tolerant layer: the resume        *)
(* records of dtn_save.rs (`restore_one`'s parse, `check_runs`,            *)
(* `take_runs`, the writers `dtn_save_held`, `dtn_save_received`,          *)
(* `dtn_save_partial`, `put_head`) and the frames of dtn_wire.rs (`start`, *)
(* `finish`, `next`, `take_u64`, `take_u16`), with the operators of        *)
(* NodeDtnCodecOps.tla.                                                    *)
(*                                                                         *)
(* Each case is a state of a machine whose root has one successor per      *)
(* case; Part picks the cases of a config:                                 *)
(*  - "record": every record the writers make over the boundary values     *)
(*    (copies 0, 1, 65535; custody; algorithm tags 1 and 4; bytes and      *)
(*    expiry 0, 1, u64::MAX; each head of HEADS; partials with none, one   *)
(*    and two runs), every proper prefix of one record of each kind, and   *)
(*    each byte of those changed to 0, 1, 2, 3, 5 or 255, or one byte      *)
(*    added at the end;                                                    *)
(*  - "runs": the runs of a partial record over a bundle of TOTAL bytes in *)
(*    slices of SLICE: every header (a, b) from 0, 1, 2, 4, 5, u64::MAX    *)
(*    alone and after each run the writer can make, and a torn tail (a     *)
(*    prefix of a run cut 1, 7, 8, 9, 15 or 16 bytes in, or one byte short)*)
(*    after none or one whole run;                                         *)
(*  - "frame": a frame of type 0, 1, 5, 255 with a body of 0, 1, 16,       *)
(*    BODY_MAX - 1, BODY_MAX, BODY_MAX + 1, 2^24, 2^32 - 1, 2^32 and 2^40  *)
(*    bytes (the input as its first bytes and its length: `next` reads     *)
(*    only the header), whole with 0, 1 or 7 bytes after it and cut at 0,  *)
(*    1, 4, 5 bytes and one byte short; and take_u64 and take_u16 on whole *)
(*    and short inputs.                                                    *)
(*                                                                         *)
(* Checked (the documentation of dtn_save.rs and dtn_wire.rs):             *)
(*  - RoundTrip, Sizes: a record written is read back as written; a        *)
(*    received record is 10 bytes, a held one 48 plus its head;            *)
(*  - Unique, Strict: a record read is exactly the encoding of what was    *)
(*    read (no other bytes are accepted: wrong version or kind, a custody  *)
(*    byte other than 0 or 1, an unknown algorithm, a head that does not   *)
(*    verify, a byte short or a byte too many are all refused);            *)
(*  - Whole: a record that cannot be read back whole is refused, except a  *)
(*    partial record cut inside its runs, which keeps exactly the whole    *)
(*    runs before the cut; the cut record reads whole, and the runs        *)
(*    appended to it after the cut read back after the kept ones;          *)
(*  - RunsSpec, CheckSpec, CheckThenTake, CutWhole: the runs are taken     *)
(*    whole and in order, a bad header or an unaligned whole run refuses   *)
(*    the record, a torn last run is left out; the check made before the   *)
(*    ledger is charged accepts only runs the read then takes;             *)
(*  - FrameOK, FrameWait, FrameBreak, NeverPast, TakeRight: a parser takes *)
(*    a frame only when it is whole and never reads past it; a frame       *)
(*    announcing a body over BODY_MAX is a protocol break (also a frame    *)
(*    whose body passes u32::MAX, whose length saturates).                 *)
(* NodeDtnCodec_agree.cfg checks Agree, that the check and the read accept *)
(* the same runs: with fix N5 both read a header with one parser, and a    *)
(* torn last run whose whole header is not on a slice refuses the record   *)
(* in both. Before N5 the read left such a run out while the check refused *)
(* it (the finding).                                                       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Nanos
CONSTANTS Part, HEADS, TOTAL, SLICE
VARIABLE c

INSTANCE NodeDtnCodecOps

\* the model's domains: two heads of different lengths, a bundle of two slices of two bytes
HeadsDef == {<<9, 9, 9>>, <<7>>}
TotalDef == W(4)
SliceDef == W(2)

BYTES == {0, 1, 2, 3, 5, 255}
Key == [j \in 1..32 |-> j]
AHead == CHOOSE h \in HEADS : \A g \in HEADS : Len(g) <= Len(h)
\* a run from a to b (native) with data bytes that name their place
R(a, b) == [a |-> W(a), b |-> W(b), data |-> [j \in 1..(b - a) |-> 100 + a + j]]

(***************************************************************************)
(* Records                                                                 *)
(***************************************************************************)
RunLists == {<<>>, <<R(0, 2)>>, <<R(0, 2), R(2, 4)>>}
Bases == {Received(e) : e \in {Zero, One, U!Max64}}
         \cup {Held(cp, cu, al, Key, by, hd) : cp \in {0, 1, 65535}, cu \in BOOLEAN, al \in {1, 4},
                                              by \in {Zero, U!Max64}, hd \in HEADS}
         \cup {Partial(hd, RunsBytes(rs)) : hd \in HEADS, rs \in RunLists}
\* one record of each kind whose prefixes and changed bytes are cases
Scanned == {[x |-> Received(W(77)), rs |-> <<>>],
            [x |-> Held(1, TRUE, 1, Key, One, AHead), rs |-> <<>>],
            [x |-> Partial(AHead, RunsBytes(<<R(0, 2), R(2, 4)>>)), rs |-> <<R(0, 2), R(2, 4)>>]}

RecCases ==
    {[t |-> "base", x |-> x, rs |-> <<>>, b |-> EncOf(x)] : x \in Bases}
    \cup (UNION {{[t |-> "cut", x |-> s.x, rs |-> s.rs, b |-> SubSeq(EncOf(s.x), 1, n)] :
                  n \in 0..(Len(EncOf(s.x)) - 1)} : s \in Scanned})
    \cup (UNION {{[t |-> "other", x |-> s.x, rs |-> s.rs, b |-> [EncOf(s.x) EXCEPT ![j] = v]] :
                  j \in 1..Len(EncOf(s.x)), v \in BYTES} : s \in Scanned})
    \cup {[t |-> "other", x |-> s.x, rs |-> s.rs, b |-> EncOf(s.x) \o <<0>>] : s \in Scanned}

(***************************************************************************)
(* Runs                                                                    *)
(***************************************************************************)
Vals == {Zero, One, W(2), W(4), W(5), U!Max64}
\* a header passes the first test of take_runs; and lies on slices
Fit(r) == Lt(r.a, r.b) /\ Le(r.b, TOTAL)
OnSlice(r) == U!IsMultipleOf(r.a, SLICE) /\ U!IsMultipleOf(r.b, SLICE)
\* a run with header (a, b), and its data when the header fits
Run(a, b) == [a |-> a, b |-> b,
              data |-> IF Lt(a, b) /\ Le(b, TOTAL) THEN [j \in 1..U!Val(U!Sub(b, a)) |-> 200 + j] ELSE <<>>]
AllRuns == {Run(a, b) : a, b \in Vals}
Fitting == {r \in AllRuns : Fit(r)}
Good == {r \in Fitting : OnSlice(r)}
Cuts(r) == {k \in {1, 7, 8, 9, 15, 16, Len(RunBytes(r)) - 1} : 1 <= k /\ k < Len(RunBytes(r))}
NoRun == Run(Zero, Zero)

RunCases ==
    {[t |-> "runs", rs |-> <<r>>, r2 |-> NoRun, cut |-> 0] : r \in AllRuns}
    \cup {[t |-> "runs", rs |-> <<r, q>>, r2 |-> NoRun, cut |-> 0] : r \in Fitting, q \in AllRuns}
    \cup UNION {{[t |-> "runs", rs |-> p, r2 |-> q, cut |-> k] :
                  p \in {<<>>} \cup {<<r>> : r \in Good}, k \in Cuts(q)} : q \in AllRuns}

RunsOf(x) == RunsBytes(x.rs) \o SubSeq(RunBytes(x.r2), 1, x.cut)

\* the index of the first run that is not taken, 0 when every run is
FirstBad(rs) == IF \E j \in 1..Len(rs) : ~(Fit(rs[j]) /\ OnSlice(rs[j]))
                THEN CHOOSE j \in 1..Len(rs) : ~(Fit(rs[j]) /\ OnSlice(rs[j])) /\ \A i \in 1..(j - 1) : Fit(rs[i]) /\ OnSlice(rs[i])
                ELSE 0
\* the expected results, from the structure of the case: a tail of 16 bytes or more holds the whole header of r2
TailHdr(x) == x.cut >= 16
\* (fix N5: a torn last run whose whole header is off the slices refuses the record, as the check does)
ExpectTake(x) ==
    IF FirstBad(x.rs) # 0 THEN FALSE
    ELSE x.cut = 0 \/ ~TailHdr(x) \/ (Fit(x.r2) /\ OnSlice(x.r2))
ExpectCheck(x) ==
    IF FirstBad(x.rs) # 0 THEN FALSE
    ELSE x.cut = 0 \/ ~TailHdr(x) \/ (Fit(x.r2) /\ OnSlice(x.r2))

(***************************************************************************)
(* Frames                                                                  *)
(***************************************************************************)
BM == BODYMAX
Bodies == {Zero, One, W(16), U!Sub(BM, One), BM, U!Add(BM, One), U!Pw(24), U!Sub(U!Pw(32), One), U!Pw(32),
           U!Pw(40)}
Full(body, e) == U!Add(U!Add(W(5), body), W(e))
Short(body) == {W(0), W(1), W(4), W(5)} \cup (IF body = Zero THEN {} ELSE {U!Sub(U!Add(W(5), body), One)})
FrameCases ==
    UNION {{[t |-> "frame", ty |-> ty, body |-> body, len |-> l] :
               ty \in {0, 1, 5, 255}, l \in {Full(body, e) : e \in {0, 1, 7}} \cup Short(body)} : body \in Bodies}
\* the bytes of the input next sees: the header the writer made, as far as the input reaches
Seen(x) == SubSeq(Finish(x.ty, x.body), 1, IF Lt(x.len, W(5)) THEN U!Val(x.len) ELSE 5)
\* the length the header announces: the body, or u32::MAX for a body past it
Announced(body) == IF Lt(body, U!Pw(32)) THEN body ELSE U!Sub(U!Pw(32), One)

TakeCases ==
    {[t |-> "take", s |-> Be8(w) \o r] : w \in Vals, r \in {<<>>, <<7>>}}
    \cup {[t |-> "take", s |-> SubSeq(Be8(U!Max64), 1, k)] : k \in 0..7}
    \cup {[t |-> "take", s |-> Be2(v) \o r] : v \in {0, 1, 255, 256, 65535}, r \in {<<>>, <<7>>}}
    \cup {[t |-> "take", s |-> <<255>>]}

(***************************************************************************)
(* The machine                                                             *)
(***************************************************************************)
Cases == CASE Part = "record" -> RecCases
           [] Part = "runs" -> RunCases
           [] Part = "frame" -> FrameCases \cup TakeCases

Init == c = [t |-> "root"]
Next == c.t = "root" /\ \E x \in Cases : c' = x
Spec == Init /\ [][Next]_c

IsRec == c.t \in {"base", "cut", "other"}

RoundTrip == c.t = "base" => Read(c.b) = c.x
Sizes == c.t = "base" =>
    /\ c.x.k = "received" => Len(c.b) = 10
    /\ c.x.k = "held" => Len(c.b) = 48 + Len(c.x.head)
Unique == IsRec /\ Read(c.b).ok => EncOf(Read(c.b)) = c.b
Strict == IsRec /\ Read(c.b).ok =>
    /\ c.b[1] = VERSION /\ c.b[2] \in {HELD, PARTIAL, RECEIVED}
    /\ Read(c.b).head \in HEADS \cup {<<>>}
    /\ Read(c.b).k = "held" => c.b[5] \in {0, 1} /\ c.b[6] \in ALGS /\ Read(c.b).head \in HEADS
    /\ Read(c.b).k = "partial" => Read(c.b).head \in HEADS

\* the number of runs of rs that lie whole in the first m bytes of their encoding
Kept(rs, m) == CHOOSE k \in 0..Len(rs) :
                   /\ Len(RunsBytes(SubSeq(rs, 1, k))) <= m
                   /\ k = Len(rs) \/ Len(RunsBytes(SubSeq(rs, 1, k + 1))) > m
Whole == c.t = "cut" =>
    IF c.x.k # "partial" \/ Len(c.b) < 4 + Len(c.x.head) THEN ~Read(c.b).ok
    ELSE LET runs == Read(c.b).runs
             tk == TakeRuns(runs, TOTAL, SLICE)
             k == Kept(c.rs, Len(runs))
             cutRec == SubSeq(c.b, 1, Len(c.b) - Len(tk.rest))
             cutRuns == Read(cutRec).runs
             more == RunsBytes(SubSeq(c.rs, k + 1, Len(c.rs)))
         IN /\ Read(c.b).ok /\ Read(c.b).head = c.x.head
            /\ CheckRuns(runs, TOTAL, SLICE)
            /\ tk.ok /\ tk.runs = SubSeq(c.rs, 1, k)
            /\ Read(cutRec).ok /\ TakeRuns(cutRuns, TOTAL, SLICE) = [ok |-> TRUE, runs |-> tk.runs, rest |-> <<>>]
            /\ TakeRuns(cutRuns \o more, TOTAL, SLICE) = [ok |-> TRUE, runs |-> c.rs, rest |-> <<>>]
\* the partial records of the scan: what the check accepts the read takes
PartialSafe == IsRec /\ Read(c.b).ok /\ Read(c.b).k = "partial" =>
    (CheckRuns(Read(c.b).runs, TOTAL, SLICE) => TakeRuns(Read(c.b).runs, TOTAL, SLICE).ok)

RunsSpec == c.t = "runs" =>
    LET tk == TakeRuns(RunsOf(c), TOTAL, SLICE)
    IN /\ tk.ok = ExpectTake(c)
       /\ tk.ok => tk.runs = c.rs /\ tk.rest = SubSeq(RunBytes(c.r2), 1, c.cut)
CheckSpec == c.t = "runs" => CheckRuns(RunsOf(c), TOTAL, SLICE) = ExpectCheck(c)
CheckThenTake == c.t = "runs" => (CheckRuns(RunsOf(c), TOTAL, SLICE) => TakeRuns(RunsOf(c), TOTAL, SLICE).ok)
CutWhole == c.t = "runs" =>
    LET bs == RunsOf(c)
        tk == TakeRuns(bs, TOTAL, SLICE)
    IN tk.ok => TakeRuns(SubSeq(bs, 1, Len(bs) - Len(tk.rest)), TOTAL, SLICE) = [tk EXCEPT !.rest = <<>>]
\* check_runs and take_runs accept the same runs (before fix N5 take_runs left out a torn last run off the slices)
Agree == c.t = "runs" => CheckRuns(RunsOf(c), TOTAL, SLICE) = TakeRuns(RunsOf(c), TOTAL, SLICE).ok

FrameOK == c.t = "frame" /\ Le(c.body, BM) /\ Le(U!Add(W(5), c.body), c.len) =>
    NextFrame(Seen(c), c.len) = [k |-> "ok", ty |-> c.ty, n |-> U!Add(W(5), c.body)]
FrameWait == c.t = "frame" /\ Lt(c.len, U!Add(W(5), c.body)) /\ (Lt(c.len, W(5)) \/ Le(c.body, BM)) =>
    NextFrame(Seen(c), c.len) = NoFrame
FrameBreak == c.t = "frame" /\ Lt(BM, c.body) /\ Le(W(5), c.len) =>
    NextFrame(Seen(c), c.len).k = "err"
NeverPast == c.t = "frame" =>
    LET r == NextFrame(Seen(c), c.len)
    IN r.k = "ok" => Le(r.n, c.len) /\ r.n = U!Add(W(5), Announced(c.body))
TakeRight == c.t = "take" =>
    /\ IF Len(c.s) >= 8 THEN TakeU64(c.s).ok /\ Be8(TakeU64(c.s).v) \o TakeU64(c.s).rest = c.s
       ELSE ~TakeU64(c.s).ok
    /\ IF Len(c.s) >= 2 THEN TakeU16(c.s).ok /\ Be2(TakeU16(c.s).v) \o TakeU16(c.s).rest = c.s
       ELSE ~TakeU16(c.s).ok
=============================================================================
