------------------------------ MODULE TablePool ------------------------------
(***************************************************************************)
(* The slot pool of pinc-table (pool.rs, `Pool`: new, take, give, write,   *)
(* read, free, taken) over every sequence of calls at small sizes: S       *)
(* slots of Z bytes, generations wrapping after GM (the code's u32::MAX,   *)
(* here small so the wrap is reached), every handle (index 0..S, the last  *)
(* one past the pool, generation 0..GM: live, given back, old, forged),    *)
(* and data of 0..Z+1 bytes over the byte values 1..BV. A slot is taken at *)
(* most TMAX times (the bound of the exploration). TablePoolOps.tla has    *)
(* the operators of the code.                                              *)
(*                                                                         *)
(* The specification beside the code: `out`, the slots taken and not      *)
(* given back; `takes`, how often each slot was taken; `own`, the bytes    *)
(* the current holder of each slot wrote. A handle is accepted exactly     *)
(* when its slot is out and its generation is that of the slot's last      *)
(* take, 2 * takes - 1 modulo GM + 1 (pool.rs: the generation goes up by 2 *)
(* each time the slot is taken and given back).                            *)
(*                                                                         *)
(* Checked, in every state reached (pool.rs module comment):               *)
(*  - StackOK: the live stack holds each slot not out exactly once, so the *)
(*    free stack hands each slot out at most once (with TakeOK);           *)
(*  - Conserved: free + slots out = capacity (taken = capacity - free);    *)
(*  - ParityOK: a slot is on the free stack exactly when its generation is *)
(*    even;                                                                *)
(*  - AcceptOK: a handle is live exactly when the specification accepts    *)
(*    it, so a handle given back, given back and taken by another, or      *)
(*    forged reads and writes nothing, until its slot has been taken       *)
(*    (GM + 1) / 2 times since (2^31 in the code, error.rs `Stale`);       *)
(*  - ReadOK: `read` returns exactly the bytes the current holder wrote,   *)
(*    never a previous holder's; WrittenOK: a written length is at most   *)
(*    the slot size;                                                       *)
(*  - ResultOK: every call returns what the specification says (none only  *)
(*    when every slot is out, Stale before Length);                        *)
(* and in every step:                                                      *)
(*  - TakeOK: `take` returns a slot not out, with the generation of that   *)
(*    take;                                                                *)
(*  - RefusedUnchanged: a refused call (none, Stale, Length) changes       *)
(*    nothing.                                                             *)
(* Witnesses: TablePool_exhausted (every slot out), TablePool_wrap (a      *)
(* handle of an earlier take of its slot matches again after the wrap,     *)
(* which the documentation states).                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS S, Z, GM, TMAX, BV
VARIABLES s, out, takes, own, res, want
vars == <<s, out, takes, own, res, want>>

INSTANCE TablePoolOps

Init == /\ s = Pool0(S, Z, GM)
        /\ out = {}
        /\ takes = [k \in 0..(S - 1) |-> 0]
        /\ own = [k \in 0..(S - 1) |-> <<>>]
        /\ res = <<"init", "ok", -1>>
        /\ want = <<"init", "ok", -1>>

(* the generation of the last take of slot i, and the handles the specification accepts *)
SpecGen(i) == (2 * takes[i] - 1) % (GM + 1)
Accepts(i, g) == i \in out /\ g = SpecGen(i)

(* the bytes a write leaves for the holder: d over the start, the rest of what it wrote before *)
Over(a, d) == [k \in 1..(IF Len(d) > Len(a) THEN Len(d) ELSE Len(a)) |-> IF k <= Len(d) THEN d[k] ELSE a[k]]

Datas == UNION {[1..k -> 1..BV] : k \in 0..(Z + 1)}

DoTake ==
    LET x == Take(s)
    IN /\ x.r[2] = "none" \/ takes[x.r[3]] < TMAX
       /\ s' = x.s
       /\ res' = <<"take", x.r[2], x.r[3]>>
       /\ want' = <<"take", IF out = 0..(S - 1) THEN "none" ELSE "ok", x.r[3]>>
       /\ IF x.r[2] = "ok"
          THEN /\ out' = out \cup {x.r[3]}
               /\ takes' = [takes EXCEPT ![x.r[3]] = @ + 1]
               /\ own' = [own EXCEPT ![x.r[3]] = <<>>]
          ELSE UNCHANGED <<out, takes, own>>

DoGive(i, g) ==
    LET x == Give(s, i, g)
    IN /\ s' = x.s
       /\ res' = <<"give", x.r[2], -1>>
       /\ want' = <<"give", IF Accepts(i, g) THEN "ok" ELSE "stale", -1>>
       /\ out' = IF Accepts(i, g) THEN out \ {i} ELSE out
       /\ UNCHANGED <<takes, own>>

DoWrite(i, g, d) ==
    LET x == Write(s, i, g, d)
    IN /\ s' = x.s
       /\ res' = <<"write", x.r[2], -1>>
       /\ want' = <<"write", IF ~Accepts(i, g) THEN "stale" ELSE IF Len(d) > Z THEN "length" ELSE "ok", -1>>
       /\ own' = IF Accepts(i, g) /\ Len(d) <= Z THEN [own EXCEPT ![i] = Over(own[i], d)] ELSE own
       /\ UNCHANGED <<out, takes>>

Next == \/ DoTake
        \/ \E i \in 0..S, g \in 0..GM : DoGive(i, g)
        \/ \E i \in 0..S, g \in 0..GM, d \in Datas : DoWrite(i, g, d)
Spec == Init /\ [][Next]_vars

TypeOK == /\ s.free \in 0..S
          /\ s.st \in [0..(S - 1) -> 0..(S - 1)]
          /\ s.gen \in [0..(S - 1) -> 0..GM]
          /\ out \subseteq 0..(S - 1)
StackOK == LET live == {s.st[k] : k \in 0..(s.free - 1)}
           IN live = (0..(S - 1)) \ out /\ Cardinality(live) = s.free
Conserved == s.free + Cardinality(out) = S
ParityOK == \A k \in 0..(S - 1) : (s.gen[k] % 2 = 0) <=> (k \notin out)
AcceptOK == \A i \in 0..S, g \in 0..GM : Live(s, i, g) <=> Accepts(i, g)
ReadOK == \A i \in 0..S, g \in 0..GM :
            LET r == Read(s, i, g)
            IN IF Accepts(i, g) THEN r.ok /\ SeqEq(r.d, own[i]) ELSE ~r.ok /\ r.d = <<>>
WrittenOK == \A k \in 0..(S - 1) : s.wr[k] <= Z
ResultOK == res = want

TakeOK == [][(res'[1] = "take" /\ res'[2] = "ok")
             => (res'[3] \notin out /\ s'.gen[res'[3]] = (2 * takes'[res'[3]] - 1) % (GM + 1))]_vars
RefusedUnchanged == [][res'[2] \in {"none", "stale", "length"} => UNCHANGED <<s, out, takes, own>>]_vars

\* reachability witnesses: every slot is out; a handle of an earlier take of its slot is live again
NotExhausted == s.free > 0
NoOldMatch == \A i \in 0..(S - 1), t \in 1..(takes[i] - 1) : ~Live(s, i, (2 * t - 1) % (GM + 1))
=============================================================================
