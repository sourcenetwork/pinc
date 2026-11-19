---------------------------- MODULE TablePoolOps ----------------------------
(***************************************************************************)
(* The operators of the slot pool, pinc-table pool.rs (`Pool`, `Slot`),    *)
(* step for step, shared by TablePool.tla (the model check) and            *)
(* TraceTablePool.tla (the trace check).                                   *)
(*                                                                         *)
(* A state is the pool's block as the code reads it: `st` the free stack  *)
(* (n u32 entries, the first `free` of them live, the rest left as the     *)
(* code leaves them), `gen` the generation of each slot, `wr` the written  *)
(* length of each slot, `dat` the bytes of each slot (z of them, 0 before  *)
(* any write), `free`. `gm` is the largest generation: u32::MAX in the     *)
(* code, a small odd number in the model check, so that the wrapping add   *)
(* (`wrapping_add(1)`, Wrap) is reached; the parity argument of pool.rs    *)
(* needs only that gm + 1 is even. A handle is the pair (index,            *)
(* generation), any pair, so an old, a forged and an out-of-range handle   *)
(* are all arguments. A result is <<call, outcome, index, generation>>.    *)
(* A give-back that would push past the stack (into the generations)       *)
(* stops TLC with an error.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

(* Pool::new(mem, n, z) once accepted (TableBytes.tla has the refusals): stack entry k is slot n - 1 - k, so slot 0
   is on top; every generation and written length 0 *)
Pool0(n, z, gm) == [n |-> n, z |-> z, gm |-> gm,
                    st |-> [k \in 0..(n - 1) |-> n - 1 - k],
                    gen |-> [k \in 0..(n - 1) |-> 0],
                    wr |-> [k \in 0..(n - 1) |-> 0],
                    dat |-> [k \in 0..(n - 1) |-> [b \in 0..(z - 1) |-> 0]],
                    free |-> n]

(* u32::wrapping_add(1) on a generation *)
Wrap(s, g) == IF g = s.gm THEN 0 ELSE g + 1

(* Pool::live: an odd generation, an index below the capacity, the slot's generation *)
Live(s, i, g) == g % 2 = 1 /\ i < s.n /\ s.gen[i] = g

(* Pool::take: none when free is 0; else the slot on top of the stack, its generation plus one, its written
   length 0, the stack one shorter *)
Take(s) ==
    IF s.free = 0 THEN [s |-> s, r |-> <<"take", "none", -1, -1>>]
    ELSE LET top == s.free - 1
             i == s.st[top]
             g == Wrap(s, s.gen[i])
         IN [s |-> [s EXCEPT !.gen[i] = g, !.wr[i] = 0, !.free = top], r |-> <<"take", "ok", i, g>>]

(* Pool::give: Stale for a handle not live; else the generation plus one and the slot pushed at `free` *)
Give(s, i, g) ==
    IF ~Live(s, i, g) THEN [s |-> s, r |-> <<"give", "stale", i, g>>]
    ELSE IF s.free >= s.n
         THEN IF Assert(FALSE, "a give-back pushes past the free stack") THEN [s |-> s, r |-> <<"give", "ok", i, g>>]
              ELSE [s |-> s, r |-> <<"give", "ok", i, g>>]
    ELSE [s |-> [s EXCEPT !.gen[i] = Wrap(s, g), !.st[s.free] = i, !.free = s.free + 1],
          r |-> <<"give", "ok", i, g>>]

(* Pool::write: Stale before Length (more bytes than the slot); the bytes at the start of the slot, the written
   length raised to cover them *)
Write(s, i, g, d) ==
    IF ~Live(s, i, g) THEN [s |-> s, r |-> <<"write", "stale", i, g>>]
    ELSE IF Len(d) > s.z THEN [s |-> s, r |-> <<"write", "length", i, g>>]
    ELSE [s |-> [s EXCEPT !.dat[i] = [b \in 0..(s.z - 1) |-> IF b < Len(d) THEN d[b + 1] ELSE s.dat[i][b]],
                          !.wr[i] = IF Len(d) > s.wr[i] THEN Len(d) ELSE s.wr[i]],
          r |-> <<"write", "ok", i, g>>]

(* Pool::read: none for a handle not live; else the written prefix *)
Read(s, i, g) ==
    IF ~Live(s, i, g) THEN [ok |-> FALSE, d |-> <<>>]
    ELSE [ok |-> TRUE, d |-> [k \in 1..s.wr[i] |-> s.dat[i][k - 1]]]

(* two sequences are equal, element by element *)
SeqEq(a, b) == Len(a) = Len(b) /\ \A k \in 1..Len(a) : a[k] = b[k]
=============================================================================
