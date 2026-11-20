---------------------------- MODULE TraceTablePool ----------------------------
(***************************************************************************)
(* Trace validation of the slot pool: pinc-table pool.rs.                 *)
(*                                                                         *)
(* The Rust test tests/trace_table_pool.rs drives real pools (pinc-table   *)
(* built with the cargo feature `trace` for the stack, the generations and *)
(* the written lengths) with seeded calls: takes until exhausted and past  *)
(* it, give-backs of live, given-back, old, forged and out-of-range        *)
(* handles, a second give-back, writes of 0 bytes, of a prefix, of the     *)
(* whole slot and of one byte too many, reads of every kind of handle.     *)
(* Every call must be the step the operators of TablePoolOps.tla compute,  *)
(* with the result, the handle taken and the bytes read, and the pool      *)
(* after it (free, the live stack, every generation and written length)    *)
(* must be the model's.                                                    *)
(*                                                                         *)
(* The recorded generations stay below 2^31 - 1 (the test asserts it; a    *)
(* run takes a slot a few thousand times at most), so the wrap at          *)
(* u32::MAX is not in the trace: the model check reaches it                *)
(* (TablePool_wrap.cfg) and the code's unit test sets a generation at the  *)
(* top of its range. GM here is the largest TLC integer, never reached.    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds table_pool.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLES i, s
vars == <<i, s>>
INSTANCE TablePoolOps

GMTrace == 2147483647

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/table_pool.ndjson")
Ev0 == Trace[i]

(* the recorded view: free, the live stack from the bottom, the generation and the written length of every slot *)
Same(y, v) == /\ v.free = y.free
              /\ Len(v.stack) = y.free /\ \A k \in 0..(y.free - 1) : v.stack[k + 1] = y.st[k]
              /\ Len(v.gen) = y.n /\ \A k \in 0..(y.n - 1) : v.gen[k + 1] = y.gen[k]
              /\ Len(v.written) = y.n /\ \A k \in 0..(y.n - 1) : v.written[k + 1] = y.wr[k]

InitEv == /\ Ev0.op = "init" /\ s' = Pool0(Ev0.n, Ev0.z, GMTrace) /\ Same(s', Ev0.v)
TakeEv == LET x == Take(s)
          IN /\ Ev0.op = "take" /\ x.r = <<"take", Ev0.res, Ev0.idx, Ev0.gen>> /\ s' = x.s /\ Same(s', Ev0.v)
GiveEv == LET x == Give(s, Ev0.idx, Ev0.gen)
          IN /\ Ev0.op = "give" /\ x.r[2] = Ev0.res /\ s' = x.s /\ Same(s', Ev0.v)
WriteEv == LET x == Write(s, Ev0.idx, Ev0.gen, Ev0.data)
           IN /\ Ev0.op = "write" /\ x.r[2] = Ev0.res /\ s' = x.s /\ Same(s', Ev0.v)
ReadEv == LET x == Read(s, Ev0.idx, Ev0.gen)
          IN /\ Ev0.op = "read" /\ x.ok = Ev0.ok /\ SeqEq(x.d, Ev0.data) /\ s' = s /\ Same(s', Ev0.v)

Init == i = 1 /\ s = Pool0(0, 0, GMTrace)
Step == /\ i <= Len(Trace) /\ Ev0.t = "tpool"
        /\ (InitEv \/ TakeEv \/ GiveEv \/ WriteEv \/ ReadEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the live stack holds distinct slots, and a slot is on it exactly when its generation is even
Inv == LET live == {s.st[k] : k \in 0..(s.free - 1)}
       IN /\ Cardinality(live) = s.free
          /\ \A k \in 0..(s.n - 1) : (k \in live) <=> (s.gen[k] % 2 = 0)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
