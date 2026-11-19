---------------------------- MODULE TraceLimitsFit ----------------------------
(***************************************************************************)
(* Trace check of Limits::check and fits on the real code: the unit test   *)
(* mem::tests::trace_limits (crates/pinc/src/mem.rs, branch                 *)
(* work9/platform) writes limits.ndjson, one line per case:                *)
(*   {name, l, pb, slot, chunk, wok, worst, fits, check}                   *)
(* l the limit set (fields conn, pool, sw, snd, streams, ast, as, tmsg,    *)
(* tlog, topics), pb the pointer width given to fits and check_for, slot   *)
(* SLOT_BYTES and chunk CHUNK_SIZE as built, wok whether worst_case is     *)
(* Some, worst its value as 15-bit limbs lowest first, fits the answer of  *)
(* fits, check "ok", "range" (a limit is out of range) or "address" (the   *)
(* sentence of the address space), name "" or the name of a case the      *)
(* operator's decision lists.                                              *)
(*                                                                         *)
(* Checked (AllOK): every case is what LimitsFitOps computes: the same     *)
(* worst case to the byte, the same fits, the same outcome of check_for.   *)
(* Covered: every named case was recorded.                                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds limits.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, Json, IOUtils, LimitsFitOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/limits.ndjson")

OK(e) == LET w == Worst(e.l, e.slot, e.chunk)
         IN /\ e.wok = w.ok
            /\ e.wok => Norm(e.worst) = w.v
            /\ e.fits = Fits(e.l, e.pb, e.slot, e.chunk)
            /\ e.check = Check(e.l, e.pb, e.slot, e.chunk)
AllOK == \A k \in 1..Len(Trace) : OK(Trace[k])

\* the cases of the operator's decision (t-99p-task-4, "Operator decision for R1")
Names == {"default-4", "default-8", "largest-4", "largest-8", "wasm-4", "wasm-8", "wasm-64-4", "wasm-65-4",
          "wasm-128-4", "wasm-128-8", "room-4", "room1-4", "room1-8", "above-ladder-8", "width-0"}
Covered == \A n \in Names : \E k \in 1..Len(Trace) : Trace[k].name = n

VARIABLE x
Init == x = 0
Next == UNCHANGED x
=============================================================================
