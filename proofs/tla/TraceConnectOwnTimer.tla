------------------------- MODULE TraceConnectOwnTimer -------------------------
(***************************************************************************)
(* Trace validation of the record's publish timer: pinc-connect            *)
(* client/timers.rs `publish` (140-153) and the end of `tick`, the record  *)
(* arm of client/signing.rs `sign_response` (118-136, `complete` 145-153)  *)
(* and `start_jobs` (196-212), conn.rs `set_hints` (484-492), and the      *)
(* sites that set `next_publish = now` (conn.rs 682, 807, carriers.rs 450, *)
(* 554, mapped.rs 55). The operators are those of the Lean model           *)
(* proofs/lean/Pinc/ConnectOwn.lean (`publish`, `changed`, `start`,        *)
(* `signed`, `setHints`), transcribed one for one.                         *)
(*                                                                         *)
(* The test tests/trace_connect_own_timer.rs (file connect_own_timer.ndjson)*)
(* drives a real Connectivity on the connect rig and writes one line per   *)
(* public call, with the probe `trace_publish` read before and after it:   *)
(*   {op, now, w, ok, sent, before, after}                                 *)
(* op "tick" (w: it was given a wall clock), "sign" (the answer to a       *)
(* record job: ok, a signature of the right length that finished; sent,    *)
(* the home carrier took the record), "hints" (set_hints accepted), or     *)
(* "other" (any other call). before and after are                          *)
(*   {np, want, job, wall, can}                                            *)
(* next_publish in milliseconds (u64::MAX as -1; the test's clock moves in *)
(* whole milliseconds, so every value is exact), sign.record, a record job *)
(* outstanding, a wall clock known, can_publish.                           *)
(*                                                                         *)
(* A call is one composition of the operators:                             *)
(*   tick   the wall clock; then changed or not (update_class, a home      *)
(*          found inside tick); publish with can_publish after the call;   *)
(*          start                                                          *)
(*   sign   signed; start                                                  *)
(*   hints  the record wanted                                              *)
(*   other  nothing, changed, start, changed then start, start then changed*)
(* start is open on its outcome when a record is wanted, none outstanding *)
(* and a wall clock known: a job, or (no home or class) a retry period;    *)
(* what the job holds is TraceConnectOwn's.                                *)
(*                                                                         *)
(* Checked (AllOK): the first before is the new node's state, each before  *)
(* is the previous after, and each after is one outcome of the call.       *)
(* Witness (TraceConnectOwnTimer_change.cfg, NoLostChange must fail on the *)
(* trace's fixed prefix): a change made while a record job is outstanding  *)
(* (next_publish set to now from u64::MAX) is overwritten by the answer,   *)
(* which arms the republish 1800 s on; the record that went out was built *)
(* before the change. The Lean model does the same (signed, line 165).     *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* connect_own_timer.ndjson.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, Json, IOUtils

REPUB == 1800000   \* RECORD_REPUBLISH_NS, in ms
RETRY == 2000      \* HOME_RETRY_NS, in ms
MAX == -1          \* u64::MAX

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_own_timer.ndjson")

\* the part of the probe the operators act on
P(x) == [np |-> x.np, want |-> x.want, job |-> x.job, wall |-> x.wall]
New == [np |-> 0, want |-> FALSE, job |-> FALSE, wall |-> FALSE]

Publish(s, now, can) ==
    IF s.np = 0 \/ s.np = MAX \/ now < s.np \/ s.want \/ s.job THEN s
    ELSE IF can THEN [s EXCEPT !.want = TRUE, !.np = MAX] ELSE s
Changed(s, now) == [s EXCEPT !.np = now]
Start(s, now) ==
    IF s.job \/ ~s.wall \/ ~s.want THEN {s}
    ELSE {[s EXCEPT !.want = FALSE, !.job = TRUE], [s EXCEPT !.want = FALSE, !.np = now + RETRY]}
Signed(s, now, ok, sent) ==
    IF ~s.job THEN s
    ELSE IF ok /\ sent THEN [s EXCEPT !.job = FALSE, !.np = now + REPUB]
    ELSE IF ok THEN [s EXCEPT !.job = FALSE, !.np = now]
    ELSE [s EXCEPT !.job = FALSE, !.np = now + RETRY]
StartAll(ss, now) == UNION {Start(s, now) : s \in ss}

Results(e) ==
    LET s == P(e.before)
        n == e.now
    IN CASE e.op = "tick" ->
              LET s0 == [s EXCEPT !.wall = @ \/ e.w]
              IN StartAll({Publish(c, n, e.after.can) : c \in {s0, Changed(s0, n)}}, n)
         [] e.op = "sign" -> Start(Signed(s, n, e.ok, e.sent), n)
         [] e.op = "hints" -> {[s EXCEPT !.want = TRUE]}
         [] e.op = "other" -> {s, Changed(s, n)} \cup StartAll({s, Changed(s, n)}, n)
                              \cup {Changed(x, n) : x \in Start(s, n)}
         [] OTHER -> {}

OK(k) == /\ P(Trace[k].before) = IF k = 1 THEN New ELSE P(Trace[k - 1].after)
         /\ P(Trace[k].after) \in Results(Trace[k])
AllOK == \A k \in 1..Len(Trace) : OK(k)

\* a change while a record job is outstanding, then the answer arms the republish with no record wanted in between
LostChange(j, k) ==
    /\ j < k
    /\ Trace[j].op # "sign" /\ Trace[j].before.job /\ Trace[j].before.np = MAX /\ Trace[j].after.np = Trace[j].now
    /\ Trace[k].op = "sign" /\ Trace[k].after.np = Trace[k].now + REPUB
    /\ \A m \in (j + 1)..(k - 1) : Trace[m].op # "sign"
NoLostChange == ~\E j, k \in 1..Len(Trace) : LostChange(j, k)

VARIABLE x
Init == x = 0
Next == UNCHANGED x
=============================================================================
