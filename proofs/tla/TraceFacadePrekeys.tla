-------------------------- MODULE TraceFacadePrekeys --------------------------
(***************************************************************************)
(* Trace validation of the engine's prekeys: crates/pinc/src/keys.rs       *)
(* `Prekeys` and the trigger in crates/pinc/src/engine.rs `Core::service`. *)
(*                                                                         *)
(* The unit tests `keys::tests::trace_prekeys` and                         *)
(* `engine::prekey_tests::trace_prekey_service` (they run in the build     *)
(* with `std` and in the one without) drive real `Prekeys` and a real core *)
(* with boundary and seeded calls and record every call with the state     *)
(* after it (the generations held, next, rotate_at, used). Every call must *)
(* be the step of the rule of FacadePrekeys.tla and PrekeyRotation.tla:    *)
(* Push, Holds, Newest, SatSub, Counted and Answered are reused; due and   *)
(* the rotation are the same rule over u64 words (U64.tla), because a time *)
(* and rotate_at reach u64::MAX and TLC integers are 32 bits wide: a time  *)
(* is four 16-bit limbs. The use count stays below 2^31 in the traces (the *)
(* u32 saturation is FacadePrekeys.cfg's), so the instance takes           *)
(* 2^31 - 1 for its maximum. A mismatch leaves no successor: TLC reports a *)
(* deadlock at the event.                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds prekeys.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, s
vars == <<i, s>>

U == INSTANCE U64
R == INSTANCE PrekeyRotation
P == INSTANCE FacadePrekeys WITH LIFE <- 0, USES <- 64, TOP <- 0, TS <- {}, UTOP <- 2147483647, GMAX <- 0,
                                 pk <- [held |-> <<>>, next |-> 1, at |-> 0, used |-> 0], dropped <- {}, born <- -1

\* PREKEY_LIFE = 600_000_000_000 ns and PREKEY_USES = 64
LIFEW == U!FromLimbs(<<28672, 45769, 139, 0>>)
USESN == 64
Deadline(t) == LET r == U!CAdd(t, LIFEW) IN IF r.ok THEN <<r.v>> ELSE <<>>

\* rotate_at as <<word>>, or <<>> when none (past the clock's last instant: deadline_after)
WNew == [held |-> <<>>, next |-> 1, at |-> <<U!Zero>>, used |-> 0]
\* Prekeys::due and the state after a rotation whose draws succeeded, over words
DueW(x, t) == (x.at # <<>> /\ U!Le(x.at[1], t)) \/ x.used >= USESN
RotW(x, t) == [held |-> R!Push(x.held, x.next, 2), next |-> x.next + 1, at |-> Deadline(t), used |-> 0]

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/prekeys.ndjson")
Ev == Trace[i]
Rec(st) == [held |-> st.held, next |-> st.next, at |-> IF st.at = <<>> THEN <<>> ELSE <<U!FromLimbs(st.at)>>, used |-> st.used]
Same(st) == s' = Rec(st)

NewEv == Ev.op = "new" /\ s' = WNew /\ Same(Ev.st)
\* a core's prekeys as start::build left them (one rotation at the time of the build)
LoadEv == /\ Ev.op = "load"
          /\ Len(Ev.st.held) <= 2 /\ R!Increasing(Ev.st.held)
          /\ (Ev.st.held # <<>> => R!Newest(Ev.st.held) = Ev.st.next - 1)
          /\ Same(Ev.st)
RotEv == /\ Ev.op = "rot"
         /\ IF Ev.ok THEN Ev.res /\ Ev.gen = s.next /\ s' = RotW(s, U!FromLimbs(Ev.now))
                     ELSE ~Ev.res /\ s' = s
         /\ Same(Ev.st)
DueEv == Ev.op = "due" /\ Ev.r = DueW(s, U!FromLimbs(Ev.now)) /\ s' = s
DecEv == /\ Ev.op = "dec"
         /\ Ev.ans = P!Answered(s, Ev.h, Ev.valid)
         /\ s' = P!Counted(s, Ev.h)
         /\ Same(Ev.st)
\* Core::service: the identity of the test core is in a store seeded by the host (a generator), so the fresh entropy
\* is asked for exactly once when the prekey rotates, and the draws from that store do not fail
SvcEv == /\ Ev.op = "svc"
         /\ IF DueW(s, U!FromLimbs(Ev.now)) /\ ~Ev.b
            THEN Ev.asked = 1 /\ s' = RotW(s, U!FromLimbs(Ev.now))
            ELSE Ev.asked = 0 /\ s' = s
         /\ Same(Ev.st)

Init == i = 1 /\ s = WNew
Step == /\ i <= Len(Trace) /\ Ev.t = "pk"
        /\ (NewEv \/ LoadEv \/ RotEv \/ DueEv \/ DecEv \/ SvcEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the shape the model keeps, on the recorded states
Inv == /\ Len(s.held) <= 2 /\ R!Increasing(s.held)
       /\ (s.held # <<>> => R!Newest(s.held) = s.next - 1)
=============================================================================
