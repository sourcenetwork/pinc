-------------------------- MODULE TraceBroadcastRepair --------------------------
(***************************************************************************)
(* Trace validation of gap repair: pinc-broadcast gap.rs `since_ms`,       *)
(* `resubscribe`, `gap_ae`, `hub_ae`, `on_have`, `on_get`, with msg.rs     *)
(* `hub_store` and log.rs behind them.                                     *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_repair.rs runs the network of       *)
(* BroadcastRepair.tla on real nodes (built with the cargo feature         *)
(* `trace`, whose probe `Topics::log_holds` says whether a hub logs a      *)
(* message): hubs 1 and 2 (nodes 0 and 1), the subscriber S (node 2, its   *)
(* primary hub 1, its link to hub 2 cut for good) and the publisher P      *)
(* (node 3), started at time 0, time in whole seconds. The test cuts and   *)
(* heals the links S-hub1 and hub1-hub2 (healing S-hub1 is followed by     *)
(* membership's resubscribe), has P publish (each publish is handed to hub *)
(* 1 at once; a chosen push to S is dropped as a dead session would), and  *)
(* moves time to the model's next deadline (the next scheduled action, the *)
(* next GAP_AE of S, the next HUB_AE of a hub). Events: `publish`, `tohub` *)
(* (m, lose), `flip` (a link), `tick` (to now), then at that instant `ae`  *)
(* (hub h, in hub order) and `gap` (S) for the timers that were due. The   *)
(* last event of each call carries what the test sees after it: the time, *)
(* the links, the messages each hub logs and those S delivered.            *)
(*                                                                         *)
(* Each event must be the step of BroadcastRepair.tla it names (Publish,   *)
(* ToHub, Flip, Tick, HubAe, GapAe) with that state, and the model's       *)
(* invariants hold on every state. HubAe stores a fetched message as      *)
(* hub_store does: eviction first, the fetching hub's time, or a LogFull   *)
(* refusal; which branch a call took is read from the logs the event      *)
(* reports. The run stays under LOG_WINDOW (no expiry) and under LOG_CAP   *)
(* 2048 (no eviction, no refusal), P's link to hub 1 and its member link   *)
(* stay up (no retry, no fallback): BroadcastRepair_*.cfg check those.     *)
(* The first event flips P2: P never reaches hub 2, since the code hands a *)
(* publish to every hub it reaches and the run records the hand-over to    *)
(* hub 1 only (the fan-out to both hubs is not traced here).               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/repair.ndjson.                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS Times, Mids, Window, LogCap, GapEvery, GapSpan, GapLive, ResubBack, AeEvery, AeFrom, AeTo, HaveMax, GiveUp,
          RxHubOnly, GapMark, Resub, Born, MaxTime, Quiet, MaxFlips

VARIABLES i, now, lnk, hl, hseen, nextAe, pubd, dlv, lastRx, newest, nextGap, cont, skipped, step, nf, lastGap
mvars == <<now, lnk, hl, hseen, nextAe, pubd, dlv, lastRx, newest, nextGap, cont, skipped, step, nf, lastGap>>
vars == <<i, mvars>>

M == INSTANCE BroadcastRepair

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/repair.ndjson")
\* every instant the test acts at is an instant of the model's environment
TimesDef == {0} \union {Trace[k].now : k \in {x \in 1..Len(Trace) : "now" \in DOMAIN Trace[x]}}
Ev == Trace[i]
Range(s) == {s[k] : k \in 1..Len(s)}

\* what the test sees after a call (on its last event only)
Proj == "lnk" \in DOMAIN Ev =>
          /\ now' = Ev.now
          /\ lnk' = Ev.lnk
          /\ {m \in Mids : hl'[1][m] # M!NoT} = Range(Ev.hl1)
          /\ {m \in Mids : hl'[2][m] # M!NoT} = Range(Ev.hl2)
          /\ {m \in Mids : dlv'[m] # M!NoT} = Range(Ev.dlv)

PublishEv == Ev.op = "publish" /\ M!Publish /\ pubd'[Ev.m] # M!NoT
ToHubEv == Ev.op = "tohub" /\ M!ToHub /\ Ev.m \in hseen'[1] \ hseen[1]
FlipEv == Ev.op = "flip" /\ M!Flip /\ lnk'[Ev.l] # lnk[Ev.l]
TickEv == Ev.op = "tick" /\ M!Tick /\ now' = Ev.now
\* the run stays under LOG_CAP, so hub_store never refuses (LogFull): with the hub link up, the other hub holds the
\* whole window after the exchange (a refused fetch is a branch the record cannot show until the call's last event)
AeEv == /\ Ev.op = "ae" /\ M!HubAe /\ nextAe'[Ev.h] # nextAe[Ev.h]
        /\ lnk["H"] => M!WindowIds(Ev.h) \subseteq hseen'[3 - Ev.h]
GapEv == Ev.op = "gap" /\ M!GapAe

Init == i = 1 /\ M!Init
Step == /\ i <= Len(Trace) /\ Ev.t = "rep"
        /\ (PublishEv \/ ToHubEv \/ FlipEv \/ TickEv \/ AeEv \/ GapEv)
        /\ Proj
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == M!TypeOK /\ M!SinceCoversMissed /\ M!HealCovers /\ M!AeCovers /\ M!PeriodicDelivers
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
