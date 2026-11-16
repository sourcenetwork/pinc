----------------------------- MODULE SegmentTimer -----------------------------
(***************************************************************************)
(* The spare pool segments of one endpoint and the timer that gives them   *)
(* back to the system (vinc#435).                                          *)
(*                                                                         *)
(* Who acts: the endpoint's inputs (a packet, a command), which run on the *)
(* receive path, and its timer (handle_timeout). A session that needs pool *)
(* memory takes a segment: a spare one if the endpoint has one, else a new *)
(* one the system maps. A session that goes quiet frees its segment to the *)
(* spares. After every input and every timer the host asks the endpoint    *)
(* for its deadline (poll_timeout), which arms the spares' expiry one      *)
(* period after the last input. When the deadline comes the timer gives    *)
(* back the spares no session took since the last expiry: as many of the   *)
(* oldest as the spares held at their lowest (`low`), then arms again.     *)
(*                                                                         *)
(* What must never happen: a segment unmapped on the receive path (the     *)
(* first attempt at #435 did, and the unmapping stalled a server's accepts *)
(* in a LAN burst); an endpoint with spare segments and no deadline (it    *)
(* would hold them forever once idle); a segment given back in the period  *)
(* it was freed in (a burst would map it again at once). What must happen: *)
(* once the inputs stop, every spare segment goes back.                    *)
(*                                                                         *)
(* Code: Segments::take, put, deadline, expire and Grown::make, release in *)
(* crates/vinc-transport/src/stream/pool/grown.rs; Endpoint::poll_timeout  *)
(* and handle_timeout in crates/vinc-core/src/timers.rs; the trim caller   *)
(* Streams::settle in stream/table.rs. Time is counted in ticks of a       *)
(* period's length D (SEGMENT_DECAY).                                      *)
(*                                                                         *)
(* An Acquire is a session that needs a chunk past its first and gets a    *)
(* segment. A session that only shakes hands (its first chunk is its own), *)
(* and one the system refused a segment (its chunks are then apart), take  *)
(* none and are no step here: who gets which spare, and what it finds in   *)
(* it, is SegmentHandoff.tla.                                              *)
(*                                                                         *)
(* Lean counterpart: PoolGrown.lean, section "The spare segments of an     *)
(* endpoint" (the counts, for any sizes).                                  *)
(***************************************************************************)
EXTENDS Naturals

\* MaxInUse: the most segments sessions hold at once; MaxOps: the inputs in a run (so a run goes quiet); D: the
\* ticks of one period; Bug: "none" for the code, or the bug a RED configuration plants.
CONSTANTS MaxInUse, MaxOps, D, Bug

VARIABLES
    inUse,      \* segments the sessions hold now
    held,       \* spare segments, kept by the endpoint for the next session
    fresh,      \* the spare segments freed in the current period (the newest ones)
    low,        \* the fewest spare segments held since the last expiry: what the next expiry gives back
    armed,      \* the endpoint's deadline covers the expiry
    wait,       \* ticks left until the expiry is due (meaningful while armed)
    ops,        \* inputs so far
    peak,       \* the most segments the sessions held at once
    mapped,     \* segments the system mapped for the endpoint, in all
    unmapped,   \* segments given back to the system, in all
    rxFreed,    \* segments given back on the receive path (an input), in all
    freshFreed  \* segments given back in the period they were freed in, in all

vars == <<inUse, held, fresh, low, armed, wait, ops, peak, mapped, unmapped, rxFreed, freshFreed>>

\* The smaller of two numbers.
Min(a, b) == IF a < b THEN a ELSE b

\* The host asks for the deadline after an input (Segments::deadline through Endpoint::poll_timeout), given the spare
\* count `h`, the sessions' count `iu` and the low mark `l` the input left: nothing spare means no expiry and the low
\* mark starts over; spares and no deadline yet arm one a whole period away; an armed deadline stays where it was.
\* RED "noarm": the deadline covers the spares only while a session is open (a timer that only sessions drive).
Poll(h, iu, l) ==
    /\ low' = IF h = 0 THEN 0 ELSE l           \* an empty cache starts its low mark over
    /\ IF h = 0 \/ (Bug = "noarm" /\ iu = 0)
       THEN /\ armed' = FALSE                  \* no expiry to wake for
            /\ wait' = 0                       \* nothing to count down
       ELSE IF armed
            THEN UNCHANGED <<armed, wait>>     \* the deadline set before still stands
            ELSE /\ armed' = TRUE              \* arm the expiry
                 /\ wait' = D                  \* one whole period after the input

\* An input in which a session takes a segment (Grown::take; Segments::take for a spare).
Acquire ==
    /\ ops < MaxOps                            \* the run still has inputs
    /\ inUse < MaxInUse                        \* the sessions may hold one more
    /\ ops' = ops + 1                          \* one more input
    /\ inUse' = inUse + 1                      \* the session holds the segment
    /\ peak' = IF inUse + 1 > peak THEN inUse + 1 ELSE peak   \* the most held at once
    /\ IF held > 0
       THEN /\ held' = held - 1                \* the spare freed last is taken
            /\ fresh' = IF fresh > 0 THEN fresh - 1 ELSE 0     \* the newest spares are the fresh ones
            /\ mapped' = mapped                \* the system maps nothing
            /\ Poll(held - 1, inUse + 1, Min(low, held - 1))   \* the low mark follows the spares down
       ELSE /\ UNCHANGED <<held, fresh>>       \* no spare to take
            /\ mapped' = mapped + 1            \* the system maps a new segment
            /\ Poll(0, inUse + 1, 0)
    /\ UNCHANGED <<unmapped, rxFreed, freshFreed>>

\* An input after which a session is quiet and frees its segment (Streams::settle trims; Grown::release puts it in
\* Segments). RED "eager": the freed segment goes back to the system at once, on the receive path (the first attempt).
Release ==
    /\ ops < MaxOps                            \* the run still has inputs
    /\ inUse > 0                               \* a session holds a segment
    /\ ops' = ops + 1                          \* one more input
    /\ inUse' = inUse - 1                      \* the session lets go of it
    /\ IF Bug = "eager"
       THEN /\ UNCHANGED <<held, fresh>>       \* nothing is kept
            /\ unmapped' = unmapped + 1        \* the system unmaps it now
            /\ rxFreed' = rxFreed + 1          \* and on the receive path
            /\ Poll(held, inUse - 1, low)
       ELSE /\ held' = held + 1                \* kept spare
            /\ fresh' = fresh + 1              \* freed in this period
            /\ UNCHANGED <<unmapped, rxFreed>> \* nothing goes to the system
            /\ Poll(held + 1, inUse - 1, low)  \* a put does not lower the low mark
    /\ UNCHANGED <<mapped, peak, freshFreed>>

\* Time passes towards the armed deadline. Without a deadline nothing waits on time.
Tick ==
    /\ armed /\ wait > 0                       \* an expiry is coming
    /\ wait' = wait - 1                        \* one tick closer
    /\ UNCHANGED <<inUse, held, fresh, low, armed, ops, peak, mapped, unmapped, rxFreed, freshFreed>>

\* The deadline has come: handle_timeout runs Segments::expire, which gives back the `low` oldest spares (none of them
\* fresh), starts the next period with the low mark at what is left, and the host asks for the deadline again.
\* RED "all": the expiry gives back every spare, the ones freed in this period too.
Wake ==
    /\ armed /\ wait = 0                       \* the deadline is now
    /\ LET n == IF Bug = "all" THEN held ELSE Min(low, held)   \* how many go back
           old == held - fresh                 \* the spares that were spare a whole period
       IN /\ held' = held - n                  \* the oldest leave the cache
          /\ unmapped' = unmapped + n          \* the system unmaps them
          /\ freshFreed' = freshFreed + (IF n > old THEN n - old ELSE 0)   \* fresh ones among them
          /\ fresh' = 0                        \* the survivors are a period old now
          /\ IF held - n = 0
             THEN /\ armed' = FALSE /\ wait' = 0 /\ low' = 0   \* nothing spare: no deadline
             ELSE IF Bug = "noarm" /\ inUse = 0
                  THEN /\ armed' = FALSE /\ wait' = 0 /\ low' = held - n   \* RED: an idle endpoint is not woken
                  ELSE /\ armed' = TRUE /\ wait' = D /\ low' = held - n    \* the next period starts
    /\ UNCHANGED <<inUse, ops, peak, mapped, rxFreed>>

Init ==
    /\ inUse = 0 /\ held = 0 /\ fresh = 0 /\ low = 0      \* a new endpoint: no segment at all
    /\ armed = FALSE /\ wait = 0                          \* and no deadline
    /\ ops = 0 /\ peak = 0 /\ mapped = 0 /\ unmapped = 0 /\ rxFreed = 0 /\ freshFreed = 0

Next == Acquire \/ Release \/ Tick \/ Wake

\* The timer runs when its deadline comes and time passes while one is armed; inputs need no fairness (they may stop).
Spec == Init /\ [][Next]_vars /\ WF_vars(Tick) /\ WF_vars(Wake)

\* Nothing is unmapped on the receive path: only the timer gives segments back.
RxNeverUnmaps == rxFreed = 0

\* No segment is given back in the period it was freed in, so a burst finds the segments its quiet sessions freed.
NoFreshFreed == freshFreed = 0

\* While a segment is spare the endpoint has a deadline, with or without a session.
ArmedWhileSpare == held > 0 => armed

\* Every segment mapped is held by a session, spare, or given back: none is lost or given back twice.
Conserved == mapped = inUse + held + unmapped

\* The endpoint never holds more segments than its sessions held at once.
Bounded == inUse + held <= peak

\* The counts the expiry relies on: the low mark and the fresh spares fit in what is spare, and do not overlap.
Marks == low + fresh <= held

\* Once the inputs stop, every spare segment goes back to the system.
QuietReturns == <>[](held = 0)
=============================================================================
