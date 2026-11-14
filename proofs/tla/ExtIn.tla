-------------------------------- MODULE ExtIn ---------------------------------
(***************************************************************************)
(* The ring of extension frames held for the application (vinc-core        *)
(* ext_in.rs): every interleaving of put and take at small sizes           *)
(* (ExtInOps.tla has the operators).                                         *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the ring never grows: at most CAP frames, the head in 0..CAP-1, and  *)
(*    the length is the number of frames held (Bounded);                   *)
(*  - a body longer than MX is never stored (Short);                       *)
(*  - frames leave in the order they arrived: the held frames have         *)
(*    increasing places, all after the last one taken (Fifo);              *)
(*  - every frame kept is taken, dropped by a full ring or held:           *)
(*    kept = takes + dropped + held (Balance; `dropped` is the sum of what *)
(*    put returned); a refused body is not kept (refused is a ghost);      *)
(*  - every frame lost is counted (Counted): what the endpoint adds to its *)
(*    count, put's return or 1 for a refused body (`lost`), is the frames  *)
(*    a full ring dropped plus the bodies refused;                         *)
(*  - the rule of a put (PutRule): a too-long body changes nothing and is  *)
(*    refused (put returns None, gv = -1); otherwise onto a ring with room *)
(*    it appends and returns Some(0); onto a full ring it drops the oldest *)
(*    frame, appends and returns Some(1), so the newest frame is always    *)
(*    held after a put that kept it (NewestKept);                          *)
(*  - the rule of a take (TakeRule): an empty ring gives nothing; a frame  *)
(*    longer than the buffer changes nothing and reports its length; else  *)
(*    the oldest frame goes.                                               *)
(* Witnesses: ExtIn_newest drops the newest frame of a full ring (PutRule    *)
(* fails); ExtIn_evict, ExtIn_refuse and ExtIn_stay are reachability witnesses: a full   *)
(* ring drops a frame, a body is refused, a frame stays held for a short   *)
(* buffer.                                                                 *)
(* Lean counterpart: proofs/lean/Vinc/CoreExtIn*.lean.                       *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS CAP, MX, PMAX, LS, OC, NEWEST
VARIABLES r, kept, takes, dropped, refused, nextId, lastTake, act, arg, ocv, gv, lost
vars == <<r, kept, takes, dropped, refused, nextId, lastTake, act, arg, ocv, gv, lost>>

INSTANCE ExtInOps

Init == /\ r = Ring0
        /\ kept = 0 /\ takes = 0 /\ dropped = 0 /\ refused = 0
        /\ nextId = 1 /\ lastTake = 0 /\ act = "init" /\ arg = None /\ ocv = 0 /\ gv = 0 /\ lost = 0

\* a frame of session 1 or 2 and of body length l in LS
PutStep == \E l \in LS, s \in {1, 2} :
    LET it == <<nextId, s, 0, l>>
        x == EPut(r, CAP, MX, it, NEWEST)
    IN /\ r' = x.r
       /\ nextId' = nextId + 1
       /\ kept' = IF x.ok THEN kept + 1 ELSE kept
       /\ refused' = IF x.ok THEN refused ELSE refused + 1
       /\ gv' = IF x.ok THEN x.gave ELSE -1
       /\ dropped' = dropped + (IF x.ok THEN x.gave ELSE 0)
       /\ lost' = lost + (IF x.ok THEN x.gave ELSE 1)
       /\ act' = "put" /\ arg' = it
       /\ UNCHANGED <<takes, lastTake, ocv>>

TakeStep == \E oc \in OC :
    LET x == ETake(r, CAP, oc)
    IN /\ r' = x.r
       /\ takes' = IF x.res = "ok" THEN takes + 1 ELSE takes
       /\ lastTake' = IF x.res = "ok" THEN x.out[1] ELSE lastTake
       /\ act' = "take" /\ ocv' = oc /\ arg' = x.out
       /\ UNCHANGED <<kept, dropped, refused, nextId, gv, lost>>

Next == PutStep \/ TakeStep
Spec == Init /\ [][Next]_vars
Bound == nextId <= PMAX

Q == r.q
Bounded == /\ r.len \in 0..CAP /\ r.head \in 0..CAP - 1 /\ Len(Q) = r.len
Short == \A i \in 1..Len(Q) : Q[i][4] <= MX
Fifo == /\ \A i, j \in 1..Len(Q) : i < j => Q[i][1] < Q[j][1]
        /\ \A i \in 1..Len(Q) : lastTake < Q[i][1]
Balance == kept = takes + dropped + r.len
Counted == lost = dropped + refused
Inv == Bounded /\ Short /\ Fifo /\ Balance /\ Counted /\ (nextId - 1 = kept + refused)

PutRuleA ==
    act' = "put" =>
        LET it == arg'
        IN IF it[4] > MX
           THEN r'.q = Q /\ r'.head = r.head /\ gv' = -1
           ELSE IF Len(Q) < CAP
                THEN r'.q = Append(Q, it) /\ gv' = 0
                ELSE r'.q = Append(Tail(Q), it) /\ gv' = 1
NewestKeptA == (act' = "put" /\ arg'[4] <= MX) => r'.q[Len(r'.q)] = arg'
TakeRuleA == (act' # "put" /\ act' # "init") =>
    IF Len(Q) = 0 THEN r'.q = Q
    ELSE IF Q[1][4] > ocv' THEN r'.q = Q
    ELSE r'.q = Tail(Q) /\ arg' = Q[1]
PutRule == [][PutRuleA]_vars
NewestKept == [][NewestKeptA]_vars
TakeRule == [][TakeRuleA]_vars

\* reachability witnesses: a full ring drops a frame, a body is refused, a frame stays for a short buffer
NoEvict == [][~(act' = "put" /\ arg'[4] <= MX /\ Len(Q) = CAP)]_vars
NoRefuse == [][~(act' = "put" /\ arg'[4] > MX)]_vars
NoStay == [][~(act' # "put" /\ act' # "init" /\ Len(Q) > 0 /\ Q[1][4] > ocv')]_vars
=============================================================================
