------------------------------ MODULE MemCore -------------------------------
(***************************************************************************)
(* The vocabulary of the membership model: the constants of consts.rs as    *)
(* Nanos words, the data shapes, the ordered-map helpers, and the output    *)
(* of a call (sent frames, broadcast-layer calls, closes, events, traces).  *)
(*                                                                         *)
(* Shapes. A NodeId is a small integer; the order of ids is the order of    *)
(* the 32-byte arrays in the trace (the harness ids are 32 equal bytes).    *)
(* An Option is <<>> or <<x>>. A BTreeMap is a function with an explicit    *)
(* domain; its ordered iteration is NextKey. A record is [inc, ver, th]     *)
(* with inc a U64 word. A frame is a record with a kind k:                  *)
(*   hello (rec, snap, homed), ack, probe, delta (m, rec, a with a 0 down,  *)
(*   1 alive, 2 left), snap (partial, more, es : seq of [m, rec]), down (m, *)
(*   inc, sil, pr : seq of [age, path]), other (ty, topic, rest).           *)
(*                                                                         *)
(* A call into a machine is a pure operator from (state, env, inputs) to a  *)
(* state; the output of the call is collected in the state (sent, bc, cl,   *)
(* ev, tr) and drained by Drain, which also applies the queue bound         *)
(* QUEUE_CAP and the Lost records of event.rs.                              *)
(*                                                                         *)
(* Lean counterpart: Pinc/MembershipModelTypes.lean.                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

N == INSTANCE Nanos
U == INSTANCE U64

(* ---- consts.rs, in Nanos (U64 limb words) ---- *)
LEASE == <<8192, 41055, 18, 0, 0>>
RENEW == <<47616, 53789, 5, 0, 0>>
HUB_STALE == <<11776, 30297, 17, 0, 0>>
PULSE_FRESH == <<56832, 39298, 15, 0, 0>>
QUIET == <<58368, 21515, 2, 0, 0>>
RECHECK_GAP == <<61952, 10757, 1, 0, 0>>
WAKE_GAP == <<37888, 30517, 0, 0, 0>>
SLEEP_WIN == <<58368, 21515, 2, 0, 0>>
PROBE_WAIT_MIN == <<45696, 3814, 0, 0, 0>>
CONFIRM == <<51712, 15258, 0, 0, 0>>
SLOW_TICK == <<61952, 10757, 1, 0, 0>>
NODE_TICK == <<25856, 7629, 0, 0, 0>>
HUB_TICK == <<51712, 15258, 0, 0, 0>>
ACK_WAIT == <<48128, 26016, 1, 0, 0>>
HS_GRACE == <<44032, 64547, 6, 0, 0>>
HEAL_SILENCE == <<22528, 63559, 13, 0, 0>>
HYST_ABS == <<11520, 305, 0, 0, 0>>
RTT_SAMPLE_MAX == <<61952, 10757, 1, 0, 0>>
RTT_UNKNOWN == <<0, 0, 256, 0, 0>>
MOVE_SETTLE == <<24064, 45776, 0, 0, 0>>
RTT_QUIET == 4000
MAX_TABLE == 4096
MAX_HUBS == 64
QUEUE_CAP == 8192
SNAP_CHUNK == 64
FLOOR_MAX == 4096
MAX_BODY == <<0, 4, 0, 0, 0>>

(* ---- helpers ---- *)
Z == U!Zero
One == U!One
NONE == -1                            \* no id (a cursor before the first key)
Opt(x) == <<x>>
Some(o) == o # <<>>
IsNoneOr(o, P(_)) == o = <<>> \/ P(o[1])
IsSomeAnd(o, P(_)) == o # <<>> /\ P(o[1])
Get(o, d) == IF o = <<>> THEN d ELSE o[1]

Put(f, k, v) == [x \in DOMAIN f \cup {k} |-> IF x = k THEN v ELSE f[x]]
Del(f, k) == [x \in DOMAIN f \ {k} |-> f[x]]
EmptyFn == [x \in {} |-> 0]
Lookup(f, k) == IF k \in DOMAIN f THEN <<f[k]>> ELSE <<>>

(* the first key of a set strictly after `after` (the first key when after = NONE) *)
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y
NextKey(dom, after) ==
    LET c == {x \in dom : x > after} IN IF c = {} THEN NONE ELSE MinOf(c)

(* max of two Nanos words, min, a - b saturating *)
SatSub(a, b) == N!SatSub(a, b)
SatAdd(a, b) == N!SatAdd(a, b)
Lt(a, b) == U!Lt(a, b)
Le(a, b) == U!Le(a, b)
Gt(a, b) == U!Lt(b, a)
Ge(a, b) == U!Le(b, a)
Max2(a, b) == U!Max(a, b)
Min2(a, b) == U!Min(a, b)

(* the epoch of an incarnation word: inc >> 16 *)
Epoch(w) == U!Shr(w, 16)

TyOf(f) == CASE f.k = "hello" -> 1 [] f.k = "ack" -> 2 [] f.k = "delta" -> 3 [] f.k = "snap" -> 4
             [] f.k = "probe" -> 12 [] f.k = "down" -> 13 [] f.k = "other" -> f.ty

(* ---- the output of a call ---- *)
\* emit an event / a trace record; a full queue drops the newest and counts it
Emit(S, e) == IF Len(S.ev) >= QUEUE_CAP THEN [S EXCEPT !.lostE = @ + 1] ELSE [S EXCEPT !.ev = Append(@, e)]
Trace(S, t) ==
    IF ~S.tracing THEN S
    ELSE IF Len(S.tr) >= QUEUE_CAP THEN [S EXCEPT !.lostT = @ + 1] ELSE [S EXCEPT !.tr = Append(@, t)]

\* the records of the Rust enums (kinds as in the trace schema)
EvJoined(m) == [k |-> "joined", m |-> m]
EvDown(m) == [k |-> "down", m |-> m]
EvLeft(m) == [k |-> "left", m |-> m]
EvRevoked(m) == [k |-> "revoked", m |-> m]
EvAddr(m) == [k |-> "addr", m |-> m]
EvStack(m, v) == [k |-> "stack", m |-> m, v |-> v]
EvView(epoch, n) == [k |-> "view", epoch |-> epoch, n |-> n]

\* what the machine asked of the broadcast layer
Bc(S, c) == [S EXCEPT !.bc = Append(@, c)]
Close(S, p, why) == [S EXCEPT !.cl = Append(@, <<p, why>>)]

(* drain the queues at the end of a call: Lost first, then the queue, as poll_event and poll_trace do *)
Drain(S) ==
    [S EXCEPT !.ev = (IF S.lostE > 0 THEN <<[k |-> "lost", n |-> S.lostE]>> ELSE <<>>) \o S.ev,
              !.tr = (IF S.lostT > 0 THEN <<[k |-> "lost", n |-> S.lostT]>> ELSE <<>>) \o S.tr,
              !.lostE = 0, !.lostT = 0]
ClearOut(S) == [S EXCEPT !.sent = <<>>, !.bc = <<>>, !.cl = <<>>, !.ev = <<>>, !.tr = <<>>, !.lostE = 0, !.lostT = 0]

(* ---- the host (env of a call) ---- *)
\* env: ev (function id -> evidence), car (function id -> carrier), acc (set), ver, tk, refl, pers, sealed (Option),
\* failseal, failunseal, floor, gu (function id -> Nanos word: the peers whose give_up is not the default)
Evidence(env, p) == Lookup(env.ev, p)
CarrierOf(env, m) == IF m \in DOMAIN env.car THEN env.car[m] ELSE [k |-> "unknown"]
LocalOf(env) == [pers |-> env.pers, sealed |-> env.sealed, rf |-> env.failunseal, sf |-> env.failseal]

\* Session::give_up: the host's bound on silence before a path is given up; HEAL_SILENCE for a peer it does not list
GiveUp(env, p) == IF p \in DOMAIN env.gu THEN env.gu[p] ELSE HEAL_SILENCE

IsHubIn(S, x) == \E i \in 1..Len(S.boot) : S.boot[i] = x
=============================================================================
