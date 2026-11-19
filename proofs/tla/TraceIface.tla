------------------------------ MODULE TraceIface ------------------------------
(***************************************************************************)
(* Trace validation of interfaces, link changes and suspension: pinc-core  *)
(* iface.rs (Endpoint::iface_event, Command::Suspend, Command::Resume).    *)
(*                                                                         *)
(* The Rust test tests/trace_iface.rs drives a real endpoint (built with   *)
(* the cargo feature `trace`) with sessions to peers, and records one      *)
(* event per call in iface.ndjson: the call (an interface id plus one, or  *)
(* 0 for a command; the kind, the new address, moved), the time and        *)
(* quiet_until before and after as four 16-bit limbs, the node before and  *)
(* after it (the address of every interface, dark, suspended, moved, and   *)
(* per session slot its state, the local address of its active path and   *)
(* of every path it holds, whether a probe timeout runs, sleep_doubt and   *)
(* its generation), and the calls the code made on the connections, in     *)
(* order (the probe's trace records). Each call is replayed through        *)
(* IfaceOps.tla from the node before it: the link, sleep, wake and redial *)
(* calls of each session must be the model's, the flags, the interfaces   *)
(* and the doubts after it the model's, quiet_until now + RESUME_QUIET     *)
(* (saturating at u64::MAX) exactly when the model sets it and unchanged   *)
(* otherwise; on an address change each session moves (rebinds or         *)
(* replaces) exactly its paths that left from the old address and holds a  *)
(* route from the new one for each. Whether a session is asleep (a SLEEP   *)
(* went out since its last wake) is not in the code's view: the replay     *)
(* keeps it per slot and generation from the model's suspend and resume.   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds iface.ndjson.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

CONSTANTS K, NI

VARIABLES i, asl, gen
vars == <<i, asl, gen>>

U == INSTANCE U64
I == INSTANCE IfaceOps WITH NI <- NI, K <- K

(* RESUME_QUIET = 10 s in nanoseconds, 10^10, as a word *)
QuietW == <<58368, 21515, 2, 0, 0>>
SatAdd(a, b) == IF U!Le(U!Add(a, b), U!Max64) THEN U!Add(a, b) ELSE U!Max64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/iface.ndjson")

Asleep(s, v) == asl[s] /\ gen[s] = v.ses[s].gen /\ v.ses[s].st = "est"

(* the model's node from a recorded view *)
Node(v) == [ifs |-> [j \in 1..NI |-> v.ifs[j]], dark |-> v.dark, susp |-> v.susp, moved |-> v.moved,
            ses |-> [s \in 1..K |-> [st |-> v.ses[s].st, act |-> v.ses[s].act, sb |-> 0, pto |-> v.ses[s].pto,
                                     doubt |-> v.ses[s].doubt, asleep |-> Asleep(s, v)]]]

Kinds(seq) == [j \in 1..Len(seq) |-> seq[j].kind]
CallsOf(ev, s) == Kinds(SelectSeq(ev.calls, LAMBDA c : c.slot = s - 1))
LinkCalls(ev, s) == SelectSeq(CallsOf(ev, s), LAMBDA c : c \in {"down", "up", "sleep", "wake", "redial"})
Moves(ev, s) == Len(SelectSeq(CallsOf(ev, s), LAMBDA c : c \in {"rebind", "replace"}))

(* an address change on a live interface: the old address, or 0 *)
Old(ev) == IF ev.id \in 1..NI /\ ev.ev.k = "addr" /\ ev.b.ifs[ev.id] # 0 THEN ev.b.ifs[ev.id] ELSE 0

(* a path is [l, r]: its local and its remote address *)
PathsOK(ev, s) ==
    LET old == Old(ev)
        new == ev.ev.a
        pb == ev.b.ses[s].paths
        pa == ev.a.ses[s].paths
    IN IF old = 0 \/ ev.b.ses[s].st = "free"
       THEN Moves(ev, s) = 0
       ELSE /\ Moves(ev, s) = Len(SelectSeq(pb, LAMBDA p : p.l = old))
            /\ \A j \in 1..Len(pb) : pb[j].l = old => \E k \in 1..Len(pa) : pa[k].l = new /\ pa[k].r = pb[j].r

CallOK(ev) ==
    LET n0 == Node(ev.b)
        r == I!Event(n0, ev.id, ev.ev)
        va == ev.a
    IN /\ ev.t = "iface"
       /\ Len(ev.b.ifs) = NI /\ Len(ev.a.ifs) = NI /\ Len(ev.b.ses) = K /\ Len(ev.a.ses) = K
       /\ \A j \in 1..NI : va.ifs[j] = r.nd.ifs[j]
       /\ va.dark = r.nd.dark /\ va.susp = r.nd.susp /\ va.moved = r.nd.moved
       /\ U!FromLimbs(ev.qa) = IF r.qset THEN SatAdd(U!FromLimbs(ev.now), QuietW) ELSE U!FromLimbs(ev.qb)
       /\ \A s \in 1..K :
            /\ LinkCalls(ev, s) = r.calls[s]
            /\ va.ses[s].doubt = r.nd.ses[s].doubt
            /\ r.calls[s] = <<"redial">> => va.ses[s].st \in {"other", "free"}
            /\ PathsOK(ev, s)

Init == i = 1 /\ asl = [s \in 1..K |-> FALSE] /\ gen = [s \in 1..K |-> 0]
Step == /\ i <= Len(Trace)
        /\ CallOK(Trace[i])
        /\ LET ev == Trace[i]
               r == I!Event(Node(ev.b), ev.id, ev.ev)
           IN /\ asl' = [s \in 1..K |-> r.nd.ses[s].asleep]
              /\ gen' = [s \in 1..K |-> ev.a.ses[s].gen]
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

(* the replay's asleep flags stay on established sessions of a suspended node *)
Inv == i > 1 /\ i <= Len(Trace) + 1 =>
           \A s \in 1..K : asl[s] => Trace[i - 1].a.susp
=============================================================================
