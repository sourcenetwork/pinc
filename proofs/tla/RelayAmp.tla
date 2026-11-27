------------------------------- MODULE RelayAmp -------------------------------
(***************************************************************************)
(* The UDP answers of the relay role and the amplification ledger of the  *)
(* node that carries the role: pinc-connect relay/discovery.rs            *)
(* (Relay::datagram answers an address query with a QADR and a lookup     *)
(* with a DNSR, to the datagram's source), pinc relay/state.rs (Core:     *)
(* the queue of datagrams to send, take_udp, which asks the gate of the    *)
(* ledger for each) and its three hosts: an ordinary node's role           *)
(* (drive/role_io.rs, the gate of its endpoint's ledger), the relay        *)
(* binary with a hub (the hub endpoint's ledger) and without one (a        *)
(* ledger of its own). Every host counts a datagram the role took as       *)
(* received from its source (Endpoint::host_received, Ledger::on_receive)  *)
(* and sends what the role queued only if the ledger allows it             *)
(* (Endpoint::host_send, Ledger::allow_send); the endpoint's own sessions  *)
(* send and receive through the same ledger (EpSend, EpRecv), and an       *)
(* address proves itself (Prove: Ledger::validate, a path the transport   *)
(* validated) or is dialed (Open).                                         *)
(*                                                                         *)
(* The sizes are the code's: a QAD is QAD_LEN (19) bytes and a DNSQ        *)
(* DNSQ_LEN (484) bytes, the padded forms of pinc-connect datagram.rs;     *)
(* a QADR is 16 (IPv4) or 28 (IPv6) bytes and a DNSR 35 (no record) up to  *)
(* MAX_DNS_DATAGRAM (1424) bytes; a sent datagram is charged its size plus *)
(* 28 and FACTOR is 3. LedgerOps.tla has the ledger; its table holds every *)
(* address here (CAP = NA), so no eviction happens: the eviction trade is  *)
(* Ledger.tla's.                                                           *)
(*                                                                         *)
(* Checked, in every state reached:                                        *)
(*  - AmpUnproved: an address that proved nothing (not proved, not dialed, *)
(*    not one the endpoint wrote to first) was sent, headers included, at  *)
(*    most three times the bytes it sent;                                  *)
(*  - PaddedPays (RelayAmp_served.cfg, no session traffic): the ledger     *)
(*    never refuses an answer of the role, so the padding of a query pays  *)
(*    for the longest answer to it. With session traffic an endpoint send *)
(*    may spend the budget a query brought before its answer is taken, and *)
(*    the answer is then refused: only AmpUnproved is checked there.       *)
(*  - ChargedOnce: every datagram is charged once: what the ledger        *)
(*    charged an address is what left for it plus what waits in the queue  *)
(*    already charged. On the relay binary with a hub (Hub) the hub        *)
(*    endpoint's own datagrams pass its gate (EpSend) and then wait in the *)
(*    role's queue for the one socket (Hub::cycle, Part::queue_udp); the   *)
(*    queue takes them without asking the gate again. A full queue drops   *)
(*    such a datagram after its charge, which only makes the bound         *)
(*    stricter and is not modelled (EpSend waits for room).               *)
(* RelayAmp.cfg: the fix (Gate, Pad) with session traffic; RelayAmp_pad:   *)
(* the padding without the gate also keeps AmpUnproved (each answer is     *)
(* paid by its own query), which the gate then holds whatever the size of  *)
(* a later answer.                                                         *)
(* Witnesses: RelayAmp_w_nogate (Gate = FALSE, Pad = FALSE: the code       *)
(* before the fix; AmpUnproved is violated by one answer to a spoofed      *)
(* source); RelayAmp_w_short (Pad = FALSE behind the gate: PaddedPays is   *)
(* violated, an answer is refused, so the gate alone would stop the role   *)
(* from serving); RelayAmp_w_twice (Hub, Twice: the queue asks the gate   *)
(* again of a datagram the hub endpoint's gate charged, so an address      *)
(* that proved nothing gets half its budget: ChargedOnce is violated).     *)
(* RelayAmp_hub: the fix on the relay binary with a hub.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NA, QMax, MaxSteps, Gate, Pad, EpTraffic, EpSizes, Hub, Twice

ASSUME NA >= 1 /\ QMax >= 1 /\ MaxSteps >= 1 /\ Gate \in BOOLEAN /\ Pad \in BOOLEAN /\ EpTraffic \in BOOLEAN
       /\ Hub \in BOOLEAN /\ Twice \in BOOLEAN

OVH == 28
U == 1000000

IPlus(a, c) == a + c
ILeq(a, c) == a <= c
ITimes3(a) == 3 * a

L == INSTANCE LedgerOps WITH Zero <- 0, Top <- U, Plus <- IPlus, Leq <- ILeq, Times3 <- ITimes3, OVH <- OVH,
                             CAP <- NA

Addr == 1..NA

(* the longest answers, and the query lengths that pay for them: (answer + 28) / 3 rounded up *)
MaxQadr == 28
MaxDnsr == 1424
QueryLen(a) == (a + OVH + 2) \div 3
QadLen == IF Pad THEN QueryLen(MaxQadr) ELSE 9
DnsqLen == IF Pad THEN QueryLen(MaxDnsr) ELSE 34
ASSUME QueryLen(MaxQadr) = 19 /\ QueryLen(MaxDnsr) = 484

(* each kind of query, its length and the lengths of its answers *)
Queries == {[len |-> QadLen, ans |-> 16], [len |-> QadLen, ans |-> MaxQadr],
            [len |-> DnsqLen, ans |-> 35], [len |-> DnsqLen, ans |-> MaxDnsr]}

VARIABLES t, q, got, sent, ok, refused, steps
vars == <<t, q, got, sent, ok, refused, steps>>

Held(tb) == {tb[k].addr : k \in 1..Len(tb)}

Init == /\ t = <<>>
        /\ q = <<>>
        /\ got = [x \in Addr |-> 0]
        /\ sent = [x \in Addr |-> 0]
        /\ ok = {}
        /\ refused = 0
        /\ steps = 0

Tick == steps < MaxSteps /\ steps' = steps + 1

(* a query from x (its own or a spoofed source): the host counts it, the role queues its answer, or drops it when *)
(* the queue is full (UDP_BACKLOG)                                                                                 *)
Query == \E x \in Addr, d \in Queries :
    /\ Tick
    /\ t' = IF Gate THEN L!OnReceive(t, x, d.len).tab ELSE t
    /\ got' = [got EXCEPT ![x] = @ + d.len]
    /\ q' = IF Len(q) < QMax THEN Append(q, [to |-> x, len |-> d.ans, pre |-> FALSE]) ELSE q
    /\ UNCHANGED <<sent, ok, refused>>

(* the host takes the next datagram: the role's is sent if the ledger allows it, else dropped and counted; one the *)
(* hub endpoint's gate charged is sent as it is (with Twice, the rule this replaced, it is asked again)              *)
Take == /\ q # <<>>
        /\ Tick
        /\ LET a == Head(q)
               r == L!AllowSend(t, a.to, a.len)
           IN IF ~Gate \/ (a.pre /\ ~Twice)
              THEN /\ sent' = [sent EXCEPT ![a.to] = @ + a.len + OVH]
                   /\ UNCHANGED <<t, ok, refused>>
              ELSE IF r.ok
              THEN /\ t' = r.tab
                   /\ sent' = [sent EXCEPT ![a.to] = @ + a.len + OVH]
                   /\ ok' = IF a.to \in Held(t) THEN ok ELSE ok \cup {a.to}
                   /\ UNCHANGED refused
              ELSE /\ refused' = refused + 1
                   /\ UNCHANGED <<t, sent, ok>>
        /\ q' = Tail(q)
        /\ UNCHANGED got

(* the endpoint's own sessions, through the same ledger; with a hub its datagram, charged, waits in the role's queue *)
EpSend == \E x \in Addr, n \in EpSizes :
    /\ EpTraffic
    /\ Tick
    /\ LET r == L!AllowSend(t, x, n)
       IN /\ r.ok
          /\ t' = r.tab
          /\ ok' = IF x \in Held(t) THEN ok ELSE ok \cup {x}
          /\ IF Hub
             THEN /\ Len(q) < QMax
                  /\ q' = Append(q, [to |-> x, len |-> n, pre |-> TRUE])
                  /\ UNCHANGED sent
             ELSE /\ sent' = [sent EXCEPT ![x] = @ + n + OVH]
                  /\ UNCHANGED q
    /\ UNCHANGED <<got, refused>>

EpRecv == \E x \in Addr, n \in EpSizes :
    /\ EpTraffic
    /\ Tick
    /\ t' = L!OnReceive(t, x, n).tab
    /\ got' = [got EXCEPT ![x] = @ + n]
    /\ UNCHANGED <<q, sent, ok, refused>>

Prove == \E x \in Addr :
    /\ x \in Held(t)
    /\ Tick
    /\ t' = L!Validate(t, x)
    /\ ok' = ok \cup {x}
    /\ UNCHANGED <<q, got, sent, refused>>

Dial == \E x \in Addr :
    /\ Tick
    /\ t' = L!Open(t, x)
    /\ ok' = ok \cup {x}
    /\ UNCHANGED <<q, got, sent, refused>>

Next == Query \/ Take \/ EpSend \/ EpRecv \/ Prove \/ Dial
Spec == Init /\ [][Next]_vars

TypeOK == /\ Len(q) <= QMax
          /\ ok \subseteq Addr
          /\ got \in [Addr -> Nat]
          /\ sent \in [Addr -> Nat]

AmpUnproved == \A x \in Addr \ ok : sent[x] <= 3 * got[x]

PaddedPays == refused = 0

(* the bytes charged for the datagrams of queue s to x that a gate already passed *)
RECURSIVE QCharged(_, _)
QCharged(s, x) == IF s = <<>> THEN 0
                  ELSE (IF Head(s).pre /\ Head(s).to = x THEN Head(s).len + OVH ELSE 0) + QCharged(Tail(s), x)

ChargedOnce == Gate => \A k \in 1..Len(t) : t[k].ent.tx = sent[t[k].addr] + QCharged(q, t[k].addr)
=============================================================================
