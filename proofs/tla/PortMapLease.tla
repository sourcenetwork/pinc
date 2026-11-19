------------------------------ MODULE PortMapLease ------------------------------
(***************************************************************************)
(* The lease of one port mapping, between the client of                    *)
(* crates/pinc-portmap/src/client.rs (PortMap) and the gateway that grants *)
(* it.                                                                     *)
(*                                                                         *)
(* Who acts. The client asks the gateway for a mapping (PortMap::enter of  *)
(* Step::Pcp, then poll_datagram), takes a grant (PortMap::grant), renews  *)
(* half way (lease::renew_at, the renew branch of handle_timeout), tries a *)
(* failed renewal again half way to the end (PortMap::fail), drops the     *)
(* mapping at its own lease end (lease::expiry, the first branch of        *)
(* handle_timeout), drops it when an answer to its request shows the       *)
(* gateway restarted (lease::restarted, PortMap::note_epoch, whatever the  *)
(* answer says), and stops (PortMap::stop: the mapping is dropped at once  *)
(* and a release is sent). An announce answers no request and carries no   *)
(* nonce, so anyone on the link can send one: it only brings the renewal   *)
(* of a held mapping forward (PortMap::announce, bring_forward), at least  *)
(* Floor apart, and the renewal's answer decides. The gateway grants or    *)
(* refuses each request, forgets a mapping when its own clock passes the   *)
(* mapping's end, restarts (losing every mapping and starting its epoch    *)
(* again from 0) and announces its epoch; a host on the link sends         *)
(* announces of its own (Spoof). The network loses any datagram.           *)
(*                                                                         *)
(* What can happen. A lease starts on the client's clock when its request  *)
(* first left (`started`), and on the gateway's clock when the request     *)
(* arrived, so the client's end is never later than the gateway's. A       *)
(* gateway that restarts loses the mapping while the client still          *)
(* publishes it: until the client hears from the restarted gateway it      *)
(* cannot know, and that window cannot be closed.                          *)
(*                                                                         *)
(* What must never happen. A published mapping (PortMap::mapped is Some,   *)
(* what the node puts in its signed record) that the gateway no longer     *)
(* holds, other than in that window (HeldByGateway); a published mapping   *)
(* after stop (StoppedUnpublished); a published mapping past the client's  *)
(* own lease end (LeaseLive); a lease that runs out without the client     *)
(* having asked to renew it (RenewedBeforeLapse); an announce that takes   *)
(* a mapping the gateway holds out of the record (AnnounceKeeps); two      *)
(* renewals brought forward by announces less than Floor apart             *)
(* (AnnounceSpaced).                                                       *)
(*                                                                         *)
(* Time is discrete: one tick is Sec seconds. The epoch rule is the code's *)
(* lease::restarted, on seconds. Stated assumptions: a datagram arrives in *)
(* the tick it was sent in or never (Tick drops what is in flight); a      *)
(* restart takes longer than a datagram's trip (Restart drops what is in   *)
(* flight); the host calls handle_timeout and poll_datagram when they are  *)
(* due (Tick waits for a due expiry or renewal); a round of tries ends     *)
(* within its tick (the three PCP tries take 1.75 s, below Sec; Tick waits *)
(* while the client asks). Only PCP is modelled: NAT-PMP and UPnP renew    *)
(* through the same fail and grant steps.                                  *)
(*                                                                         *)
(* Configurations. PortMapLease.cfg is the code and checks every           *)
(* invariant. Each RED configuration switches one guard off:               *)
(* PortMapLease_norenew.cfg (Renew = FALSE), PortMapLease_noepoch.cfg      *)
(* (Epoch = FALSE), PortMapLease_noexpiry.cfg (Expiry = FALSE),            *)
(* PortMapLease_nostopdrop.cfg (StopDrop = FALSE),                        *)
(* PortMapLease_refusal.cfg (RefusalDrops = FALSE: the code before this   *)
(* model found that a refused renewal kept a mapping the restarted        *)
(* gateway had lost), PortMapLease_announcedrop.cfg (AnnounceDrops = TRUE: *)
(* the client as first written, which believed an announce's epoch),       *)
(* PortMapLease_nofloor.cfg (FloorOn = FALSE) and PortMapLease_stalefloor  *)
(* (KeepFloor = FALSE: found by this model in the floor as first written:  *)
(* an announce kept across a renewal that failed was acted on at its old   *)
(* start after the next grant, inside the floor a later announce had set); *)
(* each says in its own comment what goes wrong.                           *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/PortMapLease.lean (renew_at before   *)
(* expiry, the clamp, and the two sides of lease::restarted).              *)
(***************************************************************************)
\* Integer arithmetic (-1 marks "no epoch heard yet"), and TLC's helpers.
EXTENDS Integers, TLC

\* L: the lifetime the gateway grants, in ticks (even, so half way is a tick);
\* Sec: the seconds in one tick, for the epoch rule;
\* MaxT: the last tick explored; MaxRestarts: how often the gateway may restart;
\* Tries: the tries of one request (TRIES, shrunk);
\* Renew, Epoch, Expiry, StopDrop: the guards of the code, TRUE in the code;
\* RefusalDrops: whether a refusal that shows a restart drops the mapping (TRUE in the code: note_epoch drops it);
\* AnnounceDrops: whether an announce's epoch is believed and may drop the mapping (FALSE in the code);
\* Floor: the least ticks between two renewals brought forward by announces (ANNOUNCE_FLOOR, 10 s, rounded up to
\* ticks); FloorOn: whether that floor is kept (TRUE in the code); Spoofs: whether a host on the link sends announces.
\* KeepFloor: whether a start kept from before waits for the floor a later announce set (TRUE in the code).
\* The wait of 0 to 5 s between an announce and the renewal it brings (announce_delay) is below a tick: 0 here.
CONSTANTS L, Sec, MaxT, MaxRestarts, Tries, Renew, Epoch, Expiry, StopDrop, RefusalDrops, AnnounceDrops, Floor, FloorOn,
          KeepFloor, Spoofs

\* now: the clock, in ticks, shared by client and gateway (only their readings of it differ).
\* boot: the tick the gateway last started at; restarts: how often it restarted.
\* gmap: the gateway holds the mapping; gexp: the last tick it holds it on its clock.
\* req: the requests in flight to the gateway ("map" or "release").
\* resp: the answers in flight to the client: kind, epoch in seconds, and the gateway's boot (a ghost).
\* cstep: the client's step: "ask" (Step::Pcp), "held" (Step::Held), "idle" (Step::Idle and the fallbacks, which
\* hold nothing) or "stopped" (Step::Stopped).
\* tries: the tries sent in this round; renewing: the round renews a held mapping.
\* pub: the client publishes the mapping (PortMap::mapped is Some).
\* started: the tick the round's first request left; renewAt, cexp: the lease's renewal and end on the client's clock.
\* prevAt, prevSrv: the last epoch the client heard (PortMap::epoch): when (ticks, -1 for none) and what (seconds).
\* heardBoot: the gateway boot of the last answer the client took in (a ghost).
\* grantBoot: the gateway boot that granted the published mapping (a ghost).
\* renewTried: a renewal request left since the last grant (a ghost).
\* lapseUntried: some lease ran out with no renewal request sent (a ghost).
\* floorEnd: the earliest tick an announce may start another brought-forward renewal (PortMap::floor_end).
\* annNext: an announce came while a renewal was in flight: the tick its brought-forward renewal may start once that
\* renewal is granted (PortMap::announce_next; -1 for none).
\* lastBrought: the start of the last renewal an announce brought forward (a ghost; -1 for none).
\* fast: two such starts were less than Floor apart (a ghost).
\* dropBad: an announce took a mapping the gateway held out of the record (a ghost).
VARIABLES now, boot, restarts, gmap, gexp, req, resp, cstep, tries, renewing, pub, started, renewAt, cexp,
          prevAt, prevSrv, heardBoot, grantBoot, renewTried, lapseUntried, floorEnd, annNext, lastBrought, fast,
          dropBad

\* the gateway's part of the state
gw == <<boot, restarts, gmap, gexp>>
\* the client's part of the state
cl == <<cstep, tries, renewing, pub, started, renewAt, cexp, prevAt, prevSrv>>
\* the ghosts, which only the properties read
gh == <<heardBoot, grantBoot, renewTried, lapseUntried>>
\* what the announces move: the floor, the announce kept for after a renewal, and their ghosts
an == <<floorEnd, annNext, lastBrought, fast, dropBad>>
\* every variable
vars == <<now, gw, req, resp, cl, gh, an>>

\* The larger and the smaller of two ticks.
Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

\* The gateway's epoch now, in seconds since it last started (what every answer carries).
EpochNow == (now - boot) * Sec

\* lease::restarted(prev, now, server) with the client's times in seconds: the epoch went back by more than one
\* second, or the client's clock and the epoch advanced at paces more than a sixteenth and two seconds apart.
Restarted(at, srv, t, server) ==
    \* c: seconds the client's clock advanced since it heard `srv`
    LET c == (t - at) * Sec
        \* g: seconds the epoch advanced (saturating at 0, as server.saturating_sub)
        g == IF server >= srv THEN server - srv ELSE 0
    \* the three tests of the code, in its order
    IN \/ server + 1 < srv
       \/ c + 2 < g - g \div 16
       \/ g + 2 < c - c \div 16

\* PortMap::note_epoch: whether the epoch `server` heard now shows a restart (never on the first epoch heard).
Lost(server) == Epoch /\ prevAt >= 0 /\ Restarted(prevAt, prevSrv, now, server)

\* The gateway holds the mapping on its own clock: it has one and its end has not passed.
GwHolds == gmap /\ now <= gexp

\* The client's lease end is due (handle_timeout drops the mapping first).
ExpiryDue == Expiry /\ pub /\ now >= cexp
\* The renewal is due (the renew branch of handle_timeout), unless the end is due first.
RenewDue == Renew /\ cstep = "held" /\ pub /\ now >= renewAt /\ ~ExpiryDue

\* PortMap::enter(Step::Pcp, now): a new round: the lease of its answer starts now.
NewRound == /\ cstep' = "ask" /\ tries' = 0 /\ started' = now

(* ------------------------------ the start ------------------------------ *)
\* PortMap::new: the client starts asking at tick 0; the gateway started at tick 0 and holds nothing.
Init == /\ now = 0 /\ boot = 0 /\ restarts = 0 /\ gmap = FALSE /\ gexp = 0
        \* nothing in flight
        /\ req = {} /\ resp = {}
        \* the client asks, holds nothing, has heard no epoch
        /\ cstep = "ask" /\ tries = 0 /\ renewing = FALSE /\ pub = FALSE /\ started = 0
        /\ renewAt = 0 /\ cexp = 0 /\ prevAt = -1 /\ prevSrv = 0
        \* the ghosts start empty
        /\ heardBoot = 0 /\ grantBoot = 0 /\ renewTried = FALSE /\ lapseUntried = FALSE
        \* no announce yet
        /\ floorEnd = 0 /\ annNext = -1 /\ lastBrought = -1 /\ fast = FALSE /\ dropBad = FALSE

(* ------------------------------ time ------------------------------ *)
\* The clock moves on one tick, once nothing due is left undone; what is in flight is lost (the delivery bound).
Tick == /\ now < MaxT
        \* the host runs handle_timeout when due, and a round of tries ends within its tick
        /\ ~ExpiryDue /\ ~RenewDue /\ cstep /= "ask"
        /\ now' = now + 1
        \* a datagram not delivered within its tick never is
        /\ req' = {} /\ resp' = {}
        /\ UNCHANGED <<gw, cl, gh, an>>

(* ------------------------------ the client ------------------------------ *)
\* handle_timeout, first branch: the lease reached its end on the client's clock: drop the mapping and ask again.
ClientExpire ==
    /\ ExpiryDue
    \* the mapping is unpublished at once
    /\ pub' = FALSE /\ renewing' = FALSE
    \* PortMap::first is Step::Pcp: a new round
    /\ NewRound
    \* the ghost notes a lease that ran out with no renewal request sent
    /\ lapseUntried' = (lapseUntried \/ ~renewTried)
    /\ UNCHANGED <<now, gw, req, resp, renewAt, cexp, prevAt, prevSrv, heardBoot, grantBoot, renewTried, an>>

\* handle_timeout, renew branch (PortMap::renew): half way, ask the gateway again with the same protocol.
ClientRenew ==
    /\ RenewDue
    /\ renewing' = TRUE
    \* a new round: its grant's lease starts now
    /\ NewRound
    /\ UNCHANGED <<now, gw, req, resp, pub, renewAt, cexp, prevAt, prevSrv, gh, an>>

\* poll_datagram: a try of the round's request leaves (the timer of the tries is not modelled: any time).
ClientSend ==
    /\ cstep = "ask" /\ tries < Tries
    /\ tries' = tries + 1
    /\ req' = req \cup {"map"}
    \* the ghost notes that a renewal was asked for
    /\ renewTried' = (renewTried \/ renewing)
    /\ UNCHANGED <<now, gw, resp, cstep, renewing, pub, started, renewAt, cexp, prevAt, prevSrv,
                   heardBoot, grantBoot, lapseUntried, an>>

\* PortMap::fail, as the client state changes it: a failed renewal of a held mapping goes back to held and renews
\* again half way to the end; any other failure goes idle (the fallbacks to NAT-PMP and UPnP and the RETRY wait,
\* which hold nothing, are one step here) and asks again later (ClientRetry).
FailVars ==
    IF renewing /\ pub
    THEN /\ cstep' = "held" /\ tries' = 0 /\ renewing' = FALSE
         \* renew = max(now + (expiry - now) / 2, now + FIRST_GAP), with expiry - now saturating at 0;
         \* FIRST_GAP (0.25 s) rounds up to one tick here, so the clock moves on between two retries
         /\ renewAt' = now + (IF cexp - now >= 2 THEN (cexp - now) \div 2 ELSE 1)
         /\ UNCHANGED <<started, pub>>
    ELSE /\ cstep' = "idle" /\ tries' = 0 /\ renewing' = FALSE
         /\ UNCHANGED <<started, renewAt, pub>>

\* handle_timeout once the tries are spent (the `_ => self.fail(now)` arm).
ClientGiveUp ==
    /\ cstep = "ask" /\ tries = Tries
    /\ FailVars
    /\ UNCHANGED <<now, gw, req, resp, cexp, prevAt, prevSrv, gh, an>>

\* handle_timeout in Step::Idle once RETRY has passed (any time here): PortMap::first, a new PCP round.
ClientRetry ==
    /\ cstep = "idle"
    /\ NewRound
    /\ UNCHANGED <<now, gw, req, resp, renewing, pub, renewAt, cexp, prevAt, prevSrv, gh, an>>

\* PortMap::bring_forward(at) on a lease whose renewal is at `r`: the renewal moves to the start (at the earliest
\* now) if that is sooner, and the next announce-brought renewal starts no sooner than Floor after it. The ghosts
\* note the start, and whether it came less than Floor after the one before.
BringForward(at, r) ==
    \* a start noted before a later announce was acted on waits for the floor that one set (KeepFloor; without it the
    \* start is taken as it was noted)
    LET start == IF KeepFloor THEN Max(at, floorEnd) ELSE at
    IN /\ renewAt' = Min(r, Max(start, now))
       /\ floorEnd' = start + Floor
       /\ lastBrought' = start
       /\ fast' = (fast \/ (lastBrought >= 0 /\ start < lastBrought + Floor))

\* handle_datagram of a MAP answer (pcp_answer): taken only in Step::Pcp; it notes the epoch, then a grant is
\* held (PortMap::grant: renewal at started + L/2, end at started + L, brought forward if an announce came while
\* the request was in flight), and a refusal fails the round.
ClientMapAnswer ==
    /\ cstep = "ask"
    /\ \E m \in resp :
        /\ m.k \in {"grant", "refuse"}
        \* the datagram is consumed
        /\ resp' = resp \ {m}
        \* note_epoch: the client now remembers this epoch
        /\ prevAt' = now /\ prevSrv' = m.e
        \* the ghost: the last gateway incarnation the client heard
        /\ heardBoot' = m.b
        /\ IF m.k = "grant"
           \* a grant: the lease that started when the round's first request left
           THEN /\ pub' = TRUE /\ cstep' = "held" /\ tries' = 0 /\ renewing' = FALSE
                /\ cexp' = started + L
                \* an announce kept for after this answer brings the new lease's renewal forward
                /\ IF annNext >= 0
                   THEN BringForward(annNext, started + L \div 2)
                   ELSE /\ renewAt' = started + L \div 2 /\ UNCHANGED <<floorEnd, lastBrought, fast>>
                /\ annNext' = -1
                \* the ghosts: who granted, and no renewal asked for yet
                /\ grantBoot' = m.b /\ renewTried' = FALSE
                /\ UNCHANGED <<started, lapseUntried, dropBad>>
           \* a refusal: with RefusalDrops a refusal that shows a restart drops the mapping (note_epoch) and fail
           \* asks again; without it fail keeps a mapping it was renewing (the code before the fix)
           ELSE /\ IF RefusalDrops /\ Lost(m.e)
                   THEN /\ pub' = FALSE /\ renewing' = FALSE /\ NewRound /\ UNCHANGED renewAt
                   ELSE FailVars
                /\ UNCHANGED <<cexp, grantBoot, renewTried, lapseUntried, an>>
    /\ UNCHANGED <<now, gw, req>>

\* handle_datagram of an ANNOUNCE (pcp_answer, Header with OP_ANNOUNCE; PortMap::announce): taken in any step but
\* Stopped. Nothing asked for it and it has no nonce, so its epoch is not noted and nothing is dropped: with a mapping
\* held it brings the renewal forward, from now or from the end of the floor, whichever is later; one that comes while
\* a renewal is in flight is kept for after that renewal's answer; with no mapping held it changes nothing. With
\* AnnounceDrops (the client as first written) the epoch is noted and one that shows a restart drops the mapping.
ClientAnnounce ==
    /\ cstep /= "stopped"
    /\ \E m \in resp :
        /\ m.k = "announce"
        /\ resp' = resp \ {m}
        /\ IF AnnounceDrops
           THEN /\ prevAt' = now /\ prevSrv' = m.e
                /\ heardBoot' = m.b
                /\ IF Lost(m.e) /\ pub
                   THEN /\ pub' = FALSE /\ renewing' = FALSE /\ NewRound
                        /\ dropBad' = (dropBad \/ GwHolds)
                   ELSE UNCHANGED <<pub, renewing, cstep, tries, started, dropBad>>
                /\ UNCHANGED <<renewAt, floorEnd, annNext, lastBrought, fast>>
           ELSE LET start == IF FloorOn THEN Max(now, floorEnd) ELSE now
                IN /\ IF ~pub
                      THEN UNCHANGED <<renewAt, floorEnd, annNext, lastBrought, fast>>
                      ELSE IF cstep /= "held"
                           THEN /\ annNext' = IF annNext < 0 THEN start ELSE Min(annNext, start)
                                /\ UNCHANGED <<renewAt, floorEnd, lastBrought, fast>>
                           ELSE IF start < renewAt
                                THEN BringForward(start, renewAt) /\ UNCHANGED annNext
                                ELSE UNCHANGED <<renewAt, floorEnd, annNext, lastBrought, fast>>
                   /\ UNCHANGED <<pub, renewing, cstep, tries, started, prevAt, prevSrv, heardBoot, dropBad>>
    /\ UNCHANGED <<now, gw, req, cexp, grantBoot, renewTried, lapseUntried>>

\* PortMap::stop: the held mapping is dropped at once (unless StopDrop is off) and a release is sent for it.
ClientStop ==
    /\ cstep /= "stopped"
    /\ cstep' = "stopped" /\ renewing' = FALSE /\ tries' = 0
    /\ pub' = (pub /\ ~StopDrop)
    \* the release (lifetime 0) goes out only for a mapping that was held
    /\ req' = IF pub THEN req \cup {"release"} ELSE req
    /\ UNCHANGED <<now, gw, resp, started, renewAt, cexp, prevAt, prevSrv, gh, an>>

(* ------------------------------ the gateway ------------------------------ *)
\* A MAP request arrives: the gateway grants it (its lease ends L ticks after the arrival) or refuses it, and
\* answers with its epoch.
GwMap ==
    /\ "map" \in req
    /\ req' = req \ {"map"}
    /\ \E k \in {"grant", "refuse"} :
        \* a grant (re)starts the gateway's lease now; a refusal leaves what it holds
        /\ gmap' = (gmap \/ k = "grant")
        /\ gexp' = IF k = "grant" THEN now + L ELSE gexp
        /\ resp' = resp \cup {[k |-> k, e |-> EpochNow, b |-> boot]}
    /\ UNCHANGED <<now, boot, restarts, cl, gh, an>>

\* A release arrives: the gateway deletes the mapping.
GwRelease ==
    /\ "release" \in req
    /\ req' = req \ {"release"} /\ gmap' = FALSE
    /\ UNCHANGED <<now, boot, restarts, gexp, resp, cl, gh, an>>

\* The gateway sends an ANNOUNCE with its epoch (after a restart, or at any time).
GwAnnounce ==
    /\ ~\E m \in resp : m.k = "announce"
    /\ resp' = resp \cup {[k |-> "announce", e |-> EpochNow, b |-> boot]}
    /\ UNCHANGED <<now, gw, req, cl, gh, an>>

\* A host on the link sends an announce of its own, with an epoch that reads as a gateway just started.
Spoof ==
    /\ Spoofs /\ ~\E m \in resp : m.k = "announce"
    /\ resp' = resp \cup {[k |-> "announce", e |-> 0, b |-> boot]}
    /\ UNCHANGED <<now, gw, req, cl, gh, an>>

\* The gateway restarts: every mapping is lost and its epoch starts again from 0; it had run at least a tick.
GwRestart ==
    /\ restarts < MaxRestarts /\ now > boot
    /\ boot' = now /\ restarts' = restarts + 1 /\ gmap' = FALSE
    \* a restart takes longer than a datagram's trip: what was in flight is lost
    /\ req' = {} /\ resp' = {}
    /\ UNCHANGED <<now, gexp, cl, gh, an>>

(* ------------------------------ the network ------------------------------ *)
\* The network loses a request.
LoseReq == /\ \E r \in req : req' = req \ {r}
           /\ UNCHANGED <<now, gw, resp, cl, gh, an>>
\* The network loses an answer.
LoseResp == /\ \E m \in resp : resp' = resp \ {m}
            /\ UNCHANGED <<now, gw, req, cl, gh, an>>

\* Every step the system can take.
Next == \/ Tick \/ ClientExpire \/ ClientRenew \/ ClientSend \/ ClientGiveUp \/ ClientRetry \/ ClientMapAnswer
        \/ ClientAnnounce \/ ClientStop \/ GwMap \/ GwRelease \/ GwAnnounce \/ Spoof \/ GwRestart \/ LoseReq
        \/ LoseResp

\* The behaviours: start in Init, then take any steps.
Spec == Init /\ [][Next]_vars

(* ------------------------------ the checked properties ------------------------------ *)
\* A published mapping is held by the gateway, unless the gateway restarted since it granted it and the client has
\* heard nothing from the restarted gateway (the window no client can close).
HeldByGateway == pub => (GwHolds \/ (grantBoot < boot /\ heardBoot < boot))

\* After stop nothing is published.
StoppedUnpublished == cstep = "stopped" => ~pub

\* A published mapping has not passed its lease end on the client's clock (it is dropped at that instant).
LeaseLive == pub => now <= cexp

\* No lease runs out without the client having sent a request to renew it.
RenewedBeforeLapse == ~lapseUntried

\* No announce takes a mapping the gateway holds out of the record: an announce has no nonce, so a host on the link
\* can send one with any epoch.
AnnounceKeeps == ~dropBad

\* Two renewals brought forward by announces start at least Floor apart, so announces cannot make the client renew
\* at the gateway's round-trip rate.
AnnounceSpaced == ~fast

\* The types of the variables, as a sanity check of the model.
TypeOK == /\ now \in 0..MaxT /\ boot \in 0..MaxT /\ restarts \in 0..MaxRestarts
          /\ cstep \in {"ask", "held", "idle", "stopped"} /\ tries \in 0..Tries
          /\ pub \in BOOLEAN /\ renewing \in BOOLEAN /\ req \subseteq {"map", "release"}
          \* a start kept for after a renewal takes the next free floor, so these run at most a few floors ahead
          /\ floorEnd \in 0..(MaxT + 3 * Floor) /\ annNext \in -1..(MaxT + 3 * Floor)
          /\ lastBrought \in -1..(MaxT + 3 * Floor)
          /\ fast \in BOOLEAN /\ dropBad \in BOOLEAN

\* the quick profile (proofs/tla/quick): every behaviour up to a depth, as a CONSTRAINT
PortMapLeaseQuickBound == TLCGet("level") <= 14
=============================================================================
