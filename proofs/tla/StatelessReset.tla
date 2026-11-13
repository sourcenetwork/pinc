--------------------------- MODULE StatelessReset ---------------------------
(***************************************************************************)
(* Stateless reset: how a peer that restarted ends the sessions a node     *)
(* still holds to it, and why nothing else can end them.                   *)
(*                                                                         *)
(* Who acts. Our node A, which holds a session "p" to the peer B and a     *)
(* sub-session "c" opened over it. The peer B, which can restart: a new    *)
(* incarnation on the same address and identity that holds none of the    *)
(* old sessions. An attacker on the network, which can read the resets it  *)
(* sees go by, replay them, make up tokens and spoof datagrams, but cannot *)
(* read a session's encrypted frames. Datagrams arrive in any order, any *)
(* time after they were sent, or not at all. A round trip passing is a    *)
(* step of its own: after it, what A heard before is more than a round     *)
(* trip old.                                                               *)
(*                                                                         *)
(* What can happen. While a session is up, B has given A, inside it, a     *)
(* token for the id A sends to: Tok(key, id), from B's reset key. A sends  *)
(* packets; B answers those on an id it holds, and answers a packet on an  *)
(* id it does not hold with a reset (the id and Tok(key, id)), if the      *)
(* packet is longer than a reset. A closes the session whose id and token  *)
(* the reset carries, and its sub-session, if it heard nothing from B for  *)
(* a round trip. After its old sessions end, A's next dial reaches the new *)
(* B with a fresh session "f" and a fresh id.                              *)
(*                                                                         *)
(* What must never happen:                                                 *)
(*  ResetOnlyDead   a reset ends a session the running B still holds (a    *)
(*                  forged or replayed reset worked);                      *)
(*  ResetCloses     a reset from a restarted B reaches a held session of   *)
(*                  the old B that heard nothing for a round trip, and the *)
(*                  session stays up;                                      *)
(*  ChildrenFollow  a session ended by a reset leaves its sub-session up;  *)
(*  QuietOnly       a reset ends a session that heard B within a round     *)
(*                  trip;                                                  *)
(*  NoAmplify       B sends a reset no smaller than what caused it.        *)
(* Assumed, not modelled: a new session's ids differ from every id an old  *)
(* reset named (ids are random or derived from the session secret: 4       *)
(* bytes, so two collide one time in 2^32), and the keyed hash behind      *)
(* Tok is collision free.                                                  *)
(*                                                                         *)
(* Rust: crates/vinc-core/src/reset.rs (`token`, `give_token`,             *)
(* `answer_unknown`, `take_token`, `on_reset`, `end_reset`);               *)
(* crates/vinc-core/src/rx.rs `handle_datagram` and `deliver` (where a     *)
(* reset is read, answered and a token given); crates/vinc-core/src/tx.rs  *)
(* `poll_transmit` (the one waiting reset leaves through the ledger);      *)
(* crates/vinc/src/keys.rs `Identity::reset_key` (the key from the         *)
(* identity seed, so it survives a restart).                               *)
(* Lean: proofs/lean/Vinc/StatelessReset.lean (the token check).           *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc), one per guard:               *)
(*  _notoken   A takes a reset whatever its token: the attacker's made-up  *)
(*             reset ends a live session; ResetOnlyDead fails.             *)
(*  _freshkey  B's key does not survive a restart: the new B's token does  *)
(*             not match the one A holds, the dead session stays up;       *)
(*             ResetCloses fails.                                          *)
(*  _noquiet   A takes a reset however recently it heard B: a late answer  *)
(*             of the old B arrives just before the reset, and the reset   *)
(*             still ends the session; QuietOnly fails.                    *)
(*  _nosize    B answers a datagram of any length: a datagram of a         *)
(*             reset's size gets a reset as large; NoAmplify fails.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    MaxInc,       \* the most incarnations of B explored
    MaxForge,     \* the most datagrams the attacker sends
    CheckToken,   \* guard: A takes a reset only with the token of its id (`on_reset`)
    KeySurvives,  \* guard: B's reset key is the same in every incarnation (`Identity::reset_key`)
    QuietGuard,   \* guard: A takes a reset only after a round trip without hearing B (`on_reset`)
    SizeBound     \* guard: B answers only a datagram longer than a reset (`answer_unknown`)

\* The three sessions A may have: the held session, its sub-session, and the one a later dial opens.
S == {"p", "c", "f"}
\* The id A sends to on each session (B's id for it); every session has its own.
Id == [s \in S |-> CASE s = "p" -> "idp" [] s = "c" -> "idc" [] OTHER -> "idf"]
\* Every id a datagram can name: the three, and one no session ever uses.
Ids == {"idp", "idc", "idf", "idx"}
\* The bytes of a reset (21), and of the packets A sends (at least 22: a short header, a packet number, a tag).
ResetLen == 21
Big == 22
\* B's reset key in incarnation i: one key for all of them, or a new key each time (the _freshkey witness).
Key(i) == IF KeySurvives THEN 0 ELSE i
\* The token of an id under a key: a pair, so two tokens are equal only for the same key and id (the hash is
\* collision free).
Tok(k, id) == <<k, id>>
\* The token the attacker makes up; no key gives it (a key number no incarnation has).
Forged == <<MaxInc + 1, "forged">>
\* What a datagram that is no reset carries in place of a token, and what A holds before B gives one.
NoTok == <<MaxInc + 2, "none">>
\* Every token there is.
Tokens == {Tok(k, id) : k \in 0..MaxInc, id \in Ids} \cup {Forged, NoTok}
\* The kinds of datagram: A's packets, B's answers, resets.
Kinds == {"pkt", "ack", "reset"}

VARIABLES
    inc,      \* B's incarnation, from 1
    holds,    \* the ids the running B holds a session for
    up,       \* up[s]: A's session s is open
    opened,   \* opened[s]: A ever opened session s
    owner,    \* owner[s]: the incarnation of B that held session s when it opened
    tok,      \* tok[s]: the token B gave A in session s
    heard,    \* heard[s]: A heard B on session s within the last round trip
    why,      \* why[s]: "reset" once a reset ended s, "" otherwise
    net,      \* the datagrams in flight
    seen,     \* the resets the attacker saw go by, as <<id, token>>
    forged,   \* the datagrams the attacker sent so far
    wrong,    \* a reset ended a session the running B still holds
    missed,   \* a reset from a restarted B reached a quiet held session of the old B and did not end it
    loud,     \* a reset ended a session that heard B within a round trip
    amp       \* B sent a reset no smaller than what caused it

vars == <<inc, holds, up, opened, owner, tok, heard, why, net, seen, forged, wrong, missed, loud, amp>>

\* A datagram: its kind, the id it names, the token it carries (resets only), its length, and who sent it.
Msg == [k : Kinds, id : Ids, t : Tokens, len : {ResetLen, Big}, src : {"a", "b", "x"}]

TypeOK ==
    /\ inc \in 1..MaxInc
    /\ holds \subseteq Ids
    /\ up \in [S -> BOOLEAN]
    /\ opened \in [S -> BOOLEAN]
    /\ owner \in [S -> 0..MaxInc]
    /\ tok \in [S -> Tokens]
    /\ heard \in [S -> BOOLEAN]
    /\ why \in [S -> {"", "reset"}]
    /\ net \subseteq Msg
    /\ seen \subseteq (Ids \X Tokens)
    /\ forged \in 0..MaxForge
    /\ wrong \in BOOLEAN /\ missed \in BOOLEAN /\ loud \in BOOLEAN /\ amp \in BOOLEAN

\* At the start A holds "p" and "c" to the first B, which gave a token in each; nothing is in flight.
Init ==
    /\ inc = 1
    /\ holds = {"idp", "idc"}
    /\ up = [s \in S |-> s # "f"]
    /\ opened = [s \in S |-> s # "f"]
    /\ owner = [s \in S |-> IF s = "f" THEN 0 ELSE 1]
    /\ tok = [s \in S |-> IF s = "f" THEN NoTok ELSE Tok(Key(1), Id[s])]
    /\ heard = [s \in S |-> FALSE]
    /\ why = [s \in S |-> ""]
    /\ net = {}
    /\ seen = {}
    /\ forged = 0
    /\ wrong = FALSE /\ missed = FALSE /\ loud = FALSE /\ amp = FALSE

\* A round trip passes: whatever A heard is now more than a round trip old.
RoundTrip ==
    /\ \E s \in S : heard[s]
    /\ heard' = [s \in S |-> FALSE]
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, why, net, seen, forged, wrong, missed, loud, amp>>

\* A sends a packet on an open session, one in flight per session (the next waits for its probe timeout).
ASend(s) ==
    /\ up[s]
    /\ ~\E m \in net : m.src = "a" /\ m.id = Id[s]
    /\ net' = net \cup {[k |-> "pkt", id |-> Id[s], t |-> NoTok, len |-> Big, src |-> "a"]}
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, heard, why, seen, forged, wrong, missed, loud, amp>>

\* B takes a packet that has arrived. An id it holds gets an answer; an id it does not hold gets a reset if the
\* packet is longer than a reset (always, in the _nosize witness), which the attacker sees go by.
BRecv(m) ==
    /\ m \in net /\ m.k = "pkt"
    /\ IF m.id \in holds
       THEN /\ net' = (net \ {m}) \cup {[k |-> "ack", id |-> m.id, t |-> NoTok, len |-> Big,
                                          src |-> "b"]}
            /\ UNCHANGED <<seen, amp>>
       ELSE IF ~SizeBound \/ m.len > ResetLen
            THEN LET r == [k |-> "reset", id |-> m.id, t |-> Tok(Key(inc), m.id), len |-> ResetLen,
                           src |-> "b"]
                 IN /\ net' = (net \ {m}) \cup {r}
                    /\ seen' = seen \cup {<<m.id, r.t>>}
                    \* A reset at least as long as the datagram it answers amplifies.
                    /\ amp' = (amp \/ ResetLen >= m.len)
            ELSE /\ net' = net \ {m}
                 /\ UNCHANGED <<seen, amp>>
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, heard, why, forged, wrong, missed, loud>>

\* A takes an answer of B: the open sessions of that id heard B within the round trip.
ARecvAck(m) ==
    /\ m \in net /\ m.k = "ack"
    /\ net' = net \ {m}
    /\ heard' = [s \in S |-> heard[s] \/ (up[s] /\ Id[s] = m.id)]
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, why, seen, forged, wrong, missed, loud, amp>>

\* Whether session s is quiet: it heard nothing from B for a round trip.
Quiet(s) == ~heard[s]

\* Whether A takes reset m for session s (`on_reset`): s is open, holds the id, has its token, and is quiet; with a
\* guard removed, that check is skipped.
Takes(m, s) ==
    /\ up[s]
    /\ Id[s] = m.id
    /\ (~CheckToken \/ tok[s] = m.t)
    /\ (~QuietGuard \/ Quiet(s))

\* A takes a reset that has arrived. The session it names ends, and so does its sub-session (`end_reset`).
ARecvReset(m) ==
    /\ m \in net /\ m.k = "reset"
    /\ LET hit == {s \in S : Takes(m, s)}
           \* "c" was opened over "p": it ends with it.
           ending == hit \cup (IF "p" \in hit THEN {"c"} ELSE {})
       IN /\ net' = net \ {m}
          /\ up' = [s \in S |-> up[s] /\ s \notin ending]
          /\ why' = [s \in S |-> IF s \in ending /\ up[s] THEN "reset" ELSE why[s]]
          \* A session of the running B ended: a reset that should not have worked did.
          /\ wrong' = (wrong \/ \E s \in ending : up[s] /\ owner[s] = inc)
          \* A reset ended a session that heard B within a round trip.
          /\ loud' = (loud \/ \E s \in hit : ~Quiet(s))
          \* B's own reset reached a quiet session of an older B by its id, and the session stayed up.
          /\ missed' = (missed \/ \E s \in S : m.src = "b" /\ up[s] /\ Id[s] = m.id /\ owner[s] < inc
                                                 /\ Quiet(s) /\ s \notin ending)
    /\ UNCHANGED <<inc, holds, opened, owner, tok, heard, seen, forged, amp>>

\* A datagram is lost.
Lose(m) ==
    /\ m \in net
    /\ net' = net \ {m}
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, heard, why, seen, forged, wrong, missed, loud, amp>>

\* B restarts: a new incarnation that holds no session. What was in flight stays in flight.
Restart ==
    /\ inc < MaxInc
    /\ inc' = inc + 1
    /\ holds' = {}
    /\ UNCHANGED <<up, opened, owner, tok, heard, why, net, seen, forged, wrong, missed, loud, amp>>

\* Once the held sessions are over, A's next dial opens "f" with a handshake to the running B, which gives its token.
Dial ==
    /\ ~up["p"] /\ ~up["c"] /\ ~opened["f"]
    /\ up' = [up EXCEPT !["f"] = TRUE]
    /\ opened' = [opened EXCEPT !["f"] = TRUE]
    /\ owner' = [owner EXCEPT !["f"] = inc]
    /\ holds' = holds \cup {"idf"}
    /\ tok' = [tok EXCEPT !["f"] = Tok(Key(inc), "idf")]
    /\ heard' = [heard EXCEPT !["f"] = TRUE]
    /\ UNCHANGED <<inc, why, net, seen, forged, wrong, missed, loud, amp>>

\* The attacker sends a reset to A from B's address: any id, with a token it made up or one it saw go by (a replay),
\* or a datagram of any length to B on an id nobody holds.
ForgeReset(id, t) ==
    /\ forged < MaxForge
    /\ t \in {Forged} \cup {p[2] : p \in seen}
    /\ forged' = forged + 1
    /\ net' = net \cup {[k |-> "reset", id |-> id, t |-> t, len |-> ResetLen, src |-> "x"]}
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, heard, why, seen, wrong, missed, loud, amp>>

ForgePkt(len) ==
    /\ forged < MaxForge
    /\ forged' = forged + 1
    /\ net' = net \cup {[k |-> "pkt", id |-> "idx", t |-> NoTok, len |-> len, src |-> "x"]}
    /\ UNCHANGED <<inc, holds, up, opened, owner, tok, heard, why, seen, wrong, missed, loud, amp>>

Next ==
    \/ RoundTrip
    \/ \E s \in S : ASend(s)
    \/ \E m \in net : BRecv(m) \/ ARecvAck(m) \/ ARecvReset(m) \/ Lose(m)
    \/ Restart
    \/ Dial
    \/ \E id \in Ids, t \in Tokens : ForgeReset(id, t)
    \/ \E len \in {ResetLen, Big} : ForgePkt(len)

Spec == Init /\ [][Next]_vars

\* A forged or replayed reset never ends a session the running B still holds.
ResetOnlyDead == ~wrong
\* A reset from a restarted B ends every quiet held session of an older B that it names.
ResetCloses == ~missed
\* A session a reset ended takes its sub-session with it.
ChildrenFollow == why["p"] = "reset" => ~up["c"]
\* A reset never ends a session that heard B within a round trip.
QuietOnly == ~loud
\* Every reset is smaller than the datagram it answers.
NoAmplify == ~amp
=============================================================================
