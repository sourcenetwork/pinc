------------------------------ MODULE CoreStateOps ------------------------------
(***************************************************************************)
(* The operators of the endpoint's saved state (vinc-core state.rs, with   *)
(* ClientTickets::{export, restore} of vinc-security and the two tables of *)
(* vinc-core): the bytes `export_state` writes, the parse `restore_state`  *)
(* makes of them, and what a restore does to the three tables.             *)
(*                                                                         *)
(* A state is [tk, kr, ek]: the tickets (alg, node, alpn, tid, psk, aead,  *)
(* expiry, credit), the round trips (alg, node, rtt) and the prekey peers  *)
(* (alg, node, hash), each list oldest first, as the bytes hold them.      *)
(* `export_state` is `Enc`: version(1) tickets_len(4) tickets              *)
(* krtt_count(2) krtt ekk_count(2) ekk, the tickets as version(1)          *)
(* count(1) entries. `restore_state` reads the same fields in the order of *)
(* the code from a reader that fails on a short input (`Hdr`), checks      *)
(* every round trip and prekey entry before anything is stored (`PreOK`),  *)
(* lets `ClientTickets::restore` check its whole slice and then store it   *)
(* (`ParseTk`, `ApTk`), and then stores the round trips (`ApKr`) and the   *)
(* prekey peers (`ApEk`), which cannot fail. `Restore` runs these stages   *)
(* against a live state, so that a refusal that came after a write would   *)
(* show as a changed table.                                                *)
(*                                                                         *)
(* Numbers: the u64 fields (expiry, round trip) stay byte strings and are  *)
(* compared as such (`Ge`, `NonZero`), so a mutated byte never overflows   *)
(* TLC's integers; the length fields u32 and u16 are read saturated at     *)
(* 10^6 (every input of the checks is shorter, so a claim past the end     *)
(* is a claim past the end).                                               *)
(*                                                                         *)
(* Two switches build the wrong readers the witness configurations use:    *)
(* LAZY checks the round trips and prekey entries only while storing them  *)
(* (a refusal then comes after the tickets were stored), LAXTAIL lets      *)
(* bytes follow the state.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CT, KR, EK, LAZY, LAXTAIL

RECURSIVE Cat(_)
Cat(s) == IF s = <<>> THEN <<>> ELSE Head(s) \o Cat(Tail(s))

BEw(v, w) == [j \in 1..w |-> LET e == w - j IN (v \div (IF e = 0 THEN 1 ELSE IF e = 1 THEN 256 ELSE IF e = 2 THEN 65536 ELSE 16777216)) % 256]
\* a number below 2^31 as w bytes, big-endian (the upper bytes of a u64 are zero)
RECURSIVE BEr(_, _)
BEr(v, w) == IF w = 0 THEN <<>> ELSE BEr(v \div 256, w - 1) \o <<v % 256>>

RECURSIVE BEs(_)
BEs(bs) == IF bs = <<>> THEN 0
           ELSE LET a == BEs(SubSeq(bs, 1, Len(bs) - 1)) * 256 + bs[Len(bs)] IN IF a > 1000000 THEN 1000000 ELSE a

\* big-endian comparison of two byte strings of one length
RECURSIVE Ge(_, _)
Ge(a, b) == IF a = <<>> THEN TRUE ELSE IF Head(a) # Head(b) THEN Head(a) > Head(b) ELSE Ge(Tail(a), Tail(b))
NonZero(a) == \E i \in 1..Len(a) : a[i] # 0

(* ---- the reader of vinc-wire ---- *)
Cur(bs) == [bs |-> bs, i |-> 0]
Rd(c, n) == IF c.i + n > Len(c.bs) THEN [ok |-> FALSE, c |-> c, v |-> <<>>]
            ELSE [ok |-> TRUE, c |-> [c EXCEPT !.i = c.i + n], v |-> SubSeq(c.bs, c.i + 1, c.i + n)]
Fail == [ok |-> FALSE]

(* ---- one entry of each kind ---- *)
EncTk(t) == Cat(<<<<t.alg>>, t.node, <<Len(t.alpn)>>, t.alpn, t.tid, t.psk, <<t.aead>>, t.expiry, t.credit>>)
EncKr(e) == Cat(<<<<e.alg>>, e.node, e.rtt>>)
EncEk(e) == Cat(<<<<e.alg>>, e.node, e.hash>>)

ReadTk(c) ==
    LET a == Rd(c, 1) IN
    IF ~a.ok \/ a.v[1] \notin 1..4 THEN Fail
    ELSE LET nd == Rd(a.c, 32) IN
    IF ~nd.ok THEN Fail
    ELSE LET l == Rd(nd.c, 1) IN
    IF ~l.ok \/ l.v[1] \notin 1..32 THEN Fail
    ELSE LET al == Rd(l.c, l.v[1]) IN
    IF ~al.ok THEN Fail
    ELSE LET tid == Rd(al.c, 16) IN
    IF ~tid.ok THEN Fail
    ELSE LET psk == Rd(tid.c, 32) IN
    IF ~psk.ok THEN Fail
    ELSE LET ae == Rd(psk.c, 1) IN
    IF ~ae.ok \/ ae.v[1] \notin 1..2 THEN Fail
    ELSE LET ex == Rd(ae.c, 8) IN
    IF ~ex.ok THEN Fail
    ELSE LET cr == Rd(ex.c, 6) IN
    IF ~cr.ok THEN Fail
    ELSE [ok |-> TRUE, c |-> cr.c,
          e |-> [alg |-> a.v[1], node |-> nd.v, alpn |-> al.v, tid |-> tid.v, psk |-> psk.v, aead |-> ae.v[1],
                 expiry |-> ex.v, credit |-> cr.v]]

ReadKr(c) ==
    LET a == Rd(c, 1) IN
    IF ~a.ok \/ a.v[1] \notin 1..4 THEN Fail
    ELSE LET nd == Rd(a.c, 32) IN
    IF ~nd.ok THEN Fail
    ELSE LET r == Rd(nd.c, 8) IN
    IF ~r.ok THEN Fail
    ELSE [ok |-> TRUE, c |-> r.c, e |-> [alg |-> a.v[1], node |-> nd.v, rtt |-> r.v]]

ReadEk(c) ==
    LET a == Rd(c, 1) IN
    IF ~a.ok \/ a.v[1] \notin 1..4 THEN Fail
    ELSE LET nd == Rd(a.c, 32) IN
    IF ~nd.ok THEN Fail
    ELSE LET h == Rd(nd.c, 32) IN
    IF ~h.ok THEN Fail
    ELSE [ok |-> TRUE, c |-> h.c, e |-> [alg |-> a.v[1], node |-> nd.v, hash |-> h.v]]

\* n entries in a row
ReadK(k, c) == IF k = "tk" THEN ReadTk(c) ELSE IF k = "kr" THEN ReadKr(c) ELSE ReadEk(c)
RECURSIVE Many(_, _, _)
Many(k, c, n) ==
    IF n = 0 THEN [ok |-> TRUE, c |-> c, l |-> <<>>]
    ELSE LET r == ReadK(k, c) IN
         IF ~r.ok THEN Fail
         ELSE LET m == Many(k, r.c, n - 1) IN
              IF ~m.ok THEN Fail ELSE [ok |-> TRUE, c |-> m.c, l |-> <<r.e>> \o m.l]

(* ---- the tickets section: ClientTickets::export and restore's check ---- *)
EncTkSec(tk) == <<1, Len(tk)>> \o Cat([i \in 1..Len(tk) |-> EncTk(tk[i])])

ParseTk(bs) ==
    LET v == Rd(Cur(bs), 1) IN
    IF ~v.ok \/ v.v[1] # 1 THEN Fail
    ELSE LET n == Rd(v.c, 1) IN
    IF ~n.ok THEN Fail
    ELSE LET m == Many("tk", n.c, n.v[1]) IN
    IF ~m.ok \/ m.c.i # Len(bs) THEN Fail ELSE [ok |-> TRUE, l |-> m.l]

(* ---- export_state ---- *)
Enc(s) ==
    LET t == EncTkSec(s.tk) IN
    <<1>> \o BEw(Len(t), 4) \o t
    \o BEw(Len(s.kr), 2) \o Cat([i \in 1..Len(s.kr) |-> EncKr(s.kr[i])])
    \o BEw(Len(s.ek), 2) \o Cat([i \in 1..Len(s.ek) |-> EncEk(s.ek[i])])

(* ---- restore_state: the fields, in the order of the code ---- *)
Hdr(bs) ==
    LET v == Rd(Cur(bs), 1) IN
    IF ~v.ok \/ v.v[1] # 1 THEN Fail
    ELSE LET tl == Rd(v.c, 4) IN
    IF ~tl.ok THEN Fail
    ELSE LET tk == Rd(tl.c, BEs(tl.v)) IN
    IF ~tk.ok THEN Fail
    ELSE LET nk == Rd(tk.c, 2) IN
    IF ~nk.ok THEN Fail
    ELSE LET kr == Rd(nk.c, BEs(nk.v) * 41) IN
    IF ~kr.ok THEN Fail
    ELSE LET ne == Rd(kr.c, 2) IN
    IF ~ne.ok THEN Fail
    ELSE LET ek == Rd(ne.c, BEs(ne.v) * 65) IN
    IF ~ek.ok THEN Fail
    ELSE IF ~LAXTAIL /\ ek.c.i # Len(bs) THEN Fail
    ELSE [ok |-> TRUE, tk |-> tk.v, nk |-> BEs(nk.v), kr |-> kr.v, ne |-> BEs(ne.v), ek |-> ek.v]

ParseKr(h) == LET m == Many("kr", Cur(h.kr), h.nk) IN IF m.ok THEN [ok |-> TRUE, l |-> m.l] ELSE Fail
ParseEk(h) == LET m == Many("ek",Cur(h.ek), h.ne) IN IF m.ok THEN [ok |-> TRUE, l |-> m.l] ELSE Fail

\* the state the bytes hold, or a refusal
Parse(bs) ==
    LET h == Hdr(bs) IN
    IF ~h.ok THEN Fail
    ELSE LET t == ParseTk(h.tk) IN
    IF ~t.ok THEN Fail
    ELSE LET k == ParseKr(h) IN
    IF ~k.ok THEN Fail
    ELSE LET e == ParseEk(h) IN
    IF ~e.ok THEN Fail
    ELSE [ok |-> TRUE, v |-> [tk |-> t.l, kr |-> k.l, ek |-> e.l]]

(* ---- the tables ---- *)
Peer(e) == <<e.alg, e.node>>
Idx(s, p) == IF \E i \in 1..Len(s) : Peer(s[i]) = p
             THEN CHOOSE i \in 1..Len(s) : Peer(s[i]) = p /\ \A j \in 1..(i - 1) : Peer(s[j]) # p
             ELSE 0
Del(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

\* ClientTickets::insert, as the exported bytes show it: one ticket per peer, the newest last; the oldest makes room
TkIns(tk, t) ==
    IF CT = 0 THEN tk
    ELSE LET i == Idx(tk, Peer(t)) IN
         IF i > 0 THEN Del(tk, i) \o <<t>>
         ELSE IF Len(tk) = CT THEN Tail(tk) \o <<t>> ELSE tk \o <<t>>

RECURSIVE ApTk(_, _, _)
ApTk(tk, es, now) ==
    IF es = <<>> THEN [tk |-> tk, n |-> 0]
    ELSE LET e == Head(es)
             live == Ge(e.expiry, BEr(now, 8))
             r == ApTk(IF live THEN TkIns(tk, e) ELSE tk, Tail(es), now)
         IN [tk |-> r.tk, n |-> r.n + (IF live THEN 1 ELSE 0)]

\* NodeRtt::restore_peer: a round trip of 0 is skipped; a known peer is overwritten in place, a new one is refused when the table is full
RECURSIVE ApKr(_, _)
ApKr(kr, es) ==
    IF es = <<>> THEN [kr |-> kr, n |-> 0]
    ELSE LET e == Head(es)
             i == Idx(kr, Peer(e))
             step == IF ~NonZero(e.rtt) THEN [kr |-> kr, k |-> 0]
                     ELSE IF i > 0 THEN [kr |-> [kr EXCEPT ![i] = e], k |-> 1]
                     ELSE IF Len(kr) < KR THEN [kr |-> kr \o <<e>>, k |-> 1]
                     ELSE [kr |-> kr, k |-> 0]
             r == ApKr(step.kr, Tail(es))
         IN [kr |-> r.kr, n |-> r.n + step.k]

\* Table::insert of the prekey peers: replaced in place, or the oldest makes room
RECURSIVE ApEk(_, _)
ApEk(ek, es) ==
    IF es = <<>> THEN ek
    ELSE LET e == Head(es)
             i == Idx(ek, Peer(e))
         IN ApEk(IF i > 0 THEN [ek EXCEPT ![i] = e]
                 ELSE IF EK = 0 THEN ek
                 ELSE IF Len(ek) = EK THEN Tail(ek) \o <<e>> ELSE ek \o <<e>>, Tail(es))

(* ---- restore_state against a live state ---- *)
Refused(live) == [ok |-> FALSE, live |-> live]

\* Every stage in the order of the code: split, check the round trips and prekey peers, tickets (checked whole, then
\* stored), round trips, prekey peers. With LAZY the check of the round trips and prekey peers is deferred to the stage
\* that stores them.
Restore(live, bs, now) ==
    LET h == Hdr(bs) IN
    IF ~h.ok THEN Refused(live)
    ELSE IF ~LAZY /\ ~(ParseKr(h).ok /\ ParseEk(h).ok) THEN Refused(live)
    ELSE LET t == ParseTk(h.tk) IN
    IF ~t.ok THEN Refused(live)
    ELSE LET tk == ApTk(live.tk, t.l, now)
             live1 == [live EXCEPT !.tk = tk.tk]
             k == ParseKr(h) IN
    IF ~k.ok THEN Refused(live1)
    ELSE LET kr == ApKr(live.kr, k.l)
             e == ParseEk(h) IN
    IF ~e.ok THEN Refused([live1 EXCEPT !.kr = kr.kr])
    ELSE [ok |-> TRUE, live |-> [tk |-> tk.tk, kr |-> kr.kr, ek |-> ApEk(live.ek, e.l)],
          res |-> <<tk.n, kr.n, h.ne>>]
=============================================================================
