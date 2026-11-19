-------------------------- MODULE TraceBroadcastWire2 --------------------------
(***************************************************************************)
(* Trace validation of the version 2 message head: pinc-broadcast          *)
(* wire2.rs `Head2::parse`, `Head2::parse_prefix` and `Head2::write`.      *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_wire2.rs writes heads of every      *)
(* algorithm with 0, 1 and 8 parents, every flag class, blen at its edges, *)
(* and heads that write refuses (reserved flags, 9 parents, parents out of *)
(* order or repeated, a key or a signature one byte off); it parses every *)
(* written message, every proper cut of some, each with a byte appended    *)
(* and with single bytes changed (version, tag, flags, np, a parent byte), *)
(* and seeded random bytes behind a version byte, with parse and with      *)
(* parse_prefix. Each event must equal ParsePrefix, Parse or Write of      *)
(* BroadcastWire2.tla at the code's widths (origin and digests 32, 64-bit  *)
(* fields 8, counter and blen 4, at most 8 parents, the key and signature *)
(* lengths of each algorithm), reason for reason, and a written head is at *)
(* most MAX_HEAD2 bytes. Integers are recorded as big-endian byte arrays.  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/wire2.ndjson.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

\* pinc-crypto identity.rs: public key and signature lengths by tag (Ed25519's key is not on the wire)
KeyLen(t) == CASE t = 1 -> 32 [] t = 2 -> 33 [] t = 3 -> 1952 [] t = 4 -> 1984
SigLen(t) == CASE t = 1 -> 64 [] t = 2 -> 64 [] t = 3 -> 3309 [] t = 4 -> 3373

W == INSTANCE BroadcastWire2 WITH Sym <- {}, MaxLen <- 0, OrgW <- 32, IntW <- 8, CtrW <- 4, BlenW <- 4, DigW <- 32,
                                  MaxParents <- 8, Tags <- 1..4, PkW <- KeyLen, SigW <- SigLen, x <- <<>>

\* Sym is empty here: the model's ASSUMEs range over no head at these widths (BroadcastWire2.cfg checks them)
\* wire2.rs MAX_HEAD2 = FIXED_LEN + 32 * MAX_PARENTS + MAX_PUBLIC_KEY_LEN + MAX_SIGNATURE_LEN
ASSUME W!FixedLen = 68 /\ W!MaxHead2 = 68 + 32 * 8 + 1984 + 3373

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/wire2.ndjson")

Init == c = [t |-> "root"]

ParseEv(ev) ==
    LET r == W!Parse(ev.b)
    IN IF "h" \in DOMAIN ev THEN r.ok /\ r.h = ev.h /\ r.len = ev.len ELSE ~r.ok /\ r.why = ev.why

PrefixEv(ev) ==
    LET r == W!ParsePrefix(ev.b)
    IN IF "h" \in DOMAIN ev THEN r.ok /\ r.h = ev.h /\ r.len = ev.len /\ r.blen = ev.blen ELSE ~r.ok /\ r.why = ev.why

WriteEv(ev) ==
    LET r == W!Write(ev.h, ev.blen)
    IN IF "b" \in DOMAIN ev THEN r.ok /\ r.b = ev.b /\ Len(ev.b) <= W!MaxHead2 ELSE ~r.ok /\ r.why = ev.why

Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        LET ev == Trace[c.i]
        IN /\ ev.t = "w2"
           /\ CASE ev.op = "parse" -> ParseEv(ev) [] ev.op = "prefix" -> PrefixEv(ev) [] ev.op = "write" -> WriteEv(ev)
                [] ev.op \notin {"parse", "prefix", "write"} -> FALSE
=============================================================================
