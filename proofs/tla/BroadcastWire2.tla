------------------------------ MODULE BroadcastWire2 ------------------------------
(***************************************************************************)
(* The version 2 message head of pinc-broadcast: wire2.rs                  *)
(* `Head2::parse_prefix`, `Head2::parse`, `Head2::check` and              *)
(* `Head2::write`, with wire.rs `read_key_sig` and `key_sig_fit`.          *)
(*                                                                         *)
(* The layout is the code's: ver1 alg1 flags1 np1 origin inc seq wall      *)
(* counter blen parents(np digests) [public key] signature, then exactly  *)
(* blen body bytes. The public key is absent for tag 1 (Ed25519, whose     *)
(* node id is the key). The widths are parameters (the code uses 32, 8, 8, *)
(* 8, 4, 4, 32 and the key and signature lengths of each algorithm);       *)
(* integers are fixed-width big-endian byte lists. The refusals carry the  *)
(* code's Malformed reasons in the code's order: "version", "algorithm",   *)
(* "parents" (np above MaxParents, read before the rest), "message cut     *)
(* short" (any read past the end), then check: "flags", "parents" (not     *)
(* strictly ascending), and for parse "body length".                       *)
(*                                                                         *)
(* Checked over every byte string up to MaxLen symbols (those of more than *)
(* 2 symbols start with the version): Canonical (a parsed head written     *)
(* back with its body gives the same bytes: one accepted encoding, and     *)
(* write accepts every head parse returns), Strict (no proper prefix and   *)
(* no one-symbol extension of a parsed message parses: blen is exact),     *)
(* PrefixOnly (parse_prefix does not look past the head). As ASSUMEs over  *)
(* every head of the alphabet (wrong key and signature lengths, reserved   *)
(* flags, too many and unordered parents included): RoundTrip (write then  *)
(* parse gives the head back) and Bound (no head is longer than MaxHead2). *)
(* Witness: BroadcastWire2_keyed.cfg (a head with a parent and a public    *)
(* key parses). TraceBroadcastWire2.tla checks the real code at the       *)
(* code's widths against ParsePrefix, Parse and Write.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Sym, MaxLen, OrgW, IntW, CtrW, BlenW, DigW, MaxParents, Tags, PkW(_), SigW(_)

Version == 2
Ed == 1
Fill(n, x) == [i \in 1..n |-> x]
\* k <= 4 only
BE(n, k) == [i \in 1..k |-> (n \div (256 ^ (k - i))) % 256]
RECURSIVE Cat(_)
Cat(s) == IF s = <<>> THEN <<>> ELSE Head(s) \o Cat(Tail(s))
LexLt(a, b) == \E k \in 1..Len(a) : a[k] < b[k] /\ \A j \in 1..(k - 1) : a[j] = b[j]
Ascending(ps) == \A i \in 1..(Len(ps) - 1) : LexLt(ps[i], ps[i + 1])
Sl(b, p, n) == SubSeq(b, p, p + n - 1)
Err(w) == [ok |-> FALSE, why |-> w]
Ok(b) == [ok |-> TRUE, b |-> b]
\* the small configs' key and signature widths (tag 1 carries no key: KeyW)
PkSmall(t) == 1
SigSmall(t) == 1

KeyW(t) == IF t = Ed THEN 0 ELSE PkW(t)
FixedLen == 4 + OrgW + 3 * IntW + CtrW + BlenW
HeadLen(t, np) == FixedLen + np * DigW + KeyW(t) + SigW(t)
Max2(S) == CHOOSE m \in S : \A y \in S : y <= m
MaxHead2 == FixedLen + DigW * MaxParents + Max2({KeyW(t) : t \in Tags}) + Max2({SigW(t) : t \in Tags})

\* parse_prefix: the head, its length and the blen it states, or the reason
ParsePrefix(b) ==
    IF Len(b) < 1 THEN Err("message cut short")
    ELSE IF b[1] # Version THEN Err("version")
    ELSE IF Len(b) < 2 THEN Err("message cut short")
    ELSE IF b[2] \notin Tags THEN Err("algorithm")
    ELSE IF Len(b) < 4 THEN Err("message cut short")
    ELSE IF b[4] > MaxParents THEN Err("parents")
    ELSE LET t == b[2]
             np == b[4]
             po == 5
             pi == po + OrgW
             ps == pi + IntW
             pw == ps + IntW
             pc == pw + IntW
             pb == pc + CtrW
             pp == pb + BlenW
             pk == pp + np * DigW
             pg == pk + KeyW(t)
         IN IF Len(b) < HeadLen(t, np) THEN Err("message cut short")
            ELSE LET h == [alg |-> t, flags |-> b[3], origin |-> Sl(b, po, OrgW), inc |-> Sl(b, pi, IntW),
                           seq |-> Sl(b, ps, IntW), wall |-> Sl(b, pw, IntW), ctr |-> Sl(b, pc, CtrW),
                           parents |-> [j \in 1..np |-> Sl(b, pp + (j - 1) * DigW, DigW)],
                           pk |-> Sl(b, pk, KeyW(t)), sig |-> Sl(b, pg, SigW(t))]
                 IN IF b[3] \div 2 # 0 THEN Err("flags")
                    ELSE IF ~Ascending(h.parents) THEN Err("parents")
                    ELSE [ok |-> TRUE, h |-> h, len |-> HeadLen(t, np), blen |-> Sl(b, pb, BlenW)]

\* parse: and the body that follows is exactly blen bytes (a body is never longer than 256^BlenW here)
Parse(b) ==
    LET r == ParsePrefix(b)
    IN IF ~r.ok THEN r
       ELSE IF BE(Len(b) - r.len, BlenW) # r.blen THEN Err("body length")
       ELSE r

\* write: check first (nothing is written on a refusal), then the layout
Write(h, blen) ==
    IF h.flags \div 2 # 0 THEN Err("flags")
    ELSE IF Len(h.parents) > MaxParents \/ ~Ascending(h.parents) THEN Err("parents")
    ELSE IF Len(h.pk) # KeyW(h.alg) \/ Len(h.sig) # SigW(h.alg) THEN Err("key or signature")
    ELSE Ok(<<Version, h.alg, h.flags, Len(h.parents)>> \o h.origin \o h.inc \o h.seq \o h.wall \o h.ctr \o blen
            \o Cat(h.parents) \o h.pk \o h.sig)

\* every head of the alphabet, wrong lengths, reserved flags and bad parent lists included
Digs == [1..DigW -> Sym]
HeadsOf(t) == {[alg |-> t, flags |-> fl, origin |-> o, inc |-> n, seq |-> n, wall |-> n, ctr |-> c, parents |-> p,
                pk |-> k, sig |-> g] :
                 fl \in {0, 1, 2}, o \in [1..OrgW -> Sym], n \in [1..IntW -> Sym], c \in [1..CtrW -> Sym],
                 p \in UNION {[1..m -> Digs] : m \in 0..(MaxParents + 1)},
                 k \in [1..KeyW(t) -> Sym] \union {Fill(KeyW(t) + 1, 0)},
                 g \in [1..SigW(t) -> Sym] \union {<<>>}}
Heads == UNION {HeadsOf(t) : t \in Tags}
Bodies == {<<>>} \union {<<s>> : s \in Sym}

RoundTrip == \A h \in Heads, bd \in Bodies :
    LET w == Write(h, BE(Len(bd), BlenW))
    IN w.ok => (Parse(w.b \o bd).ok /\ Parse(w.b \o bd).h = h /\ Parse(w.b \o bd).len = Len(w.b))
Bound == \A h \in Heads : Write(h, BE(0, BlenW)).ok => Len(Write(h, BE(0, BlenW)).b) <= MaxHead2
ASSUME RoundTrip
ASSUME Bound

AllBytes == (UNION {[1..n -> Sym] : n \in 0..2}) \union {<<Version>> \o s : s \in UNION {[1..n -> Sym] : n \in 0..(MaxLen - 1)}}

VARIABLE x
Init == x \in AllBytes
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

Canonical == LET r == Parse(x)
             IN r.ok => (Write(r.h, r.blen).ok /\ Write(r.h, r.blen).b \o SubSeq(x, r.len + 1, Len(x)) = x)

Strict == Parse(x).ok => /\ \A k \in 0..(Len(x) - 1) : ~Parse(SubSeq(x, 1, k)).ok
                         /\ \A s \in Sym : ~Parse(x \o <<s>>).ok

PrefixOnly == LET r == ParsePrefix(x)
              IN r.ok => \A k \in r.len..Len(x) :
                     LET p == ParsePrefix(SubSeq(x, 1, k)) IN p.ok /\ p.h = r.h /\ p.len = r.len /\ p.blen = r.blen

\* witness (must be violated): a head with a parent and a public key parses
NoKeyedParentHead == ~(Parse(x).ok /\ Len(Parse(x).h.parents) > 0 /\ Len(Parse(x).h.pk) > 0)
=============================================================================
