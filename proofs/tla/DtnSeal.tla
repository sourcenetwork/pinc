------------------------------ MODULE DtnSeal ------------------------------
(***************************************************************************)
(* The one-shot encryption of a bundle (pinc-dtn seal.rs, head.rs,         *)
(* endorse.rs): the bounded Dolev-Yao twin of Pinc/DtnSeal.lean.           *)
(*                                                                         *)
(* Terms are tuples; the algebra is free (perfect primitives), so two      *)
(* terms are equal iff their constructors and arguments are. Known(L, t)   *)
(* is the attacker's deduction from the leaks L:                           *)
(*   ssX(e, kp)   needs the static X25519 secret of kp, or the ephemeral   *)
(*                secret behind e, or a broken X25519 (bX);                *)
(*   ssK(sm, e)   needs the static decapsulation key, or the encapsulation *)
(*                message sm, or a broken ML-KEM (bK);                     *)
(*   key(k, x, t) = expand(extract(ck0, ss_K || ss_X), th) needs BOTH;     *)
(*   every public value is known.                                          *)
(* The senders are honest and seal bundles (Send); the leaks are chosen    *)
(* by the attacker in the initial state, which covers every order of       *)
(* compromise, a later leak of the recipient's statics included (that is   *)
(* the "no forward secrecy beyond key rotation" of the design). The        *)
(* recipient side (Decap, which recomputes the bundle id from the head's   *)
(* source, creation time and ephemeral key and refuses a mismatch) and the *)
(* slice AEAD (OpenSlice) are checked for                                  *)
(* every head the attacker can derive from a sent head by changing one     *)
(* field, against every recipient record (node, epoch, key pair).          *)
(*                                                                         *)
(* With SeedReuse = TRUE a sender may reuse its seeds: the checker then    *)
(* finds the nonce reuse the freshness assumption excludes.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Srcs,        \* honest sender nodes
          Nodes,       \* recipient nodes
          Kps,         \* recipient static key pairs
          Epochs,      \* recipient key epochs
          Walls,       \* creation times
          MaxB,        \* most bundles
          SeedReuse,   \* may a sender reuse its seeds
          LeakKinds,   \* the kinds of secret the attacker may hold
          BX0, BK0,    \* X25519 / ML-KEM broken from the start
          Pays         \* payload ids

VARIABLES bundles, L
vars == <<bundles, L>>

Seeds == 1..MaxB

(* ---- terms ---- *)
EPub(se) == <<"epub", se>>
EK(kp) == <<"ek", kp>>
Junk(n) == <<"junk", n>>
Ct(sm, e) == <<"ct", sm, e>>
SsX(e, kp) == <<"ssX", e, kp>>
SsK(sm, e) == <<"ssK", sm, e>>
Rej(kp, c) == <<"rej", kp, c>>
Bid(src, wall, ctr, e) == <<"bid", src, wall, ctr, e>>
Th(e, kp, node, epoch, c, i) == <<"th", e, kp, node, epoch, c, i>>
Key(k, x, t) == <<"key", k, x, t>>
Sealed(k, n, p) == <<"sealed", k, n, p>>

(* ---- the attacker's holdings ---- *)
Items == {<<"eK", s>> : s \in Seeds} \cup {<<"mK", s>> : s \in Seeds} \cup {<<"xK", p>> : p \in Kps}
         \cup {<<"kK", p>> : p \in Kps} \cup {<<"srcK", s>> : s \in Srcs} \cup {<<"sigK", s>> : s \in Srcs}
Allowed == {i \in Items : i[1] \in LeakKinds}
Has(kind, v) == <<kind, v>> \in L

EphK(e) == IF e[1] = "epub" THEN Has("eK", e[2]) ELSE TRUE
EkK(e) == IF e[1] = "ek" THEN Has("kK", e[2]) ELSE TRUE

RECURSIVE Known(_)
Known(t) ==
    CASE t[1] = "ssX" -> BX0 \/ Has("xK", t[3]) \/ EphK(t[2])
      [] t[1] = "ssK" -> BK0 \/ Has("mK", t[2]) \/ EkK(t[3])
      [] t[1] = "rej" -> BK0 \/ Has("kK", t[2])
      [] t[1] = "key" -> Known(t[2]) /\ Known(t[3])
      [] OTHER -> TRUE

(* ---- a bundle sealed by an honest sender ---- *)
BEph(b) == EPub(b.se)
BCt(b) == Ct(b.sm, EK(b.kp))
BId(b) == Bid(b.src, b.wall, b.ctr, BEph(b))
BTh(b) == Th(BEph(b), b.kp, b.dest, b.epoch, BCt(b), BId(b))
BKey(b) == Key(SsK(b.sm, EK(b.kp)), SsX(BEph(b), b.kp), BTh(b))
BHead(b) == [src |-> b.src, wall |-> b.wall, ctr |-> b.ctr, dst |-> b.dest, epoch |-> b.epoch, eph |-> BEph(b), ct |-> BCt(b),
             id |-> BId(b), lo |-> FALSE]
BOwn(b) == [node |-> b.dest, epoch |-> b.epoch, kp |-> b.kp]

PayloadKnown(b) == Known(BKey(b)) \/ Has("srcK", b.src)
XHalf(b) == BX0 \/ Has("xK", b.kp) \/ Has("eK", b.se)
KHalf(b) == BK0 \/ Has("mK", b.sm) \/ Has("kK", b.kp)

(* ---- the recipient: decapsulate ---- *)
DecapK(kp, c) == IF c[1] = "ct" /\ c[3] = EK(kp) THEN SsK(c[2], c[3]) ELSE Rej(kp, c)

\* the id recomputed from the head's source, creation time and ephemeral key (BundleId::derive)
Derived(h) == Bid(h.src, h.wall, h.ctr, h.eph)

\* decapsulate: the recipient and epoch, then the recomputed id (never trusted), then the key agreement
Decap(o, h) ==
    IF h.dst # o.node \/ h.epoch # o.epoch THEN [t |-> "wrong"]
    ELSE IF h.id # Derived(h) THEN [t |-> "badid"]
    ELSE IF h.lo THEN [t |-> "crypto"]
    ELSE [t |-> "ok", k |-> Key(DecapK(o.kp, h.ct), SsX(h.eph, o.kp), Th(h.eph, o.kp, o.node, o.epoch, h.ct, Derived(h)))]

Owns == [node : Nodes, epoch : Epochs, kp : Kps]

(* every head the attacker can derive from a sent head by changing one field *)
Heads(b) ==
    {BHead(b)}
    \cup {[BHead(b) EXCEPT !.dst = d] : d \in Nodes}
    \cup {[BHead(b) EXCEPT !.epoch = e] : e \in Epochs}
    \cup {[BHead(b) EXCEPT !.ct = c] : c \in {Junk(1), Ct(b.sm, EK(b.kp)), Ct(b.sm, EK(1 + (b.kp % Cardinality(Kps)))),
                                               Ct(1 + (b.sm % MaxB), EK(b.kp))}}
    \cup {[BHead(b) EXCEPT !.eph = e] : e \in {Junk(1), EPub(1 + (b.se % MaxB))}}
    \cup {[BHead(b) EXCEPT !.src = s] : s \in Srcs}
    \cup {[BHead(b) EXCEPT !.wall = w] : w \in Walls \cup {b.wall + 1}}
    \cup {[BHead(b) EXCEPT !.ctr = c] : c \in {1}}
    \cup {[BHead(b) EXCEPT !.id = Junk(1)], [BHead(b) EXCEPT !.lo = TRUE]}

(* ---- the slice AEAD: the nonce is injective in the index (Pinc.DtnSeal.nonce_inj) ---- *)
Nonce(i) == <<"nonce", i>>
SealSlice(k, i, p) == Sealed(k, Nonce(i), p)
OpenSlice(k, j, c) == IF c[1] = "sealed" /\ c[2] = k /\ c[3] = Nonce(j) THEN [ok |-> TRUE, p |-> c[4]] ELSE [ok |-> FALSE]
Idxs == 0..2

(* ---- the signed head ---- *)
HBody(b) == [src |-> b.src, id |-> BId(b), dst |-> b.dest, epoch |-> b.epoch, eph |-> BEph(b), ct |-> BCt(b),
             root |-> <<"root", b.pay>>, wall |-> b.wall]
Dig(body) == <<"hd", body>>
Sg(n, d) == <<"sg", n, d>>
HonestSigs == {<<b.src, Dig(HBody(b))>> : b \in {bundles[i] : i \in 1..Len(bundles)}}
Verify(s, body) == s = Sg(body.src, Dig(body))
KnownSig(n, d) == Has("sigK", n) \/ <<n, d>> \in HonestSigs
Tampered(b) ==
    {[HBody(b) EXCEPT !.src = s] : s \in Srcs} \cup {[HBody(b) EXCEPT !.dst = d] : d \in Nodes}
    \cup {[HBody(b) EXCEPT !.epoch = e] : e \in Epochs} \cup {[HBody(b) EXCEPT !.wall = w] : w \in Walls}
    \cup {[HBody(b) EXCEPT !.root = <<"root", p>>] : p \in Pays}
    \cup {[HBody(b) EXCEPT !.ct = Junk(1)], [HBody(b) EXCEPT !.eph = Junk(1)], [HBody(b) EXCEPT !.id = Junk(1)]}

BSet == {bundles[i] : i \in 1..Len(bundles)}

Init == /\ bundles = <<>>
        /\ L \in SUBSET Allowed

Send(src, kp, dest, epoch, wall, pay, n) ==
    /\ Len(bundles) < MaxB
    /\ \/ /\ ~SeedReuse /\ n = Len(bundles) + 1
       \/ /\ SeedReuse /\ n \in Seeds
    /\ bundles' = Append(bundles, [src |-> src, se |-> n, sm |-> n, kp |-> kp, dest |-> dest, epoch |-> epoch,
                                    wall |-> wall, ctr |-> 0, pay |-> pay])
    /\ UNCHANGED L

Next == \E src \in Srcs, kp \in Kps, dest \in Nodes, epoch \in Epochs, wall \in Walls, pay \in Pays, n \in Seeds :
            Send(src, kp, dest, epoch, wall, pay, n)

Spec == Init /\ [][Next]_vars

(* ================== properties ================== *)

\* Secrecy: the key is known exactly when both of its halves are
SecrecyIff == \A b \in BSet : Known(BKey(b)) <=> (XHalf(b) /\ KHalf(b))

\* the payload is known only to an attacker holding the sender or both halves of the key
PayloadSecret == \A b \in BSet : PayloadKnown(b) => (Has("srcK", b.src) \/ (XHalf(b) /\ KHalf(b)))

\* what the witness and single-primitive configurations assert: nothing is revealed
NotRevealed == \A b \in BSet : ~PayloadKnown(b)

\* decapsulation: agreement, the exact wrong-recipient condition, binding of the key, forged ciphertexts
DecapSound ==
    \A b \in BSet : \A o \in Owns : \A h \in Heads(b) :
        LET v == Decap(o, h)
            same == /\ o.node = b.dest /\ o.epoch = b.epoch /\ o.kp = b.kp /\ h.eph = BEph(b) /\ h.ct = BCt(b)
                    /\ h.id = BId(b)
            mine == h.dst = o.node /\ h.epoch = o.epoch
        IN /\ (v.t = "wrong") <=> ~mine
           \* the id is recomputed: a head whose id is not the derived one is never decapsulated
           /\ (v.t = "badid") <=> (mine /\ h.id # Derived(h))
           /\ (h.id # Derived(h)) => v.t # "ok"
           /\ (mine /\ h.id = Derived(h) /\ h.lo) <=> (v.t = "crypto")
           /\ (v.t = "ok") => ((v.k = BKey(b)) <=> same)
           /\ (v.t = "ok" /\ o = BOwn(b) /\ h.ct # BCt(b)) => v.k # BKey(b)
           /\ (o = BOwn(b) /\ h = BHead(b)) => v = [t |-> "ok", k |-> BKey(b)]

\* the AEAD: a slice opens exactly under its key and its index; a genuine recipient opens every slice
SliceBinding ==
    \A b \in BSet, i \in Idxs, j \in Idxs, c \in BSet :
        /\ OpenSlice(BKey(c), j, SealSlice(BKey(b), i, b.pay)).ok <=> (BKey(c) = BKey(b) /\ i = j)
        /\ (Decap(BOwn(b), BHead(b)).k = BKey(b) /\ OpenSlice(Decap(BOwn(b), BHead(b)).k, i, SealSlice(BKey(b), i, b.pay)).ok)

\* a (key, nonce) pair seals one plaintext: two bundles that share a key (and so a nonce space) seal the same payload
NonceUnique ==
    \A b \in BSet, c \in BSet, i \in Idxs : (BKey(b) = BKey(c)) => b.pay = c.pay

\* different seeds, different keys (given a fresh creation time)
KeysDistinct ==
    \A b \in BSet, c \in BSet : (BKey(b) = BKey(c)) => (b.src = c.src /\ b.se = c.se /\ b.sm = c.sm /\ b.kp = c.kp
                                                     /\ b.dest = c.dest /\ b.epoch = c.epoch /\ b.wall = c.wall /\ b.ctr = c.ctr)

\* authenticity: a tampered head never verifies under the old signature; a signature of an honest node on a digest
\* exists only if the node signed that head or its key leaked
AuthSound ==
    /\ \A b \in BSet : \A t \in Tampered(b) : Verify(Sg(b.src, Dig(HBody(b))), t) => t = HBody(b)
    /\ \A b \in BSet : \A t \in Tampered(b) : KnownSig(t.src, Dig(t)) => (Has("sigK", t.src) \/ \E c \in BSet : HBody(c) = t)
    /\ \A b \in BSet : Verify(Sg(b.src, Dig(HBody(b))), HBody(b))

TypeOK == /\ L \subseteq Allowed
          /\ Len(bundles) <= MaxB
=============================================================================
