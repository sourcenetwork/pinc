----------------------------- MODULE ConnectPack -----------------------------
(***************************************************************************)
(* Model check of the batch builder (carrier/frame.rs BatchBuilder) over   *)
(* the operators of ConnectPackOps.tla. A builder takes frames one at a    *)
(* time (DoOffer) and is closed once (DoFinish), after which a new one     *)
(* starts. The frames are real encoded carrier frames (a one-byte PING,    *)
(* SELF frames with a short and a long-header packet, a BATCH frame) and   *)
(* one whose encoder fails, offered in every order; the bounds are small   *)
(* so that every refusal is reached.                                       *)
(*                                                                         *)
(* Properties (Lean: Vinc/ConnectPackThm.lean):                            *)
(*  Inv       at most F frames and B bytes of frames, the bytes are the    *)
(*            sum of the lengths and the concatenation of the frames, they *)
(*            lie in the buffer, and no member is a long-header packet, a  *)
(*            BATCH or a frame that failed to encode (pack_bounds,         *)
(*            never_long)                                                  *)
(*  OfferOk   a frame is added exactly when it is neither BATCH nor a      *)
(*            long-header packet, the batch has room for another frame,    *)
(*            it encodes, it fits the buffer and the bytes stay within B;  *)
(*            a refused or failed offer changes nothing; an added frame is *)
(*            the last member (offer_added_iff, offer_stay, offer_order)   *)
(*  FinishOk  an empty batch finishes as nothing, one frame as itself,     *)
(*            more as a BATCH frame whose header fits the room kept for it *)
(*            and which Frame::decode reads back as exactly the members in *)
(*            order (finish_readback)                                      *)
(* Probe names a rule whose reach the Unreached invariant denies; Mut      *)
(* breaks one rule of the code for a witness run.                          *)
(***************************************************************************)
EXTENDS ConnectPackOps

CONSTANTS F, B, Cap, Mut, Probe
c == [F |-> F, B |-> B, Head |-> 2 + 3 * F, Cap |-> Cap]

Mk(raw, long, isbatch, bad, err) ==
    [raw |-> raw, n |-> Len(raw), long |-> long, isbatch |-> isbatch, bad |-> bad, err |-> err]
Ping == Mk(<<5>>, FALSE, FALSE, FALSE, "")
SelfA == Mk(<<7, 1>>, FALSE, FALSE, FALSE, "")
SelfB == Mk(<<7, 1, 2>>, FALSE, FALSE, FALSE, "")
SelfLong == Mk(<<7, 129>>, TRUE, FALSE, FALSE, "")
Bat == Mk(<<13, 2, 1, 1, 5, 6>>, FALSE, TRUE, FALSE, "")
SelfEmpty == Mk(<<7>>, FALSE, FALSE, TRUE, "packet")
Frames == {Ping, SelfA, SelfB, SelfLong, Bat, SelfEmpty}

VARIABLES st, body, acc, last, fin
vars == <<st, body, acc, last, fin>>

Init == /\ st = Empty /\ body = <<>> /\ acc = <<>>
        /\ last = [res |-> "none"] /\ fin = [kind |-> "init"]

cM == CASE Mut = "nobytes" -> [c EXCEPT !.B = c.B + 100, !.Cap = c.Cap + 100]
        [] Mut = "nocount" -> [c EXCEPT !.F = c.F + 5]
        [] Mut = "nofit" -> [c EXCEPT !.Cap = c.Cap + 100]
        [] OTHER -> c

DoOffer(fr) ==
    LET fr2 == CASE Mut = "nolong" -> [fr EXCEPT !.long = FALSE]
                 [] Mut = "nobatch" -> [fr EXCEPT !.isbatch = FALSE]
                 [] OTHER -> fr
        r == Offer(cM, st, fr2)
        added == r.r = "added"
    IN /\ st' = r.st
       /\ body' = IF added THEN body \o fr.raw ELSE body
       /\ acc' = IF added THEN Append(acc, fr) ELSE acc
       /\ last' = [pre |-> st, fr |-> fr, res |-> r.r, err |-> r.e, post |-> r.st]
       /\ fin' = fin

DoFinish ==
    LET r == Seal(c, st)
        rec == IF r.kind = "single" THEN body ELSE IF r.kind = "batch" THEN r.hd \o body ELSE <<>>
    IN /\ fin' = [kind |-> r.kind, rec |-> rec, hd |-> r.hd, len |-> r.len, ok |-> r.ok, acc |-> acc]
       /\ st' = Empty /\ body' = <<>> /\ acc' = <<>> /\ last' = [res |-> "none"]

Next == (\E fr \in Frames : DoOffer(fr)) \/ DoFinish

Spec == Init /\ [][Next]_vars

RECURSIVE SumL(_)
SumL(ls) == IF ls = <<>> THEN 0 ELSE Head(ls) + SumL(Tail(ls))
RECURSIVE CatRaw(_)
CatRaw(as) == IF as = <<>> THEN <<>> ELSE Head(as).raw \o CatRaw(Tail(as))

Inv == /\ Count(st) <= F /\ st.used <= B /\ st.used = SumL(st.lens)
       /\ (Count(st) > 0 => c.Head + st.used <= Cap)
       /\ st.lens = [i \in 1..Len(acc) |-> acc[i].n] /\ body = CatRaw(acc) /\ Len(body) = st.used
       /\ \A i \in 1..Len(acc) : /\ acc[i].n >= 1 /\ ~acc[i].long /\ ~acc[i].isbatch /\ ~acc[i].bad
                                 /\ Frame(acc[i].raw).ok

OfferOk ==
    last.res = "none" \/
    LET p == last.pre
        fr == last.fr
        start == c.Head + p.used
        fits == start + fr.n <= Cap
        added == ~fr.isbatch /\ ~fr.long /\ Count(p) < F /\ ~fr.bad /\ fits /\ p.used + fr.n <= B
        refused == ~added /\ (fr.isbatch \/ fr.long \/ Count(p) >= F \/ (Count(p) > 0 /\ ~fits)
                              \/ (~fr.bad /\ fits /\ p.used + fr.n > B))
    IN /\ (last.res = "added") <=> added
       /\ (last.res = "refused") <=> refused
       /\ (last.res = "added" => last.post = [lens |-> Append(p.lens, fr.n), used |-> p.used + fr.n])
       /\ (last.res # "added" => last.post = p)
       /\ (last.res = "err" =>
             \/ (last.err = "noroom" /\ ~fr.isbatch /\ ~fr.long /\ Count(p) < F /\ start > Cap)
             \/ (last.err = "small" /\ Count(p) = 0 /\ ~fits /\ start <= Cap /\ ~fr.isbatch /\ ~fr.long)
             \/ (last.err = fr.err /\ fr.bad /\ ~fr.isbatch /\ ~fr.long /\ Count(p) < F /\ start + fr.n <= Cap))

FinishOk ==
    fin.kind = "init" \/
    /\ fin.len = Len(fin.rec) /\ fin.ok /\ Len(fin.rec) <= c.Head + B
    /\ (fin.kind = "none") <=> (fin.acc = <<>>)
    /\ (fin.kind = "single" => /\ Len(fin.acc) = 1 /\ fin.rec = fin.acc[1].raw /\ Frame(fin.rec).ok)
    /\ (fin.kind = "batch" =>
          /\ Len(fin.acc) >= 2 /\ Len(fin.acc) <= F /\ Len(fin.hd) <= c.Head
          /\ Frame(fin.rec) = [ok |-> TRUE, v |-> [ty |-> 13, fs |-> [i \in 1..Len(fin.acc) |-> fin.acc[i].raw]],
                               r |-> <<>>])

(* reachability of each rule, for the witness configurations *)
Hit(p) ==
    CASE last.res = "none" -> FALSE
      [] p = "added" -> last.res = "added"
      [] p = "full" -> last.res = "refused" /\ Count(last.pre) = F /\ ~last.fr.long /\ ~last.fr.isbatch
      [] p = "bytes" -> last.res = "refused" /\ ~last.fr.long /\ ~last.fr.isbatch /\ Count(last.pre) < F
                         /\ ~last.fr.bad /\ c.Head + last.pre.used + last.fr.n <= Cap
                         /\ last.pre.used + last.fr.n > B
      [] p = "long" -> last.res = "refused" /\ last.fr.long
      [] p = "batch" -> last.res = "refused" /\ last.fr.isbatch
      [] p = "room" -> last.res = "refused" /\ ~last.fr.long /\ ~last.fr.isbatch /\ Count(last.pre) > 0
                        /\ Count(last.pre) < F /\ c.Head + last.pre.used + last.fr.n > Cap
      [] p = "errsmall" -> last.res = "err" /\ last.err = "small"
      [] p = "noroom" -> last.res = "err" /\ last.err = "noroom"
      [] p = "bad" -> last.res = "err" /\ last.err = "packet"
      [] OTHER -> FALSE
HitFin(p) ==
    CASE fin.kind = "init" -> FALSE
      [] p = "single" -> fin.kind = "single"
      [] p = "batchfin" -> fin.kind = "batch"
      [] p = "fullfin" -> fin.kind = "batch" /\ Len(fin.acc) = F
      [] p = "exact" -> fin.kind = "batch" /\ Len(fin.rec) - Len(fin.hd) = B
      [] p = "none" -> fin.kind = "none"
      [] OTHER -> FALSE
Unreached == ~(Hit(Probe) \/ HitFin(Probe))
=============================================================================
