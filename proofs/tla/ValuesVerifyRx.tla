---------------------------- MODULE ValuesVerifyRx ----------------------------
(***************************************************************************)
(* The receive state of one request stream (vinc-values fetch/rx.rs) and   *)
(* the GroupVerifier of ValuesVerify.tla: the verifier stays at an item    *)
(* boundary whenever a frame starts.                                       *)
(*                                                                         *)
(* A response is a sequence of frames: a GROUP header (not seen by the     *)
(* verifier), `plen` bytes of proof pairs, then the bytes of one group. The *)
(* machine mirrors `Rx`: the header step (`header`: the proof of `plen`    *)
(* bytes follows, `enter_data` at once if there is none), `proof` (the     *)
(* verifier must be waiting for a pair; `take = min(piece, left)` bytes go *)
(* to `GroupVerifier::feed`, `left -= consumed`, `enter_data` when none is *)
(* left), `enter_data` (the verifier must be waiting for exactly this      *)
(* frame's group at the start of it, else the provider is reported; when   *)
(* the store holds the group verified, `skip_group`, which must not fail), *)
(* and `data` (the group bytes go to the verifier, or nothing when the     *)
(* group was skipped; the frame ends when none is left). The stored flag   *)
(* of every frame is chosen freely. The stream is the genuine encoder      *)
(* stream of ValuesVerify.tla for every value and requested range of the   *)
(* small seeds, the piece of every call any size up to the bytes left in   *)
(* its phase (a longer piece is a call with the rest of it after).         *)
(*                                                                         *)
(* At every state `Inv` holds: a frame never starts with the verifier      *)
(* mid-item; in the proof phase it holds no half-fed group; in the data   *)
(* phase of a fed group it waits for exactly that group and has taken the  *)
(* bytes consumed so far; in the data phase of a skipped group it is at a *)
(* boundary; the provider is never reported on a genuine stream, `skip_group` *)
(* is never refused after `enter_data`'s checks, and `data` always finds   *)
(* the verifier taking all the bytes (`consumed = take`). At the end every *)
(* group of the range was passed, in order, once, and the verifier is      *)
(* complete.                                                               *)
(*                                                                         *)
(* Lean counterpart: ValuesVerifyRx.lean (RxInv, hdrDone_inv, proofStep_inv, *)
(* dataStep_inv, enterData_total).                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT SeedSet

VARIABLES cfg, its, pos, gs, ph, left, skipf, fi, frames, bad, noconsume, stored, adv
vars == <<cfg, its, pos, gs, ph, left, skipf, fi, frames, bad, noconsume, stored, adv>>

U == INSTANCE U64
V == INSTANCE ValuesVerify WITH Extra <- 0, SkipOn <- TRUE, SeedSet <- SeedSet, cfg <- cfg, its <- its, vs <- 0,
                                pos <- pos, rem <- 0, stop <- FALSE, j <- 0, gs <- gs, agree <- TRUE, op <- "none"
GV == INSTANCE ValuesVerifyOps

(* the frames of the genuine stream: the group's offset and length and the bytes of proof pairs before it *)
RECURSIVE Fr(_, _, _, _, _)
Fr(its0, k, g, plen, acc) ==
    IF k > Len(its0) THEN acc
    ELSE LET it == its0[k]
         IN IF U!Sub(it.hi, it.lo) = U!One
            THEN Fr(its0, k + 1, g, U!Zero, Append(acc, [off |-> U!Val(U!Mul64(it.lo, g)), len |-> it.need, plen |-> plen]))
            ELSE Fr(its0, k + 1, g, U!Add(plen, it.need), acc)

Init == cfg = [k |-> "root"] /\ its = <<>> /\ pos = U!Zero /\ gs = <<>> /\ ph = "hdr" /\ left = U!Zero /\ skipf = FALSE
        /\ fi = 1 /\ frames = <<>> /\ bad = FALSE /\ noconsume = FALSE /\ stored = FALSE /\ adv = FALSE

Genuine(sd) == {x \in V!VB!CfgsOf(sd) : x.tam = -1}

(* enter_data for the frame fr on the verifier g0 at the stream position p0: the checks, and skip_group when stored;
   sets gs, pos, ph, left, skipf, bad *)
Enter(g0, p0, fr, s) ==
    IF GV!GNextItem(cfg.lay, g0) = <<"g", fr.off, U!Val(fr.len)>> /\ GV!GBoundary(g0)
    THEN IF s
         THEN LET sk == V!GSkip(cfg, g0)
              IN IF sk.ok
                 THEN /\ gs' = sk.g /\ pos' = U!Add(p0, sk.size) /\ ph' = "data" /\ left' = fr.len
                      /\ skipf' = TRUE /\ bad' = bad
                 ELSE /\ bad' = TRUE /\ gs' = g0 /\ pos' = p0 /\ UNCHANGED <<ph, left, skipf>>
         ELSE /\ ph' = "data" /\ left' = fr.len /\ skipf' = FALSE /\ gs' = g0 /\ pos' = p0 /\ bad' = bad
    ELSE /\ bad' = TRUE /\ gs' = g0 /\ pos' = p0 /\ UNCHANGED <<ph, left, skipf>>

Next ==
    \/ cfg.k = "root" /\ \E sd \in V!MySeeds : cfg' = [k |-> "seed", sd |-> sd]
       /\ UNCHANGED <<its, pos, gs, ph, left, skipf, fi, frames, bad, noconsume, stored, adv>>
    \/ cfg.k = "seed" /\ \E x \in Genuine(cfg.sd) :
           /\ cfg' = x /\ its' = V!VB!Items(x) /\ gs' = V!GInit(x, V!VB!Items(x))
           /\ frames' = Fr(V!VB!Items(x), 1, x.lay.g, U!Zero, <<>>)
           /\ UNCHANGED <<pos, ph, left, skipf, fi, bad, noconsume, stored, adv>>
    \/ \* the header of the next frame is in; a hostile provider may announce a proof one byte longer or shorter
       cfg.k = "cfg" /\ ~bad /\ ph = "hdr" /\ fi <= Len(frames) /\ \E s \in BOOLEAN, dp \in {0, 1, -1} :
           LET fr == frames[fi]
               plen1 == IF dp = 0 THEN fr.plen
                        ELSE IF dp = 1 THEN U!Add(fr.plen, U!One)
                        ELSE IF fr.plen = U!Zero THEN fr.plen ELSE U!Sub(fr.plen, U!One)
           IN /\ stored' = s /\ adv' = (adv \/ plen1 # fr.plen)
              /\ UNCHANGED <<cfg, its, fi, frames, noconsume>>
              /\ IF plen1 = U!Zero THEN Enter(gs, pos, fr, s)
                 ELSE /\ ph' = "proof" /\ left' = plen1 /\ UNCHANGED <<gs, pos, skipf, bad>>
    \/ \* a call of proof
       cfg.k = "cfg" /\ ~bad /\ ph = "proof" /\ \E t \in 1..U!Val(left) :
           LET fr == frames[fi]
               gf == V!GFeed(cfg, its, gs, pos, U!W(t))
               left1 == U!Sub(left, gf.consumed)
           IN /\ UNCHANGED <<cfg, its, fi, frames, noconsume, stored, adv>>
              /\ IF GV!GNextItem(cfg.lay, gs) # <<"p">> \/ gf.res \in {"reject", "sticky", "toomuch", "outputtoosmall"}
                 THEN /\ bad' = TRUE /\ UNCHANGED <<gs, pos, ph, left, skipf>>
                 ELSE IF left1 = U!Zero
                      THEN Enter(gf.g, U!Add(pos, gf.consumed), fr, stored)
                      ELSE /\ gs' = gf.g /\ pos' = U!Add(pos, gf.consumed)
                           /\ ph' = "proof" /\ left' = left1 /\ UNCHANGED <<skipf, bad>>
    \/ \* a call of data
       cfg.k = "cfg" /\ ~bad /\ ph = "data" /\ \E t \in 1..U!Val(left) :
           LET gf == V!GFeed(cfg, its, gs, pos, U!W(t))
               left1 == U!Sub(left, U!W(t))
           IN /\ UNCHANGED <<cfg, its, frames, bad, skipf, stored, adv>>
              /\ IF skipf
                 THEN UNCHANGED <<gs, pos, noconsume>>
                 ELSE /\ gs' = gf.g /\ pos' = U!Add(pos, gf.consumed)
                      /\ noconsume' = (gf.consumed # U!W(t))
              /\ IF left1 = U!Zero THEN ph' = "hdr" /\ left' = U!Zero /\ fi' = fi + 1
                 ELSE ph' = "data" /\ left' = left1 /\ UNCHANGED fi

Spec == Init /\ [][Next]_vars

Inv ==
    IF cfg.k # "cfg" THEN TRUE
    ELSE /\ (~adv => ~bad) /\ ~noconsume
         /\ (gs.failed = "none" \/ bad)
         /\ ~bad => (ph = "hdr" => GV!GBoundary(gs))
         /\ ~bad => (ph = "proof" => gs.groupN = U!Zero)
         /\ ~bad => (ph = "data" /\ ~skipf =>
               /\ GV!GNextItem(cfg.lay, gs) = <<"g", frames[fi].off, U!Val(frames[fi].len)>>
               /\ U!Add(gs.groupN, left) = frames[fi].len /\ gs.pairN = U!Zero)
         /\ ~bad => (ph = "data" /\ skipf => GV!GBoundary(gs))
         /\ (~adv /\ fi > Len(frames) =>
               /\ gs.stack = <<>> /\ ph = "hdr"
               /\ Len(gs.done) = U!Val(U!Sub(cfg.last, cfg.first))
               /\ \A i \in 1..Len(gs.done) : gs.done[i][1] = U!Mul64(U!Add(cfg.first, U!W(i - 1)), cfg.lay.g))
=============================================================================
