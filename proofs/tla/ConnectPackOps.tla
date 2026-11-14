--------------------------- MODULE ConnectPackOps ---------------------------
(***************************************************************************)
(* The batch builder of vinc-connect/src/carrier/frame.rs (BatchBuilder,   *)
(* BatchState) as pure operators over its state. ConnectPack.tla (the      *)
(* model check) and TraceConnectPack.tla (the trace validation) both use   *)
(* them, so the two cannot differ.                                         *)
(*                                                                         *)
(* A configuration c has F (BATCH_MAX_FRAMES), B (BATCH_MAX_BYTES), Head   *)
(* (BATCH_HEAD_MAX = 2 + 3 F, the room kept before the frames for the      *)
(* header) and Cap (the length of the buffer the builder writes into; the  *)
(* real value of F is 64, of B 16384, of Head 194, and the code asks for a *)
(* buffer of MAX_FRAME_LEN = B + Head). The state is st = [lens, used]:    *)
(* the encoded length of every accepted frame in order (BatchState.lens    *)
(* and count) and the bytes they take (used). The frames are written back  *)
(* to back from offset Head of the buffer, so the header can be written    *)
(* right before them once the count is known.                              *)
(*                                                                         *)
(* An offered frame fr has n (its encoded length when it encodes, else the *)
(* bytes written before its encoder fails), long (a long-header packet),   *)
(* isbatch (a BATCH frame), bad (its encoder fails with err once the n     *)
(* bytes are written) and the bytes raw (used by the model check only).    *)
(* A put that does not fit the room left fails first: that is the wire     *)
(* error BufferTooSmall.                                                   *)
(*                                                                         *)
(* Lean counterpart: Vinc/ConnectPack.lean and ConnectPackThm.lean.        *)
(***************************************************************************)
EXTENDS ConnectCodecOps

Empty == [lens |-> <<>>, used |-> 0]
Count(st) == Len(st.lens)

\* BatchBuilder::offer; r is "added", "refused" or "err", e the error: "noroom" (FrameError::NoRoom), "small"
\* (the wire error BufferTooSmall, of the first frame of a batch) or the encoder's own
Offer(c, st, fr) ==
    LET start == c.Head + st.used
        room == c.Cap - start
        stay(r) == [r |-> r, e |-> "", st |-> st]
    IN IF fr.isbatch \/ fr.long \/ Count(st) >= c.F THEN stay("refused")
       ELSE IF start > c.Cap THEN [r |-> "err", e |-> "noroom", st |-> st]
       ELSE IF fr.n > room THEN (IF Count(st) > 0 THEN stay("refused") ELSE [r |-> "err", e |-> "small", st |-> st])
       ELSE IF fr.bad THEN [r |-> "err", e |-> fr.err, st |-> st]
       ELSE IF st.used + fr.n > c.B THEN stay("refused")
       ELSE [r |-> "added", e |-> "", st |-> [lens |-> Append(st.lens, fr.n), used |-> st.used + fr.n]]

RECURSIVE LensEnc(_)
LensEnc(ls) == IF ls = <<>> THEN <<>> ELSE VarEnc(Head(ls)) \o LensEnc(Tail(ls))

\* the header of a batch of these lengths: the type byte, the count, the lengths as varints
HeadBytes(lens) == <<13, Len(lens)>> \o LensEnc(lens)

\* BatchBuilder::finish (Seal, as Finish is the frame decoder's check of ConnectCodecOps): "none" for an empty batch, "single" for the one frame as it is, "batch" with the header
\* written in the Head bytes before the frames; the record is the header and the frames, of length len. ok is
\* whether the header fits the Head bytes kept for it (the code's NoRoom otherwise)
Seal(c, st) ==
    IF Count(st) = 0 THEN [kind |-> "none", len |-> 0, hd |-> <<>>, ok |-> TRUE]
    ELSE IF Count(st) = 1 THEN [kind |-> "single", len |-> st.used, hd |-> <<>>, ok |-> TRUE]
    ELSE LET hd == HeadBytes(st.lens)
         IN [kind |-> "batch", len |-> Len(hd) + st.used, hd |-> hd, ok |-> Len(hd) <= c.Head]
=============================================================================
