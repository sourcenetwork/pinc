------------------------- MODULE IntegrationCodecsOps -------------------------
(***************************************************************************)
(* Three small round trips of the integration layer as pure operators:     *)
(*                                                                         *)
(* relay path addresses (vinc-core relay_net.rs): RelayAddr is relay_addr  *)
(* and RelayParts is relay_parts, on the IP of an address (the port is     *)
(* not part of the model: relay_addr gives port 0 and relay_parts ignores  *)
(* the port it is given). An address is [v6, s] with s the four octets or  *)
(* the eight 16-bit segments. B is the number of values of an octet (256)  *)
(* and the peer slot is two octets (peer < B^2); M4 is the first octet of  *)
(* an IPv4 relay address (240), S0, S1, S2 the first three segments of an  *)
(* IPv6 one (0xfd56, 0x494e, 0x43), and a relay slot is below B.           *)
(*                                                                         *)
(* the stream tag (vinc protocol.rs): TagWrite is write_tag, TagRead is    *)
(* read_tag on a stream that holds the bytes given and then ends: one      *)
(* length byte (1 to MAXTAG = 64) then that many bytes. It returns the     *)
(* tag and the bytes left unread (rest); a length byte out of range is the *)
(* Config refusal with only that byte read; a stream that ends first is    *)
(* "eof" (the stream's own error, nothing is said about what is left).     *)
(*                                                                         *)
(* the stream id of a range-proof body (vinc-node values_frames.rs):       *)
(* HeadSid is head_sid and WithSid is with_sid into a buffer of EXTMAX     *)
(* bytes, on the varint of Varint.tla (machine words of U64.tla); it       *)
(* returns the bytes written.                                              *)
(*                                                                         *)
(* BUG names a deliberately wrong rule the witness configs switch on:      *)
(* "nobound" (relay_parts takes any segment as a relay slot, truncated),   *)
(* "tagzero" (read_tag accepts a length byte of 0), "readpast" (it reads   *)
(* one byte more than the length), "wlong" (write_tag accepts MAXTAG + 1), *)
(* "sidskip" (with_sid copies the rest from one byte too late) and         *)
(* "nocap" (it does not check the result against EXTMAX).                  *)
(* Lean counterparts: Vinc/RelayNet.lean, StreamTag.lean, ValuesFrames.lean.*)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS B, M4, S0, S1, S2, MAXTAG, EXTMAX, BUG

V == INSTANCE Varint WITH SmallMax <- 0, c <- 0
U == INSTANCE U64

(* ---- relay_addr and relay_parts ---- *)
RelayAddr(v6, r, p) ==
    IF v6 THEN [v6 |-> TRUE, s |-> <<S0, S1, S2, 0, 0, r, 0, p>>]
    ELSE [v6 |-> FALSE, s |-> <<M4, r, p \div B, p % B>>]

RelayParts(a) ==
    IF ~a.v6
    THEN IF a.s[1] = M4 THEN [ok |-> TRUE, relay |-> a.s[2], peer |-> a.s[3] * B + a.s[4]]
         ELSE [ok |-> FALSE]
    ELSE LET s == a.s IN
         IF s[1] = S0 /\ s[2] = S1 /\ s[3] = S2 /\ s[4] = 0 /\ s[5] = 0
            /\ (BUG = "nobound" \/ s[6] < B) /\ s[7] = 0
         THEN [ok |-> TRUE, relay |-> s[6] % B, peer |-> s[8]]
         ELSE [ok |-> FALSE]

(* ---- write_tag and read_tag ---- *)
TagWrite(t) ==
    IF Len(t) >= 1 /\ Len(t) <= (IF BUG = "wlong" THEN MAXTAG + 1 ELSE MAXTAG)
    THEN [ok |-> TRUE, b |-> <<Len(t)>> \o t]
    ELSE [ok |-> FALSE, e |-> "config"]

TagRead(b) ==
    IF Len(b) = 0 THEN [ok |-> FALSE, e |-> "eof", rest |-> <<>>]
    ELSE LET n == b[1]
             r == Tail(b)
             take == IF BUG = "readpast" THEN n + 1 ELSE n
         IN IF n < (IF BUG = "tagzero" THEN 0 ELSE 1) \/ n > MAXTAG
            THEN [ok |-> FALSE, e |-> "config", rest |-> r]
            ELSE IF take > Len(r) THEN [ok |-> FALSE, e |-> "eof", rest |-> <<>>]
            ELSE [ok |-> TRUE, tag |-> SubSeq(r, 1, take), rest |-> SubSeq(r, take + 1, Len(r))]

(* ---- head_sid and with_sid ---- *)
HeadSid(b) ==
    LET d == V!Decode(b) IN
    IF d.kind = "ok" THEN [ok |-> TRUE, v |-> d.v] ELSE [ok |-> FALSE]

WithSid(b, sid) ==
    LET d == V!Decode(b) IN
    IF d.kind # "ok" THEN [ok |-> FALSE]
    ELSE LET e == V!Encode(sid, EXTMAX) IN
         IF e.kind # "ok" THEN [ok |-> FALSE]
         ELSE LET rest == SubSeq(b, d.n + (IF BUG = "sidskip" THEN 1 ELSE 0) + 1, Len(b)) IN
              IF Len(e.bytes) + Len(rest) > EXTMAX /\ BUG # "nocap" THEN [ok |-> FALSE]
              ELSE [ok |-> TRUE, out |-> e.bytes \o rest]

=============================================================================
