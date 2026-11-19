--------------------------- MODULE ConnectNodeIdOps ---------------------------
(***************************************************************************)
(* The wire form of a node id (pinc-connect carrier/node.rs, `read` and    *)
(* `write`) as pure operators. ConnectNodeId.tla (the model check) and     *)
(* TraceConnectNodeId.tla (the trace validation) use them.                 *)
(*                                                                         *)
(* A node id is one algorithm tag byte then 32 identifier bytes            *)
(* (NODE_ID_LEN = 33). The known tags are those of                         *)
(* pinc_crypto::IdentityAlg::from_tag: 1 Ed25519, 2 EcdsaP256, 3 MlDsa65,  *)
(* 4 Hybrid. Byte strings are sequences of naturals below 256.             *)
(***************************************************************************)
EXTENDS Integers, Sequences

NODEIDLEN == 33
TAGS == 1..4

(* node::read on a reader whose remaining bytes are b. The code reads the tag with read_u8 (Truncated { needed: 1 }
   on an empty input), then 32 bytes with read_array (Truncated { needed: 32 - remaining }), and only then maps the
   tag (Unexpected for an unknown one), all on a copy of the reader that replaces it only on success: used is the
   number of bytes the reader advanced. *)
NodeRead(b) ==
    IF Len(b) = 0 THEN [kind |-> "trunc", needed |-> 1, alg |-> 0, bytes |-> <<>>, used |-> 0]
    ELSE IF Len(b) - 1 < 32 THEN [kind |-> "trunc", needed |-> 32 - (Len(b) - 1), alg |-> 0, bytes |-> <<>>, used |-> 0]
    ELSE IF b[1] \notin TAGS THEN [kind |-> "tag", needed |-> 0, alg |-> 0, bytes |-> <<>>, used |-> 0]
    ELSE [kind |-> "ok", needed |-> 0, alg |-> b[1], bytes |-> SubSeq(b, 2, 33), used |-> NODEIDLEN]

(* node::write into a writer with room bytes left: ensure(NODE_ID_LEN) first (BufferTooSmall { needed: 33 - room },
   nothing written), then the tag and the 32 bytes *)
NodeWrite(alg, bytes, room) ==
    IF NODEIDLEN > room THEN [kind |-> "small", needed |-> NODEIDLEN - room, out |-> <<>>]
    ELSE [kind |-> "ok", needed |-> 0, out |-> <<alg>> \o bytes]
=============================================================================
