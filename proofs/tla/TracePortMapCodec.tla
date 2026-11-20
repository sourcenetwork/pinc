-------------------------- MODULE TracePortMapCodec --------------------------
(***************************************************************************)
(* Trace validation of the PCP and NAT-PMP codecs (pinc-portmap pcp.rs,    *)
(* natpmp.rs) against their model, the layouts of Lean                     *)
(* proofs/lean/Pinc/PortMapCodec.lean (theorems dec_enc, enc_dec, dec_len, *)
(* pcp_map_len, pcp_header_len, nat_len, pcp_request_refuses).             *)
(*                                                                         *)
(* A layout is a sequence of fields: a constant run of bytes (Lean         *)
(* Fld.const) or a big-endian number of w bytes (Fld.num w). The layouts   *)
(* below are the Lean ones field for field, and Enc and Dec are Lean's enc *)
(* and dec: Enc writes the constants and the numbers in order; Dec reads   *)
(* an input of exactly the layout's length whose constant runs match, and  *)
(* gives the numbers. A number is written in the trace as its bytes.       *)
(*                                                                         *)
(* The Rust test tests/trace_portmap_codec.rs records one event per call   *)
(* of the eight public functions (encode_request, decode_request,          *)
(* encode_response, decode_response of each protocol):                     *)
(*  - "enc": the layout the value is written with, its numbers in field    *)
(*    order (an IPv4 address as its IPv4-mapped 16 bytes, as put_ip writes *)
(*    it) and the bytes the code wrote; they must be Enc of the layout.    *)
(*    An encode the code refuses is not recorded (which values a response  *)
(*    encoder refuses is a result-code rule, not modelled in Lean).        *)
(*  - "dec": the family decoded (pcpreq, pcpresp, natreq, natresp), the    *)
(*    input, and the code's answer: ok with the layout of the variant it   *)
(*    gave and its numbers, which must be Dec of that layout; or refused,  *)
(*    when no layout of the family reads the input, or when one of the     *)
(*    rules the Lean header lists as not modelled refuses it (a 24-byte    *)
(*    PCP MAP header with result SUCCESS; a NAT-PMP error form whose       *)
(*    opcode lacks the response bit or whose result is 0).                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds portmap/codec.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/portmap/codec.ndjson")

(* ---- the Lean layouts ---- *)
C(bs) == [k |-> "c", b |-> bs, w |-> Len(bs)]
N(w) == [k |-> "n", b |-> <<>>, w |-> w]
Z12 == <<0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>>
PcpMapRequest == <<C(<<2, 1, 0, 0>>), N(4), N(16), N(12), N(1), C(<<0, 0, 0>>), N(2), N(2), N(16)>>
PcpMapResponse == <<C(<<2, 129, 0>>), N(1), N(4), N(4), C(Z12), N(12), N(1), C(<<0, 0, 0>>), N(2), N(2), N(16)>>
PcpAnnounce == <<C(<<2, 128, 0>>), N(1), N(4), N(4), C(Z12)>>
PcpMapHeader == <<C(<<2, 129, 0>>), N(1), N(4), N(4), C(Z12)>>
NatAddressRequest == <<C(<<0, 0>>)>>
NatMapRequest == <<C(<<0, 1, 0, 0>>), N(2), N(2), N(4)>>
NatAddressResponse == <<C(<<0, 128>>), N(2), N(4), N(4)>>
NatMapResponse == <<C(<<0, 129>>), N(2), N(4), N(2), N(2), N(4)>>
NatError == <<C(<<0>>), N(1), N(2), N(4)>>

Layout(name) ==
    CASE name = "pcpMapRequest" -> PcpMapRequest
      [] name = "pcpMapResponse" -> PcpMapResponse
      [] name = "pcpAnnounce" -> PcpAnnounce
      [] name = "pcpMapHeader" -> PcpMapHeader
      [] name = "natAddressRequest" -> NatAddressRequest
      [] name = "natMapRequest" -> NatMapRequest
      [] name = "natAddressResponse" -> NatAddressResponse
      [] name = "natMapResponse" -> NatMapResponse
      [] name = "natError" -> NatError
Family(f) ==
    CASE f = "pcpreq" -> {"pcpMapRequest"}
      [] f = "pcpresp" -> {"pcpMapResponse", "pcpAnnounce", "pcpMapHeader"}
      [] f = "natreq" -> {"natAddressRequest", "natMapRequest"}
      [] f = "natresp" -> {"natAddressResponse", "natMapResponse", "natError"}

(* ---- Lean's enc and dec ---- *)
\* the widths of the numbers of a layout, in order
RECURSIVE NumWidths(_, _)
NumWidths(L, i) == IF i > Len(L) THEN <<>> ELSE (IF L[i].k = "n" THEN <<L[i].w>> ELSE <<>>) \o NumWidths(L, i + 1)
RECURSIVE Total(_, _)
Total(L, i) == IF i > Len(L) THEN 0 ELSE L[i].w + Total(L, i + 1)
Bytes(b) == \A x \in 1..Len(b) : b[x] \in 0..255
Fits(L, vs) ==
    LET ws == NumWidths(L, 1) IN Len(vs) = Len(ws) /\ \A j \in 1..Len(vs) : Len(vs[j]) = ws[j] /\ Bytes(vs[j])
RECURSIVE EncR(_, _, _, _)
EncR(L, vs, i, j) ==
    IF i > Len(L) THEN <<>>
    ELSE IF L[i].k = "c" THEN L[i].b \o EncR(L, vs, i + 1, j)
    ELSE vs[j] \o EncR(L, vs, i + 1, j + 1)
Enc(L, vs) == EncR(L, vs, 1, 1)
NoDec == [ok |-> FALSE, vs |-> <<>>]
RECURSIVE DecR(_, _, _, _)
DecR(L, b, i, off) ==
    IF i > Len(L) THEN [ok |-> TRUE, vs |-> <<>>]
    ELSE LET piece == SubSeq(b, off + 1, off + L[i].w)
             rest == DecR(L, b, i + 1, off + L[i].w)
         IN IF L[i].k = "c" THEN (IF piece = L[i].b THEN rest ELSE NoDec)
            ELSE IF rest.ok THEN [ok |-> TRUE, vs |-> <<piece>> \o rest.vs] ELSE NoDec
Dec(L, b) == IF Len(b) # Total(L, 1) THEN NoDec ELSE DecR(L, b, 1, 0)

\* the refusals the Lean header lists as not modelled
Extra(f, b) ==
    \/ f = "pcpresp" /\ Dec(PcpMapHeader, b).ok /\ b[4] = 0
    \/ f = "natresp" /\ Dec(NatError, b).ok /\ (b[2] < 128 \/ (b[3] = 0 /\ b[4] = 0))

Ev(ev) ==
    CASE ev.op = "enc" -> Bytes(ev.out) /\ Fits(Layout(ev.layout), ev.vs) /\ Enc(Layout(ev.layout), ev.vs) = ev.out
      [] ev.op = "dec" ->
           /\ Bytes(ev.b)
           /\ IF ev.ok
              THEN ev.layout \in Family(ev.fam) /\ Dec(Layout(ev.layout), ev.b) = [ok |-> TRUE, vs |-> ev.vs]
              ELSE (\A n \in Family(ev.fam) : ~Dec(Layout(n), ev.b).ok) \/ Extra(ev.fam, ev.b)

Init == c = [t |-> "root"]

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => Ev(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
