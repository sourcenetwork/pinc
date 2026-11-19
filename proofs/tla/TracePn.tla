------------------------------ MODULE TracePn -------------------------------
(***************************************************************************)
(* Trace validation of the packet-number codec: pinc-transport             *)
(* packet/number.rs.                                                       *)
(*                                                                         *)
(* The Rust test tests/trace_pn.rs calls the real encode_pn, decode_pn and *)
(* pn_len_for on seeded inputs (numbers near the edges of the window,      *)
(* every width including the refused ones, a largest received or none).    *)
(* Every call must give what the operators of PnOps.tla give, with the     *)
(* error the code returned. The trace keeps every number below 2^31 and    *)
(* the width of decode at 1 to 3; the Lean replay reads the wide file       *)
(* (numbers up to 2^64 - 1, the width 4, the real 2^62).                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds pn.ndjson.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

CONSTANTS BYTE, P62, MAXPN, TOP, WIDEWIN
VARIABLE i
INSTANCE PnOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/pn.ndjson")
Ev0 == Trace[i]

EncEv == LET r == EncodePn(Ev0.full, Ev0.len)
         IN Ev0.op = "enc" /\ r.err = Ev0.err /\ (r.err = "ok" => r.b = <<Ev0.b[1], Ev0.b[2], Ev0.b[3]>>)
DecEv == Ev0.op = "dec" /\ DecodePn(Ev0.tr, Ev0.len, Ev0.lg) = Ev0.r
ForEv == Ev0.op = "for" /\ PnLenFor(Ev0.w) = Ev0.len

Init == i = 1
Step == /\ i <= Len(Trace) /\ Ev0.t = "txpn" /\ (EncEv \/ DecEv \/ ForEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED i
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_i

Inv == TRUE
=============================================================================
