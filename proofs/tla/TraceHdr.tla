------------------------------ MODULE TraceHdr ------------------------------
(***************************************************************************)
(* Trace validation of the packet header codecs: vinc-transport            *)
(* packet/header.rs, packet/datagram.rs and the associated data of         *)
(* packet/protect.rs.                                                      *)
(*                                                                         *)
(* The Rust test tests/trace_hdr.rs calls the real LongHeader::write and   *)
(* parse, ShortHeader::write, short_dcid, unprotect_header, packets, seal  *)
(* and open on seeded inputs. Every call must give what the operators of   *)
(* HdrOps.tla give: the error with its number and the bytes a write left   *)
(* in the buffer (lw, sw), the fields and the header length (lp, sd), the  *)
(* packet-number length and key phase the first byte declares (un), every  *)
(* item of a datagram with the offset and the length of the bytes it lends *)
(* and its packet-number offset (dg), and the associated data the AEAD was *)
(* given, recorded by the provider, with the payload range (seal, open).   *)
(* The trace keeps every body length below 2^31; the Lean replay also      *)
(* reads the wide file (body lengths up to 2^64 - 1, where 2^63 and more   *)
(* are refused with nothing written). A truncated packet number of four    *)
(* bytes does not fit a TLC integer and is compared by the Lean replay.    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds hdr.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

CONSTANT Late
VARIABLE i
INSTANCE HdrOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/hdr.ndjson")
Ev0 == Trace[i]

HdrOf(e) == [ty |-> e.ty, dcid |-> e.dcid, scid |-> e.scid, bl |-> U!W(e.bl)]
SameW(r, e) == r.err = e.err /\ r.n = e.n /\ r.out = e.b
(* the truncated packet number of 1 to 3 bytes, big-endian *)
BE(pn) == IF Len(pn) = 1 THEN pn[1] ELSE IF Len(pn) = 2 THEN pn[1] * 256 + pn[2]
          ELSE (pn[1] * 256 + pn[2]) * 256 + pn[3]

LwEv == Ev0.op = "lw" /\ SameW(LongWrite(HdrOf(Ev0), Ev0.pn, Ev0.cap), Ev0)
LpEv == LET r == LongParse(Ev0.in)
        IN /\ Ev0.op = "lp" /\ r.err = Ev0.err /\ r.n = Ev0.n
           /\ r.err = "ok" => /\ r.ty = Ev0.ty /\ r.dcid = Ev0.dcid /\ r.scid = Ev0.scid
                              /\ r.bl = U!W(Ev0.bl) /\ r.hl = Ev0.hl
SwEv == Ev0.op = "sw" /\ SameW(ShortWrite([kp |-> Ev0.kp, dcid |-> Ev0.dcid], Ev0.pn, Ev0.cap), Ev0)
SdEv == LET r == ShortDcid(Ev0.in, Ev0.dl)
        IN Ev0.op = "sd" /\ r.err = Ev0.err /\ (r.err = "ok" => r.id = Ev0.id)
UnEv == LET r == ReadFirst(Ev0.first)
        IN /\ Ev0.op = "un" /\ r.err = Ev0.err
           /\ r.err = "ok" => /\ r.pl = Ev0.pl /\ r.kp = Ev0.kp /\ Len(Ev0.pn) = r.pl
                              /\ r.pl <= 3 => BE(Ev0.pn) = Ev0.tr

ItemOK(m, e) ==
    /\ m.k = e.k
    /\ m.k = "long" => /\ m.ty = e.ty /\ m.dcid = e.dcid /\ m.scid = e.scid /\ m.bl = U!W(e.bl) /\ m.hl = e.hl
                       /\ m.s = e.s /\ m.len = e.len /\ PnOff(m) = e.po
    /\ m.k = "short" => m.dcid = e.dcid /\ m.s = e.s /\ m.len = e.len /\ PnOff(m) = e.po
    /\ m.k = "err" => m.err = e.err /\ m.n = e.n /\ m.s = e.s
DgEv == LET R == Packets(Ev0.in, Ev0.dl)
        IN Ev0.op = "dg" /\ Len(R) = Len(Ev0.items) /\ \A k \in 1..Len(R) : ItemOK(R[k], Ev0.items[k])

SealEv == LET r == SealParts(Ev0.pk, Ev0.po, Ev0.pl, Ev0.pay)
          IN /\ Ev0.op = "seal" /\ r.err = Ev0.err /\ r.n = Ev0.n
             /\ r.err = "ok" => r.aad = Ev0.aad /\ r.total = Ev0.total
(* a packet the model splits reached the AEAD with the model's associated data, whether it then verified or not *)
OpenEv == LET r == OpenParts(Ev0.pk, Ev0.po, Ev0.pl)
          IN /\ Ev0.op = "open"
             /\ IF r.err = "ok"
                THEN /\ Ev0.reached /\ Ev0.err \in {"ok", "Record"} /\ r.aad = Ev0.aad
                     /\ Ev0.err = "ok" => r.ps = Ev0.ps /\ r.pe = Ev0.pe
                ELSE ~Ev0.reached /\ Ev0.err = r.err

Init == i = 1
Step == /\ i <= Len(Trace) /\ Ev0.t = "txhd"
        /\ (LwEv \/ LpEv \/ SwEv \/ SdEv \/ UnEv \/ DgEv \/ SealEv \/ OpenEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED i
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_i

Inv == TRUE
=============================================================================
