------------------------------ MODULE TraceHdr ------------------------------
(***************************************************************************)
(* Trace validation of the packet header codecs: pinc-transport            *)
(* packet/header.rs, packet/datagram.rs and the associated data of         *)
(* packet/protect.rs, and the body of a Handshake packet (write_handshake  *)
(* and on_fragment), pad_to and sample_at: hw (a datagram a real client    *)
(* built), hf (a body handed to a real connection's on_fragment, with the  *)
(* reassembly around it), pad, smp and smpp (the sample of a protected     *)
(* packet and of the unmasked one).                                        *)
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
(* variable PINC_TRACE_DIR, the directory that holds hdr.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

CONSTANT Late
VARIABLE i
INSTANCE HdrOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/hdr.ndjson")
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

(* a datagram a real client built: its Handshake packet carries the three parts, and the writer of the model puts
   the same bytes in a window of the size given *)
HwEv == LET r == LongParse(Ev0.d)
        IN /\ Ev0.op = "hw" /\ r.err = "ok" /\ r.ty = 0
           /\ LET end == r.hl + U!Val(r.bl)
                  body == SubSeq(Ev0.d, r.hl + 1, end)
                  p == HsRead(body)
              IN /\ p.ok /\ body = HsBody(p.total, p.off, p.data)
                 /\ r.bl = U!W(HsBodyLen(p.total, p.off, Len(p.data)))
                 /\ Len(p.data) > 0 /\ U!Le(U!Add(p.off, U!W(Len(p.data))), p.total)
                 /\ end <= Ev0.win
                 /\ LET w == HsWrite(r.dcid, r.scid, p.total, p.off, p.data, Ev0.win)
                    IN w.err = "ok" /\ w.out = SubSeq(Ev0.d, 1, end)
(* a body handed to on_fragment: the reassembly before and after, the length handed over, and the first bytes of
   the buffer at the offset: the fragment's bytes when the model keeps it *)
RunsOf(l) == [k \in 1..Len(l) |-> <<l[k][1], l[k][2]>>]
St(v) == [runs |-> RunsOf(v.runs), total |-> v.total]
HfWindow(x) ==
    LET p == HsRead(Ev0.body)
    IN IF ~p.ok \/ ~U!Lt(p.total, U!W(Ev0.max + 1)) \/ ~U!Lt(p.off, p.total) THEN TRUE
       ELSE LET t == U!Val(p.total)
                o == U!Val(p.off)
                stop == R!Mn(o + Len(p.data), t)
                ak == St(Ev0.a)
                kept == x.out = t \/ (ak.total = t /\ \E k \in 1..Len(ak.runs) : ak.runs[k][1] <= o /\ stop <= ak.runs[k][2])
                n == R!Mn(48, stop - o)
            IN (o < stop /\ kept) => /\ Ev0.mo = o /\ Len(Ev0.w) >= n /\ \A k \in 1..n : Ev0.w[k] = p.data[k]
HfEv == LET x == HsRecv(St(Ev0.b), Ev0.max, Ev0.nr, Ev0.body)
        IN /\ Ev0.op = "hf" /\ x.out = Ev0.ret /\ x.r = St(Ev0.a) /\ HfWindow(x)
PadEv == LET r == PadTo(Ev0.cap, Ev0.min, Ev0.pre)
         IN /\ Ev0.op = "pad" /\ r.err = Ev0.err /\ r.n = Ev0.n /\ r.out = Ev0.out
SmpEv == LET r == SampleAt(Ev0.pk, Ev0.po)
         IN /\ Ev0.op = "smp" /\ r.err = Ev0.err /\ (r.err = "ok" => r.s = Ev0.s) /\ (r.err # "ok" => Ev0.s = <<>>)
SmppEv == LET r == SampleAt(Ev0.p, Ev0.po)
          IN /\ Ev0.op = "smpp" /\ Len(Ev0.p) = Len(Ev0.u)
             /\ \A k \in 2..Len(Ev0.p) : (k <= Ev0.po \/ k > Ev0.po + SAMPLESKIP) => Ev0.p[k] = Ev0.u[k]
             /\ r = SampleAt(Ev0.u, Ev0.po) /\ (r.err = "ok" => r.s = Ev0.s) /\ (r.err # "ok" => Ev0.s = <<>>)

Init == i = 1
Step == /\ i <= Len(Trace) /\ Ev0.t = "txhd"
        /\ (LwEv \/ LpEv \/ SwEv \/ SdEv \/ UnEv \/ DgEv \/ SealEv \/ OpenEv \/ HwEv \/ HfEv \/ PadEv \/ SmpEv \/ SmppEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED i
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_i

Inv == TRUE
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
