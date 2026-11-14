import Vinc.Json
import Vinc.TransportHdrBody

/-!
# Replay of the packet header traces

The Lean half of the trace validation of the packet header codecs (`packet/header.rs`, `packet/datagram.rs` and the
associated data of `packet/protect.rs`), the port of `proofs/tla/TraceHdr.tla`. It reads the `txhd` events written by
the Rust test `trace_hdr` and replays every call through the functions of `Vinc.TransportHdr`: the error and the
bytes of every write (the bytes a refused write left included), the fields, the header length and the error of every
parse, every item the datagram iterator yielded with its offset, its length and its packet-number offset, the first
byte `unprotect_header` read, and the associated data the AEAD was given by `seal` and `open` with the payload range.
The wide file has body lengths up to `2^64 - 1`.
-/

namespace Vinc.TraceHdr
open Vinc.Json Vinc.TransportHdr Vinc.TransportHdrBody Vinc.TransportReasm

def isTag (t : String) : Bool := t == "txhd"

/-- The name of an error and the number it carries, as `trace_hdr` writes them. -/
def errName : PErr → String × Nat
  | .truncated n => ("Truncated", n)
  | .bufferTooSmall n => ("BufferTooSmall", n)
  | .varintTooLong => ("VarintTooLong", 0)
  | .varintOverflow => ("VarintOverflow", 0)
  | .varintNonMinimal => ("VarintNonMinimal", 0)
  | .form => ("Form", 0)
  | .longType => ("LongType", 0)
  | .version v => ("Version", v)
  | .connIdLength => ("ConnIdLength", 0)
  | .reserved => ("Reserved", 0)
  | .pnLength => ("PnLength", 0)
  | .tooShort => ("TooShort", 0)
  | .length => ("Length", 0)

def tyOf (n : Nat) : LongType := if n = 1 then .zeroRtt else if n = 2 then .retry else .handshake

def bytesF (j : J) (k : String) : Except String (List Nat) := do natList (← field j k)

/-- The result of a write against the recorded one: the error, its number and the bytes left in the buffer. -/
def checkWrite (op : String) (r : WRes) (j : J) : Except String Unit := do
  let (e, n) := match r.err with
    | none => ("ok", 0)
    | some e => errName e
  check (e == (← strF j "err") && n == (← natF j "n")) s!"{op}: the model answers {e} {n}, the code {← strF j "err"}"
  check (r.out == (← bytesF j "b")) s!"{op}: the model leaves {r.out} in the buffer"

/-- One item of a datagram against the recorded one (an error carries no offset in the code). -/
def checkItem (it : Item) (j : J) : Except String Unit := do
  match it, ← strF j "k" with
  | .long h hl s n, "long" =>
    check (h == ⟨tyOf (← natF j "ty"), ← bytesF j "dcid", ← bytesF j "scid", ← natF j "bl"⟩) "dg: a long header differs"
    check (hl == (← natF j "hl") && s == (← natF j "s") && n == (← natF j "len") && it.pnOff == (← natF j "po"))
      s!"dg: the model has a long packet at {s} of {n} bytes with a header of {hl}"
  | .short d s n, "short" =>
    check (d == (← bytesF j "dcid") && s == (← natF j "s") && n == (← natF j "len") && it.pnOff == (← natF j "po"))
      s!"dg: the model has a short packet at {s} of {n} bytes"
  | .err e _, "err" =>
    let (e, n) := errName e
    check (e == (← strF j "err") && n == (← natF j "n")) s!"dg: the model ends with {e} {n}, the code with {← strF j "err"}"
  | _, k => throw s!"dg: the code yields {k} where the model yields another kind"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "lw" =>
    let h : LongHeader := ⟨tyOf (← natF j "ty"), ← bytesF j "dcid", ← bytesF j "scid", ← natF j "bl"⟩
    checkWrite "lw" (writeLong h (← natF j "pn") (← natF j "cap")) j
  | "lp" =>
    let err ← strF j "err"
    match parseLong (← bytesF j "in") with
    | .error e =>
      let (e, n) := errName e
      check (e == err && n == (← natF j "n")) s!"lp: the model answers {e} {n}, the code {err}"
    | .ok (h, hl) =>
      check (err == "ok") s!"lp: the model accepts, the code answers {err}"
      check (h == ⟨tyOf (← natF j "ty"), ← bytesF j "dcid", ← bytesF j "scid", ← natF j "bl"⟩ && hl == (← natF j "hl"))
        s!"lp: the fields differ: the model has a header of {hl} bytes and a body of {h.bodyLen}"
  | "sw" => checkWrite "sw" (writeShort ⟨← boolF j "kp", ← bytesF j "dcid"⟩ (← bytesF j "pn") (← natF j "cap")) j
  | "sd" =>
    let err ← strF j "err"
    match shortDcid (← bytesF j "in") (← natF j "dl") with
    | .error e => check ((errName e).1 == err) s!"sd: the model answers {(errName e).1}, the code {err}"
    | .ok d => check (err == "ok" && d == (← bytesF j "id")) s!"sd: the model reads {d}, the code answers {err}"
  | "un" =>
    let err ← strF j "err"
    match readFirst (← natF j "first") with
    | .error e => check ((errName e).1 == err) s!"un: the model answers {(errName e).1}, the code {err}"
    | .ok (pl, kp) =>
      let pn ← bytesF j "pn"
      check (err == "ok" && pl == (← natF j "pl") && kp == (← boolF j "kp") && pn.length == pl)
        s!"un: the model reads a length of {pl} and the key phase {kp}, the code answers {err}"
      check (pn.foldl (fun a b => a * 256 + b) 0 == (← natF j "tr")) "un: the truncated number differs"
  | "dg" =>
    let items := packets (← bytesF j "in") (← natF j "dl")
    match (← field j "items").arr? with
    | none => throw "dg: expected an array of items"
    | some a =>
      check (items.length == a.size) s!"dg: the model yields {items.length} items, the code {a.size}"
      for (it, v) in items.zip a.toList do
        checkItem it v
  | "seal" =>
    let err ← strF j "err"
    match sealParts (← bytesF j "pk") (← natF j "po") (← natF j "pl") (← natF j "pay") with
    | .error e =>
      let (e, n) := errName e
      check (e == err && n == (← natF j "n")) s!"seal: the model answers {e} {n}, the code {err}"
    | .ok p =>
      check (err == "ok") s!"seal: the model splits the packet, the code answers {err}"
      check (p.aad == (← bytesF j "aad") && p.total == (← natF j "total"))
        s!"seal: the associated data differs: the model takes {p.aad}"
  | "open" =>
    let err ← strF j "err"
    match openParts (← bytesF j "pk") (← natF j "po") (← natF j "pl") with
    | .error e =>
      check ((errName e).1 == err && !(← boolF j "reached")) s!"open: the model answers {(errName e).1}, the code {err}"
    | .ok p =>
      check ((err == "ok" || err == "Record") && (← boolF j "reached"))
        s!"open: the model splits the packet, the code answers {err}"
      check (p.aad == (← bytesF j "aad")) s!"open: the associated data differs: the model takes {p.aad}"
      if err == "ok" then
        check (p.payloadStart == (← natF j "ps") && p.payloadEnd == (← natF j "pe")) "open: the payload range differs"
  | "hw" =>
    -- a datagram a real client built: its Handshake packet, and the writer's puts reproduced by the model
    let d ← bytesF j "d"
    match parseLong d with
    | .error e => throw s!"hw: the model refuses the datagram: {(errName e).1}"
    | .ok (h, hl) =>
      let body := (d.drop hl).take h.bodyLen
      check (h.ty == .handshake) "hw: not a Handshake packet"
      match hsRead body with
      | none => throw "hw: the body does not parse"
      | some (t, o, data) =>
        check (body == hsBody t o data && h.bodyLen == hsBodyLen t o data.length)
          "hw: the body is not the three parts the header counts"
        check (!data.isEmpty && o + data.length ≤ t) "hw: the fragment is empty or runs past the message"
        check (hl + h.bodyLen ≤ (← natF j "win")) "hw: the packet is longer than the window"
        let w := hsWrite h.dcid h.scid t o data (← natF j "win")
        check (w.err == none && w.out == d.take (hl + h.bodyLen)) "hw: the model writes other bytes"
  | "hf" =>
    -- a body handed to `on_fragment`: the parse, the reassembly, and the bytes the buffer holds
    let body ← bytesF j "body"
    let mx ← natF j "max"
    let nr ← natF j "nr"
    let viewOf (v : J) : Except String R := do pure { runs := ← pairList (← field v "runs"), total := ← natF v "total" }
    let b ← viewOf (← field j "b")
    let a ← viewOf (← field j "a")
    let (out, r2) := hsRecv b mx nr body
    check ((out.map (fun t => (t : Int))).getD (-1) == (← intF j "ret")) "hf: the length handed over differs"
    check (r2 == a) s!"hf: the model computes {repr r2}, the code recorded {repr a}"
    match hsRead body with
    | none => pure ()
    | some (t, o, data) =>
      let stop := min (o + data.length) t
      let kept := out == some t || (r2.total == t && r2.runs.any fun (s, e) => s ≤ o && stop ≤ e)
      if o < stop && kept then
        let w ← bytesF j "w"
        check ((← natF j "mo") == o && w.take (stop - o) == data.take (min 48 (stop - o)))
          "hf: the buffer does not hold the bytes of the fragment"
  | "pad" =>
    let pre ← bytesF j "pre"
    let (e, n, out) := match padTo (← natF j "cap") (← natF j "min") pre with
      | .ok o => ("ok", 0, o)
      | .error e => ((errName e).1, (errName e).2, pre)
    check (e == (← strF j "err") && n == (← natF j "n") && out == (← bytesF j "out"))
      s!"pad: the model answers {e} {n} and leaves {out}"
  | "smp" =>
    let pk ← bytesF j "pk"
    let (e, s) := match sampleAt pk (← natF j "po") with
      | .ok s => ("ok", s)
      | .error e => ((errName e).1, [])
    check (e == (← strF j "err") && s == (← bytesF j "s")) s!"smp: the model answers {e}"
  | "smpp" =>
    -- the sample of a protected packet and of the same packet unmasked
    let p ← bytesF j "p"
    let u ← bytesF j "u"
    let po ← natF j "po"
    check (p.length == u.length && (List.range p.length).all fun i =>
        i == 0 || (po ≤ i && i < po + sampleSkip) || p[i]? == u[i]?)
      "smpp: unmasking changed a byte other than the first and the packet number"
    let sm (x : List Nat) : Option (List Nat) := match sampleAt x po with
      | .ok s => some s
      | .error _ => none
    check (sm p == sm u && (sm p).getD [] == (← bytesF j "s")) "smpp: the sample is not the same before and after"
  | op => throw s!"unknown header op {op}"

end Vinc.TraceHdr
