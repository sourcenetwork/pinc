import Vinc.Json
import Vinc.TransportHdr

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
open Vinc.Json Vinc.TransportHdr

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

def tyOf (n : Nat) : LongType := if n = 1 then .zeroRtt else .handshake

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
  | op => throw s!"unknown header op {op}"

end Vinc.TraceHdr
