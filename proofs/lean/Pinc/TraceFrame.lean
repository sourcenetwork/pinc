import Pinc.Json
import Pinc.TransportFrame

/-!
# Replay of the frame codec traces

The Lean half of the trace validation of the PINCER frame codecs (`pinc-transport` `frame/`), the port of
`proofs/tla/TraceFrame.tla`. It reads the `txfr` events written by the Rust test `trace_frame` and replays every
call through the functions of `Pinc.TransportFrame`: the frame decoded and the bytes it took, the ranges of an ACK,
the bytes written and `encoded_len`, the frames `FrameIter` yields, `ack_len`, the overheads, and the error of every
refusal with its number must be the ones recorded, in the narrow file and in the wide one (numbers up to `2^64 - 1`,
the real `2^63` and `2^62 - 1`, varints of nine bytes and more).
-/

namespace Pinc.TraceFrame
open Pinc.Json Pinc.TransportFrame

def isTag (t : String) : Bool := t == "txfr"

def bytesF (j : J) (k : String) : Except String (List Nat) := do natList (← field j k)

def ticketOf (j : J) : Except String (List Nat × Nat) := do
  match ← natList (← field j "lt") with
  | [hi, lo] => pure (← bytesF j "tid", hi * 65536 + lo)
  | _ => throw "a ticket lifetime is not two halves"

def frameOf (j : J) : Except String Frame := do
  match ← strF j "k" with
  | "Padding" => pure (.padding (← natF j "len"))
  | "Ping" => pure .ping
  | "Ack" => pure (.ack (← natF j "largest") (← natF j "first") (← natF j "extra") (← bytesF j "tail"))
  | "ResetStream" => pure (.resetStream (← natF j "id") (← natF j "error") (← natF j "fs"))
  | "StopSending" => pure (.stopSending (← natF j "id") (← natF j "error"))
  | "Stream" =>
    pure (.stream (← natF j "id") (← natF j "off") (← boolF j "fin") (← bytesF j "data") (← boolF j "imp"))
  | "MaxStreamData" => pure (.maxStreamData (← natF j "id") (← natF j "max"))
  | "MaxStreams" => pure (.maxStreams (← natF j "limit"))
  | "PathChallenge" => pure (.pathChallenge (← bytesF j "d"))
  | "PathResponse" => pure (.pathResponse (← bytesF j "d"))
  | "Close" => pure (.close (← natF j "error"))
  | "Datagram" => pure (.datagram (← bytesF j "data") (← boolF j "imp"))
  | "MtuProbeEcho" => pure (.mtuProbeEcho (← natF j "mtu"))
  | "Sleep" => pure .sleep
  | "Wake" => pure .wake
  | "Rekey" => pure (.rekey (← boolF j "ans") (← bytesF j "sh") (← bytesF j "echo") (← natF j "spn"))
  | "Ready" => pure .ready
  | "NewTickets" =>
    match (← field j "es").arr? with
    | some a => pure (.newTickets (← a.toList.mapM ticketOf))
    | none => throw "the tickets are not an array"
  | "Extension" => pure (.ext (← natF j "ty") (← bytesF j "body"))
  | k => throw s!"unknown frame kind {k}"

def sameErr (what : String) (e : Err) (name : String) (n : Nat) : Except String Unit :=
  check (e.tag == (name, n)) s!"{what}: the model answers {e.tag.1} {e.tag.2}, the code {name} {n}"

/-- A write against the event: the same bytes, or the same refusal. -/
def sameWrite (what : String) (r : Except Err (List Nat)) (j : J) : Except String Unit := do
  match r with
  | .ok bs =>
    check (← boolF j "ok") s!"{what}: the model writes, the code refuses"
    check (bs == (← bytesF j "b")) s!"{what}: the bytes differ: model {bs}"
  | .error e =>
    check (!(← boolF j "ok")) s!"{what}: the model refuses with {e.tag.1}, the code writes"
    sameErr what e (← strF j "err") (← natF j "en")

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "dec" =>
    let b ← bytesF j "b"
    match decode b with
    | .ok (f, r) =>
      check (← boolF j "ok") s!"dec: the model accepts {repr f}, the code refuses"
      check (f == (← frameOf (← field j "f"))) s!"dec: the frame differs: model {repr f}"
      check (b.length - r.length == (← natF j "n")) "dec: the bytes consumed differ"
      match f with
      | .ack l fr x tail =>
        check (ackRanges l fr x tail == (← pairList (← field j "rg"))) "dec: the ranges of the ACK differ"
      | _ => pure ()
    | .error e =>
      check (!(← boolF j "ok")) s!"dec: the model refuses with {e.tag.1}, the code accepts"
      sameErr "dec" e (← strF j "err") (← natF j "en")
  | "enc" =>
    let f ← frameOf (← field j "f")
    check (f.encodedLen == (← natF j "len")) s!"enc: encoded_len differs: model {f.encodedLen}"
    sameWrite "enc" (f.write (← natF j "cap") []) j
  | "ack" =>
    let rs ← pairList (← field j "rs")
    sameWrite "ack" (writeAck (← natF j "cap") [] rs) j
    match ackLen rs with
    | .ok n =>
      check (← boolF j "lok") "ack: the model gives a length, the code refuses"
      check (n == (← natF j "len")) s!"ack: ack_len differs: model {n}"
    | .error e =>
      check (!(← boolF j "lok")) "ack: the model refuses the length, the code gives one"
      check (e.tag.1 == (← strF j "lerr")) "ack: the error of ack_len differs"
  | "iter" =>
    let (fs, e) := frames (← bytesF j "b")
    let want ← match (← field j "fs").arr? with
      | some a => a.toList.mapM frameOf
      | none => throw "the frames are not an array"
    check (fs == want) s!"iter: the frames differ: model {repr fs}"
    match e with
    | none => check ((← strF j "e") == "none") "iter: the model ends without an error, the code with one"
    | some e => sameErr "iter" e (← strF j "e") (← natF j "en")
  | "ovh" =>
    let dlen ← natF j "dlen"
    let imp ← boolF j "imp"
    check (streamOverhead (← natF j "id") (← natF j "off") dlen imp == (← natF j "so")) "ovh: stream_overhead differs"
    check (datagramOverhead dlen imp == (← natF j "do")) "ovh: datagram_overhead differs"
  | op => throw s!"unknown frame op {op}"

end Pinc.TraceFrame
