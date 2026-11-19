import Pinc.Json
import Pinc.TransportFramePack

/-!
# Replay of the packet builder traces

The Lean half of the trace validation of the PINCER packet builder (`pinc-transport` `conn/send.rs`), the port of
`proofs/tla/TraceFramePack.tla`. It reads the `txpk` events written by the Rust test `trace_framepack`:

* a sealed packet (`pkt`): its mode, whether it took the pending tail repair as it was sealed and whether a repair
  is still pending then must be what `pick` gives for its path and some state of the probes (a probe or the probe
  timeout's packet takes no repair, so one due with it stays pending); the frames of the fill must parse (`frames`)
  with no error, none PADDING or CLOSE (CLOSE alone in the CLOSE packet) and none without its length; their kinds
  come in the order of the fill's slots for its mode (`ordered`); the place kept is the last frame exactly when a
  normal fill ends with a STREAM frame, with the size of the header before the length; `finish` of the fill is the
  payload sealed, and that payload parses into the frames written, the last without its length when it was dropped,
  then one PADDING frame for the padding (`expected`);
* a direct call of `implicit_stream_len` (`imp`) or `put_stream_header` (`hdr`): the model's answer and bytes.

Both files are replayed: the narrow one and the wide one (stream ids, offsets and lengths up to `2^64 - 1`).
-/

namespace Pinc.TraceFramePack
open Pinc.Json Pinc.TransportFrame Pinc.TransportFramePack

def isTag (t : String) : Bool := t == "txpk"

def bytesF (j : J) (k : String) : Except String (List Nat) := do natList (← field j k)

def modeOf : String → Except String Mode
  | "normal" => pure .normal
  | "pingonly" => pure .pingOnly
  | "probe" => pure .probe
  | "repair" => pure .repair
  | "close" => pure .close
  | m => throw s!"unknown mode {m}"

/-- Where the code keeps the place of the last STREAM frame: a normal fill that ends with one. -/
def hintOf (m : Mode) (b : List Nat) (fs : List Frame) : Option (Nat × Nat) :=
  match m, fs.getLast? with
  | .normal, some (.stream id off fin data imp) =>
    some (b.length - (Frame.stream id off fin data imp).encodedLen,
      streamOverhead id off data.length false - Varint.encodedLen data.length)
  | _, _ => none

def implicitFrame : Frame → Bool
  | .stream _ _ _ _ imp | .datagram _ imp => imp
  | _ => false

def isPadding : Frame → Bool
  | .padding _ => true
  | _ => false

def isClose : Frame → Bool
  | .close _ => true
  | _ => false

def replayPkt (j : J) : Except String Unit := do
  let b ← bytesF j "frames"
  let mode ← modeOf (← strF j "mode")
  let hint ← match ← bytesF j "hint" with
    | [] => pure none
    | [p, h] => pure (some (p, h))
    | _ => throw "pkt: the place kept is not a pair"
  let took ← boolF j "took"
  let left ← boolF j "left"
  let active ← boolF j "active"
  let name ← strF j "mode"
  check (mode == .close || [false, true].any fun probes => [false, true].any fun mtu =>
      pick probes mtu (took || left) active == (mode, took, left))
    (s!"pkt: a {name} packet that took the tail repair ({took}) and left one pending ({left}) " ++
      s!"on the active path ({active}) is not the choice of build_app")
  let (fs, e) := frames b
  check (e.isNone && !fs.isEmpty) "pkt: the fill does not parse into frames"
  check (fs.all (fun f => !isPadding f && !implicitFrame f)) "pkt: the fill wrote PADDING or left a length out"
  check (fs.all (fun f => isClose f == (mode == .close))) "pkt: CLOSE outside the CLOSE packet, or something else in it"
  check (ordered mode fs) s!"pkt: the frames are out of order: {fs.map Frame.kind}"
  check ((← strF j "kind") != "zrtt" || (← boolF j "client")) "pkt: a server sealed a 0-RTT packet"
  check (hint == hintOf mode b fs) s!"pkt: the place kept {hint} is not the model's {hintOf mode b fs}"
  match finish b hint (← natF j "min") with
  | none => throw "pkt: the model gives the packet up"
  | some (pay, pad, n) =>
    check (pay == (← bytesF j "pay")) "pkt: the payload sealed differs from the model's"
    check (frames pay == (expected fs pad n, none)) "pkt: the payload does not read back as the frames written"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "pkt" => replayPkt j
  | "imp" =>
    let b ← bytesF j "b"
    match implicitStreamLen b (← natF j "at") (← natF j "head") with
    | some (n, out) =>
      check (← boolF j "ok") "imp: the model drops the length, the code refuses"
      check (n == (← natF j "n")) "imp: the bytes dropped differ"
      check (out == (← bytesF j "out")) "imp: the frames after differ"
    | none =>
      check (!(← boolF j "ok")) "imp: the model refuses, the code drops the length"
      check (b == (← bytesF j "out")) "imp: a refusal changed the frames"
  | "hdr" =>
    let cap ← natF j "cap"
    let (ok, w) := putStreamHeader cap (← natF j "id") (← natF j "off") (← natF j "len") (← boolF j "fin")
    check (ok == (← boolF j "ok")) "hdr: the answer differs"
    check (w ++ List.replicate (cap - w.length) 170 == (← bytesF j "b")) "hdr: the bytes written differ"
  | op => throw s!"unknown packet builder op {op}"

end Pinc.TraceFramePack
