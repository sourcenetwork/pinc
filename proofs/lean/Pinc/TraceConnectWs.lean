import Pinc.Json
import Pinc.ConnectWs

/-!
# Replay of the WebSocket framing traces

The Lean half of the trace validation of the WebSocket framing of the carrier (`carrier/ws.rs`), the port of
`proofs/tla/TraceConnectWs.tla`. It reads the `ws` events written by the Rust test `trace_connect_ws` and replays every
call of the real encoder (`encode`) and decoder (`Decoder::decode`) through `Pinc.ConnectWs`: the model must write the
bytes the code wrote or refuse as the code did, and must ask for more, refuse with the same error, or accept the same
frame (kind, unmasked payload, close status, bytes used) as the code did. A decoder's one bit of state (a fragmented
message is open) is tracked per decoder by the model from its calls, so every later answer checks it.
-/

namespace Pinc.TraceConnectWs
open Pinc.Json Pinc.ConnectWs

def isTag (t : String) : Bool := t == "ws"

structure W where
  mp : Nat := 0
  dec : Std.HashMap Nat (Peer × Bool) := {}

def errName : Err → String
  | .reserved => "reserved"
  | .opcode => "opcode"
  | .mask => "mask"
  | .control => "control"
  | .sequence => "sequence"
  | .tooLong => "toolong"
  | .lenForm => "lenform"
  | .noRoom => "noroom"

def kindName : Kind → String
  | .data => "data"
  | .close => "close"
  | .ping => "ping"
  | .pong => "pong"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let mp ← natF j "mp"
    check (decide (mp < 65536)) "MAX_PAYLOAD must be under 65536 (the 64-bit length form is then never accepted)"
    pure { w with mp }
  | "new" =>
    let peer ← match ← strF j "peer" with
      | "client" => pure Peer.client
      | "server" => pure Peer.server
      | s => throw s!"unknown peer {s}"
    pure { w with dec := w.dec.insert (← natF j "id") (peer, false) }
  | "enc" =>
    let key ← natList (← field j "mask")
    let mk := if key.isEmpty then none else some key
    let r := encode w.mp (← natF j "code") (← natList (← field j "pl")) mk (← natF j "cap")
    match r, ← strF j "res" with
    | .ok b, "ok" => check (b == (← natList (← field j "b"))) "enc: different bytes written"
    | .ok _, res => throw s!"enc: the model writes the frame, the code answered {res}"
    | .error e, res => check (errName e == res) s!"enc: the model refuses with {errName e}, the code answered {res}"
    pure w
  | "dec" =>
    let id ← natF j "id"
    let (peer, inm) ← match w.dec.get? id with
      | some x => pure x
      | none => throw s!"dec: no decoder {id}"
    let buf ← natList (← field j "buf")
    let r := decode w.mp peer inm (bf buf) buf.length
    match r, ← strF j "res" with
    | .idle, "idle" => pure w
    | .err e, "err" =>
      check (errName e == (← strF j "e")) s!"dec: the model refuses with {errName e}, the code with {← strF j "e"}"
      pure w
    | .frame k pl st used inm', "frame" =>
      check (kindName k == (← strF j "f")) "dec: a different frame kind"
      check (pl == (← natList (← field j "pl"))) "dec: a different payload"
      check (((st.map (fun x => (x : Int))).getD (-1)) == (← intF j "st")) "dec: a different close status"
      check (used == (← natF j "used")) "dec: a different number of bytes taken"
      pure { w with dec := w.dec.insert id (peer, inm') }
    | r, res =>
      let m := match r with | .idle => "idle" | .err e => s!"err {errName e}" | .frame .. => "a frame"
      throw s!"dec: the model gives {m}, the code answered {res}"
  | op => throw s!"unknown ws op {op}"

end Pinc.TraceConnectWs
