import Vinc.TransportFrameCodec

/-!
# The VINCER packet builder: the model

What `crates/vinc-transport/src/conn/send.rs` puts into a packet, over the frame codecs of `TransportFrame.lean`:

* `implicitStreamLen` is `implicit_stream_len`: the varint at `pos + head` is read (`Varint.decode`), and only when
  it gives exactly the bytes from its end to the end of the frames is the LEN bit of the type byte at `pos` cleared
  and the varint taken out; `putStreamHeader` is `put_stream_header` (the type, the id, the offset when it is not
  0 and the length, each a `put_varint` that stops the rest when it fails, then the check that the buffer is full);
* `finish` is the tail of `build_packet`: the padding to the least payload, or the length of the kept STREAM frame
  dropped (`implicit_stream_len` under the `?`, so a refusal gives the packet up: `none`), or nothing;
* `Fill` is what `fill_frames` wrote, slot by slot in the order of the code: the ACK, the control frames (SLEEP,
  WAKE, the MTU echo, READY, the tickets, REKEY, the extension frames, the stream layer's credit and resets), the
  path frames (PATH_RESPONSE, PING, PATH_CHALLENGE), the stream chunks (each header from `put_stream_header`, then
  the data), the datagrams (with their length), the credit an answered stream gives back, and the PING a forced
  packet gets when nothing else elicits an acknowledgement; or the probe timeout's ACK, WAKE and PING; or a path
  MTU probe's ACK and PING; or a tail repair's ACK and stream chunks. Which pending frames a slot writes depends on
  the room and the counts the code tests; the model takes what each slot wrote, so the theorems hold whatever those
  tests decide. `Fill.hint` is `last_stream` as the fill leaves it: the last chunk written, forgotten when a
  datagram or a credit frame follows it;
* `pick` is what `build_app` decides before the fill: the mode, and whether the fill takes the pending tail repair
  (only a packet built as a repair does, so a repair due together with a path MTU probe stays pending).

The theorems are in `TransportFramePackThm.lean`. The TLA+ counterpart is `proofs/tla/FramePackOps.tla` with
`FramePack.tla`; the trace is replayed by `Vinc/TraceFramePack.lean`.
-/

namespace Vinc.TransportFramePack
open Vinc Vinc.TransportFrame

/-! ## The byte functions -/

/-- The type byte with the LEN bit (`0x02`) cleared. -/
def clearLen (b : Nat) : Nat := if b / 2 % 2 = 1 then b - 2 else b

/-- `implicit_stream_len(frames, pos, head)`: the bytes dropped and the frames that remain, or `none`. -/
def implicitStreamLen (fr : List Nat) (pos head : Nat) : Option (Nat × List Nat) :=
  if fr.length < pos + head then none
  else match Varint.decode (fr.drop (pos + head)) with
    | .error _ => none
    | .ok (v, n) =>
      if v ≠ fr.length - (pos + head + n) then none
      else
        let pre := fr.take (pos + head)
        some (n, (if pos < pos + head then pre.set pos (clearLen (fr.getD pos 0)) else pre) ++ fr.drop (pos + head + n))

/-- The calls in order against a buffer of `cap` bytes up to the first that fails: whether all went, the bytes. -/
def runPutsPart (cap : Nat) : List Nat → List Put → Bool × List Nat
  | w, [] => (true, w)
  | w, p :: ps =>
    match put cap w p with
    | .error _ => (false, w)
    | .ok w' => runPutsPart cap w' ps

/-- The calls of `put_stream_header`. -/
def headerPuts (id off len : Nat) (fin : Bool) : List Put :=
  [.v (streamType off fin false), .v id] ++ (if off = 0 then [] else [.v off]) ++ [.v len]

/-- `put_stream_header` into a buffer of `cap` bytes: whether it filled it exactly, and the bytes written. -/
def putStreamHeader (cap id off len : Nat) (fin : Bool) : Bool × List Nat :=
  let r := runPutsPart cap [] (headerPuts id off len fin)
  (r.1 && r.2.length == cap, r.2)

/-- The tail of `build_packet`: the payload sealed, the padding and the bytes dropped; `none` when the `?` after
`implicit_stream_len` gives the packet up. -/
def finish (fr : List Nat) (hint : Option (Nat × Nat)) (minp : Nat) : Option (List Nat × Nat × Nat) :=
  if fr.length < minp then some (fr ++ List.replicate (minp - fr.length) 0, minp - fr.length, 0)
  else match hint with
    | some (p, h) =>
      if p + h ≤ fr.length then
        match implicitStreamLen fr p h with
        | some (n, out) => some (out, 0, n)
        | none => none
      else some (fr, 0, 0)
    | none => some (fr, 0, 0)

/-! ## The fill -/

/-- A chunk the stream layer gives: the frame `fill_streams` writes for it. -/
structure Chunk where
  id : Nat
  off : Nat
  fin : Bool
  data : List Nat
  deriving DecidableEq, Repr

/-- The STREAM frame of a chunk, with its length. -/
def Chunk.frame (c : Chunk) : Frame := .stream c.id c.off c.fin c.data false

/-- The size of its header before the length: what `last_stream` keeps besides the place. -/
def Chunk.head (c : Chunk) : Nat := streamOverhead c.id c.off c.data.length false - Varint.encodedLen c.data.length

/-- The bytes `fill_streams` writes for a chunk: `put_stream_header` into `stream_overhead` bytes, then the data. -/
def Chunk.bytes (c : Chunk) : List Nat :=
  (putStreamHeader (streamOverhead c.id c.off c.data.length false) c.id c.off c.data.length c.fin).2 ++ c.data

/-- One thing a slot wrote: a frame through `put` (or `write_ack`), or a stream chunk. -/
inductive Item where
  | fr (f : Frame)
  | ch (c : Chunk)
  deriving DecidableEq, Repr

def Item.frame : Item → Frame
  | .fr f => f
  | .ch c => c.frame

def Item.bytes : Item → List Nat
  | .fr f => f.bytes
  | .ch c => c.bytes

/-- Whether the item makes the packet elicit an acknowledgement (`weak` or `strong` in the code): all but the ACK
and the MTU echo. -/
def Item.elicits : Item → Bool
  | .fr (.ack ..) => false
  | .fr (.mtuProbeEcho _) => false
  | _ => true

/-- What the control slots wrote: SLEEP, WAKE, the MTU echo, READY, the tickets, REKEY, the extension frames and
the stream layer's control frames. -/
structure Ctl where
  sleep : Bool := false
  wake : Bool := false
  echo : Option Nat := none
  ready : Bool := false
  tickets : Option (List (List Nat × Nat)) := none
  rekey : Option Frame := none
  exts : List (Nat × List Nat) := []
  sc : List Frame := []

/-- What the path slots wrote. -/
structure PathFr where
  resp : Option (List Nat) := none
  ping : Bool := false
  chal : Option (List Nat) := none

/-- What `fill_frames` wrote, by mode. `ping` of a normal fill is a forced packet's PING (written only when nothing
else elicits an acknowledgement). -/
inductive Fill where
  | normal (ack : Option Frame) (ctl : Ctl) (path : PathFr) (streams : List Chunk) (dgrams : List (List Nat))
      (late : List Frame) (ping : Bool)
  | pingOnly (ack : Option Frame) (wake ping : Bool)
  | probe (ack : Option Frame) (ping : Bool)
  | repair (ack : Option Frame) (chunks : List Chunk)

def opt (s : Nat) (b : Bool) (f : Frame) : List (Nat × Item) := if b then [(s, .fr f)] else []
def optF (s : Nat) : Option Frame → List (Nat × Item)
  | some f => [(s, .fr f)]
  | none => []

/-- The control slots, 2 to 9. -/
def Ctl.items (c : Ctl) : List (Nat × Item) :=
  opt 2 c.sleep .sleep ++ opt 3 c.wake .wake ++ optF 4 (c.echo.map .mtuProbeEcho) ++ opt 5 c.ready .ready ++
    optF 6 (c.tickets.map .newTickets) ++ optF 7 c.rekey ++ c.exts.map (fun e => (8, .fr (.ext e.1 e.2))) ++
    c.sc.map (fun f => (9, .fr f))

/-- The path slots, 10 to 12. -/
def PathFr.items (p : PathFr) : List (Nat × Item) :=
  optF 10 (p.resp.map .pathResponse) ++ opt 11 p.ping .ping ++ optF 12 (p.chal.map .pathChallenge)

/-- Everything a normal fill wrote before the forced PING: slots 1 to 15. -/
def bodyItems (ack : Option Frame) (ctl : Ctl) (path : PathFr) (streams : List Chunk) (dgrams : List (List Nat))
    (late : List Frame) : List (Nat × Item) :=
  optF 1 ack ++ ctl.items ++ path.items ++ streams.map (fun c => (13, .ch c)) ++
    dgrams.map (fun d => (14, .fr (.datagram d false))) ++ late.map (fun f => (15, .fr f))

/-- What the fill wrote, each with its slot, in order. -/
def Fill.items : Fill → List (Nat × Item)
  | .normal ack ctl path streams dgrams late ping =>
    let body := bodyItems ack ctl path streams dgrams late
    body ++ (if ping && !(body.any (fun x => x.2.elicits)) then [(16, .fr .ping)] else [])
  | .pingOnly ack wake ping => optF 1 ack ++ opt 2 wake .wake ++ opt 3 ping .ping
  | .probe ack ping => optF 1 ack ++ opt 2 ping .ping
  | .repair ack chunks => optF 1 ack ++ chunks.map (fun c => (2, .ch c))

/-- The bytes of items written one after the other. -/
def itemBytes (xs : List (Nat × Item)) : List Nat := (xs.map (fun x => x.2.bytes)).flatten

/-- The bytes of the fill. -/
def Fill.bytes (f : Fill) : List Nat := itemBytes f.items

/-- The frames of the fill, in order. -/
def Fill.frames (f : Fill) : List Frame := f.items.map (fun x => x.2.frame)

/-- `last_stream` as `fill_frames` returns it: the place and the header size of the last chunk of a normal fill,
forgotten when a datagram or a credit frame follows it, and dropped when it does not lie in the fill. -/
def Fill.hint : Fill → Option (Nat × Nat)
  | f@(.normal ack ctl path streams dgrams late _) =>
    if dgrams = [] ∧ late = [] then
      match streams.getLast? with
      | some c =>
        let p := (itemBytes (optF 1 ack ++ ctl.items ++ path.items ++ streams.dropLast.map (fun c => (13, .ch c)))).length
        if p + c.head ≤ f.bytes.length then some (p, c.head) else none
      | none => none
    else none
  | _ => none

/-! ## What a receiver reads -/

/-- The frames written, the last one without its length when it was dropped, and the padding as one PADDING frame. -/
def expected (fs : List Frame) (pad n : Nat) : List Frame :=
  let base := if n > 0 then
      match fs.getLast? with
      | some (.stream id off fin data _) => fs.dropLast ++ [.stream id off fin data true]
      | _ => fs
    else fs
  if pad > 0 then base ++ [.padding pad] else base

/-! ## The order of the slots -/

/-- The kind of a frame, as the traces name it. -/
def _root_.Vinc.TransportFrame.Frame.kind : Frame → String
  | .padding _ => "Padding" | .ping => "Ping" | .ack .. => "Ack" | .resetStream .. => "ResetStream"
  | .stopSending .. => "StopSending" | .stream .. => "Stream" | .maxStreamData .. => "MaxStreamData"
  | .maxStreams _ => "MaxStreams" | .pathChallenge _ => "PathChallenge" | .pathResponse _ => "PathResponse"
  | .close _ => "Close" | .datagram .. => "Datagram" | .mtuProbeEcho _ => "MtuProbeEcho" | .sleep => "Sleep"
  | .wake => "Wake" | .rekey .. => "Rekey" | .ready => "Ready" | .newTickets _ => "NewTickets" | .ext .. => "Extension"

/-- The modes of a fill, and the CLOSE packet. -/
inductive Mode where
  | normal | pingOnly | probe | repair | close
  deriving DecidableEq, Repr

def scKinds : List String := ["MaxStreamData", "MaxStreams", "StopSending", "ResetStream"]

/-- The slots of `fill_frames` for a mode, numbered from 1 in the order it fills them: the kinds each writes and
whether it writes any number of frames. -/
def slotTable : Mode → List (List String × Bool)
  | .normal =>
    [(["Ack"], false), (["Sleep"], false), (["Wake"], false), (["MtuProbeEcho"], false), (["Ready"], false),
     (["NewTickets"], false), (["Rekey"], false), (["Extension"], true), (scKinds, true), (["PathResponse"], false),
     (["Ping"], false), (["PathChallenge"], false), (["Stream"], true), (["Datagram"], true), (scKinds, true),
     (["Ping"], false)]
  | .pingOnly => [(["Ack"], false), (["Wake"], false), (["Ping"], false)]
  | .probe => [(["Ack"], false), (["Ping"], false)]
  | .repair => [(["Ack"], false), (["Stream"], true)]
  | .close => [(["Close"], false)]

/-- Slot `s` (numbered from 1) of a table. -/
def slotAt (tbl : List (List String × Bool)) (s : Nat) : List String × Bool := tbl.getD (s - 1) ([], false)

/-- The first of the `n` slots from `j` that writes kind `k`. -/
def firstSlotFrom (tbl : List (List String × Bool)) (k : String) : Nat → Nat → Option Nat
  | _, 0 => none
  | j, n + 1 => if (slotAt tbl j).1.contains k then some j else firstSlotFrom tbl k (j + 1) n

/-- The first slot from `i` that writes kind `k`. -/
def firstSlot (tbl : List (List String × Bool)) (k : String) (i : Nat) : Option Nat :=
  firstSlotFrom tbl k (max i 1) (tbl.length + 1 - max i 1)

/-- Where the next frame may go after one in slot `s`: the same slot if it writes any number of frames, else the
next. -/
def nextSlot (tbl : List (List String × Bool)) (s : Nat) : Nat := if (slotAt tbl s).2 then s else s + 1

/-- Whether the kinds come in the order of the slots: each frame takes the first slot from the current one that
writes its kind, and a slot of at most one frame is then passed (the first such slot is never worse than a later
one, `matchFrom_of`). -/
def matchFrom (tbl : List (List String × Bool)) : List String → Nat → Bool
  | [], _ => true
  | k :: ks, i =>
    match firstSlot tbl k i with
    | none => false
    | some j => matchFrom tbl ks (nextSlot tbl j)

def ordered (m : Mode) (fs : List Frame) : Bool := matchFrom (slotTable m) (fs.map Frame.kind) 1

def Fill.mode : Fill → Mode
  | .normal .. => .normal
  | .pingOnly .. => .pingOnly
  | .probe .. => .probe
  | .repair .. => .repair

/-! ## The choice before the fill -/

/-- What `build_app` decides before the fill: the mode, whether the fill takes the pending tail repair, and whether
a repair is still pending after it. `probes`: the probe timeout owes packets; `mtu`: a path MTU probe is due for this
packet; `pending`: a tail repair is pending; `active`: the packet goes on the active path. The repair is taken only
for a packet built as a repair, so a repair that is due together with a probe stays pending for the next packet. -/
def pick (probes mtu pending active : Bool) : Mode × Bool × Bool :=
  let took := pending && active && !probes && !mtu
  (if probes then .pingOnly else if mtu then .probe else if took then .repair else .normal, took, pending && !took)

end Vinc.TransportFramePack
