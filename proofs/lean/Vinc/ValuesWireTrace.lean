import Vinc.Json
import Vinc.ValuesWireReqThm
import Vinc.ValuesWireGroup
import Vinc.ValuesWireProof

/-!
# Replay of the value wire traces

The Lean half of the trace validation of the value wire codecs: it reads the `w*` events written by the Rust test
`trace_values_wire` (`values_wire.ndjson`) and replays every one through the functions the theorems of
`Vinc.ValuesWireReq`, `ValuesWireReqThm`, `ValuesWireGroup`, `ValuesWireProof` and `ValuesWireProofThm` are about
(`reqParse`, `reqTotalLen`, `reqEncode`, `ghParse`, `ghEncode`, `pfParse`, `pfWriteHead`, `prParse`, `prEncode`). It is
the port of `proofs/tla/TraceValuesWire.tla`: the recorded accept or refuse decision, every field, the error kind, the
reason and the shortfall, and the buffer after an encode must equal what the model computes. A `u64` is four 16-bit
limbs in the trace.
-/

namespace Vinc.ValuesWireTrace

open Vinc Vinc.Json Vinc.ValuesWire

/-- The events this module replays. -/
def isWireTag (t : String) : Bool :=
  t == "wreq" || t == "wreqenc" || t == "wgh" || t == "wghenc" || t == "wpf" || t == "wpfhead" || t == "wpr" ||
    t == "wprenc"

/-- A `u64` recorded as four 16-bit limbs. -/
def limbVal (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] => pure (a + b * 65536 + c * 4294967296 + d * 281474976710656)
  | _ => throw "expected four limbs"

def limbF (j : J) (k : String) : Except String Nat := do limbVal (← field j k)

/-- The recorded error name, shortfall and reason of a model error. -/
def errFields : Err → String × Nat × String
  | .truncated n => ("truncated", n, "")
  | .bufferTooSmall n => ("small", n, "")
  | .tooLong => ("toolong", 0, "")
  | .overflow => ("overflow", 0, "")
  | .nonMinimal => ("nonminimal", 0, "")
  | .unexpected m => ("unexpected", 0, m)

/-- The recorded refusal is the model's. -/
def sameErr (what : String) (res : J) (e : Err) : Except String Unit := do
  let (k, n, m) := errFields e
  check ((← strF res "err") == k && (← natF res "needed") == n && (← strF res "msg") == m)
    s!"{what}: recorded {← strF res "err"}/{← natF res "needed"}/{← strF res "msg"}, model {k}/{n}/{m}"

/-- The recorded result `res` is the model's: the same refusal, or success with the same length. -/
def sameLen (what : String) (res : J) (r : Except Err Nat) : Except String Unit := do
  match r with
  | .ok n =>
    check (← boolF res "ok") s!"{what}: recorded a refusal, model accepts"
    check ((← natF res "n") == n) s!"{what}: length {← natF res "n"}, model {n}"
  | .error e =>
    check (!(← boolF res "ok")) s!"{what}: recorded success, model refuses with {repr e}"
    sameErr what res e

def spansJ (j : J) : Except String (List (Nat × Nat)) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => do
    match v.arr? with
    | some #[x, y] => pure (← limbVal x, ← limbVal y)
    | _ => throw "expected a pair of limbs"
  | none => throw "expected an array"

def replayReq (j : J) : Except String Unit := do
  let b ← natList (← field j "in")
  let res ← field j "res"
  match reqParse b with
  | .ok (r, n) =>
    check (← boolF res "ok") s!"wreq {b}: recorded a refusal, model accepts"
    check ((← natList (← field res "root")) == r.root) "wreq: root"
    check ((← spansJ (← field res "ranges")) == spansOf (r.ranges.length / 16) r.ranges) "wreq: ranges"
    check ((← natF res "n") == n) "wreq: length"
  | .error e =>
    check (!(← boolF res "ok")) s!"wreq {b}: recorded success, model refuses with {repr e}"
    sameErr "wreq" res e
  sameLen "wreq total_len" (← field j "tot") (reqTotalLen b)

def replayReqEnc (j : J) : Except String Unit := do
  let root ← natList (← field j "root")
  let spans ← spansJ (← field j "spans")
  let cap ← natF j "cap"
  let (r, after) := reqEncode root spans (List.replicate cap 170)
  sameLen "wreqenc" (← field j "res") r
  check ((← natList (← field j "after")) == after) "wreqenc: buffer after"

def replayGh (j : J) : Except String Unit := do
  let b ← natList (← field j "in")
  let res ← field j "res"
  match ghParse b with
  | .ok g =>
    check (← boolF res "ok") s!"wgh {b}: recorded a refusal, model accepts"
    check ((← limbF res "off") == g.off && (← limbF res "len") == g.len && (← natF res "plen") == g.plen &&
      (← boolF res "follows") == g.follows) "wgh: fields"
  | .error e =>
    check (!(← boolF res "ok")) s!"wgh {b}: recorded success, model refuses with {repr e}"
    sameErr "wgh" res e

def replayGhEnc (j : J) : Except String Unit := do
  let g : GH := ⟨← limbF j "off", ← limbF j "len", ← natF j "plen", ← boolF j "follows"⟩
  check ((← natList (← field j "out")) == ghEncode g) "wghenc: bytes"

def replayPf (j : J) : Except String Unit := do
  let b ← natList (← field j "in")
  let res ← field j "res"
  match pfParse b with
  | .ok f =>
    check (← boolF res "ok") s!"wpf {b}: recorded a refusal, model accepts"
    check ((← limbF res "sid") == f.sid && (← natF res "glog") == f.glog && (← limbF res "start") == f.start &&
      (← limbF res "wn") == f.wn && (← limbF res "ln") == f.ln && (← natList (← field res "proof")) == f.proof)
      "wpf: fields"
  | .error e =>
    check (!(← boolF res "ok")) s!"wpf {b}: recorded success, model refuses with {repr e}"
    sameErr "wpf" res e

def replayPfHead (j : J) : Except String Unit := do
  let cap ← natF j "cap"
  let (r, after) := pfWriteHead (← limbF j "sid") (← natF j "glog") (← limbF j "start") (← limbF j "wn")
    (← limbF j "ln") (List.replicate cap 170)
  sameLen "wpfhead" (← field j "res") r
  check ((← natList (← field j "after")) == after) "wpfhead: buffer after"

def replayPr (j : J) : Except String Unit := do
  let b ← natList (← field j "in")
  let res ← field j "res"
  match prParse b with
  | .ok r =>
    check (← boolF res "ok") s!"wpr {b}: recorded a refusal, model accepts"
    check ((← limbF res "sid") == r.sid && (← limbF res "from") == r.from_ && (← limbF res "upto") == r.upto)
      "wpr: fields"
  | .error e =>
    check (!(← boolF res "ok")) s!"wpr {b}: recorded success, model refuses with {repr e}"
    sameErr "wpr" res e

def replayPrEnc (j : J) : Except String Unit := do
  let cap ← natF j "cap"
  let r : PR := ⟨← limbF j "sid", ← limbF j "from", ← limbF j "upto"⟩
  let (res, after) := prEncode r (List.replicate cap 170)
  sameLen "wprenc" (← field j "res") res
  check ((← natList (← field j "after")) == after) "wprenc: buffer after"

/-- Replay one value wire event. -/
def replayEvent (j : J) : Except String Unit := do
  match ← strF j "t" with
  | "wreq" => replayReq j
  | "wreqenc" => replayReqEnc j
  | "wgh" => replayGh j
  | "wghenc" => replayGhEnc j
  | "wpf" => replayPf j
  | "wpfhead" => replayPfHead j
  | "wpr" => replayPr j
  | "wprenc" => replayPrEnc j
  | t => throw s!"unknown value wire event {t}"

end Vinc.ValuesWireTrace
