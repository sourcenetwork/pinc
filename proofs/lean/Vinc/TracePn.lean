import Vinc.Json
import Vinc.TransportPn

/-!
# Replay of the packet-number traces

The Lean half of the trace validation of the packet-number codec (`packet/number.rs`), the port of
`proofs/tla/TracePn.tla`. It reads the `txpn` events written by the Rust test `trace_pn` and replays every call
through the functions of `Vinc.TransportPn`: the expansion, the bytes and the error of the encoding and the width
chosen for a window must be the ones recorded, in the narrow file and in the wide one (the real `2^62`, the width 4,
numbers up to `2^64 - 1`).
-/

namespace Vinc.TracePn
open Vinc.Json Vinc.TransportPn

def isTag (t : String) : Bool := t == "txpn"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "enc" =>
    let full ← natF j "full"
    let len ← natF j "len"
    let err ← strF j "err"
    match encodePn full len with
    | .error e => check (e == err) s!"enc {full} {len}: the model answers {e}, the code {err}"
    | .ok bs =>
      check (err == "ok") s!"enc {full} {len}: the model writes bytes, the code answers {err}"
      check (bs == (← natList (← field j "b"))) s!"enc {full} {len}: the bytes differ: model {bs}"
  | "dec" =>
    let lg ← intF j "lg"
    let r := decodePn (← natF j "tr") (← natF j "len") (if lg < 0 then none else some lg.toNat)
    check (r == (← natF j "r")) s!"dec: the model expands to {r}, the code to {← natF j "r"}"
  | "for" => check (pnLenFor (← natF j "w") == (← natF j "len")) "for: the width differs"
  | op => throw s!"unknown packet number op {op}"

end Vinc.TracePn
