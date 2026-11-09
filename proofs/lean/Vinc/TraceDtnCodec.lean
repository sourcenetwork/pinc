import Vinc.Json
import Vinc.DtnCodecWire

/-!
# Replay of the codec traces

The Lean half of the trace validation of the head and acknowledgement codecs (`dtn_codec.ndjson`, written by the Rust
test `trace_dtn_codec`): the byte strings of the `cx` events are decoded by the codecs the theorems of
`Vinc.DtnCodec` and `Vinc.DtnCodecWire` are about (`signedC`, `ackC` through `decodeAll`). An `enc` event must decode
and re-encode to the same bytes; a `mut` event replaces one byte of its base encoding and the code's verdict must be
the model's (accepted only if the model decodes it and re-encodes it to the mutated bytes); `trunc` and `trail` events
must be rejected by the model. It is the port of `proofs/tla/TraceDtnCodec.tla`.
-/

namespace Vinc.TraceDtnCodec
open Vinc.Json Vinc.DtnCodec Vinc.DtnCodecWire

/-- The replay state: the `enc` events seen so far, as (kind, bytes). -/
structure W where
  encs : Array (String × Bytes) := #[]

def isTag (t : String) : Bool := t == "cx"

def toBytes (l : List Nat) : Bytes := l.map (Fin.ofNat 256)

/-- Whether the model accepts `bs` as a canonical encoding of `kind`. -/
def accepted (kind : String) (bs : Bytes) : Bool :=
  if kind == "head" then
    match decodeAll signedC bs with
    | some v => signedC.emit v == bs
    | none => false
  else
    match decodeAll ackC bs with
    | some v => ackC.emit v == bs
    | none => false

/-- Whether the model rejects `bs` outright. -/
def rejected (kind : String) (bs : Bytes) : Bool :=
  if kind == "head" then (decodeAll signedC bs).isNone else (decodeAll ackC bs).isNone

def replayEvent (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  let kind ← strF j "kind"
  match op with
  | "enc" =>
    let bs := toBytes (← natList (← field j "b"))
    check (accepted kind bs) s!"{kind}: the model does not decode a valid encoding to itself"
    pure { encs := w.encs.push (kind, bs) }
  | _ =>
    let b ← natF j "base"
    let some (_, base) := w.encs[b]? | throw s!"unknown base {b}"
    match op with
    | "mut" =>
      let pos ← natF j "pos"
      let v ← natF j "val"
      let ok ← boolF j "ok"
      let m := base.set pos (Fin.ofNat 256 v)
      check ((if ok then accepted kind m else rejected kind m)) s!"{kind}: mutation at {pos} to {v}: code {ok}"
      pure w
    | "trunc" =>
      let n ← natF j "n"
      check (rejected kind (base.take n)) s!"{kind}: the model accepts a prefix of {n} bytes"
      pure w
    | "trail" =>
      let x ← natF j "extra"
      check (rejected kind (base ++ (List.range x).map fun i => Fin.ofNat 256 (i + 9))) s!"{kind}: trailing bytes accepted"
      pure w
    | _ => throw s!"unknown op {op}"

end Vinc.TraceDtnCodec
