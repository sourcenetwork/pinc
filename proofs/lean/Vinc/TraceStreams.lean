import Vinc.Json
import Vinc.TransportStreams

/-!
# Replay of the stream table traces

The Lean half of the trace validation of the receive and credit path of the stream layer (`stream/table.rs`,
`recv.rs`, `flow.rs`, `ranges.rs`, `pool.rs`), the port of `proofs/tla/TraceStreams.tla`. It reads the `st` events
written by the Rust test `trace_streams` and replays every call through the functions of `Vinc.TransportStreams`
(`frame`, `reset`, `consume`, `pending`, `ctlLostMsd`, `ctlLostReset`, `ctlAckedReset`, `openLocal`, `appReset`,
`finish`, `extTo`, `closeAll`, and the stop-sending ones `stopReq`, `onStop`, `ctlLostStop`, `ctlAckedStop`): the state the model computes must be the state recorded, and the error it computes
the error the call returned. The constants are those of the test: chunks of 16384 bytes, a ring of 5, 96 ranges,
4 slots, 2 peer streams, a pool of 8 chunks, windows of 2 and 4 chunks, 2 local streams.
-/

namespace Vinc.TraceStreams
open Vinc.Json Vinc.TransportStreams

/-- The constants of `trace_streams`. -/
def params : P :=
  { ch := 16384, ring := 7, rr := 96, n := 4, maxrem := 2, b := 20, swc := 81920, mswc := 98304, pm := 2, firstk := 4,
    maxoff := 2000000000, retry := true }

def optNat (j : J) (k : String) : Except String (Option Nat) := do
  let v ← intF j k
  pure (if v < 0 then none else some v.toNat)

def slotOf (j : J) : Except String Slot := do
  if (← intF j "id") < 0 then pure Slot.new
  else
    pure { id := some (← natF j "id"), open_ := ← boolF j "open", held := ← natList (← field j "held"),
           rs := ← pairList (← field j "rs"), read := ← natF j "read", hi := ← natF j "hi",
           contig := ← natF j "contig", fin := ← optNat j "fin", limit := ← natF j "limit",
           size := ← natF j "size", pend := ← boolF j "pend", defer := ← boolF j "defer",
           rst := ← optNat j "rst", obs := ← boolF j "obs", sdone := ← boolF j "sdone", srst := ← natF j "srst",
           stop := ← natF j "stop", qcode := ← optNat j "qcode", scode := ← optNat j "scode" }

def pairN (j : J) (k : String) : Except String (Nat × Nat) := do
  match ← natList (← field j k) with
  | [a, b] => pure (a, b)
  | _ => throw s!"{k} is not a pair"

/-- The table a recorded view shows. -/
def tabOf (v : J) : Except String Tab := do
  let slots ← match (← field v "slots").arr? with
    | some a => a.toList.mapM slotOf
    | none => throw "slots is not an array"
  let ad ← natList (← field v "ad")
  check (ad.length == 3) "ad is not a triple"
  pure { slots, rn := ← pairN v "rn", lo := ← pairN v "lo", rl := ← natF v "rl", ll := ← natF v "ll",
         ext := ← natF v "ext", tgt := ← natF v "tgt",
         ms := ← optNat v "ms", mb := ← natF v "mb", mr := ← natF v "mr",
         adlim := ad[0]!, adv := ad[1]!, adat := ad[2]!, adpend := ← boolF v "adp" }

/-- The replay state: the table, and whether a run is open. -/
structure St where
  tab : Tab := Tab.init params
  run : Nat := 0

def same (T : Tab) (v : J) (what : String) : Except String Unit := do
  let rec' ← tabOf v
  if T == rec' then pure () else throw s!"{what}: the model computes {repr T}, the code recorded {repr rec'}"

def replayEvent (j : J) (st : St) : Except String St := do
  let op ← strF j "op"
  let v ← field j "v"
  let p := params
  let T := st.tab
  let upd (T2 : Tab) (what : String) : Except String St := do
    same T2 v what
    pure { st with tab := T2 }
  match op with
  | "init" =>
    check (st.run == 0) "init inside a run"
    same (Tab.init p) v "init"
    pure { tab := Tab.init p, run := ← natF j "run" }
  | "end" =>
    check (st.run == (← natF j "run")) "end of another run"
    pure {}
  | _ =>
    check (st.run == (← natF j "run")) "event outside its run"
    match op with
    | "frame" =>
      let (T2, err) := frame p T (← natF j "id") (← natF j "off") (← natF j "len") (← boolF j "fin") (← boolF j "diff")
      check (err == (← strF j "err")) s!"frame: the model answers {err}, the code {← strF j "err"}"
      upd T2 "frame"
    | "reset" =>
      let (T2, err) := reset p T (← natF j "id") (← natF j "code") (← natF j "fs")
      check (err == (← strF j "err")) s!"reset: the model answers {err}, the code {← strF j "err"}"
      upd T2 "reset"
    | "consume" =>
      let (T2, err) := consume p T (← natF j "id") (← natF j "n") (← natF j "now") (← natF j "srtt")
      check (err == (← strF j "err")) s!"consume: the model answers {err}, the code {← strF j "err"}"
      upd T2 "consume"
    | "pending" =>
      let (T2, kind, id, mx) := pending T
      check (kind == (← strF j "kind")) s!"pending: kind {kind}"
      check ((if kind == "none" || kind == "msts" then -1 else (id : Int)) == (← intF j "fid")) "pending: stream"
      check (mx == (← natF j "max")) "pending: limit"
      upd T2 "pending"
    | "lostmsd" => upd (ctlLostMsd T (← natF j "id") (← natF j "max")) "lostmsd"
    | "lostmsts" => upd (ctlLostMsts T (← natF j "limit")) "lostmsts"
    | "maxstreams" => upd (recvMaxStreams T (← natF j "limit")) "maxstreams"
    | "lostreset" => upd (ctlLostReset T (← natF j "id")) "lostreset"
    | "loststop" => upd (ctlLostStop T (← natF j "id")) "loststop"
    | "ackedstop" => upd (ctlAckedStop T (← natF j "id")) "ackedstop"
    | "stopreq" =>
      let (T2, err) := stopReq T (← natF j "id") (← natF j "code")
      check (err == (← strF j "err")) s!"stopreq: the model answers {err}, the code {← strF j "err"}"
      upd T2 "stopreq"
    | "onstop" =>
      let (T2, err, fresh) := onStop p T (← natF j "id") (← natF j "code") (← natF v "ext")
      check (err == (← strF j "err")) s!"onstop: the model answers {err}, the code {← strF j "err"}"
      check (fresh == (← boolF j "fresh")) "onstop: the model and the code differ on whether the stop reset the stream"
      upd T2 "onstop"
    | "ackedreset" => upd (ctlAckedReset p T (← natF j "id")) "ackedreset"
    | "open" => upd (openLocal p T) "open"
    | "appreset" => upd (appReset p T (← natF j "id") (← natF j "code") (← natF v "ext")) "appreset"
    | "finish" => upd (finish p T (← natF j "id") (← natF v "ext") (← boolF j "done")) "finish"
    | "ext" => upd (extTo p T (← natF j "ext")) "ext"
    | "close" => upd (closeAll p T (← natF v "ext")) "close"
    | _ => throw s!"unknown stream op {op}"

end Vinc.TraceStreams
