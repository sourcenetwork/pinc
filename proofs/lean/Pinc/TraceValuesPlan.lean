import Pinc.Json
import Pinc.ValuesPlanProofsFrames
import Pinc.ValuesPlanSourceRead
import Pinc.ValuesPlanServer

/-!
# Replay of the plan, source and server traces

The replay half of the trace validation of `crates/pinc-values` plan geometry, `ValueSource::read_at` and the
server's proof frames (the Rust test `trace_values_plan`; the TLA+ half is `TraceValuesPlan.tla`). Every
recorded call is replayed through the Lean functions the theorems of `ValuesPlan*`, `ValuesPlanSource*` and
`ValuesPlanProofs*` are about, and any difference exits with an error naming the line:

* `vplan`: `planNew` gives the recorded refusal, or the recorded total and ranges; the recorded frames are
  `PlanM.frame`; each recorded `locate`, `frame_of_group` and `proof_pair` answer is `PlanM.locate`,
  `PlanM.frameOfGroup`, `PlanM.proofPair`.
* `vread`: the chunks `read_at` took, replayed with `PlanM.locate` and `PlanM.proofPair`: the same store reads
  (kind, offset, length asked) in the same order, the same lengths returned, and the length `read_at` returned.
* `vk`: `protoK`.
* `vsrvnew` / `vsrv`: the server's state machine (`proofsCall` with its `armed`, send frontier, window) on the
  events fed to it; the frames it sent are the frames the model computes, with the pair count of
  `parentsIn` and the body length of the head and the pairs.
-/

set_option linter.unusedVariables false

namespace Pinc.TraceValuesPlan
open Pinc.Json Pinc.ValuesPlan Pinc.Layout

/-- The lists of numbers in an array. -/
def natLists (j : J) : Except String (List (List Nat)) := do
  match j.arr? with
  | some a => a.toList.mapM natList
  | none => throw "expected an array"

def nums (j : J) (k : String) : Except String (List (List Nat)) := do natLists (← field j k)

def planErr : Nat → Option PErr
  | 1 => some .outOfBounds
  | 2 => some .tooManyRanges
  | 3 => some .tooLong
  | _ => none

def frameRow (f : FrameM) : List Nat :=
  [f.range, f.k, f.start, f.off, f.dlen, f.plen, if f.follows then 1 else 0]

/-- A plan event: the refusal, or the whole recorded behaviour of the plan. -/
def replayPlan (j : J) : Except String Unit := do
  let len ← natF j "len"
  let spans ← pairList (← field j "spans")
  have hlen : True := trivial
  match j.get? "err" with
  | some e =>
    let code ← natF j "err"
    match planNew len spans with
    | .error p => check (planErr code == some p) s!"plan {len} {spans}: refused as {repr p}, code recorded {code}"
    | .ok _ => throw s!"plan {len} {spans}: the model accepts a plan the code refused ({code})"
  | none =>
    match planNew len spans with
    | .error p => throw s!"plan {len} {spans}: the model refuses ({repr p}) a plan the code accepted"
    | .ok pl =>
      check (pl.total == (← natF j "total")) s!"plan {len} {spans}: total {pl.total}, code {← natF j "total"}"
      let rs ← nums j "ranges"
      check (pl.rs.map (fun r => [r.first, r.last, r.start]) == rs) s!"plan {len} {spans}: ranges"
      for row in ← nums j "frames" do
        match row with
        | [i, k, st, off, dl, pl', fo] =>
          match pl.frame i k with
          | some f => check (frameRow f == row) s!"plan {len} {spans}: frame {i} {k} model {frameRow f}, code {row}"
          | none => throw s!"plan {len} {spans}: no frame {i} {k} in the model"
        | _ => throw "bad frame row"
      for row in ← nums j "loc" do
        match row with
        | [at_, i, k] =>
          match pl.locate at_ with
          | some f => check (f.range == i && f.k == k) s!"plan {len} {spans}: locate {at_} model ({f.range}, {f.k}), code ({i}, {k})"
          | none => throw s!"plan {len} {spans}: the model locates nothing at {at_}"
        | _ => throw "bad loc row"
      for at_ in ← natList (← field j "nloc") do
        check (pl.locate at_ == none) s!"plan {len} {spans}: the model locates a frame at {at_}"
      for row in ← nums j "fog" do
        match row with
        | [off, i, k] =>
          match pl.frameOfGroup off with
          | some f => check (f.range == i && f.k == k) s!"plan {len} {spans}: frame_of_group {off} model ({f.range}, {f.k}), code ({i}, {k})"
          | none => throw s!"plan {len} {spans}: no frame of group {off} in the model"
        | _ => throw "bad fog row"
      for off in ← natList (← field j "nfog") do
        check (pl.frameOfGroup off == none) s!"plan {len} {spans}: the model has a frame of group {off}"
      for row in ← nums j "pp" do
        match row with
        | [i, k, jj, off] =>
          match pl.frame i k with
          | some f => check (pl.proofPair f jj == some off) s!"plan {len} {spans}: proof_pair {i} {k} {jj} model {pl.proofPair f jj}, code {off}"
          | none => throw "pp: no frame"
        | _ => throw "bad pp row"
      for row in ← nums j "npp" do
        match row with
        | [i, k, jj] =>
          match pl.frame i k with
          | some f => check (pl.proofPair f jj == none) s!"plan {len} {spans}: proof_pair {i} {k} {jj} is {pl.proofPair f jj} in the model"
          | none => throw "npp: no frame"
        | _ => throw "bad npp row"

/-- The chunks `read_at` takes, replayed: header chunks read no store, pair and group chunks read the store once. -/
def replayChunks (pl : PlanM) : Nat → Nat → Nat → List (List Nat) → Nat → Except String (Nat × List (List Nat))
  | 0, _, _, acc, done => pure (done, acc)
  | fuel + 1, at_, rem, acc, done =>
    if rem = 0 then pure (done, acc) else
    match pl.locate at_ with
    | none => pure (done, acc)
    | some f =>
      if at_ < f.proofStart then
        let chunk := min (16 - (at_ - f.start)) rem
        replayChunks pl fuel (at_ + chunk) (rem - chunk) acc (done + chunk)
      else if at_ < f.dataStart then do
        let into := at_ - f.proofStart
        let room := min (64 - into % 64) rem
        match pl.proofPair f (into / 64), acc with
        | some base, [kind, o, q, got] :: rest =>
          check (kind == 0 && o == base + into % 64 && q == room && got ≤ room)
            s!"read at {at_}: outboard read {[kind, o, q, got]}, model (0, {base + into % 64}, {room})"
          if got < room then pure (done + got, rest)
          else replayChunks pl fuel (at_ + got) (rem - got) rest (done + got)
        | _, _ => throw s!"read at {at_}: no outboard read recorded where the model reads"
      else do
        let into := at_ - f.dataStart
        let room := min (f.dlen - into) rem
        match acc with
        | [kind, o, q, got] :: rest =>
          check (kind == 1 && o == f.off + into && q == room && got ≤ room)
            s!"read at {at_}: value read {[kind, o, q, got]}, model (1, {f.off + into}, {room})"
          if got < room then pure (done + got, rest)
          else replayChunks pl fuel (at_ + got) (rem - got) rest (done + got)
        | _ => throw s!"read at {at_}: no value read recorded where the model reads"

def replayRead (j : J) : Except String Unit := do
  let len ← natF j "len"
  let spans ← pairList (← field j "spans")
  let off ← natF j "off"
  let n ← natF j "n"
  let ret ← natF j "ret"
  match planNew len spans with
  | .error p => throw s!"read: the model refuses the plan ({repr p})"
  | .ok pl =>
    let (done, rest) ← replayChunks pl n off n (← nums j "acc") 0
    check (rest.isEmpty) s!"read {off} {n}: the code read the store {rest.length} more times than the model"
    check (done == ret) s!"read {off} {n}: the model returns {done}, the code {ret}"

/-- The model of a served response: the value length, its plan, and the state `proofs` keeps. -/
structure Srv where
  ln : Nat := 0
  pl : Option PlanM := none
  st : PState := ⟨false, 0⟩
  vfront : Nat := 0
  window : Nat := 0
  armed : Bool := false
  tab : Slots := []

instance : Inhabited Srv := ⟨{}⟩

/-- `front_of`: the value offset the stream offset `sent` has reached. -/
def frontOf (pl : PlanM) (sent : Nat) : Nat :=
  match pl.locate (sent - 1) with
  | none => 0
  | some f => f.off + min (sent - f.dataStart) f.dlen

def satAdd (a b : Nat) : Nat := min (a + b) u64Max

/-- One server event: the new state and the frames of the call, `(start, length)`. -/
def serverStep (s : Srv) (kind : String) (a b w : Nat) : Except String (Srv × List (Nat × Nat)) := do
  let some pl := s.pl | throw "no server run"
  match kind with
  | "loss" =>
    let vf := max s.vfront (frontOf pl b)
    let from_ := match pl.locate a with | none => 0 | some f => f.off
    let (st', fr) := proofsCall s.ln s.st vf w from_ 0 (fun _ => true)
    pure ({ s with st := st', vfront := vf, window := w, armed := true }, fr)
  | "sent" =>
    let vf := max s.vfront (frontOf pl a)
    let s1 := { s with vfront := vf, window := w }
    if s1.armed && !s1.st.deep && satAdd vf (w / 2) > s1.st.pfTo then
      let (st', fr) := proofsCall s.ln s1.st vf w (vf - 1) (satAdd vf (min w LEAD)) (fun _ => true)
      pure ({ s1 with st := st' }, fr)
    else pure (s1, [])
  | "ext" =>
    let s1 := { s with armed := true }
    let (st', fr) := proofsCall s.ln s1.st s1.vfront s1.window a b (fun _ => true)
    pure ({ s1 with st := st' }, fr)
  | _ => throw s!"unknown server event {kind}"

def replayServer (j : J) (s : Srv) : Except String Srv := do
  match ← strF j "t" with
  | "vsrvnew" =>
    let ln ← natF j "ln"
    let spans ← pairList (← field j "spans")
    match planNew ln spans with
    | .ok pl => pure { ln, pl := some pl }
    | .error p => throw s!"server run: the model refuses the plan ({repr p})"
  | _ =>
    let kind ← strF j "ev"
    let (s', fr) ← serverStep s kind (← natF j "a") (← natF j "b") (← natF j "w")
    let rec_ ← nums j "fr"
    let n := groups s.ln lg
    let model := fr.map (fun (at_, wn) =>
      let pairs := parentsIn (at_ / G) (divCeil (at_ + wn) G) 0 n
      [at_, wn, pairs * 64, 22 + pairs * 64])
    check (rec_ == model) s!"server {kind} (ln {s.ln}): the code sent frames {rec_}, the model {model}"
    pure s'

/-- A slot of the recorded table: free `[]`, collecting `[stream, peer]`, serving `[stream, peer, root, ranges]`. -/
def parseSlot (j : J) : Except String (Option Slot) := do
  let some a := j.arr? | throw "a slot is an array"
  match a.toList with
  | [] => pure none
  | [s, p] =>
    let some s := s.nat? | throw "slot stream"
    let some p := p.nat? | throw "slot peer"
    pure (some ⟨s, p, none⟩)
  | [s, p, r, rg] =>
    let some s := s.nat? | throw "slot stream"
    let some p := p.nat? | throw "slot peer"
    let some r := r.nat? | throw "slot root"
    pure (some ⟨s, p, some (r, ← pairList rg)⟩)
  | _ => throw "a slot has 0, 2 or 4 fields"

def parseTable (j : J) : Except String Slots := do
  let some a := j.arr? | throw "a table is an array"
  a.toList.mapM parseSlot

/-- One slot event: the model of `ValuesPlanServer` on the recorded table gives the recorded table and resets. -/
def replaySlot (j : J) (tab : Slots) : Except String Slots := do
  match ← strF j "t" with
  | "vslotnew" => pure (List.replicate (← natF j "s") none)
  | _ =>
    let before ← parseTable (← field j "before")
    let after ← parseTable (← field j "after")
    let rc ← pairList (← field j "rc")
    check (before == tab) "slot event: the table before is not the table after the last event"
    let ev ← strF j "ev"
    let (model, mrc) : Slots × List (Nat × Nat) ← match ev with
      | "open" => pure (opened before (← natF j "stream") (← natF j "peer"))
      | "done" | "reset" => pure (done before (← natF j "stream"), [])
      | "closed" => pure (closed before (← natF j "peer"), [])
      | "req" =>
        let stream ← natF j "stream"
        let len ← natF j "len"
        let spans ← pairList (← field j "spans")
        match before.findIdx? (fun x => match x with | some o => decide (o.stream = stream) && o.serving.isNone | none => false) with
        | none => throw s!"request on stream {stream}: no slot collects it"
        | some i =>
          match (if len == 0 then none else (planNew len spans).toOption) with
          | none => pure (refuse before i UNAVAILABLE)
          | some pl =>
            let mine := (List.range pl.rs.length).filterMap pl.rangeSpan
            pure (answer before i (← natF j "root") mine spans ((← natF j "inst") == 1))
      | _ => throw s!"unknown slot event {ev}"
    check (model == after) s!"slot {ev}: the model gives {repr model}, the code {repr after}"
    check (mrc == rc) s!"slot {ev}: the model resets {mrc}, the code {rc}"
    pure after

def replayK (j : J) : Except String Unit := do
  let ln ← natF j "ln"
  let k ← natF j "k"
  check (protoK ln == (if k == 0 then none else some k)) s!"proof_k {ln}: model {protoK ln}, code {k}"

/-- The event tags of this trace. -/
def isTag (t : String) : Bool :=
  t == "vplan" || t == "vread" || t == "vk" || t == "vsrvnew" || t == "vsrv" || t == "vslotnew" || t == "vslot"

/-- Replay one event; the server model state is threaded. -/
def replayEvent (j : J) (s : Srv) : Except String Srv := do
  match ← strF j "t" with
  | "vplan" => replayPlan j; pure s
  | "vread" => replayRead j; pure s
  | "vk" => replayK j; pure s
  | "vslotnew" | "vslot" => do pure { s with tab := ← replaySlot j s.tab }
  | _ => replayServer j s

end Pinc.TraceValuesPlan
