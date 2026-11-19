import Pinc.Json
import Pinc.Tree
import Pinc.Sizes
import Pinc.VerifyBytes
import Pinc.MachineEnc
import Std.Data.HashMap

/-!
# Replay of the verifier and size traces

The replay half of the trace validation of `RangeVerifier` and of `Layout`: it reads the events written by the
Rust test `trace_verifier` and checks them against the proved model.

A `vrun` event starts a run: the value length, group log and requested byte range must give the recorded group
count and group range (`Layout.groups`, `Layout.groupRange`), and the model verifier starts at the recorded root
(`Tree.init`). A `vfeed` event is one call of `feed`. The replay keeps the model state and the number of bytes
buffered, and checks, in this order:

* the verifier's `next_len` before the call and the fast-path predicate equal the model's;
* a failed verifier repeats its error; an empty input does nothing; a complete verifier says "too much data";
* otherwise the call takes the whole item from the input when nothing is buffered and the input holds it (the
  fast path), else `min(input, still needed)` bytes into the buffer; the bytes consumed must equal that;
* when the item is complete, the hash call the model makes for it (`Tree.query`) must be the recorded one, the
  recorded hash values must form a function, and `Tree.feed` run under the recorded value (`Tree.feed_congr`
  shows the step depends on the hash only through this one call) must release, push or fail exactly as the
  verifier did, with the error kind and released offset it reported;
* a released group borrows the input exactly on the fast path, and is the bytes that were hashed;
* the step that the range encoder emitted for the item is the model's node: a parent's outboard offset is
  `64 * preorderIndex`, a group's offset and length are `lo * group_len` and `group_size`;
* the `next_len` and `is_complete` reported after the call equal the model's, and the stack stays within 55.

Every `vfeed` event is also replayed through the byte-level model `VerifyBytes.feedCode` on the real stream
offsets: the input of the call is the bytes `pos .. pos + ilen` of the stream (a byte is represented by its offset),
the model's buffer holds the offsets already taken, and the model must give the recorded result: the bytes consumed,
the error, whether a group is released, its byte offset, that its bytes are exactly the offsets of the completed item
(`istart`), the path (`input` on the fast path, `buf` otherwise), and the same state as the item model afterwards.
`pos` must advance by the bytes consumed, so the stream is fed contiguously, with the unconsumed tail fed again.

An `enc` event is the complete list of steps of `RangeEncoder` for a layout (up to `u64::MAX` bytes) and a range, and
must equal the model `Encode.encRun`: every parent step is `64 * preorderIndex` of the node the model visits and every
group step is the model's group, so the split `leftGroups` of every node visited and the position of every parent are
checked on trees of up to `2^54` groups. An `encout` event is `encode_range` with an output buffer of a given size,
and must equal `Machine.encodeRangeM` on a 64-bit `usize`: `OutputTooSmall` exactly when the buffer is short.

A `sizes` event is checked against `Layout.groups`, `Layout.hh` (the tree height, `Sizes.ht_eq`, and
`Sizes.depth_eq` for the `leading_zeros` form), `Layout.outboardSize` and `Layout.groupSize`.
-/

namespace Pinc.TraceVerifier
open Pinc.Json Pinc.Layout Pinc.Tree

/-- The model state of the current run. -/
structure Run where
  len : Nat
  log : Nat
  n : Nat
  first : Nat
  last : Nat
  st : State Nat Nat
  filled : Nat
  errk : String
  bs : VerifyBytes.BS Nat
  pos : Nat

/-- The replay state of a file: the current run and the oracle (hash call to recorded value). -/
structure RState where
  run : Option Run := none
  oracle : Std.HashMap (List Nat) Nat := {}

/-- The size of the stream item for a node. -/
def needOf (len log : Nat) (nd : Node Nat) : Nat := if nd.hi - nd.lo = 1 then groupSize len log nd.lo else 64

/-- `next_len`: `none` when complete or failed. -/
def Run.nl (r : Run) : Int :=
  if r.st.failed then -1 else
  match r.st.stack with
  | [] => -1
  | nd :: _ => (needOf r.len r.log nd : Int) - r.filled

/-- The key of a hash call, as the trace spells it. -/
def keyOf : Query Nat Nat → List Nat
  | .leaf b i d => [0, if b then 1 else 0, i, d]
  | .parent b l r => [1, if b then 1 else 0, l, r]

private def keyF (j : J) : Except String (List Nat) := do
  match (← field j "key").arr? with
  | some #[k, b, x, y] =>
    let kind ← match k.str? with
      | some "L" => pure 0
      | some "P" => pure 1
      | _ => throw "bad key kind"
    let bb ← match b.bool? with
      | some bb => pure (if bb then 1 else 0)
      | none => throw "bad key flag"
    match x.nat?, y.nat? with
    | some x, some y => pure [kind, bb, x, y]
    | _, _ => throw "bad key"
  | _ => throw "bad key"

private def itemF (j : J) : Except String (Raw Nat Nat) := do
  let it ← field j "item"
  pure ⟨← natF it "l", ← natF it "r", ← natF it "d"⟩

private def stepF (j : J) : Except String (List Nat × String) := do
  match (← field j "step").arr? with
  | some a =>
    let tag ← match a[0]? with
      | some t => match t.str? with
        | some s => pure s
        | none => throw "bad step"
      | none => pure ""
    let nums ← (a.toList.drop 1).mapM fun v => match v.nat? with
      | some x => pure x
      | none => throw "bad step"
    pure (nums, tag)
  | none => throw "bad step"

/-- Replay a `vrun` event. -/
def replayRun (rs : RState) (j : J) : Except String RState := do
  let len ← natF j "len"
  let log ← natF j "log"
  let s ← natF j "s"
  let e ← natF j "e"
  check (log ≤ 20 && len ≤ u64Max) "run outside the supported layout"
  let n := groups len log
  check (n == (← natF j "n")) s!"groups {len} {log}"
  match groupRange len log s e with
  | some (a, b) =>
    check (a == (← natF j "first") && b == (← natF j "last")) s!"group_range {len} {log} {s} {e}"
    let root ← natF j "root"
    let run : Run := ⟨len, log, n, a, b, Tree.init root n a b, 0, "none", ⟨Tree.init root n a b, [], false⟩, 0⟩
    pure { rs with run := some run }
  | none => throw s!"group_range {len} {log} {s} {e}: model rejects a recorded run"

private def errName : VerifyBytes.E → String
  | .parentMismatch => "parent"
  | .groupMismatch => "group"
  | .tooMuchData => "toomuch"
  | .outputTooSmall => "small"

private def nodeKeys {D : Type} (st : State Nat D) : List (Nat × Nat × Nat) :=
  st.stack.map fun nd => (nd.cv, nd.lo, nd.hi)

/-- The recorded result of a call against the byte-level model's. -/
private def checkRes (res : VerifyBytes.Res) (err : String) (consumed off : Int) (ptr : String) (fast : Bool)
    (istart : Int) : Except String Unit :=
  match res with
  | .err e =>
    check (err == errName e && consumed == -1 && off == -1 && ptr == "none") s!"byte model: error {errName e}"
  | .ok k v => do
    check (err == "none" && consumed == (k : Int)) s!"byte model: {k} bytes consumed"
    match v with
    | none => check (off == -1 && ptr == "none") "byte model: no group released"
    | some (o, d) =>
      check (off == (o : Int) && ptr == (if fast then "input" else "buf")) "byte model: released group and path"
      check (istart ≥ 0 && d == List.range' istart.toNat d.length) "byte model: released bytes are the item's"

/-- Replay a `vfeed` event. -/
def replayFeed (rs : RState) (j : J) : Except String RState := do
  let some r := rs.run | throw "vfeed before vrun"
  let ilen ← natF j "ilen"
  let out ← strF j "out"
  let err ← strF j "err"
  let consumed ← intF j "consumed"
  let off ← intF j "off"
  let ptr ← strF j "ptr"
  let nl0 ← intF j "nl0"
  let nl ← intF j "nl"
  let cmp ← boolF j "cmp"
  let fast ← boolF j "fast"
  let rd ← natF j "rd"
  let pos ← natF j "pos"
  let istart ← intF j "istart"
  check (pos == r.pos) s!"the input starts at stream offset {pos}, the model expects {r.pos}"
  check (r.filled == r.bs.buf.length) "the buffered bytes equal filled"
  check (nl0 == r.nl) s!"next_len before: code {nl0}, model {r.nl}"
  let fastM := r.filled == 0 && r.nl ≥ 0 && (ilen : Int) ≥ r.nl
  check (fast == fastM) "fast-path predicate"
  check (rd == 0 || out == "release") "released bytes outside a release"
  check (r.st.stack.length ≤ 55) "stack above 55"
  -- the byte-level model: the call on the real stream offsets
  let item0 ← itemF j
  let hout0 ← natF j "hout"
  let cfg : VerifyBytes.Cfg Nat :=
    { H := ⟨fun _ _ _ => hout0, fun _ _ _ => hout0⟩, rd := fun _ => ⟨item0.l, item0.r, []⟩,
      len := r.len, log := r.log, n := r.n, first := r.first, last := r.last }
  let some (bres, bs1) := VerifyBytes.feedCode 64 cfg r.bs (if ilen == 0 then [] else List.range' pos ilen)
    | throw "the byte-level model failed arithmetically"
  checkRes bres err consumed off ptr fast istart
  let pos' := match bres with | .ok k _ => pos + k | .err _ => pos
  let coherent (r' : Run) : Except String Unit := do
    check (bs1.buf.length == r'.filled) "buffered bytes after the call"
    check (bs1.core.failed == r'.st.failed) "failed flag after the call"
    check (nodeKeys bs1.core == nodeKeys r'.st) "stack after the call"
  if r.st.failed then
    check (out == "sticky" && err == r.errk && consumed == -1 && off == -1 && ptr == "none" && nl == -1 && !cmp)
      "a failed verifier must repeat its error"
    return rs
  if ilen == 0 then
    check (out == "empty" && err == "none" && consumed == 0 && off == -1 && ptr == "none" && nl == r.nl &&
      cmp == r.st.stack.isEmpty) "an empty input must do nothing"
    return rs
  match r.st.stack with
  | [] =>
    check (out == "toomuch" && err == "toomuch" && consumed == -1 && off == -1 && ptr == "none" && nl == -1 && cmp)
      "a complete verifier must refuse more data"
    return rs
  | nd :: _ =>
    let need := needOf r.len r.log nd
    let take := if fastM then need else min ilen (need - r.filled)
    if r.filled + take < need then
      let r' := { r with filled := r.filled + take, bs := bs1, pos := pos' }
      check (out == "more" && err == "none" && consumed == take && off == -1 && ptr == "none" &&
        nl == r'.nl && !cmp) "partial item"
      coherent r'
      return { rs with run := some r' }
    -- the item is complete
    let it ← itemF j
    let hout ← natF j "hout"
    let key ← keyF j
    match query r.n r.st it with
    | some q => check (keyOf q == key) s!"hash call: model {keyOf q}, code {key}"
    | none => throw "model makes no hash call for a completed item"
    let oracle ← match rs.oracle[key]? with
      | some v => do check (v == hout) s!"the recorded hash is not a function at {key}"; pure rs.oracle
      | none => pure (rs.oracle.insert key hout)
    let (stepNums, tag) ← stepF j
    let leaf := nd.hi - nd.lo == 1
    if leaf then
      check (tag == "g" && stepNums == [nd.lo * groupLen r.log, groupSize r.len r.log nd.lo])
        s!"encoder step for group {nd.lo}: {tag} {stepNums}"
    else
      check (tag == "p" && stepNums == [64 * preorderIndex r.n nd.lo nd.hi])
        s!"encoder step for parent [{nd.lo}, {nd.hi}): {tag} {stepNums}"
    let H : Hash Nat Nat := ⟨fun _ _ _ => hout, fun _ _ _ => hout⟩
    let st' := feed H r.n r.first r.last r.st it
    let r' := { r with st := st', filled := 0, bs := bs1, pos := pos' }
    if st'.failed then
      let ek := if leaf then "group" else "parent"
      check (out == "reject" && err == ek && consumed == -1 && off == -1 && ptr == "none" && nl == -1 && !cmp)
        s!"rejection of [{nd.lo}, {nd.hi})"
      coherent r'
      return { rs with run := some { r' with errk := ek }, oracle }
    check (err == "none" && consumed == take && nl == r'.nl && cmp == st'.stack.isEmpty) "accepted item report"
    if leaf then
      check (st'.released == r.st.released ++ [(nd.lo, it.d)]) "release"
      check (out == "release" && off == (nd.lo * groupLen r.log : Nat) && rd == it.d &&
        ptr == (if fastM then "input" else "buf")) "released group report"
    else
      check (out == "parent" && off == -1 && ptr == "none" && st'.released == r.st.released) "parent report"
    coherent r'
    return { rs with run := some r', oracle }

/-- The steps of a recorded `enc` event as the model's `Encode.Step`s. -/
private def stepsF (j : J) : Except String (List Encode.Step) := do
  match (← field j "steps").arr? with
  | some a => a.toList.mapM fun st => do
    match st.arr? with
    | some v =>
      let tag ← match v[0]? with
        | some t => match t.str? with
          | some s => pure s
          | none => throw "bad step"
        | none => throw "bad step"
      let nums ← (v.toList.drop 1).mapM fun x => match x.nat? with
        | some n => pure n
        | none => throw "bad step"
      match tag, nums with
      | "p", [o] => pure (Encode.Step.parent o)
      | "g", [o, l] => pure (Encode.Step.group o l)
      | _, _ => throw "bad step"
    | none => throw "bad step"
  | none => throw "bad steps"

private def stepEq : Encode.Step → Encode.Step → Bool
  | .parent a, .parent b => a == b
  | .group a l, .group b m => a == b && l == m
  | _, _ => false

/-- Replay an `enc` event: the recorded steps of the encoder are the model's, in order. -/
def replayEncoder (j : J) : Except String Unit := do
  let len ← natF j "len"
  let log ← natF j "log"
  let s ← natF j "s"
  let e ← natF j "e"
  check (log ≤ 20 && len ≤ u64Max) "encoder run outside the supported layout"
  let n := groups len log
  let some (first, last) := groupRange len log s e | throw s!"group_range {len} {log} {s} {e}: model rejects a recorded run"
  let model := (Encode.encRun len log first last (2 * n) (Encode.encInit len log first last)).1
  let steps ← stepsF j
  check (model.length == steps.length) s!"encoder {len} {log} [{s}, {e}): {steps.length} steps, model {model.length}"
  for (m, c) in model.zip steps do
    check (stepEq m c) s!"encoder {len} {log} [{s}, {e}): a step differs from the model"

/-- Replay an `encout` event: `encode_range` with an output buffer of `olen` bytes. -/
def replayEncout (j : J) : Except String Unit := do
  let len ← natF j "len"
  let log ← natF j "log"
  let s ← natF j "s"
  let e ← natF j "e"
  let olen ← natF j "olen"
  let res ← strF j "res"
  let n ← natF j "n"
  check (log ≤ 20 && len ≤ u64Max) "encode_range run outside the supported layout"
  let some (first, last) := groupRange len log s e | throw "group_range rejects a recorded run"
  match Machine.encodeRangeM Nat.log2 64 len (outboardSize len log) len log first last olen with
  | some (.ok m) => check (res == "ok" && n == m) s!"encode_range {len} {log} [{s}, {e}) into {olen}: model writes {m}"
  | some (.error .outputTooSmall) => check (res == "small") s!"encode_range {len} {log} [{s}, {e}) into {olen}: model says too small"
  | some (.error .rangeOutOfBounds) => throw "the model reads out of bounds"
  | none => throw "the machine model of encode_range failed arithmetically"

/-- Replay a `sizes` event. -/
def replaySizes (j : J) : Except String Unit := do
  let len ← natF j "len"
  let log ← natF j "log"
  check (log ≤ 20 && len ≤ u64Max) "sizes outside the supported layout"
  let n := groups len log
  check (n == (← natF j "groups")) s!"groups {len} {log}"
  let depth := if n ≤ 1 then 0 else hh n
  check (depth == (← natF j "depth")) s!"depth of {n} groups"
  check (outboardSize len log == (← natF j "ob")) s!"outboard_size {len} {log}"
  for p in ← pairList (← field j "gs") do
    check (groupSize len log p.1 == p.2) s!"group_size {len} {log} {p.1}"

end Pinc.TraceVerifier
