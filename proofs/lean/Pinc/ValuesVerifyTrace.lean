import Pinc.Json
import Pinc.TraceVerifier
import Pinc.ValuesVerify

/-!
# Replay of the `GroupVerifier` traces

The replay half of the trace validation of `pinc_values::verify::GroupVerifier` against `RangeVerifier`: it reads the
events written by the Rust test `trace_values_verify` and checks them against the proved models.

* `gvrun` starts a run and `gvfeed` is one call of `feed` on both verifiers with the same input. The
  `RangeVerifier` half is replayed by `TraceVerifier.replayRun` and `replayFeed` (the item model, the hash oracle,
  the byte-level model `VerifyBytes.feedCode`). The `GroupVerifier` half is replayed through `ValuesVerify.feedG` on
  the real stream offsets: the input of the call is the bytes `pos .. pos + ilen` (a byte is represented by its
  offset), the hash is the recorded oracle, restricted to the bytes `istart ..` the call completed (so the model hashes
  exactly the bytes of the item, and reads the pair from exactly those bytes). The model must give the recorded
  result: the bytes consumed, the error, the group (offset and length, and its bytes are the item's), and the
  observables `next_len`, `next_item`, `at_boundary`, `is_complete`, `failure` before and after the call. The two
  verifiers must also agree: the same consumed bytes, group offset and error, the same stack, the same groups passed,
  the same number of bytes buffered, the same failure.
* `gvrfeed` is a call of `RangeVerifier::feed` alone (the genuine group fed whole in place of a skipped one), replayed
  by `TraceVerifier.replayFeed`.
* `gvskip` is `GroupVerifier::skip_group`: the model `ValuesVerify.skipG` must give the recorded result and the
  observables before and after; a refused skip leaves the verifier as it was; an accepted one leaves the
  `GroupVerifier` in the state the `RangeVerifier` reached by being fed the group (the `gvrfeed` before it).
-/

namespace Pinc.ValuesVerifyTrace
open Pinc.Json Pinc.Layout Pinc.Tree Pinc.VerifyBytes Pinc.ValuesVerify

/-- The replay state of a file: the `RangeVerifier` replay state and the model state of the `GroupVerifier`. -/
structure W where
  rs : TraceVerifier.RState := {}
  gs : Option (GS Nat) := none

def isTag (t : String) : Bool := t == "gvrun" || t == "gvfeed" || t == "gvrfeed" || t == "gvskip"

private def errName : Err → String
  | .parentMismatch => "parent"
  | .groupMismatch => "group"
  | .tooMuchData => "toomuch"
  | .outputTooSmall => "small"
  | .stackOverflow => "overflow"

private def itemOf (j : J) (k : String) : Except String (Option GItem) := do
  match (← field j k).arr? with
  | some #[] => pure none
  | some #[t] => if t.str? == some "p" then pure (some .pair) else throw s!"bad item {k}"
  | some #[t, o, l] =>
    match t.str?, o.nat?, l.nat? with
    | some "g", some o, some l => pure (some (.group o l))
    | _, _, _ => throw s!"bad item {k}"
  | _ => throw s!"bad item {k}"

private def nodeKeys (st : List (Node Nat)) : List (Nat × Nat × Nat) := st.map fun nd => (nd.cv, nd.lo, nd.hi)

/-- The model configuration of a call: the hash is the recorded oracle value, valid only for the bytes of the item
the call completed (`istart` onwards) and, for a pair, the two chaining values the item read as. -/
private def gcfg (r : TraceVerifier.Run) (istart : Int) (hout l rr : Nat) : Cfg Nat :=
  { H := ⟨fun _ _ d => if istart ≥ 0 && d == List.range' istart.toNat d.length then hout else 0,
          fun _ a b => if istart ≥ 0 && a == l && b == rr then hout else 0⟩,
    rd := fun b => if istart ≥ 0 && b == List.range' istart.toNat 64 then ⟨l, rr, b⟩ else ⟨0, 0, b⟩,
    len := r.len, log := r.log, n := r.n, first := r.first, last := r.last }

private def itemLR (j : J) : Except String (Nat × Nat) := do
  let it ← field j "item"
  pure (← natF it "l", ← natF it "r")

private def obsCheck (c : Cfg Nat) (s : GS Nat) (pre : String) (nl : Int) (bound : Bool) (item : Option GItem)
    (cmp : Bool) (fail : String) : Except String Unit := do
  check (((nextLenG c s).map (fun x => (x : Int))).getD (-1) == nl) s!"{pre}next_len"
  check (atBoundaryG s == bound) s!"{pre}at_boundary"
  check (nextItemG c s == item) s!"{pre}next_item"
  check (isCompleteG s == cmp) s!"{pre}is_complete"
  check ((match failureG s with | none => "none" | some e => errName e) == fail) s!"{pre}failure"

/-- The `RangeVerifier` run and the `GroupVerifier` model are in the same state. -/
private def sameState (g : GS Nat) (r : TraceVerifier.Run) : Except String Unit := do
  check (nodeKeys g.stack == nodeKeys r.st.stack) "the two verifiers have different stacks"
  check (g.released.map Prod.fst == r.st.released.map Prod.fst) "the two verifiers passed different groups"
  check (g.pair.length + g.hb.length == r.filled) "the two verifiers buffered different bytes"
  check (g.failed.isSome == r.st.failed) "the two verifiers differ on failure"

/-- Replay one event of a `GroupVerifier` trace. -/
def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "t" with
  | "gvrun" =>
    let rs ← TraceVerifier.replayRun w.rs j
    let some r := rs.run | throw "gvrun left no run"
    let c := gcfg r (-1) 0 0 0
    pure { rs := rs, gs := some (initG c (← natF j "root")) }
  | "gvrfeed" =>
    pure { w with rs := ← TraceVerifier.replayFeed w.rs j }
  | "gvfeed" =>
    let some g := w.gs | throw "gvfeed before gvrun"
    let some r0 := w.rs.run | throw "gvfeed before gvrun"
    let ilen ← natF j "ilen"
    let pos ← natF j "pos"
    let istart ← intF j "istart"
    let (l, rr) ← itemLR j
    let c := gcfg r0 istart (← natF j "hout") l rr
    -- the observables before the call
    check (((nextLenG c g).map (fun x => (x : Int))).getD (-1) == (← intF j "gnl0")) "before: next_len"
    check (atBoundaryG g == (← boolF j "gb0")) "before: at_boundary"
    check (nextItemG c g == (← itemOf j "gi0")) "before: next_item"
    -- the RangeVerifier half
    let rs1 ← TraceVerifier.replayFeed w.rs j
    let some r1 := rs1.run | throw "no run"
    -- the GroupVerifier half, on the real stream offsets
    let some (gr, g1) := feedG 64 c g (if ilen == 0 then [] else List.range' pos ilen)
      | throw "the model of GroupVerifier failed arithmetically"
    let err ← strF j "err"
    let consumed ← intF j "consumed"
    let off ← intF j "off"
    let glen ← intF j "glen"
    match gr with
    | .ok k grp =>
      check (err == "none" && consumed == (k : Int)) s!"GroupVerifier model: {k} bytes consumed"
      match grp with
      | none => check (off == -1 && glen == -1) "GroupVerifier model: no group"
      | some (o, n) =>
        check (off == (o : Int) && glen == (n : Int)) "GroupVerifier model: group offset and length"
        match g1.released.getLast? with
        | some (_, d) => check (istart ≥ 0 && d == List.range' istart.toNat n) "GroupVerifier model: the bytes hashed are the item's"
        | none => throw "GroupVerifier model: no group logged"
        check ((← natF j "rd") == (← natF j "grd")) "the bytes the caller kept differ from the ones RangeVerifier returned"
    | .err e =>
      check (err == errName e && consumed == -1 && off == -1 && glen == -1) s!"GroupVerifier model: error {errName e}"
    -- the observables after the call, and the agreement of the two verifiers
    obsCheck c g1 "after: " (← intF j "gnl") (← boolF j "gb") (← itemOf j "gi") (← boolF j "gcmp") (← strF j "gfail")
    sameState g1 r1
    check ((← boolF j "gcmp") == (← boolF j "cmp")) "is_complete differs between the verifiers"
    pure { rs := rs1, gs := some g1 }
  | "gvskip" =>
    let some g := w.gs | throw "gvskip before gvrun"
    let some r := w.rs.run | throw "gvskip before gvrun"
    let c := gcfg r (-1) 0 0 0
    obsCheck c g "before: " (← intF j "nl0") (← boolF j "bound0") (← itemOf j "item0") (← boolF j "cmp0") (← strF j "fail0")
    let ok ← boolF j "ok"
    let (res, g1) := skipG c g []
    obsCheck c g1 "after: " (← intF j "nl1") (← boolF j "bound1") (← itemOf j "item1") (← boolF j "cmp1") (← strF j "fail1")
    match res with
    | .ok (o, n) =>
      check (ok && (← intF j "off") == (o : Int) && (← intF j "glen") == (n : Int)) "skip_group model: group offset and length"
      -- RangeVerifier was fed the group: the two are in the same state
      sameState g1 r
    | .error e =>
      check (!ok && e == .tooMuchData) "skip_group model: refusal"
      check (g1.stack.length == g.stack.length && g1.released.length == g.released.length) "a refused skip changed the verifier"
    pure { w with gs := some g1 }
  | t => throw s!"unknown event {t}"

end Pinc.ValuesVerifyTrace
