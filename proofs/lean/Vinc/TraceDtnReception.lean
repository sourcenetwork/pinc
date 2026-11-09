import Vinc.Json
import Vinc.TraceDtnLayout
import Vinc.DtnReception

/-!
# Replay of the reception traces

The Lean half of the trace validation of `Reception` (`dtn_reception.ndjson`, written by the Rust test
`trace_dtn_reception`). Every `rx` event is replayed through the functions the theorems of `Vinc.DtnReception` are
about: a feed through `feed` (`feedGo` with the held set of `Vinc.Ranges`; the number of groups that verified is not
recorded, so the stream is an intact one, one with a wrong group at some position, a short one or one with trailing
bytes, and some choice must reproduce the recorded verdict and the recorded held set); the answers of `holds`,
`containsRange`, `heldIn` and the layout of `Vinc.DtnLayout` for `is_complete` and `is_decodable`; `finish` by the
verdict rules proved per block in `Vinc.DtnReception` (Incomplete exactly when a block holds fewer than `k` symbols;
Inconsistent only when a block that is not fully held has a parity that is not a code word, exactly so while no
earlier finish rewrote a block); `resume` by its checks. `nextMissing` is the loop of the code, replayed here and
checked by TLC (`DtnReception.tla`) but not proved. It is the port of `proofs/tla/TraceDtnReception.tla`.
-/

namespace Vinc.TraceDtnReception
open Vinc.Json Vinc.DtnLayout Vinc.DtnReception Vinc.Ranges Vinc.TraceDtnLayout

def isTag (t : String) : Bool := t == "rx"

/-- The replay state: the run's constants and the held set the previous event recorded. -/
structure W where
  cap : Nat := 0
  g : Nat := 1
  total : Nat := 0
  faulty : List Nat := []
  lay : L := ⟨1, 0, 0, 1⟩
  have_ : List Interval := []
  touched : Bool := false

/-- `Reception::next_missing`, the loop of the code. -/
def nmGo (g total : Nat) : List Interval → Nat → Option (Nat × Nat)
  | [], at_ => if at_ < total * g then some (at_ / g, total) else none
  | iv :: rest, at_ =>
    if iv.2 ≤ at_ then nmGo g total rest at_
    else if iv.1 > at_ then some (at_ / g, min iv.1 (total * g) / g)
    else nmGo g total rest iv.2

def decodableB (l : L) (g total : Nat) (h : List Interval) : Bool :=
  (List.range l.blocks).all fun b => decide (l.blockK b ≤ heldIn g total h (b * (l.k + l.m)) (l.blockN b))

def fullB (l : L) (g total : Nat) (h : List Interval) (b : Nat) : Bool :=
  decide (heldIn g total h (b * (l.k + l.m)) (l.blockN b) = l.blockN b)

def decB (l : L) (g total : Nat) (h : List Interval) (b : Nat) : Bool :=
  decide (l.blockK b ≤ heldIn g total h (b * (l.k + l.m)) (l.blockN b))

/-- Some block is rewritten by `finish`: a block that is not fully held, is decodable, and every block before it is
fully held or decodable. -/
def touchedNow (l : L) (g total : Nat) (h : List Interval) : Bool :=
  (List.range l.blocks).any fun b =>
    !fullB l g total h b && decB l g total h b &&
      (List.range b).all fun b2 => fullB l g total h b2 || decB l g total h b2

def pairs (j : J) (k : String) : Except String (List Interval) := do
  match (← field j k).arr? with
  | some a => a.toList.mapM fun r => match r.arr? with
    | some #[x, y] => do
      match x.nat?, y.nat? with
      | some a, some b => pure (a, b)
      | _, _ => throw s!"field {k}: not numbers"
    | _ => throw s!"field {k}: not a pair"
  | none => throw s!"field {k} is not an array"

/-- The class of a feed: the stream fault first, then the full set. -/
def feedClass (n nv : Nat) (extra full : Bool) : String :=
  if nv < n || extra then "tree" else if full then "full" else "ok"

/-- The answers of the helpers on the recorded held set. -/
def snap (j : J) (w : W) (h : List Interval) : Except String Unit := do
  let hold ← natList (← field j "hold")
  for s in List.range w.total do
    check ((holds w.g w.total h s) == (hold.getD s 0 == 1)) s!"holds {s}"
  check ((containsRange h (0, w.total * w.g)) == (← boolF j "cmp")) "is_complete"
  check (decodableB w.lay w.g w.total h == (← boolF j "dec")) "is_decodable"
  match (← field j "nm").arr? with
  | some a =>
    for f in List.range (w.total + 1) do
      let want := a[f]?.bind (·.arr?)
      match nmGo w.g w.total h (f * w.g), want with
      | some (x, y), some r => check (r.toList.map (·.nat?) == [some x, some y]) s!"next_missing {f}"
      | none, some r => check r.isEmpty s!"next_missing {f}: model none"
      | _, none => throw "nm entry"
  | none => throw "nm is not an array"

def replayEvent (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  match op with
  | "new" =>
    let lay : L := ⟨← natF j "k", ← natF j "m", ← natF j "log", ← natF j "payload"⟩
    check lay.valid "the layout of the run is valid"
    check (lay.totalSyms == (← natF j "total")) "total symbols"
    pure { cap := ← natF j "W", g := ← natF j "g", total := ← natF j "total", faulty := ← natList (← field j "faulty"),
           lay, have_ := [], touched := false }
  | "feed" =>
    let a ← natF j "a"
    let b ← natF j "b"
    let kind ← strF j "kind"
    let res ← strF j "res"
    let h2 ← pairs j "have"
    snap j w h2
    if kind == "range" then
      check (w.lay.byteRange a b).isNone "the range is past the last symbol"
      check (res == "buffer" && h2 == w.have_) "a bad range changes nothing"
    else
      check (!(w.lay.byteRange a b).isNone) "the range is inside the bundle"
      let n := b - a
      let good := List.replicate n 0
      let cands : List (List Nat × Bool) :=
        if a == b then [(good, false)]
        else if kind == "good" then [(good, false)]
        else if kind == "trail" then [(good, true)]
        else if kind == "short" then (List.range n).map fun jj => (List.replicate jj 0, false)
        else (List.range n).map fun p => ((List.range n).map fun i => if i == p then 1 else 0, false)
      let ok := cands.any fun (vals, extra) =>
        let ct : Nat → Nat := fun _ => 0
        let r := feedGo ct w.cap w.g (fun _ => 9) w.have_ false a vals
        let cls := if a == b then "ok" else feedClass n (nverified ct a vals) extra r.2.2.1
        let h' := if a == b then w.have_ else r.2.1
        cls == res && h' == h2
      check ok s!"feed {a}..{b} ({kind}): no stream gives {res} and the recorded held set"
    pure { w with have_ := h2 }
  | "fin" =>
    let res ← strF j "res"
    let h2 ← pairs j "have"
    snap j w h2
    let pre := w.have_
    let dec := decodableB w.lay w.g w.total pre
    check ((res == "incomplete") == !dec) "Incomplete exactly when a block holds fewer than k symbols"
    let faultyNonfull := w.faulty.any fun b => !fullB w.lay w.g w.total pre b
    if !w.touched then
      check ((res == "inconsistent") == (dec && faultyNonfull)) "Inconsistent exactly on a non-code-word block that is not fully held"
    check (res != "inconsistent" || !w.faulty.isEmpty) "an honest sender is never inconsistent"
    check (res == "incomplete" || res == "inconsistent" || res == "ok") "finish verdict"
    check (h2 == if res == "ok" then [(0, w.total * w.g)] else pre) "finish records the whole bundle only on Ok"
    pure { w with have_ := h2, touched := w.touched || touchedNow w.lay w.g w.total pre }
  | "res" =>
    let res ← strF j "res"
    let h2 ← pairs j "have"
    snap j w h2
    let c ← natF j "case"
    check (res == (if c == 0 then "crypto" else if c == 1 then "expired" else if c == 2 then "buffer" else "ok"))
      "resume verdict"
    check (h2 == w.have_) "resume keeps the verified ranges"
    pure w
  | _ => throw s!"unknown op {op}"

end Vinc.TraceDtnReception
