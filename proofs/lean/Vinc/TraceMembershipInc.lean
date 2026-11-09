import Vinc.Json
import Vinc.MembershipInc

/-!
# Replay of the incarnation traces

The Lean half of the trace validation of `Incarnation` and `AddressTag` (the Rust test `trace_membership`, part `inc`;
the TLA+ half is `TraceIncarnation.tla`). Every `mi` event carries the host store as the call found it (`pers`, `sl`,
`rf`, `sf`) and the result of the real code; the replay applies the model function of `Vinc.MemInc` to the same inputs
and requires the same result (ok or the error, the word, the store afterwards).

* `st`: `MemInc.start`; on success the model's `Inc` of the run is the new life.
* `nr`: `MemInc.nextRecord`; `nrn`: `n` of them, stopping at the first error, with the count done.
* `ob`: `MemInc.observe`.
* `mv` / `tg`: `Tag.moved` and `Tag.tag` with the host's `address_hash(m) = [tk, m, 0, 0, 0, 0, 0, 7]`.

A new `run` starts from no incarnation and a fresh tag.
-/

namespace Vinc.TraceMembershipInc
open Vinc.Json Vinc.MemInc

/-- The replay state: the run, its incarnation and its tag. -/
structure W where
  run : Option Nat := none
  inc : Option Inc := none
  tag : Tag := Tag.init

instance : Inhabited W := ⟨{}⟩

def isTag (t : String) : Bool := t == "mi"

/-- Four 16-bit limbs, least significant first. -/
def limbsOf (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] =>
    check (a < 65536 && b < 65536 && c < 65536 && d < 65536) "limb out of range"
    pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw "not four limbs"

def u64F (j : J) (k : String) : Except String Nat := do limbsOf (← field j k)

/-- An optional `u64`: a list of length 0 or 1 of limbs. -/
def optF (j : J) (k : String) : Except String (Option Nat) := do
  match (← field j k).arr? with
  | some a =>
    match a.toList with
    | [] => pure none
    | [x] => pure (some (← limbsOf x))
    | _ => throw s!"field {k} is not an option"
  | none => throw s!"field {k} is not an option"

def errName : Err → String
  | .store => "store"
  | .exhausted => "exhausted"

/-- The host store of an event. -/
def localOf (j : J) : Except String Local := do
  pure ⟨← boolF j "pers", ← optF j "sl", ← boolF j "rf", ← boolF j "sf"⟩

/-- Compare the recorded outcome with the model's: ok or the error name, the word, the store after. -/
def cmpOut (j : J) (what : String) (before : Option Nat) (r : Except Err (Nat × Local)) : Except String Unit := do
  let ok ← boolF j "ok"
  let err ← strF j "err"
  match r with
  | .ok (w, l') =>
    check ok s!"{what}: the model succeeds, the code failed with {err}"
    check ((← u64F j "w") == w) s!"{what}: word, model {w}"
    check ((← optF j "sl2") == l'.sealed) s!"{what}: store after, model {repr l'.sealed}"
  | .error e =>
    check (!ok) s!"{what}: the model fails with {errName e}, the code succeeded"
    check (err == errName e) s!"{what}: error, model {errName e}, code {err}"
    check ((← optF j "sl2") == before) s!"{what}: a failed call changed the store"

/-- `address_hash(moves)` of the test host. -/
def hashOf (tk : Nat) (m : Nat) : List Nat := [tk, m, 0, 0, 0, 0, 0, 7]

def replayEvent (j : J) (w : W) : Except String W := do
  let run ← natF j "run"
  let w := if w.run == some run then w else { run := some run }
  let op ← strF j "op"
  match op with
  | "st" =>
    let l ← localOf j
    let r := start l (← u64F j "wall") (← u64F j "fl")
    cmpOut j "start" l.sealed (r.map fun (i, l') => (i.word, l'))
    match r with
    | .ok (i, _) => pure { w with inc := some i }
    | .error _ => pure w
  | "nr" =>
    let some i := w.inc | throw "nr before a start"
    let l ← localOf j
    let r := nextRecord l i
    cmpOut j "next_record" l.sealed (r.map fun (wd, _, l') => (wd, l'))
    match r with
    | .ok (_, i', _) => pure { w with inc := some i' }
    | .error _ => pure w
  | "nrn" =>
    let some i := w.inc | throw "nrn before a start"
    let l ← localOf j
    let n ← natF j "n"
    let rec go : Nat → Nat → Inc → Local → Nat → Except Err (Nat × Local) → (Nat × Inc × Local × Except Err (Nat × Local))
      | 0, done, i, l, _, last => (done, i, l, last)
      | k + 1, done, i, l, _, _ =>
        match nextRecord l i with
        | .ok (wd, i', l') => go k (done + 1) i' l' wd (.ok (wd, l'))
        | .error e => (done, i, l, .error e)
    let (done, i', l', last) := go n 0 i l 0 (.ok (i.word, l))
    check ((← natF j "done") == done) s!"next_record x{n}: done, model {done}"
    cmpOut j s!"next_record x{n}" l'.sealed last
    pure { w with inc := some i' }
  | "ob" =>
    let some i := w.inc | throw "ob before a start"
    let l ← localOf j
    let seen ← u64F j "seen"
    let r := observe l i seen
    cmpOut j "observe" l.sealed (r.map fun (_, i', l') => (i'.word, l'))
    match r with
    | .ok (ch, i', _) =>
      check ((← boolF j "ch") == ch) "observe: changed flag"
      pure { w with inc := some i' }
    | .error _ => pure w
  | "mv" =>
    pure { w with tag := w.tag.moved (← u64F j "now") }
  | "tg" =>
    let now ← u64F j "now"
    let tk ← natF j "tk"
    let (t, tag') := w.tag.tag now (← boolF j "refl") (hashOf tk)
    check ((← natList (← field j "tag")) == t) s!"tag, model {t}"
    check ((← natF j "mv") == tag'.moves) "tag: move counter"
    pure { w with tag := tag' }
  | _ => throw s!"unknown incarnation event {op}"

end Vinc.TraceMembershipInc
