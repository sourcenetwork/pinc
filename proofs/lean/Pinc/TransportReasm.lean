/-!
# Handshake fragments: the model

A model of `pinc-transport` `conn/reasm.rs` (`Reassembly`), as `proofs/tla/ReasmOps.tla` has it, over unbounded
`Nat`: one handshake message put together from fragments that arrive in any order and any number of times, kept as
at most `nr` disjoint sorted runs `[start, end)`. `Pinc.TraceReasm` replays the recorded calls of the real code
through these functions; the theorems are in `Pinc.TransportReasmThm`. The bytes are not in the model: the code
copies a fragment into the buffer at its offset when it keeps it.
-/

namespace Pinc.TransportReasm

abbrev Iv := Nat × Nat

structure R where
  runs : List Iv := []
  total : Nat := 0
  deriving BEq, Repr

/-- The runs that do not touch the new one are kept; the ones that do are folded into it. -/
def mergeRuns : List Iv → Nat → Nat → List Iv → List Iv × Nat × Nat
  | [], lo, hi, keep => (keep, lo, hi)
  | (s, e) :: t, lo, hi, keep =>
    if e < lo ∨ hi < s then mergeRuns t lo hi (keep ++ [(s, e)]) else mergeRuns t (min lo s) (max hi e) keep

/-- The new run among the kept ones, in order of start. -/
def insertRun : List Iv → Iv → List Iv
  | [], iv => [iv]
  | x :: t, iv => if x.1 < iv.1 then x :: insertRun t iv else iv :: x :: t

/-- A fragment of `dlen` bytes at `off` of a message of `total` bytes: the length of the message when it is complete
(and a fresh reassembly), and the new state. `mx` is the largest message, `nr` the most runs. -/
def add (r : R) (mx nr total off dlen : Nat) : Option Nat × R :=
  if total = 0 ∨ mx < total then (none, r)
  else
    let r1 : R := if total ≠ r.total then { runs := [], total } else r
    let stop := min (off + dlen) total
    if stop ≤ off then (none, r1)
    else
      let m := mergeRuns r1.runs off stop []
      if m.1.length = nr then (none, r1)
      else
        let runs2 := insertRun m.1 (m.2.1, m.2.2)
        if runs2.length = 1 ∧ m.2.1 = 0 ∧ m.2.2 = total then (some total, {})
        else (none, { runs := runs2, total := r1.total })

end Pinc.TransportReasm
