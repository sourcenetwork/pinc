/-!
# The deadline heap: the model

A model of `vinc-core` `heap.rs` (`DeadlineHeap`), as `proofs/tla/HeapOps.tla` has it, over unbounded `Nat`: the
indexed binary min-heap of `(deadline, id)` pairs for the ids below `n`. The heap, the position index and the
deadlines are total functions, as the code's three arrays are; `put`, `up`, `down` and `set` follow the code call
for call (the hole of the code's sifts is the model's `put` at the end). `Vinc.TraceHeap` replays the recorded
calls of the real code through these functions; the theorems are in `Vinc.CoreHeapThm`.
-/

namespace Vinc.CoreHeap

/-- Replace the value of `f` at `i`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

/-- The state: the capacity (ids are below `n`), the heap of ids, the position of each id (`none` for the code's
`NONE`), the deadline of each id (kept, stale, after the id is removed), and the number of ids in the heap. -/
structure S where
  n : Nat
  heap : Nat → Nat
  pos : Nat → Option Nat
  dl : Nat → Nat
  len : Nat

/-- An empty heap for `n` ids. -/
def init (n : Nat) : S := { n, heap := fun _ => 0, pos := fun _ => none, dl := fun _ => 0, len := 0 }

/-- The order of the pairs: the deadline first, the lower id on a tie. -/
def lexLe (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))
def lexLt (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

/-- The key of the id at heap index `j`. -/
def key (s : S) (j : Nat) : Nat × Nat := (s.dl (s.heap j), s.heap j)

def put (s : S) (i id : Nat) : S := { s with heap := upd s.heap i id, pos := upd s.pos id (some i) }

/-- `up`: the element moves toward the root while its parent is later. -/
def upLoop (s : S) (i id : Nat) (k : Nat × Nat) : S :=
  if 0 < i ∧ lexLe (key s ((i - 1) / 2)) k = false then
    upLoop (put s i (s.heap ((i - 1) / 2))) ((i - 1) / 2) id k
  else put s i id
termination_by i
decreasing_by omega

def up (s : S) (i : Nat) : S := upLoop s i (s.heap i) (key s i)

/-- The child `down` looks at: the right one if it is earlier than the left one, else the left one. -/
def minChild (s : S) (i : Nat) : Nat :=
  if 2 * i + 2 < s.len ∧ lexLt (key s (2 * i + 2)) (key s (2 * i + 1)) = true then 2 * i + 2 else 2 * i + 1

theorem minChild_ge (s : S) (i : Nat) : 2 * i + 1 ≤ minChild s i := by
  unfold minChild; split <;> omega

theorem minChild_lt (s : S) (i : Nat) (h : 2 * i + 1 < s.len) : minChild s i < s.len := by
  unfold minChild; split <;> omega

set_option linter.unusedVariables false in
/-- `down`: the element moves toward the leaves while its earlier child is earlier. -/
def downLoop (s : S) (i id : Nat) (k : Nat × Nat) : S :=
  if h : 2 * i + 1 < s.len then
    if lexLe k (key s (minChild s i)) = true then put s i id
    else downLoop (put s i (s.heap (minChild s i))) (minChild s i) id k
  else put s i id
termination_by s.len - i
decreasing_by
  have := minChild_ge s i
  have := minChild_lt s i h
  simp only [put]
  omega

def down (s : S) (i : Nat) : S := downLoop s i (s.heap i) (key s i)

/-- After the last element sits in the hole it has gone up from: look where it is now and sift it down from there. -/
def settle (s3 : S) (last : Nat) : S :=
  match s3.pos last with
  | some q => down s3 q
  | none => s3

/-- `set id t`: give `id` the deadline `t`, or remove its deadline; an id outside `0..n` is ignored. -/
def set (s : S) (id : Nat) (t : Option Nat) : S :=
  if id < s.n then
    match s.pos id, t with
    | none, some t =>
      let s1 : S := { s with dl := upd s.dl id t, len := s.len + 1 }
      up (put s1 s.len id) s.len
    | some p, some t =>
      let s1 : S := { s with dl := upd s.dl id t }
      if t < s.dl id then up s1 p else if s.dl id < t then down s1 p else s1
    | some p, none =>
      let s1 : S := { s with len := s.len - 1, pos := upd s.pos id none }
      let last := s.heap (s.len - 1)
      if last ≠ id then
        settle (up (put s1 p last) p) last
      else s1
    | none, none => s
  else s

/-- The earliest deadline and its id. -/
def peek (s : S) : Option (Nat × Nat) := if s.len = 0 then none else some (s.dl (s.heap 0), s.heap 0)

/-- Remove the earliest, `f` times at most, and list what came out. -/
def drain : Nat → S → List (Nat × Nat)
  | 0, _ => []
  | f + 1, s =>
    match peek s with
    | none => []
    | some (t, id) => (t, id) :: drain f (set s id none)

/-- A run of calls. -/
def run (s : S) : List (Nat × Option Nat) → S
  | [] => s
  | (id, t) :: l => run (set s id t) l

end Vinc.CoreHeap
