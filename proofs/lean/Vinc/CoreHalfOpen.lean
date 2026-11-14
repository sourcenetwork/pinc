/-!
# The half-open cap: the model

A model of the half-open bookkeeping of the `vinc-core` endpoint, as `proofs/tla/HalfOpenOps.tla` has it, over
unbounded `Nat`: the admission of a first flight for an id no session holds (`rx.rs` `unrouted`, `accept`), or for an
id that sessions hold, each of which refused it as a first flight other than its own (`offer`: it gets a session beside
them while the id has fewer than `holders` of them, and frees none), the end of the unauthenticated phase
(`events.rs` `on_established`), the release of a slot (`endpoint.rs` `free_slot`), the deadline a session holds in the
heap (`timers.rs` `settle`), `poll_timeout`, and the timer loop (`timers.rs` `handle_timeout`, `run_timer`).
`Vinc.TraceHalfOpen` replays the recorded calls of the real endpoint through these functions; the theorems are in
`Vinc.CoreHalfOpenThm`.
-/

namespace Vinc.CoreHalfOpen

/-- A session's half-open bookkeeping: when it was made, whether its peer is still unauthenticated, whether it counts
against the cap, and the deadline it holds in the endpoint's heap. -/
structure Sl where
  created : Nat
  unauth : Bool
  counted : Bool
  dl : Option Nat
  deriving BEq, DecidableEq, Repr

/-- The slots of the table (`none` for a free one) and the endpoint's counter of counted sessions. -/
structure E where
  slots : List (Option Sl) := []
  count : Nat := 0
  deriving BEq, DecidableEq, Repr

/-- The constants: the cap, the life of an unauthenticated session, the floors of a full and a short Initial, and the
most sessions that may hold one id (`rx.rs` `MAX_CANDIDATES`). -/
structure P where
  max : Nat
  life : Nat
  full : Nat
  short : Nat
  holders : Nat
  deriving Repr

/-- A table of `k` free slots. -/
def init (k : Nat) : E := { slots := List.replicate k none }

/-! ## The table -/

/-- Slot `j`, `none` when it is free or past the table. -/
def at? : List (Option Sl) → Nat → Option Sl
  | [], _ => none
  | o :: _, 0 => o
  | _ :: t, n + 1 => at? t n

/-- The table with slot `j` replaced (nothing changes past the table). -/
def put : List (Option Sl) → Nat → Option Sl → List (Option Sl)
  | [], _, _ => []
  | _ :: t, 0, x => x :: t
  | o :: t, n + 1, x => o :: put t n x

def cnt : Option Sl → Nat
  | some s => if s.counted then 1 else 0
  | none => 0

/-- How many sessions are counted. -/
def countOf : List (Option Sl) → Nat
  | [] => 0
  | o :: t => cnt o + countOf t

/-! ## Admission (`rx.rs` `unrouted`) -/

/-- A message type that starts a session: 1 a full Initial, 2 a short Initial, 6 a resumption Hello. -/
def isFirst (kind : Nat) : Bool := kind == 1 || kind == 2 || kind == 6

/-- The size floor of a first message type. -/
def floor (p : P) (kind : Nat) : Nat := if kind = 1 then p.full else if kind = 2 then p.short else 0

/-- The datagram meets the floor, and fewer than `max` sessions are counted unless the flight is exempt (`resume`: the
Hello is whole in its first packet, names a registered protocol and an unused ticket of this node that opens for it; or
a retry token that opens for the flight's address and id comes in front of it, `retry.rs`). -/
def admits (p : P) (count kind len : Nat) (resume : Bool) : Bool :=
  decide (floor p kind ≤ len) && (resume || decide (count < p.max))

/-- `offer`: a first flight for an id that `held` sessions hold, each of which refused it as a first flight other than
its own, goes to the admission only while the id has fewer than `holders` holders (none holds an id the endpoint has
not seen); else it is dropped and counted (`holders_refused`). -/
def room (p : P) (held : Nat) : Bool := decide (held < p.holders)

/-! ## The steps -/

/-- `accept`: slot `j` becomes an unauthenticated session made `now`, counted unless it resumes. -/
def make (e : E) (j now : Nat) (resume : Bool) : E :=
  { slots := put e.slots j (some { created := now, unauth := true, counted := !resume, dl := none })
    count := if resume then e.count else e.count + 1 }

/-- A dial of this node (`commands.rs` `connect`): a session that is neither unauthenticated nor counted. -/
def dial (e : E) (j now : Nat) : E :=
  { e with slots := put e.slots j (some { created := now, unauth := false, counted := false, dl := none }) }

/-- `on_established`: the peer is authenticated; a counted session leaves the count. -/
def establish (e : E) (j : Nat) : E :=
  match at? e.slots j with
  | some s => { slots := put e.slots j (some { s with unauth := false, counted := false })
                count := if s.counted then e.count - 1 else e.count }
  | none => e

/-- `free_slot`: the slot is free again; a counted session leaves the count. A free slot is left alone. -/
def release (e : E) (j : Nat) : E :=
  match at? e.slots j with
  | some s => { slots := put e.slots j none, count := if s.counted then e.count - 1 else e.count }
  | none => e

/-- `run_timer`'s test: an unauthenticated session at or past the end of its life. -/
def expired (p : P) (now : Nat) : Option Sl → Bool
  | some s => s.unauth && decide (s.created + p.life ≤ now)
  | none => false

/-- `settle`: the session's deadline is the earliest of its own `d` and, while it is unauthenticated, the end of its
life. -/
def settle (p : P) (e : E) (j d : Nat) : E :=
  match at? e.slots j with
  | some s => { e with slots := put e.slots j (some { s with dl := some (if s.unauth then min d (s.created + p.life)
                                                                          else d) }) }
  | none => e

/-! ## `poll_timeout` -/

def dlOf : Option Sl → Option Nat
  | some s => s.dl
  | none => none

def minOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

/-- The earliest deadline of the heap. -/
def earliest : List (Option Sl) → Option Nat
  | [] => none
  | o :: t => minOpt (dlOf o) (earliest t)

/-- `poll_timeout`: the earliest deadline, none while the event queue is stalled. -/
def poll (l : List (Option Sl)) (stalled : Bool) : Option Nat := if stalled then none else earliest l

/-! ## A first flight -/

/-- What a first flight did. -/
inductive Out where
  | stalled
  | notFirst
  | crowded
  | refused
  | failed
  | made (j : Nat)
  deriving DecidableEq, Repr

/-- `unrouted` and `accept`, through `offer` for an id that `held` sessions hold (each refused the flight as a first
flight other than its own; a holder that takes it is another call): with the event queue stalled nothing starts; a
type that is no first message starts nothing; an id with `holders` holders takes no more; the admission decides; an
admitted first flight takes `take`, the slot the free list gives (`none` when no protocol is registered, no slot is
free, the construction fails or the id table is full), and the session's own deadline after the first flight is `d`.
No session is freed: the new one is made beside the holders. -/
def arrive (p : P) (e : E) (stalled : Bool) (held kind len now : Nat) (resume : Bool) (take : Option Nat) (d : Nat) :
    Out × E :=
  if stalled then (.stalled, e)
  else if !isFirst kind then (.notFirst, e)
  else if !room p held then (.crowded, e)
  else if !admits p e.count kind len resume then (.refused, e)
  else match take with
    | some j => if j < e.slots.length ∧ at? e.slots j = none then (.made j, settle p (make e j now resume) j d)
                else (.failed, e)
    | none => (.failed, e)

/-! ## The timer loop (`handle_timeout`, `run_timer`) -/

/-- The deadline of a slot when it is due at `now`. -/
def dueAt (now : Nat) : Option Sl → Option Nat
  | some s => match s.dl with
    | some t => if t ≤ now then some t else none
    | none => none
  | none => none

/-- The first slot with the least due deadline, the heap's top when it is due. -/
def pop (now : Nat) : List (Option Sl) → Option Nat
  | [] => none
  | o :: t =>
    match dueAt now o, pop now t with
    | none, none => none
    | none, some k => some (k + 1)
    | some _, none => some 0
    | some a, some k => if a ≤ ((dueAt now (at? t k)).getD 0) then some 0 else some (k + 1)

def clearDl (e : E) (j : Nat) : E :=
  match at? e.slots j with
  | some s => { e with slots := put e.slots j (some { s with dl := none }) }
  | none => e

/-- A deadline not after `now` is moved to `now + 1`, so a timer cannot spin. -/
def bump (e : E) (j now : Nat) : E :=
  match at? e.slots j with
  | some s => match s.dl with
    | some t => if t ≤ now then { e with slots := put e.slots j (some { s with dl := some (now + 1) }) } else e
    | none => e
  | none => e

/-- `run_timer` of slot `j` (its deadline taken off the heap first): an expired session is freed; else the
connection's timer runs and `d` is its next deadline, `none` when the connection ended (`settle` frees it). -/
def runTimer (p : P) (now : Nat) (d : Option Nat) (e : E) (j : Nat) : E :=
  let e0 := clearDl e j
  if expired p now (at? e0.slots j) then release e0 j
  else match d with
    | none => release e0 j
    | some d => bump (settle p e0 j d) j now

/-- `handle_timeout`: pop the due deadlines, at most `fuel` times (the table's size, or fewer when the event queue
stalls on the way); `ds j` is what the connection of slot `j` asks for after its timer. -/
def loop (p : P) (now : Nat) (ds : Nat → Option Nat) : Nat → E → E
  | 0, e => e
  | fuel + 1, e =>
    match pop now e.slots with
    | none => e
    | some j => loop p now ds fuel (runTimer p now (ds j) e j)

end Vinc.CoreHalfOpen
