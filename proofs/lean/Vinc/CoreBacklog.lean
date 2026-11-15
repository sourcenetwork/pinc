/-!
# The accept room: the model

A model of how the `vinc-core` endpoint and the `vinc` facade keep a place in the accept queue for every session a
first flight makes (vinc#436), as `proofs/tla/HalfOpen.tla` has it with `QCAP > 0`, over unbounded `Nat`: the flag each
slot carries while its server session is owed to the host (`slot.rs` `Meta::owed`) and the endpoint's counter of them
(`endpoint.rs` `Endpoint::owed`); the admission of a first flight only while the owed sessions leave room
(`rx.rs` `unrouted`, `accept`), the room being the free places of the host's fullest accept queue
(`engine.rs` `sync_backlog`); the end of a session (`endpoint.rs` `free_slot`); the host reading the `Incoming` of a
session that was owed (`rx.rs` `session_taken`, `Taken::Reserved`, then `engine.rs` `session_up`), of a sub-session
that was not (`Taken::Unreserved`), and the application taking a session from the queue (`ops.rs` `accept_route`).
The theorems are in `Vinc.CoreBacklogThm`.
-/

namespace Vinc.CoreBacklog

/-- The owed flag of every slot, the endpoint's counter, and the length of the host's fullest accept queue. -/
structure B where
  owed : List Bool
  n : Nat
  q : Nat
  deriving BEq, DecidableEq, Repr

/-- A table of `k` slots, none owed, and an empty queue. -/
def init (k : Nat) : B := ⟨List.replicate k false, 0, 0⟩

/-- The flag of slot `j`, `false` past the table. -/
def get : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: t, n + 1 => get t n

/-- The flags with slot `j` set to `x` (nothing changes past the table). -/
def put : List Bool → Nat → Bool → List Bool
  | [], _, _ => []
  | _ :: t, 0, x => x :: t
  | b :: t, n + 1, x => b :: put t n x

/-- How many slots are owed. -/
def countOf : List Bool → Nat
  | [] => 0
  | b :: t => (if b then 1 else 0) + countOf t

/-- The room the host gives the endpoint: the free places of its fullest queue (`sync_backlog`). -/
def room (cap : Nat) (b : B) : Nat := cap - b.q

/-- A first flight that would make a session in slot `j`: it does only while fewer sessions are owed than the room
(`unrouted`), in a slot of the table that owes nothing (a free slot: `Meta::begin` clears the flag). -/
def make (cap : Nat) (b : B) (j : Nat) : B :=
  if b.n < room cap b ∧ j < b.owed.length ∧ get b.owed j = false then
    { b with owed := put b.owed j true, n := b.n + 1 }
  else b

/-- The session of slot `j` ends: it is owed no more (`free_slot`). -/
def release (b : B) (j : Nat) : B :=
  if get b.owed j = true then { b with owed := put b.owed j false, n := b.n - 1 } else b

/-- The host reads the `Incoming` of the owed session of slot `j` and queues it; the flag says it found the queue full
and closed it as busy. -/
def take (cap : Nat) (b : B) (j : Nat) : B × Bool :=
  if get b.owed j = true then
    ({ owed := put b.owed j false, n := b.n - 1, q := if b.q < cap then b.q + 1 else b.q }, decide (cap ≤ b.q))
  else (b, false)

/-- The host reads the `Incoming` of a sub-session, which no first flight made: it waits only in a place no owed
session holds, and is closed as busy otherwise. -/
def sub (cap : Nat) (b : B) : B := if b.q + b.n < cap then { b with q := b.q + 1 } else b

/-- The application takes the oldest waiting session. -/
def pop (b : B) : B := { b with q := b.q - 1 }

end Vinc.CoreBacklog
