/-!
# Held first-flight fragments: the model

A model of `vinc-core` `orphan.rs` (`Orphans`), as `proofs/tla/OrphanOps.tla` has it, over unbounded `Nat`: the
endpoint's table of handshake fragments that arrived ahead of the datagram that starts their message. The table has
a fixed number of entries; a new datagram takes a free entry, else the entry of the oldest arrival; a held datagram
is given out at most once, only while it is not older than `life`, and only for the message it was held for.
`Vinc.TraceOrphan` replays the recorded calls of the real code through these functions; the theorems are in
`Vinc.CoreOrphanThm`.
-/

namespace Vinc.CoreOrphan

/-- The message a datagram is a part of: the destination id, the message length, the address it came from. -/
abbrev Key := Nat × Nat × Nat

/-- A held datagram: when it arrived, its place in the order of arrival, its message, the local address it arrived
on, its length, and `tag`, which stands for its bytes. -/
structure H where
  t : Nat
  ord : Nat
  key : Key
  loc : Nat
  len : Nat
  tag : Nat
  deriving BEq, DecidableEq, Repr

structure O where
  slots : List (Option H) := []
  order : Nat := 0
  held : Nat := 0
  replayed : Nat := 0
  expired : Nat := 0
  evicted : Nat := 0
  deriving BEq, Repr

/-- An empty table of `n` entries. -/
def init (n : Nat) : O := { slots := List.replicate n none }

/-- Not older than `life` at `now`; the subtraction stops at 0 as the code's does. -/
def fresh (life now : Nat) (h : H) : Bool := now - h.t ≤ life

def ordOf : Option H → Nat
  | none => 0
  | some h => h.ord

def waiting (l : List (Option H)) : Nat := (l.filter Option.isSome).length

/-- How many entries hold a datagram older than `life`. -/
def staleCount (life now : Nat) (l : List (Option H)) : Nat :=
  (l.filter fun s => s.any fun h => !fresh life now h).length

/-- Every datagram older than `life` is let go and counted. -/
def expire (life now : Nat) (o : O) : O :=
  { o with
    slots := o.slots.map fun s => s.filter (fresh life now)
    expired := o.expired + staleCount life now o.slots }

/-- The first free entry. -/
def firstFree : List (Option H) → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: t => (firstFree t).map (· + 1)

/-- The first entry with the least order among those `p` picks. -/
def least (p : Option H → Bool) : List (Option H) → Option Nat
  | [] => none
  | s :: t =>
    match least p t with
    | none => if p s then some 0 else none
    | some k => if p s ∧ ordOf s ≤ ordOf (t.getD k none) then some 0 else some (k + 1)

/-- Hold a datagram of `len` bytes that arrived at `now`: refused, before anything else, when longer than `max`;
else the old ones are let go and it takes the first free entry, or the entry of the oldest arrival, which is counted
as evicted. -/
def hold (max life now : Nat) (key : Key) (loc len tag : Nat) (o : O) : Bool × O :=
  if max < len then (false, o)
  else
    let o1 := expire life now o
    let (k, o2) : Nat × O := match firstFree o1.slots with
      | some k => (k, o1)
      | none => ((least (fun _ => true) o1.slots).getD 0, { o1 with evicted := o1.evicted + 1 })
    if k < o2.slots.length then
      (true, { o2 with
        slots := o2.slots.set k (some { t := now, ord := o2.order, key, loc, len, tag })
        order := o2.order + 1
        held := o2.held + 1 })
    else (false, o2)

def isMsg (key : Key) : Option H → Bool
  | none => false
  | some h => h.key == key

/-- Give out the oldest arrival of the message `key` still held, after the old ones are let go. -/
def take (life now : Nat) (key : Key) (o : O) : Option H × O :=
  let o1 := expire life now o
  match least (isMsg key) o1.slots with
  | none => (none, o1)
  | some k =>
    match o1.slots.getD k none with
    | none => (none, o1)
    | some h => (some h, { o1 with slots := o1.slots.set k none, replayed := o1.replayed + 1 })

end Vinc.CoreOrphan
