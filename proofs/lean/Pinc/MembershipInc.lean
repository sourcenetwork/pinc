/-!
# Membership: the incarnation and the address tag

`crates/pinc-membership/src/incarnation.rs` as the code writes it: the incarnation word (a 48-bit epoch above a 16-bit
record sequence), `Incarnation::start`, `next_record` and `observe` over a host `Local` (the persistent counter and its
failures), and the `AddressTag` with its move counter and the settle time.

A function returns `Except Err` of the new value and the new host store; an error returns no state, which is how the
code behaves (`next_record` and `observe` assign `*self` only after the new epoch is sealed, and `sealEpoch` writes the store
only after the exhaustion check passes).

Model conventions: a `u64` is a `Nat` below `2^64`; `saturating_add` is `satAdd`; the epoch is checked against
`EPOCH_MAX` by `seal` before any value that carries it exists, so every epoch of a constructed `Inc` is at most
`EPOCH_MAX` and the shift `epoch << 16` of the code loses no bit (`word`).

The theorems are in `MembershipIncThm.lean`.
-/

namespace Pinc.MemInc

/-- The largest epoch: 48 bits. -/
def EPOCH_MAX : Nat := 2 ^ 48 - 1

/-- `u64::MAX`. -/
def U64MAX : Nat := 2 ^ 64 - 1

/-- `a.saturating_add(b)` on a `u64`. -/
def satAdd (a b : Nat) : Nat := min (a + b) U64MAX

/-- The host's incarnation store (`Local`): whether the counter is persistent, what it holds, and whether reading or
writing it fails. -/
structure Local where
  persistent : Bool
  sealed : Option Nat
  readFails : Bool
  sealFails : Bool
  deriving DecidableEq, Repr

/-- Why an incarnation could not be issued. -/
inductive Err where
  | store
  | exhausted
  deriving DecidableEq, Repr

/-- The incarnation: an epoch and a record sequence. -/
structure Inc where
  epoch : Nat
  seq : Nat
  deriving DecidableEq, Repr

/-- The incarnation word `(epoch << 16) | seq`. -/
def Inc.word (i : Inc) : Nat := i.epoch * 65536 + i.seq

/-- `Incarnation::seal`: the exhaustion check, then the store write when the counter is persistent. -/
def sealEpoch (l : Local) (epoch : Nat) : Except Err Local :=
  if EPOCH_MAX < epoch then .error .exhausted
  else if l.persistent then
    (if l.sealFails then .error .store else .ok { l with sealed := some epoch })
  else .ok l

/-- `Incarnation::start`: `wall_ms` is the wall clock in milliseconds, `floor` an epoch the host remembers by other
means. -/
def start (l : Local) (wallMs floor : Nat) : Except Err (Inc × Local) := do
  let remembered ← if l.persistent then (if l.readFails then throw .store else pure (l.sealed.getD 0)) else pure 0
  let base := max remembered floor
  let epoch := if l.persistent then satAdd base 1 else max (satAdd wallMs 1) (satAdd base 1)
  let l' ← sealEpoch l epoch
  pure (⟨epoch, 0⟩, l')

/-- `Incarnation::next_record`: the next record of this life; a full sequence starts the next epoch. Returns the word,
the new value and the new store. -/
def nextRecord (l : Local) (i : Inc) : Except Err (Nat × Inc × Local) :=
  if i.seq + 1 ≤ 65535 then
    let i' : Inc := { i with seq := i.seq + 1 }
    .ok (i'.word, i', l)
  else do
    let epoch := satAdd i.epoch 1
    let l' ← sealEpoch l epoch
    let i' : Inc := ⟨epoch, 0⟩
    pure (i'.word, i', l')

/-- `Incarnation::observe`: a peer reported the word `seen` for this node. Returns whether the word changed, the new
value and the new store. -/
def observe (l : Local) (i : Inc) (seen : Nat) : Except Err (Bool × Inc × Local) :=
  if seen ≤ i.word then .ok (false, i, l)
  else do
    let epoch := satAdd (max (seen / 65536) i.epoch) 1
    let l' ← sealEpoch l epoch
    pure (true, ⟨epoch, 0⟩, l')

/-! ## The address tag -/

/-- `MOVE_SETTLE`, in nanoseconds. -/
def MOVE_SETTLE : Nat := 3000000000

/-- `AddressTag`: the move counter (a `u8`), when the last move happened, and the tag in use (8 bytes). -/
structure Tag where
  moves : Nat
  movedAt : Option Nat
  current : Option (List Nat)
  deriving DecidableEq, Repr

/-- `AddressTag::default`. -/
def Tag.init : Tag := { moves := 0, movedAt := none, current := none }

/-- `AddressTag::moved`: several changes at one instant count once; the counter wraps at 256. -/
def Tag.moved (t : Tag) (now : Nat) : Tag :=
  { t with moves := if t.movedAt = some now then t.moves else (t.moves + 1) % 256, movedAt := some now }

/-- Whether the previous tag is still kept: a move less than `MOVE_SETTLE` ago while the reflexive address is unknown. -/
def Tag.settling (t : Tag) (now : Nat) (reflexiveKnown : Bool) : Bool :=
  match t.movedAt with
  | some m => decide (now - m < MOVE_SETTLE) && !reflexiveKnown
  | none => false

/-- `AddressTag::tag`: `hash` is the host's `address_hash`. Returns the tag and the new state. -/
def Tag.tag (t : Tag) (now : Nat) (reflexiveKnown : Bool) (hash : Nat → List Nat) : List Nat × Tag :=
  match t.current with
  | some prev => if t.settling now reflexiveKnown then (prev, t) else (hash t.moves, { t with current := some (hash t.moves) })
  | none => (hash t.moves, { t with current := some (hash t.moves) })

end Pinc.MemInc
