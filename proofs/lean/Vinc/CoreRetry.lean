/-!
# The retry ring and the retry token: the model

A model of `vinc-core` `retry.rs` over unbounded `Nat`. A first flight that the half-open cap refuses is offered a
retry; the retries wait in a ring of `cap` places (`RETRIES = 32`) until `poll_transmit` sends them, oldest first. The
ring is its head and the waiting retries in order (`q`, from the head on); the code keeps them in an array and takes
both ends modulo `cap`, which `head` tracks. `keyed` is whether the endpoint holds its retry key: it is drawn the first
time the cap refuses a flight, and without it nothing is queued.

`rpush`: with no key, or a full ring, nothing changes and the push reports that nothing was kept (the code counts it
in `retries_dropped`; the dialer resends on its own timer); otherwise the retry is appended. `rpop`: nothing from an
empty ring, else the oldest retry, and the head moves on.

The token is the second it was made and a tag over a message: `msg` lays out the made-at second (4 bytes), the
address family (1 byte), the address as 16 bytes, the port (2 bytes), the length of the dialer's id and the id. `opens`
is the age test: the token opens at second `now` when `now - at`, wrapping at `2^32`, is at most `life`
(`TOKEN_LIFE_S = 10`). The theorems are in `Vinc.CoreRetryThm`.
-/

namespace Vinc.CoreRetry

structure R (α : Type) where
  head : Nat := 0
  q : List α := []
  keyed : Bool := false
  deriving Repr

def rpush {α : Type} (cap : Nat) (r : R α) (x : α) : Bool × R α :=
  if r.keyed && decide (r.q.length < cap) then (true, { r with q := r.q ++ [x] }) else (false, r)

def rpop {α : Type} (cap : Nat) (r : R α) : Option α × R α :=
  match r.q with
  | [] => (none, r)
  | x :: t => (some x, { r with head := (r.head + 1) % cap, q := t })

/-- The bytes the tag is computed over. -/
def msg (at_ : List Nat) (fam : Nat) (ip port id : List Nat) : List Nat :=
  at_ ++ ([fam] ++ (ip ++ (port ++ ([id.length] ++ id))))

/-- `second(now).wrapping_sub(at) <= TOKEN_LIFE_S`, for seconds below `2^32`. -/
def opens (life now at_ : Nat) : Bool := decide ((now + 4294967296 - at_) % 4294967296 ≤ life)

end Vinc.CoreRetry
