/-!
# The node's table of failed dials: the model

A model of `pinc-node` `io.rs` (`backoff`, `deny_back`, `set_failed`), `duties.rs` (`dial_peer`, `prune`) and
`events.rs` (`hub_closed`, `hub_connect_failed`, and `hub_connected`, whose session the full session table shed: that
is `backoff`), as `proofs/tla/NodeBackoffOps.tla` has it, over unbounded `Nat`.
A time and a wait are `u64` nanoseconds; the code saturates where it adds and doubles (`satAdd`, `satMul2`), and so
does the model: `MAXU` is `u64::MAX`.

The table of failed dials `Tab` is a list of `(peer, until, back)`: when the next dial of the peer may start and the
wait that was used (the `failed` map of `Io`, a `BTreeMap`, so one entry per peer). The dials in progress are a list
of peers. `Pinc.TraceNodeBackoff` replays the recorded calls of the real code through these functions; the theorems
are in `Pinc.CoreNodeBackoffThm`.
-/

namespace Pinc.NodeBackoff

/-- `u64::MAX`. -/
def MAXU : Nat := 2 ^ 64 - 1

/-- `a.saturating_add(b)`. -/
def satAdd (a b : Nat) : Nat := min (a + b) MAXU

/-- `b.saturating_mul(2)`. -/
def satMul2 (b : Nat) : Nat := min (2 * b) MAXU

/-- `BACKOFF_FIRST`. -/
def first : Nat := 2_000_000_000
/-- `BACKOFF_HUB_CAP`. -/
def hubCap : Nat := 16_000_000_000
/-- `BACKOFF_CAP`. -/
def cap : Nat := 60_000_000_000
/-- `SESSION_LIVED`. -/
def lived : Nat := 5_000_000_000
/-- `DENY_FIRST`. -/
def denyFirst : Nat := 60_000_000_000
/-- `DENY_CAP`. -/
def denyCap : Nat := 900_000_000_000
/-- `FAILED_KEEP`. -/
def keep : Nat := 3_600_000_000_000

/-- The table of failed dials: peer, the time its next dial may start, the wait that was used. -/
abbrev Tab := List (Nat × Nat × Nat)

/-- The entry of a peer. -/
def get : Tab → Nat → Option (Nat × Nat)
  | [], _ => none
  | (q, u, b) :: r, p => if q == p then some (u, b) else get r p

/-- Insert or overwrite the entry of a peer (`BTreeMap::insert`). -/
def put : Tab → Nat → Nat → Nat → Tab
  | [], p, u, b => [(p, u, b)]
  | (q, u', b') :: r, p, u, b => if q == p then (p, u, b) :: r else (q, u', b') :: put r p u b

/-- Forget the entry of a peer (`BTreeMap::remove`). -/
def del (f : Tab) (p : Nat) : Tab := f.filter fun e => e.1 != p

/-- `set_failed`: a full table refuses a peer it has no entry for and changes nothing. -/
def setFailed (max : Nat) (f : Tab) (now p back : Nat) : Tab :=
  if f.length < max || (get f p).isSome then put f p (satAdd now back) back else f

/-- The cap of a wait: a hub's or any other node's. -/
def capOf (hub : Bool) : Nat := if hub then hubCap else cap

/-- `backoff`'s wait: the first, then twice the wait of the entry up to the cap. -/
def backWait (hub : Bool) (f : Tab) (p : Nat) : Nat :=
  match get f p with
  | none => first
  | some (_, b) => min (satMul2 b) (capOf hub)

/-- `backoff`: the wait, and the table. -/
def backoff (max : Nat) (hub : Bool) (f : Tab) (now p : Nat) : Nat × Tab :=
  (backWait hub f p, setFailed max f now p (backWait hub f p))

/-- `deny_back`'s wait: a wait of at least `DENY_FIRST` doubles up to `DENY_CAP`, else `DENY_FIRST`. -/
def denyWait (f : Tab) (p : Nat) : Nat :=
  match get f p with
  | some (_, b) => if denyFirst ≤ b then min (satMul2 b) denyCap else denyFirst
  | none => denyFirst

/-- `deny_back`: the wait, and the table. -/
def denyBack (max : Nat) (f : Tab) (now p : Nat) : Nat × Tab :=
  (denyWait f p, setFailed max f now p (denyWait f p))

/-- The backoff window: `now < until`. -/
def window (f : Tab) (now p : Nat) : Bool :=
  match get f p with
  | some (u, _) => decide (now < u)
  | none => false

/-- `dial_peer`'s guard: not leaving, no session, no dial in progress, not revoked, outside the window. -/
def gate (f : Tab) (now p : Nat) (conn c rev : List Nat) (lv : Bool) : Bool :=
  !lv && !conn.contains p && !c.contains p && !rev.contains p && !window f now p

/-- The dial reached the transport: the peer joins the dials in progress if there is room. -/
def connecting (max : Nat) (c : List Nat) (p : Nat) : List Nat :=
  if c.length < max then (if c.contains p then c else c ++ [p]) else c

/-- `hub_closed` for the session of `p` that opened at `opened`: a refusal is `deny_back`, a session that lived less
than `SESSION_LIVED` is a failure, a longer one forgets the entry. -/
def closed (max : Nat) (hub : Bool) (f : Tab) (now p opened : Nat) (den : Bool) : Option Nat × Tab :=
  if den then
    let x := denyBack max f now p
    (some x.1, x.2)
  else if now - opened < lived then
    let x := backoff max hub f now p
    (some x.1, x.2)
  else (none, del f p)

/-- `prune`: an entry is kept while `until + KEEP` (saturating) is after `now`. -/
def prune (f : Tab) (now : Nat) : Tab := f.filter fun e => decide (now < satAdd e.2.1 keep)

end Pinc.NodeBackoff
