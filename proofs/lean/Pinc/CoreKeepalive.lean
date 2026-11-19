/-!
# The keepalive schedule: the model

A model of `pinc-core` `keepalive.rs` (`Inputs::plan`, `standby_due`), as `proofs/tla/KeepaliveOps.tla` has it, over
unbounded `Nat`: the pure function from what the schedule reads about one session (role, side, path kind, the clock,
the times of the last send, receive and application data, the end of the quiet period after a resume, whether
packets are in flight) to the next ping and the next moment to compute the plan again. Times are `u64`
nanoseconds; an addition of the code saturates at `u64::MAX` (`satAdd`). `Pinc.TraceKeepalive` replays the recorded
calls of the real code through these functions; the theorems are in `Pinc.CoreKeepaliveThm`.
-/

namespace Pinc.CoreKeepalive

def sec : Nat := 1000000000
def u64Max : Nat := 2 ^ 64 - 1

def pathKeep : Nat := 5 * sec
def activeKeep : Nat := 20 * sec
def idleKeepPlain : Nat := 40 * sec
def quietKeepDialer : Nat := 60 * sec
def quietKeepAcceptor : Nat := 70 * sec
def idleDrop : Nat := 90 * sec
def directSilence : Nat := 14 * sec
def holdWindow : Nat := 120 * sec
def resumeQuiet : Nat := 10 * sec
/-- The fixed idle timeout of a connection (`pinc-transport` `conn/config.rs`, `IDLE_TIMEOUT`). -/
def idleTimeout : Nat := 75 * sec

/-- `a.saturating_add(b)` on a `u64`. -/
def satAdd (a b : Nat) : Nat := min (a + b) u64Max

inductive Role where
  | hub | member | other
  deriving BEq, DecidableEq, Repr

def Role.quiet : Role → Bool
  | .other => false
  | _ => true

structure Inputs where
  role : Role
  dialer : Bool
  direct : Bool
  now : Nat
  lastTx : Nat
  lastRx : Nat
  lastApp : Nat
  quietUntil : Nat
  inFlight : Bool
  deriving Repr

structure Plan where
  ping : Option Nat
  review : Option Nat
  deriving BEq, Repr

/-- The idle ping interval of the active path. -/
def idleKeep (x : Inputs) : Nat :=
  if x.role.quiet then (if x.dialer then quietKeepDialer else quietKeepAcceptor) else idleKeepPlain

/-- `Some(p.map_or(t, |c| c.min(t)))`. -/
def earliest (p : Option Nat) (t : Nat) : Option Nat :=
  some (match p with | none => t | some c => min c t)

/-- The next ping of a standby path: 5 s after its last send, while data moved in the last 20 s. -/
def standbyDue (now pathLastTx lastApp : Nat) : Option Nat :=
  if max (satAdd pathLastTx pathKeep) now < satAdd lastApp activeKeep then some (max (satAdd pathLastTx pathKeep) now)
  else none

/-- A moment the answer can change by itself: it counts only after `now`. -/
def change (now : Nat) (r : Option Nat) (t : Nat) : Option Nat := if now < t then earliest r t else r

/-- `t.max(now)`: a moment already past is taken as now. -/
def after (x : Inputs) (t : Nat) : Nat := max t x.now

/-- The idle ping of the active path is due. -/
def idleDue (x : Inputs) : Nat := after x (satAdd x.lastTx (idleKeep x))

/-- Whether the quiet dialing side watches a silent direct path. -/
def watchDirect (x : Inputs) : Bool := x.role.quiet && x.dialer && x.direct

/-- The silent direct path of that session is due. -/
def directDue (x : Inputs) : Nat := after x (satAdd (max x.lastRx x.lastTx) directSilence)

/-- Right after a resume nothing is pinged unless packets are in flight. -/
def held (x : Inputs) : Bool := decide (x.now < x.quietUntil) && !x.inFlight

/-- The ping after each step of the code: per validated path, the active path after the idle interval, the silent
direct path, the quiet period after a resume. -/
def p1 (x : Inputs) : Option Nat := standbyDue x.now x.lastTx x.lastApp
-- (the code writes `earliest(None, due)`, which is `Some(due)`)

def p2 (x : Inputs) : Option Nat :=
  if x.role.quiet || decide (idleDue x < satAdd x.lastApp idleDrop) then earliest (p1 x) (idleDue x) else p1 x

def p3 (x : Inputs) : Option Nat :=
  if watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow) then earliest (p2 x) (directDue x) else p2 x

def p4 (x : Inputs) : Option Nat := if held x then (p3 x).map (max x.quietUntil) else p3 x

/-- The review moment after each step. -/
def r1 (x : Inputs) : Option Nat := change x.now none (satAdd x.lastApp activeKeep)

def r2 (x : Inputs) : Option Nat :=
  if !x.role.quiet then change x.now (r1 x) (satAdd x.lastApp idleDrop) else r1 x

def r3 (x : Inputs) : Option Nat :=
  if watchDirect x then change x.now (r2 x) (satAdd x.lastApp holdWindow) else r2 x

def r4 (x : Inputs) : Option Nat := if held x then change x.now (r3 x) x.quietUntil else r3 x

/-- The plan, step for step as the code computes it. -/
def plan (x : Inputs) : Plan := { ping := p4 x, review := r4 x }

end Pinc.CoreKeepalive
