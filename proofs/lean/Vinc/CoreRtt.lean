/-!
# The node's round trips: the model

A model of `vinc-core` `rtt.rs` (`NodeRtt`), as `proofs/tla/RttOps.tla` has it, over unbounded `Nat` with the `u64`
saturation written out: what the endpoint remembers about round trips. The table of peers (`krtt`, at most `cap`
entries, 256 in the code) is a list in insertion order; a known peer takes the new value in place, a new peer is
appended while there is room and refused when the table is full, nothing is removed. The node keeps an average
(`lrtt`), a peak (`tgr`) and a floor for the handshake (`floor`). `Vinc.TraceRtt` replays the recorded calls of the
real code through these functions; the theorems are in `Vinc.CoreRttThm`.
-/

namespace Vinc.CoreRtt

/-- `u64::MAX`. -/
def maxU : Nat := 18446744073709551615
/-- The round trip from which a node or a session is thin (250 ms). -/
def slowRtt : Nat := 250000000
/-- The shortest first resend of a dial (500 ms). -/
def firstResendMin : Nat := 500000000
/-- The highest the handshake floor rises (8 s). -/
def floorMax : Nat := 8000000000
/-- The shortest first resend of a ticket resume towards a restarted hub (300 ms). -/
def hubResendMin : Nat := 300000000
/-- The 20 ms added to the hub resend. -/
def hubPad : Nat := 20000000

/-- `a.saturating_mul(k)`. -/
def satMul (a k : Nat) : Nat := min (a * k) maxU
/-- `a.saturating_add(b)`. -/
def satAdd (a b : Nat) : Nat := min (a + b) maxU

/-- The node: the table of peer round trips in insertion order, the average, the peak and the handshake floor. -/
structure R where
  tab : List (Nat × Nat) := []
  lrtt : Nat := 0
  tgr : Nat := 0
  floor : Nat := 0
  deriving BEq, Repr

/-- The value stored for a peer. -/
def find? : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | e :: t, p => if e.1 == p then some e.2 else find? t p

def keys (tab : List (Nat × Nat)) : List Nat := tab.map (·.1)

def krtt (r : R) (p : Nat) : Option Nat := find? r.tab p

/-- `Table::insert_room`: a known peer takes the value and keeps its place; a new peer is appended if there is room,
else refused; the answer says whether it was stored. -/
def insertRoom (cap : Nat) (tab : List (Nat × Nat)) (p v : Nat) : Bool × List (Nat × Nat) :=
  if tab.any (fun e => e.1 == p) then (true, tab.map fun e => if e.1 == p then (p, v) else e)
  else if tab.length < cap then (true, tab ++ [(p, v)])
  else (false, tab)

/-- `note_handshake`: zero is ignored; else the peer's entry (room permitting), the floor to zero, the average moves. -/
def handshake (cap p v : Nat) (r : R) : R :=
  if v = 0 then r
  else
    { tab := (insertRoom cap r.tab p v).2
      lrtt := if r.lrtt = 0 then v else satAdd (satMul r.lrtt 7) v / 8
      tgr := r.tgr
      floor := 0 }

/-- `restore_peer`: the table only; the answer says whether it was stored. -/
def restore (cap p v : Nat) (r : R) : Bool × R :=
  let t := insertRoom cap r.tab p v
  (t.1, { r with tab := t.2 })

/-- `note_peak`: `peak.max(tgr - (tgr >> 5))`. -/
def peak (pk : Nat) (r : R) : R := { r with tgr := max pk (r.tgr - r.tgr / 32) }

/-- `note_timeout`: `FLOOR_MAX.min(FIRST_RESEND.max(floor.saturating_mul(2)))`. -/
def timeout (r : R) : R := { r with floor := min floorMax (max firstResendMin (satMul r.floor 2)) }

/-- The round trip a dial to `p` starts from: the peer's if it has a positive one, else the node average. -/
def base (r : R) (p : Nat) : Nat :=
  match krtt r p with
  | some k => if k ≠ 0 then k else r.lrtt
  | none => r.lrtt

/-- `first_resend`: `max(500 ms, 2 x r, hs_floor)`. -/
def firstResend (r : R) (p : Nat) : Nat := max (max firstResendMin (satMul (base r p) 2)) r.floor

/-- `remembered_for`: the peer's round trip, else the node average, raised to half the floor, rounded up; `none` when
that is zero. -/
def remembered (r : R) (p : Nat) : Option Nat :=
  let x := max (base r p) ((r.floor + 1) / 2)
  if x ≠ 0 then some x else none

/-- `hub_resend`: `max(300 ms, 3 * krtt / 2 + 20 ms)`, the product first, written as the code has it
(`krtt + krtt / 2`, saturating, then the 20 ms, saturating), only for a peer with a positive `krtt`. -/
def hub (r : R) (p : Nat) : Option Nat :=
  match krtt r p with
  | some k => if k ≠ 0 then some (max hubResendMin (satAdd (satAdd k (k / 2)) hubPad)) else none
  | none => none

/-- `thin_node`: the larger of the peak and the average is at least 250 ms. -/
def thinNode (r : R) : Bool := decide (slowRtt ≤ max r.tgr r.lrtt)

/-- `thin`: no sample, or the largest of the node peak, the node average, the smallest round trip and half the
smoothed one is at least 250 ms. -/
def thin (r : R) (srtt minRtt : Nat) : Bool :=
  decide (srtt = 0 ∨ slowRtt ≤ max (max (max r.tgr r.lrtt) minRtt) (srtt / 2))

/-- A zero is no value. -/
def opt (v : Nat) : Option Nat := if v = 0 then none else some v

/-- What a connection holds of the node's round trips. -/
structure Cv where
  thin : Bool
  rtt : Option Nat
  peak : Option Nat

/-- `conn_config` for a new connection: the values at the moment of its creation. -/
def connConfig (r : R) : Cv := { thin := thinNode r, rtt := opt r.lrtt, peak := opt r.tgr }

/-- `Connection::set_node_rtt`: a zero value leaves the input as it was. -/
def pushOf (cv : Cv) (r : R) : Cv :=
  { thin := thinNode r
    rtt := if r.lrtt ≠ 0 then some r.lrtt else cv.rtt
    peak := if r.tgr ≠ 0 then some r.tgr else cv.peak }

/-- `Timing::is_thin`: the flag, or the larger of the two node round trips the connection holds is at least 250 ms. -/
def connThin (cv : Cv) : Bool := decide (cv.thin = true ∨ slowRtt ≤ max (cv.rtt.getD 0) (cv.peak.getD 0))

/-- `Timing::first`: the first resend of a connection given the remembered round trip and the node average. -/
def connFirst (rem rtt : Option Nat) : Nat := max firstResendMin (satMul (rem.getD (rtt.getD 0)) 2)

/-- A call of the node. -/
inductive Op where
  | hs (p v : Nat)
  | restore (p v : Nat)
  | peak (v : Nat)
  | timeout
  deriving Repr

/-- One call. -/
def step (cap : Nat) (r : R) : Op → R
  | .hs p v => handshake cap p v r
  | .restore p v => (restore cap p v r).2
  | .peak v => peak v r
  | .timeout => timeout r

/-- A run of calls from an empty node. -/
def run (cap : Nat) : List Op → R → R
  | [], r => r
  | op :: ops, r => run cap ops (step cap r op)

end Vinc.CoreRtt
