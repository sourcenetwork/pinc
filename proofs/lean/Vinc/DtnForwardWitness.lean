import Vinc.DtnForwardInv

/-!
# A finding: a released bundle can be held again with fresh copies

`Forwarder` keeps no memory of a bundle after `Release`. The concrete run below, executed by the model that the trace
replay validates against the code, holds a bundle of 4 copies, delivers it to its destination, gets the delivery
acknowledged, releases it (the poll returns `Release`), and then accepts a second `Hold` of the same bundle: the
node holds 4 copies again. A late duplicate of the hold message (a retransmission whose first copy was acknowledged
but whose acknowledgement was lost) therefore re-creates copies the budget had already counted, which is why the
network-wide statement is "at most the budget while no hold is replayed after a release"; within one node the
`balance` theorem is exact. The TLC witness is `DtnForward_rehold.cfg` (property `A_NoReHold` is violated).

The fix needs a memory of finished bundles until their expiry (a table, so a capacity and an API change), which is a
design decision left to the owner of the crate.
-/

namespace Vinc.DtnForward

/-- The run: hold 4 copies for destination 2, link 2 up, deliver, acknowledge, release, hold again. -/
def reholdRun : (Option Nat × Act × Act × Err) :=
  let f0 := F.new 3 3 0 1 2 1
  let f1 := (step f0 0 (.hold 1 2 100 4)).1
  let f2 := (step f1 0 (.linkUp 2)).1
  let (f3, a3) := poll f2
  let f4 := (step f3 1 (.acked 2 1)).1
  let (f5, a5) := poll f4
  let (f6, e6) := step f5 2 (.hold 1 2 100 4)
  (copiesHeld f6 1, a3, a5, e6)

theorem rehold_after_release :
    reholdRun = (some 4, .send 2 1 0 false, .release 1, .ok) := by decide

end Vinc.DtnForward
