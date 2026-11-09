import Vinc.MembershipInvNode

/-!
# Property 9, part 6: every table of the machine stays within its capacity, over every sequence of calls

`Reach n`: `n` is a node `Membership::start` returned, or the result of any public call on a reachable node (the
host calls, in any order and with any arguments: `on_bytes`, `on_frame`, `on_timeout`, `session_up`, `session_down`,
`leave`, `revoke` (when it does not return `TableFull`), `address_changed`, `carrier_return`, `carrier_gone`, and the
draining of the event and trace queues). `reach_inv` shows that a reachable node satisfies `Inv`: the roster, the
attachments, the homed members, the suspicions, the downed set, the revoked set, the live sessions, the view, the
recheck set, the leave set, the gone versions and every hub copy are within `MAX_TABLE` (the hub copies within
`MAX_HUBS`), the per-hub tables only key the bootstrap hubs, and the queues hold at most `QUEUE_CAP` records. So an
insert into a full table refuses instead of growing, in every state the machine can reach.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership

/-- The nodes the machine can reach. -/
inductive Reach : N → Prop where
  | start {e : Env} {me : Nat} {isHub : Bool} {hubs : List Nat} {tracing : Bool} {now wall floor : Nat} {n : N} :
      N.start e me isHub hubs tracing now wall floor = .ok n → Reach n
  | onBytes {n : N} (e : Env) (now peer : Nat) (fs : List NFrame) (bad : Bool) :
      Reach n → Reach (N.onBytes e n now peer fs bad)
  | onFrame {n : N} (e : Env) (now peer : Nat) (f : NFrame) : Reach n → Reach (N.onFrame e n now peer f)
  | onTimeout {n : N} (e : Env) (now : Nat) : Reach n → Reach (N.onTimeout e n now)
  | sessionUp {n : N} (e : Env) (now peer : Nat) (incoming : Bool) : Reach n → Reach (N.sessionUp e n now peer incoming)
  | sessionDown {n : N} (e : Env) (now peer code : Nat) : Reach n → Reach (N.sessionDown e n now peer code)
  | leave {n : N} : Reach n → Reach (N.leave n)
  | revoke {n n' : N} (e : Env) (now member : Nat) : Reach n → N.revoke e n now member = some n' → Reach n'
  | addressChanged {n : N} (now : Nat) : Reach n → Reach (N.addressChanged n now)
  | carrierReturn {n : N} (e : Env) (now member : Nat) : Reach n → Reach (N.carrierReturn e n now member)
  | carrierGone {n : N} (e : Env) (now member : Nat) : Reach n → Reach (N.carrierGone e n now member)
  | drained {n : N} : Reach n → Reach n.drained

theorem inv_drained {B : List Nat} {n : N} (hx : Inv B n) : Inv B n.drained := by
  unfold N.drained
  inv_keep hx
  all_goals simp

/-- Property 9 for the whole machine: a table of a reachable node never exceeds its capacity. -/
theorem reach_inv {n : N} (h : Reach n) : Inv n.boot n := by
  induction h with
  | start hs => obtain ⟨B, hB⟩ := inv_start hs; exact hB.bootEq ▸ hB
  | onBytes e now peer fs bad _ ih => exact (inv_onBytes ih now peer fs bad).bootEq ▸ inv_onBytes ih now peer fs bad
  | onFrame e now peer f _ ih => exact (inv_onFrame ih now peer f).bootEq ▸ inv_onFrame ih now peer f
  | onTimeout e now _ ih => exact (inv_onTimeout ih now).bootEq ▸ inv_onTimeout ih now
  | sessionUp e now peer incoming _ ih => exact (inv_sessionUp ih now peer incoming).bootEq ▸ inv_sessionUp ih now peer incoming
  | sessionDown e now peer code _ ih => exact (inv_sessionDown ih now peer code).bootEq ▸ inv_sessionDown ih now peer code
  | leave _ ih => exact (inv_leave ih).bootEq ▸ inv_leave ih
  | revoke e now member _ hr ih => exact (inv_revoke ih now member _ hr).bootEq ▸ inv_revoke ih now member _ hr
  | addressChanged now _ ih => exact (inv_addressChanged ih now).bootEq ▸ inv_addressChanged ih now
  | carrierReturn e now member _ ih => exact (inv_carrierReturn ih now member).bootEq ▸ inv_carrierReturn ih now member
  | carrierGone e now member _ ih => exact (inv_carrierGone ih now member).bootEq ▸ inv_carrierGone ih now member
  | drained _ ih => exact (inv_drained ih).bootEq ▸ inv_drained ih

/-- Every table of a reachable node is within its capacity (the readable form of `reach_inv`). -/
theorem reach_bounds {n : N} (h : Reach n) :
    n.roster.length ≤ MAX_TABLE ∧ n.attached.length ≤ MAX_TABLE ∧ n.homed.length ≤ MAX_TABLE ∧
    n.susp.length ≤ MAX_TABLE ∧ n.downed.length ≤ MAX_TABLE ∧ n.revoked.length ≤ MAX_TABLE ∧
    n.up.length ≤ MAX_TABLE ∧ n.members.length ≤ MAX_TABLE ∧ n.recheck.length ≤ MAX_TABLE ∧
    n.left.length ≤ MAX_TABLE ∧ n.goneVer.length ≤ MAX_TABLE ∧ n.hv.length ≤ MAX_HUBS ∧
    (∀ p ∈ n.hv, p.2.entries.length ≤ MAX_TABLE) ∧ n.events.length ≤ QUEUE_CAP ∧ n.traces.length ≤ QUEUE_CAP :=
  let i := reach_inv h
  ⟨i.roster.2, i.attached.2, i.homed.2, i.susp.2, i.downed.2, i.revoked.2, i.up.2, i.members.2, i.recheck.2,
    i.left.2, i.goneVer.2, i.hv.2.1, fun p hp => (i.hv.2.2 p hp).2, i.events, i.traces⟩

end Vinc.Membership
