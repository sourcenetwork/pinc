import Vinc.MembershipCompleteTick
import Vinc.MembershipCompleteSlow

/-!
# Completeness and accuracy over timed hypotheses, part 8: one call of `on_timeout` and the lease of a silent member

`on_timeout` is cut at the seams of the code (`N.otPre`: the pulse refresh, the local refresh, the renewal, the
confirmation deadline; `N.otTick`: the tick; `N.tkPre`: everything in the tick but `hub_tick`) and proved equal to the
model by `rfl` (`onTimeout_split`, `tick_split`). Then, under `Silent t0 e m` (the host shows no evidence of `m` after
`t0`, `m`'s carrier is not open):

* `onTimeout_held`: a call never makes the lease of `m` younger than `t0`;
* `onTimeout_none`: a lease that is gone stays gone;
* `onTimeout_expires` (property 2, hub side): a call that runs the tick of a hub after `t0 + LEASE` leaves no lease for `m`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-- The first step of `tick`: the recheck of the removals a quiet window deferred. -/
def N.tkRecheck (e : Env) (n : N) (now : Nat) : N :=
  if !n.recheck.isEmpty && n.quietUntil ≤ now then
    (if n.regrace then N.recheckNow e { n with regrace := false } now
     else { n with regrace := true, quietUntil := satAdd now RECHECK_GAP })
  else n

/-- Everything in `tick` but `hub_tick`. -/
def N.tkPre (e : Env) (n : N) (now : Nat) : N :=
  let n := N.tkRecheck e n now
  let n := if n.sent != some (n.ver, n.th) then N.renew e n now false false else n
  if n.isHub || n.nextSlow ≤ now then
    N.slowTick e (if !n.isHub then { n with nextSlow := satAdd now SLOW_TICK } else n) now
  else n

theorem tick_split (e : Env) (n : N) (now : Nat) :
    N.tick e n now = (let n := N.tkPre e n now; if n.isHub then N.hubTick e n now else n) := rfl

/-- The part of `on_timeout` before the tick. -/
def N.otPre (e : Env) (n : N) (now : Nat) : N :=
  let n := N.pulseRefresh e n now
  let n := N.refreshLocal e n now
  let n := if n.nextRenew ≤ now then N.renew e n now false true else n
  if (match n.nextConf with | some c => decide (c ≤ now) | none => false) then
    let n := { n with nextConf := none }
    if n.isHub then forKeys n.susp.keys (fun m n => N.carrierWatch e n now m) n else n
  else n

/-- The node the tick branch of `on_timeout` hands to `tick`. -/
def N.otTickPre (e : Env) (n : N) (now : Nat) : N :=
  let n := match n.nextTick with
    | some t => if !n.isHub && WAKE_GAP < now - t then N.renew e (n.beginQuiet now 0) now true false else n
    | none => n
  { n with nextTick := some (satAdd now (if n.isHub then HUB_TICK else NODE_TICK)) }

/-- The tick branch of `on_timeout`. -/
def N.otTick (e : Env) (n : N) (now : Nat) : N := N.tick e (N.otTickPre e n now) now

theorem onTimeout_split (e : Env) (n : N) (now : Nat) :
    N.onTimeout e n now =
      (if n.leaving then n
       else let n := N.otPre e n now; if (n.nextTick.getD 0) ≤ now then N.otTick e n now else n) := rfl

theorem tkPre_roster (e : Env) (n : N) (now : Nat) : (N.tkPre e n now).roster = n.roster := by
  unfold N.tkPre N.tkRecheck
  simp only [ite_roster, recheckNow_roster, renew_roster, slowTick_roster, ite_self]

theorem carrierWatch_none (e : Env) (n : N) (now m : Nat) (h : n.roster.get? m = none) :
    (N.carrierWatch e n now m).roster.get? m = none := by
  rcases cw_shape e n now m with h1 | h1 | h1
  · rw [h1]; exact h
  · rw [h1]; exact AMap.get?_erase_self _ _
  · rw [h1, modify_get_self, h]; rfl

/-! ## The confirmation deadline loop -/

theorem otPre_loop_held (t0 m : Nat) (e : Env) (now : Nat) (hs : Silent t0 e m) (n : N) (hh : Held t0 m n) :
    Held t0 m (forKeys n.susp.keys (fun m n => N.carrierWatch e n now m) n) :=
  forKeys_held t0 m _ _ (fun k n hn => by
    by_cases hk : m = k
    · subst hk; exact carrierWatch_held t0 e n now m hs hn
    · exact Held.of_other hk (carrierWatch_other e n now k) hn) n hh

theorem otPre_loop_none (m : Nat) (e : Env) (now : Nat) (n : N) (hh : n.roster.get? m = none) :
    (forKeys n.susp.keys (fun m n => N.carrierWatch e n now m) n).roster.get? m = none :=
  forKeys_none m _ _ (fun k n hn => by
    by_cases hk : m = k
    · subst hk; exact carrierWatch_none e n now m hn
    · rw [carrierWatch_other e n now k m hk]; exact hn) n hh

theorem otPre_held (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.otPre e n now) := by
  unfold N.otPre
  dsimp only
  have h1 : Held t0 m (N.pulseRefresh e n now) := Held.of_eq (pulseRefresh_roster e n now) hh
  have h2 : Held t0 m (N.refreshLocal e (N.pulseRefresh e n now) now) := Held.of_eq (refreshLocal_roster ..) h1
  generalize N.refreshLocal e (N.pulseRefresh e n now) now = n2 at h2 ⊢
  have h3 : Held t0 m (if n2.nextRenew ≤ now then N.renew e n2 now false true else n2) := by
    split
    · exact Held.of_eq (renew_roster ..) h2
    · exact h2
  generalize (if n2.nextRenew ≤ now then N.renew e n2 now false true else n2) = n3 at h3 ⊢
  repeat' split
  all_goals first | exact otPre_loop_held t0 m e now hs _ (Held.of_eq rfl h3) | exact Held.of_eq rfl h3

theorem otPre_none (m : Nat) (e : Env) (n : N) (now : Nat) (hh : n.roster.get? m = none) :
    (N.otPre e n now).roster.get? m = none := by
  unfold N.otPre
  dsimp only
  have h1 : (N.pulseRefresh e n now).roster.get? m = none := by rw [pulseRefresh_roster]; exact hh
  have h2 : (N.refreshLocal e (N.pulseRefresh e n now) now).roster.get? m = none := by rw [refreshLocal_roster]; exact h1
  generalize N.refreshLocal e (N.pulseRefresh e n now) now = n2 at h2 ⊢
  have h3 : (if n2.nextRenew ≤ now then N.renew e n2 now false true else n2).roster.get? m = none := by
    split
    · rw [renew_roster]; exact h2
    · exact h2
  generalize (if n2.nextRenew ≤ now then N.renew e n2 now false true else n2) = n3 at h3 ⊢
  repeat' split
  all_goals first | exact otPre_loop_none m e now _ h3 | exact h3

/-! ## The tick -/

theorem tick_held (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.tick e n now) := by
  rw [tick_split]
  dsimp only
  have h := Held.of_eq (tkPre_roster e n now) hh
  split
  · exact hubTick_held t0 e _ now m hs h
  · exact h

theorem otTickPre_roster (e : Env) (n : N) (now : Nat) : (N.otTickPre e n now).roster = n.roster := by
  unfold N.otTickPre
  dsimp only
  split
  · split
    · simp only [renew_roster, beginQuiet_roster]
    · rfl
  · rfl

theorem otTick_held (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.otTick e n now) := by
  unfold N.otTick
  exact tick_held t0 m e _ now hs (Held.of_eq (otTickPre_roster e n now) hh)

theorem onTimeout_held (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.onTimeout e n now) := by
  rw [onTimeout_split]
  split
  · exact hh
  · dsimp only
    have h := otPre_held t0 m e n now hs hh
    split
    · exact otTick_held t0 m e _ now hs h
    · exact h

/-- **Property 2, hub side.** A call of `on_timeout` that runs the tick of a hub at an instant later than `t0 + LEASE`
leaves no lease for a member the host shows no evidence of after `t0`, whose lease was last renewed at `t0` or earlier.
The hypotheses `hl`, `htick` and `hhub` are the tests of the code: the node is not leaving, the tick is due, and the node
that reaches `hub_tick` is a hub. -/
theorem onTimeout_expires (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hh : Held t0 m n)
    (hd : t0 + LEASE < now) (hl : n.leaving = false) (htick : ((N.otPre e n now).nextTick.getD 0) ≤ now)
    (hhub : (N.tkPre e (N.otTickPre e (N.otPre e n now) now) now).isHub = true) :
    (N.onTimeout e n now).roster.get? m = none := by
  rw [onTimeout_split, if_neg (by simp [hl])]
  dsimp only
  rw [if_pos htick]
  unfold N.otTick
  rw [tick_split]
  dsimp only
  rw [if_pos hhub]
  have h := Held.of_eq (otTickPre_roster e (N.otPre e n now) now) (otPre_held t0 m e n now hs hh)
  exact hubTick_expires_c t0 e _ now m hs (Held.of_eq (tkPre_roster ..) h) hd


theorem tick_none (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hn : n.roster.get? m = none) :
    (N.tick e n now).roster.get? m = none := by
  rw [tick_split]
  dsimp only
  have h : (N.tkPre e n now).roster.get? m = none := by rw [tkPre_roster]; exact hn
  split
  · exact hubTick_none t0 e _ now m hs h
  · exact h

/-- A lease that is gone stays gone through a call of `on_timeout`. -/
theorem onTimeout_none (t0 m : Nat) (e : Env) (n : N) (now : Nat) (hs : Silent t0 e m) (hn : n.roster.get? m = none) :
    (N.onTimeout e n now).roster.get? m = none := by
  rw [onTimeout_split]
  split
  · exact hn
  · dsimp only
    have h := otPre_none m e n now hn
    split
    · unfold N.otTick
      exact tick_none t0 m e _ now hs (by rw [otTickPre_roster]; exact h)
    · exact h

end Vinc.Membership.Cmp
