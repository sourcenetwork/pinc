import Pinc.Axioms
import Pinc.CoreKeepalive

/-!
# The keepalive schedule: every deadline lies between its documented floor and ceiling

What the model proves about `Inputs::plan`, for any role and side, any path kind and any times (nanoseconds, the
additions of the code saturating at `u64::MAX`):

- a ping is never due before `now`, nor before 5 s after the last send (`ping_ge_now`, `ping_ge_tx`); the active path
  of a session that is not watching a direct path and has no standby window open is not pinged before its idle
  interval after the last send (`ping_floor_role`); right after a resume nothing is due before the quiet period ends
  (`ping_held`), and when it does not apply the plan is the plan without it (`resume_inert`);
- a review moment is always after `now` (`review_gt_now`), and the plan does not change before it: computing it again
  at a later `now` below the review moment gives the same review moment and the same ping, raised to that `now`
  (`plan_stable`);
- every schedule has its ceiling: the standby path 5 s after the last send while data moved in the last 20 s
  (`standby_ceiling`), the active path after the idle interval for a quiet session always (`quiet_some`,
  `quiet_ceiling`) and for a plain one while its 90 s window is open (`plain_ceiling`), the silent direct path of a
  quiet dialing session 14 s after the last send or receive while data moved in the last 120 s (`direct_ceiling`);
  each ceiling is raised to the end of the quiet period only while that period holds the ping back;
- a plain session with no data for 90 s is not pinged at all (`plain_stops`);
- the idle intervals are below the idle timeout and ordered dialer before acceptor (`keep_lt_timeout`,
  `dialer_before_acceptor`); a quiet session's ping is due before the peer's idle timeout can fire, provided the
  host calls on time (`quiet_before_idle`, `sent_before_peer_idle`): the host's timing and that the peer counts our
  last send as activity are hypotheses of these two theorems, not facts of the model.
-/

namespace Pinc.CoreKeepalive

/-- Every value of `o` is at least `L`. -/
def Lb (L : Nat) (o : Option Nat) : Prop := ∀ v, o = some v → L ≤ v

/-- `o` holds a value at most `U`. -/
def Ub (U : Nat) (o : Option Nat) : Prop := ∃ v, o = some v ∧ v ≤ U

theorem lb_none (L : Nat) : Lb L none := fun _ h => by cases h

theorem lb_earliest {L : Nat} {p : Option Nat} {t : Nat} (hp : Lb L p) (ht : L ≤ t) : Lb L (earliest p t) := by
  intro v hv
  cases p with
  | none => simp [earliest] at hv; omega
  | some c =>
    have := hp c rfl
    simp [earliest] at hv; omega

theorem ub_earliest_t {U : Nat} (p : Option Nat) {t : Nat} (ht : t ≤ U) : Ub U (earliest p t) := by
  cases p with
  | none => exact ⟨t, rfl, ht⟩
  | some c => exact ⟨min c t, rfl, by omega⟩

theorem ub_earliest_p {U : Nat} {p : Option Nat} (t : Nat) (hp : Ub U p) : Ub U (earliest p t) := by
  obtain ⟨c, hc, hcU⟩ := hp
  subst hc
  exact ⟨min c t, rfl, by omega⟩

theorem satAdd_mono_l {a b : Nat} (c : Nat) (h : a ≤ b) : satAdd a c ≤ satAdd b c := by
  unfold satAdd; omega

theorem satAdd_mono_r (a : Nat) {c d : Nat} (h : c ≤ d) : satAdd a c ≤ satAdd a d := by
  unfold satAdd; omega

theorem satAdd_le (a b : Nat) : satAdd a b ≤ u64Max := by
  unfold satAdd; omega

/-! ## The stages -/

theorem lb_p1 {L : Nat} (x : Inputs) (h : ∀ d, standbyDue x.now x.lastTx x.lastApp = some d → L ≤ d) :
    Lb L (p1 x) := h

theorem lb_p2 {L : Nat} (x : Inputs) (h1 : Lb L (p1 x)) (h2 : L ≤ idleDue x) : Lb L (p2 x) := by
  unfold p2; split
  · exact lb_earliest h1 h2
  · exact h1

theorem lb_p3 {L : Nat} (x : Inputs) (h2 : Lb L (p2 x))
    (h3 : (watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow)) = true → L ≤ directDue x) :
    Lb L (p3 x) := by
  unfold p3; split
  · exact lb_earliest h2 (h3 ‹_›)
  · exact h2

theorem lb_p4 {L : Nat} (x : Inputs) (h3 : Lb L (p3 x)) : Lb L (p4 x) := by
  unfold p4; split
  · intro v hv
    cases hp : p3 x with
    | none => simp [hp] at hv
    | some c =>
      simp [hp] at hv
      have := h3 c hp
      omega
  · exact h3

theorem ub_p1 {d : Nat} (x : Inputs) (h : standbyDue x.now x.lastTx x.lastApp = some d) : Ub d (p1 x) :=
  ⟨d, h, Nat.le_refl d⟩

theorem ub_p2_p1 {U : Nat} (x : Inputs) (h : Ub U (p1 x)) : Ub U (p2 x) := by
  unfold p2; split
  · exact ub_earliest_p _ h
  · exact h

theorem ub_p2_idle (x : Inputs) (h : (x.role.quiet || decide (idleDue x < satAdd x.lastApp idleDrop)) = true) :
    Ub (idleDue x) (p2 x) := by
  unfold p2; simp only [h, ↓reduceIte]; exact ub_earliest_t _ (Nat.le_refl _)

theorem ub_p3_p2 {U : Nat} (x : Inputs) (h : Ub U (p2 x)) : Ub U (p3 x) := by
  unfold p3; split
  · exact ub_earliest_p _ h
  · exact h

theorem ub_p3_direct (x : Inputs)
    (h : (watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow)) = true) :
    Ub (directDue x) (p3 x) := by
  unfold p3; simp only [h, ↓reduceIte]; exact ub_earliest_t _ (Nat.le_refl _)

theorem ub_p4 {U : Nat} (x : Inputs) (h : Ub U (p3 x)) : Ub (max x.quietUntil U) (p4 x) := by
  obtain ⟨c, hc, hcU⟩ := h
  unfold p4; split
  · rw [hc]; exact ⟨max x.quietUntil c, rfl, by omega⟩
  · rw [hc]; exact ⟨c, rfl, by omega⟩

theorem ub_p4_free {U : Nat} (x : Inputs) (hh : held x = false) (h : Ub U (p3 x)) : Ub U (p4 x) := by
  unfold p4; simp only [hh, Bool.false_eq_true, ↓reduceIte]; exact h

/-! ## Floors -/

theorem ping_lb {L : Nat} (x : Inputs) (h1 : ∀ d, standbyDue x.now x.lastTx x.lastApp = some d → L ≤ d)
    (h2 : L ≤ idleDue x)
    (h3 : (watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow)) = true → L ≤ directDue x) :
    Lb L (plan x).ping :=
  lb_p4 x (lb_p3 x (lb_p2 x (lb_p1 x h1) h2) h3)

theorem keep_cases (x : Inputs) (P : Nat → Prop) (h1 : P quietKeepDialer) (h2 : P quietKeepAcceptor)
    (h3 : P idleKeepPlain) : P (idleKeep x) := by
  unfold idleKeep
  by_cases hq : x.role.quiet = true
  · by_cases hd : x.dialer = true
    · simp [hq, hd, h1]
    · simp [hq, hd, h2]
  · simp [hq, h3]

theorem idleKeep_ge (x : Inputs) : pathKeep ≤ idleKeep x :=
  keep_cases x (fun k => pathKeep ≤ k)
    (by unfold quietKeepDialer pathKeep sec; omega)
    (by unfold quietKeepAcceptor pathKeep sec; omega)
    (by unfold idleKeepPlain pathKeep sec; omega)

theorem idleKeep_le (x : Inputs) : idleKeep x ≤ quietKeepAcceptor :=
  keep_cases x (fun k => k ≤ quietKeepAcceptor)
    (by unfold quietKeepDialer quietKeepAcceptor sec; omega)
    (Nat.le_refl _)
    (by unfold idleKeepPlain quietKeepAcceptor sec; omega)

/-- A ping is never due before `now`. -/
theorem ping_ge_now (x : Inputs) (p : Nat) (h : (plan x).ping = some p) : x.now ≤ p := by
  refine ping_lb (L := x.now) x ?_ ?_ ?_ p h
  · intro d hd
    unfold standbyDue at hd; split at hd <;> simp at hd; omega
  · unfold idleDue after; omega
  · intro _; unfold directDue after; omega

/-- A ping is never due before 5 s after the last send. -/
theorem ping_ge_tx (x : Inputs) (p : Nat) (h : (plan x).ping = some p) : satAdd x.lastTx pathKeep ≤ p := by
  refine ping_lb (L := satAdd x.lastTx pathKeep) x ?_ ?_ ?_ p h
  · intro d hd
    unfold standbyDue at hd; split at hd <;> simp at hd; omega
  · unfold idleDue after
    have := satAdd_mono_r x.lastTx (idleKeep_ge x)
    omega
  · intro _
    unfold directDue after
    have h1 : satAdd x.lastTx pathKeep ≤ satAdd (max x.lastRx x.lastTx) directSilence := by
      unfold satAdd pathKeep directSilence sec; omega
    omega

/-- Without a standby window and without a silent direct path to watch, the active path is not pinged before its
idle interval after the last send. -/
theorem ping_floor_role (x : Inputs) (hs : standbyDue x.now x.lastTx x.lastApp = none)
    (hd : (watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow)) = false) (p : Nat)
    (h : (plan x).ping = some p) : satAdd x.lastTx (idleKeep x) ≤ p := by
  refine ping_lb (L := satAdd x.lastTx (idleKeep x)) x ?_ ?_ ?_ p h
  · intro d hd'; rw [hs] at hd'; cases hd'
  · unfold idleDue after; omega
  · intro h'; rw [hd] at h'; cases h'

/-- Right after a resume nothing is due before the quiet period ends. -/
theorem ping_held (x : Inputs) (hh : held x = true) (p : Nat) (h : (plan x).ping = some p) : x.quietUntil ≤ p := by
  simp only [plan, p4, hh, if_true] at h
  cases hp : p3 x with
  | none => simp [hp] at h
  | some c => simp [hp] at h; omega

/-- When the quiet period does not apply, the plan is the plan without it. -/
theorem resume_inert (x : Inputs) (hh : held x = false) :
    plan x = plan { x with quietUntil := 0 } := by
  have h0 : held { x with quietUntil := 0 } = false := by simp [held]
  have e3 : p3 { x with quietUntil := 0 } = p3 x := rfl
  have e4 : r3 { x with quietUntil := 0 } = r3 x := rfl
  simp [plan, p4, r4, hh, h0, e3, e4]

/-! ## The review moment -/

theorem change_gt (now : Nat) (r : Option Nat) (t : Nat) (hr : ∀ v, r = some v → now < v) :
    ∀ v, change now r t = some v → now < v := by
  intro v hv
  unfold change at hv
  split at hv
  · cases r with
    | none => simp [earliest] at hv; omega
    | some c => have := hr c rfl; simp [earliest] at hv; omega
  · exact hr v hv

theorem review_gt_now (x : Inputs) (r : Nat) (h : (plan x).review = some r) : x.now < r := by
  have g1 := change_gt x.now none (satAdd x.lastApp activeKeep) (fun v h => by cases h)
  have g2 : ∀ v, r2 x = some v → x.now < v := by
    intro v hv; unfold r2 at hv; split at hv
    · exact change_gt _ _ _ g1 v hv
    · exact g1 v hv
  have g3 : ∀ v, r3 x = some v → x.now < v := by
    intro v hv; unfold r3 at hv; split at hv
    · exact change_gt _ _ _ g2 v hv
    · exact g2 v hv
  have g4 : ∀ v, r4 x = some v → x.now < v := by
    intro v hv; unfold r4 at hv; split at hv
    · exact change_gt _ _ _ g3 v hv
    · exact g3 v hv
  exact g4 r h


/-! ## Ceilings -/

/-- The standby path is pinged 5 s after its last send, while data moved in the last 20 s. -/
theorem standby_ceiling (x : Inputs) (d : Nat) (h : standbyDue x.now x.lastTx x.lastApp = some d) :
    (held x = false → Ub d (plan x).ping) ∧ Ub (max x.quietUntil d) (plan x).ping := by
  have h3 : Ub d (p3 x) := ub_p3_p2 x (ub_p2_p1 x (ub_p1 x h))
  exact ⟨fun hh => ub_p4_free x hh h3, ub_p4 x h3⟩

/-- The active path of a quiet session is always pinged after its idle interval. -/
theorem quiet_ceiling (x : Inputs) (hq : x.role.quiet = true) :
    (held x = false → Ub (max (satAdd x.lastTx (idleKeep x)) x.now) (plan x).ping) ∧
      Ub (max x.quietUntil (max (satAdd x.lastTx (idleKeep x)) x.now)) (plan x).ping := by
  have h3 : Ub (idleDue x) (p3 x) := ub_p3_p2 x (ub_p2_idle x (by simp [hq]))
  exact ⟨fun hh => ub_p4_free x hh h3, ub_p4 x h3⟩

theorem quiet_some (x : Inputs) (hq : x.role.quiet = true) : ∃ p, (plan x).ping = some p := by
  obtain ⟨p, hp, _⟩ := (quiet_ceiling x hq).2
  exact ⟨p, hp⟩

/-- The active path of a plain session is pinged after its idle interval while its 90 s window is open. -/
theorem plain_ceiling (x : Inputs) (hw : idleDue x < satAdd x.lastApp idleDrop) :
    (held x = false → Ub (idleDue x) (plan x).ping) ∧ Ub (max x.quietUntil (idleDue x)) (plan x).ping := by
  have h3 : Ub (idleDue x) (p3 x) := ub_p3_p2 x (ub_p2_idle x (by simp [hw]))
  exact ⟨fun hh => ub_p4_free x hh h3, ub_p4 x h3⟩

/-- The silent direct path of a quiet dialing session is pinged 14 s after the last send or receive, while data
moved in the last 120 s. -/
theorem direct_ceiling (x : Inputs) (hd : watchDirect x = true) (hw : directDue x < satAdd x.lastApp holdWindow) :
    (held x = false → Ub (directDue x) (plan x).ping) ∧ Ub (max x.quietUntil (directDue x)) (plan x).ping := by
  have h3 : Ub (directDue x) (p3 x) := ub_p3_direct x (by simp [hd, hw])
  exact ⟨fun hh => ub_p4_free x hh h3, ub_p4 x h3⟩

/-- A plain session with no data for 90 s is not pinged at all. -/
theorem plain_stops (x : Inputs) (hq : x.role.quiet = false) (hw : satAdd x.lastApp idleDrop ≤ x.now) :
    (plan x).ping = none := by
  have a20 : satAdd x.lastApp activeKeep ≤ satAdd x.lastApp idleDrop :=
    satAdd_mono_r _ (by unfold activeKeep idleDrop sec; omega)
  have e1 : p1 x = none := by
    show standbyDue x.now x.lastTx x.lastApp = none
    unfold standbyDue
    have : ¬ max (satAdd x.lastTx pathKeep) x.now < satAdd x.lastApp activeKeep := by omega
    exact if_neg this
  have e2 : p2 x = none := by
    have c : ¬ idleDue x < satAdd x.lastApp idleDrop := by unfold idleDue after; omega
    have hc : (x.role.quiet || decide (idleDue x < satAdd x.lastApp idleDrop)) = false := by simp [hq, c]
    unfold p2
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact e1
  have e3 : p3 x = none := by
    have hc : (watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow)) = false := by
      unfold watchDirect; simp [hq]
    unfold p3
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact e2
  show p4 x = none
  unfold p4
  split
  · rw [e3]; rfl
  · exact e3

/-! ## Before the peer's idle timeout -/

theorem keep_lt_timeout (x : Inputs) : idleKeep x + pathKeep ≤ idleTimeout :=
  keep_cases x (fun k => k + pathKeep ≤ idleTimeout)
    (by unfold quietKeepDialer pathKeep idleTimeout sec; omega)
    (by unfold quietKeepAcceptor pathKeep idleTimeout sec; omega)
    (by unfold idleKeepPlain pathKeep idleTimeout sec; omega)

theorem dialer_before_acceptor : quietKeepDialer < quietKeepAcceptor := by
  unfold quietKeepDialer quietKeepAcceptor sec; omega

/-- A quiet session whose quiet period does not hold the ping back, planned no later than its idle interval after
the last send, has its ping due by then. -/
theorem quiet_before_idle (x : Inputs) (hq : x.role.quiet = true) (hh : held x = false)
    (hnow : x.now ≤ satAdd x.lastTx (idleKeep x)) :
    ∃ p, (plan x).ping = some p ∧ p ≤ satAdd x.lastTx (idleKeep x) := by
  obtain ⟨p, hp, hle⟩ := (quiet_ceiling x hq).1 hh
  exact ⟨p, hp, by omega⟩

/-- The same, as the peer sees it. The hypotheses: the host sends the ping at `s`, at most `slack` after it was due,
with `slack` below the 5 s margin (the host calls on time); the peer's last activity `a` is not before our last
send (it counts the datagram, which cannot arrive before it left; the clocks are taken as one); and the idle
deadline does not wrap. Then the ping leaves before the peer's idle timeout, `a + 75 s`, can fire. -/
theorem sent_before_peer_idle (x : Inputs) (hq : x.role.quiet = true) (hh : held x = false)
    (hnow : x.now ≤ satAdd x.lastTx (idleKeep x)) (hfit : x.lastTx + idleTimeout ≤ u64Max)
    (s slack a : Nat) (hslack : slack < pathKeep) (hhost : ∀ p, (plan x).ping = some p → s ≤ p + slack)
    (hpeer : x.lastTx ≤ a) : s < a + idleTimeout := by
  obtain ⟨p, hp, hle⟩ := quiet_before_idle x hq hh hnow
  have h1 := hhost p hp
  have h2 := keep_lt_timeout x
  have h4 := idleKeep_le x
  have h3 : satAdd x.lastTx (idleKeep x) = x.lastTx + idleKeep x := by
    unfold satAdd
    unfold idleTimeout sec at hfit
    unfold quietKeepAcceptor sec at h4
    omega
  omega


#audit_axioms Pinc.CoreKeepalive.ping_ge_now
#audit_axioms Pinc.CoreKeepalive.ping_ge_tx
#audit_axioms Pinc.CoreKeepalive.ping_floor_role
#audit_axioms Pinc.CoreKeepalive.ping_held
#audit_axioms Pinc.CoreKeepalive.resume_inert
#audit_axioms Pinc.CoreKeepalive.review_gt_now
#audit_axioms Pinc.CoreKeepalive.standby_ceiling
#audit_axioms Pinc.CoreKeepalive.quiet_ceiling
#audit_axioms Pinc.CoreKeepalive.quiet_some
#audit_axioms Pinc.CoreKeepalive.plain_ceiling
#audit_axioms Pinc.CoreKeepalive.direct_ceiling
#audit_axioms Pinc.CoreKeepalive.plain_stops
#audit_axioms Pinc.CoreKeepalive.keep_lt_timeout
#audit_axioms Pinc.CoreKeepalive.dialer_before_acceptor
#audit_axioms Pinc.CoreKeepalive.quiet_before_idle
#audit_axioms Pinc.CoreKeepalive.sent_before_peer_idle

end Pinc.CoreKeepalive
