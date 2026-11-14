import Vinc.Axioms
import Vinc.CoreKeepaliveThm

/-!
# The keepalive schedule: the plan does not change before its review moment

`review_at` of `Inputs::plan` is documented as the first instant after `now` at which the answer can change without
any input changing. `plan_stable` states it: computing the plan again at a later `now` that is before the review
moment gives the same review moment and the same ping (a ping already due is then due at the new `now`). So no
moment before `review_at` changes the answer; and `review_at` is a moment at which a window of the schedule closes
or the quiet period ends (`w1`, `w2`, `w3`, `w4`: each window open at `now` is bounded by the review moment), which
is why the plan can differ from there on.
-/

namespace Vinc.CoreKeepalive

theorem map_earliest (n : Nat) (p : Option Nat) (t : Nat) :
    earliest (p.map (max n)) (max t n) = (earliest p t).map (max n) := by
  cases p <;> simp [earliest] <;> omega

theorem ub_change_t {U : Nat} (now : Nat) (r : Option Nat) {t : Nat} (h : now < t) (ht : t ≤ U) :
    Ub U (change now r t) := by
  unfold change; simp only [h, ↓reduceIte]; exact ub_earliest_t _ ht

theorem ub_change_r {U : Nat} (now : Nat) {r : Option Nat} (t : Nat) (h : Ub U r) : Ub U (change now r t) := by
  unfold change; split
  · exact ub_earliest_p _ h
  · exact h

theorem ub_r4 {U : Nat} (x : Inputs) (h : Ub U (r3 x)) : Ub U (r4 x) := by
  unfold r4; split
  · exact ub_change_r _ _ h
  · exact h

theorem ub_r3 {U : Nat} (x : Inputs) (h : Ub U (r2 x)) : Ub U (r3 x) := by
  unfold r3; split
  · exact ub_change_r _ _ h
  · exact h

theorem ub_r2 {U : Nat} (x : Inputs) (h : Ub U (r1 x)) : Ub U (r2 x) := by
  unfold r2; split
  · exact ub_change_r _ _ h
  · exact h

/-- Each window that is open at `now` is a review moment, or later than one. -/
theorem w1 (x : Inputs) (h : x.now < satAdd x.lastApp activeKeep) :
    Ub (satAdd x.lastApp activeKeep) (plan x).review :=
  ub_r4 x (ub_r3 x (ub_r2 x (ub_change_t _ _ h (Nat.le_refl _))))

theorem w2 (x : Inputs) (hq : x.role.quiet = false) (h : x.now < satAdd x.lastApp idleDrop) :
    Ub (satAdd x.lastApp idleDrop) (plan x).review := by
  have : Ub (satAdd x.lastApp idleDrop) (r2 x) := by
    unfold r2; simp only [hq, Bool.not_false, ↓reduceIte]; exact ub_change_t _ _ h (Nat.le_refl _)
  exact ub_r4 x (ub_r3 x this)

theorem w3 (x : Inputs) (hd : watchDirect x = true) (h : x.now < satAdd x.lastApp holdWindow) :
    Ub (satAdd x.lastApp holdWindow) (plan x).review := by
  have : Ub (satAdd x.lastApp holdWindow) (r3 x) := by
    unfold r3; simp only [hd, ↓reduceIte]; exact ub_change_t _ _ h (Nat.le_refl _)
  exact ub_r4 x this

theorem w4 (x : Inputs) (hh : held x = true) : Ub x.quietUntil (plan x).review := by
  have h : x.now < x.quietUntil := by
    unfold held at hh; simp at hh; exact hh.1
  unfold plan r4
  simp only [hh, if_true]
  exact ub_change_t _ _ h (Nat.le_refl _)

section stable
variable (x : Inputs) (n : Nat)

theorem p1_stable (hn : x.now ≤ n)
    (W : x.now < satAdd x.lastApp activeKeep → n < satAdd x.lastApp activeKeep) :
    p1 { x with now := n } = (p1 x).map (max n) := by
  unfold p1 standbyDue
  simp only []
  generalize satAdd x.lastTx pathKeep = d
  generalize satAdd x.lastApp activeKeep = a at W ⊢
  by_cases h : x.now < a
  · have := W h
    by_cases hd : d < a
    · have e1 : max d x.now < a := by omega
      have e2 : max d n < a := by omega
      simp [e1, e2]; omega
    · have e1 : ¬ max d x.now < a := by omega
      have e2 : ¬ max d n < a := by omega
      simp [e1, e2]
  · have e1 : ¬ max d x.now < a := by omega
    have e2 : ¬ max d n < a := by omega
    simp [e1, e2]

theorem idleDue_stable (hn : x.now ≤ n) : idleDue { x with now := n } = max (idleDue x) n := by
  have hk : idleKeep { x with now := n } = idleKeep x := rfl
  unfold idleDue after
  simp only [hk]
  omega

theorem directDue_stable (hn : x.now ≤ n) : directDue { x with now := n } = max (directDue x) n := by
  unfold directDue after
  simp only []
  omega

theorem p2_stable (hn : x.now ≤ n)
    (W : x.role.quiet = false → x.now < satAdd x.lastApp idleDrop → n < satAdd x.lastApp idleDrop)
    (h1 : p1 { x with now := n } = (p1 x).map (max n)) :
    p2 { x with now := n } = (p2 x).map (max n) := by
  have hI := idleDue_stable x n hn
  have hc : (({ x with now := n } : Inputs).role.quiet ||
      decide (idleDue { x with now := n } < satAdd ({ x with now := n } : Inputs).lastApp idleDrop)) =
      (x.role.quiet || decide (idleDue x < satAdd x.lastApp idleDrop)) := by
    show (x.role.quiet || decide (idleDue { x with now := n } < satAdd x.lastApp idleDrop)) = _
    rw [hI]
    cases hq : x.role.quiet
    · have hge : x.now ≤ idleDue x := by unfold idleDue after; omega
      by_cases hw : x.now < satAdd x.lastApp idleDrop
      · have := W hq hw
        simp only [Bool.false_or]
        by_cases c : idleDue x < satAdd x.lastApp idleDrop
        · have : max (idleDue x) n < satAdd x.lastApp idleDrop := by omega
          simp [c, this]
        · have : ¬ max (idleDue x) n < satAdd x.lastApp idleDrop := by omega
          simp [c, this]
      · have c : ¬ idleDue x < satAdd x.lastApp idleDrop := by omega
        have : ¬ max (idleDue x) n < satAdd x.lastApp idleDrop := by omega
        simp [c, this]
    · simp
  unfold p2
  simp only []
  rw [hc, hI, h1]
  split
  · exact map_earliest n _ _
  · rfl

theorem p3_stable (hn : x.now ≤ n)
    (W : watchDirect x = true → x.now < satAdd x.lastApp holdWindow → n < satAdd x.lastApp holdWindow)
    (h2 : p2 { x with now := n } = (p2 x).map (max n)) :
    p3 { x with now := n } = (p3 x).map (max n) := by
  have hD := directDue_stable x n hn
  have hw : watchDirect { x with now := n } = watchDirect x := rfl
  have hc : (watchDirect { x with now := n } &&
      decide (directDue { x with now := n } < satAdd ({ x with now := n } : Inputs).lastApp holdWindow)) =
      (watchDirect x && decide (directDue x < satAdd x.lastApp holdWindow)) := by
    show (watchDirect { x with now := n } && decide (directDue { x with now := n } < satAdd x.lastApp holdWindow)) = _
    rw [hD, hw]
    cases hq : watchDirect x
    · simp
    · have hge : x.now ≤ directDue x := by unfold directDue after; omega
      by_cases hwin : x.now < satAdd x.lastApp holdWindow
      · have := W hq hwin
        simp only [Bool.true_and]
        by_cases c : directDue x < satAdd x.lastApp holdWindow
        · have : max (directDue x) n < satAdd x.lastApp holdWindow := by omega
          simp [c, this]
        · have : ¬ max (directDue x) n < satAdd x.lastApp holdWindow := by omega
          simp [c, this]
      · have c : ¬ directDue x < satAdd x.lastApp holdWindow := by omega
        have : ¬ max (directDue x) n < satAdd x.lastApp holdWindow := by omega
        simp [c, this]
  unfold p3
  simp only []
  rw [hc, hD, h2]
  split
  · exact map_earliest n _ _
  · rfl

theorem held_stable (hn : x.now ≤ n) (W : held x = true → n < x.quietUntil) :
    held { x with now := n } = held x := by
  unfold held
  cases hf : x.inFlight
  · simp only [Bool.not_false, Bool.and_true, decide_eq_decide]
    show (n < x.quietUntil) ↔ (x.now < x.quietUntil)
    constructor
    · intro h; omega
    · intro h
      have := W (by unfold held; simp [hf]; exact h)
      exact this
  · simp

theorem p4_stable (hn : x.now ≤ n) (W : held x = true → n < x.quietUntil)
    (h3 : p3 { x with now := n } = (p3 x).map (max n)) :
    p4 { x with now := n } = (p4 x).map (max n) := by
  have hh := held_stable x n hn W
  unfold p4
  simp only []
  rw [hh, h3]
  split
  · have := W ‹_›
    cases p3 x <;> simp <;> omega
  · rfl

theorem r1_stable (W : x.now < satAdd x.lastApp activeKeep → n < satAdd x.lastApp activeKeep)
    (hn : x.now ≤ n) : r1 { x with now := n } = r1 x := by
  unfold r1 change
  simp only []
  generalize satAdd x.lastApp activeKeep = a at W ⊢
  by_cases h : x.now < a
  · have := W h
    simp [h, this]
  · have : ¬ n < a := by omega
    simp [h, this]

theorem change_stable (r r' : Option Nat) (t : Nat) (hn : x.now ≤ n) (W : x.now < t → n < t) (h : r' = r) :
    change n r' t = change x.now r t := by
  subst h
  unfold change
  by_cases h1 : x.now < t
  · have := W h1
    simp [h1, this]
  · have : ¬ n < t := by omega
    simp [h1, this]

theorem r2_stable (hn : x.now ≤ n)
    (W : x.role.quiet = false → x.now < satAdd x.lastApp idleDrop → n < satAdd x.lastApp idleDrop)
    (h1 : r1 { x with now := n } = r1 x) : r2 { x with now := n } = r2 x := by
  unfold r2
  simp only []
  split
  · rename_i hc
    have hq : x.role.quiet = false := by simpa using hc
    exact change_stable x n _ _ _ hn (W hq) h1
  · exact h1

theorem r3_stable (hn : x.now ≤ n)
    (W : watchDirect x = true → x.now < satAdd x.lastApp holdWindow → n < satAdd x.lastApp holdWindow)
    (h2 : r2 { x with now := n } = r2 x) : r3 { x with now := n } = r3 x := by
  unfold r3
  simp only []
  have hw : watchDirect { x with now := n } = watchDirect x := rfl
  rw [hw]
  split
  · exact change_stable x n _ _ _ hn (W ‹_›) h2
  · exact h2

theorem r4_stable (hn : x.now ≤ n) (W : held x = true → n < x.quietUntil)
    (h3 : r3 { x with now := n } = r3 x) : r4 { x with now := n } = r4 x := by
  have hh := held_stable x n hn W
  unfold r4
  simp only []
  rw [hh]
  split
  · exact change_stable x n _ _ _ hn (fun _ => W ‹_›) h3
  · exact h3

end stable

/-- Computing the plan again at a later `now` that is before its review moment changes nothing: the same review
moment, the same ping (a ping already due is due `now`). -/
theorem plan_stable (x : Inputs) (n : Nat) (hn : x.now ≤ n) (hr : ∀ r, (plan x).review = some r → n < r) :
    plan { x with now := n } = { ping := (plan x).ping.map (max n), review := (plan x).review } := by
  have lt : ∀ {U : Nat}, Ub U (plan x).review → n < U := by
    intro U ⟨v, hv, hvU⟩; have := hr v hv; omega
  have W1 : x.now < satAdd x.lastApp activeKeep → n < satAdd x.lastApp activeKeep := fun h => lt (w1 x h)
  have W2 : x.role.quiet = false → x.now < satAdd x.lastApp idleDrop → n < satAdd x.lastApp idleDrop :=
    fun hq h => lt (w2 x hq h)
  have W3 : watchDirect x = true → x.now < satAdd x.lastApp holdWindow → n < satAdd x.lastApp holdWindow :=
    fun hd h => lt (w3 x hd h)
  have W4 : held x = true → n < x.quietUntil := fun hh => lt (w4 x hh)
  have hp := p4_stable x n hn W4 (p3_stable x n hn W3 (p2_stable x n hn W2 (p1_stable x n hn W1)))
  have hq := r4_stable x n hn W4 (r3_stable x n hn W3 (r2_stable x n hn W2 (r1_stable x n W1 hn)))
  simp only [plan]
  rw [hp, hq]


#audit_axioms Vinc.CoreKeepalive.plan_stable
#audit_axioms Vinc.CoreKeepalive.w1

end Vinc.CoreKeepalive
