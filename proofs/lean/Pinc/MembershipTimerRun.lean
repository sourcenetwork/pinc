import Pinc.MembershipTimerFields

/-!
# Completeness over a run, part 2: the timer schedule

The host asks `poll_timeout` for the next deadline and calls `on_timeout`; the tick runs in the call that finds its
deadline `next_tick` passed. Over any sequence of the host's calls (`Call`, `runCalls`), with one hypothesis about
timing, the host's:

* `step_tm`, `step_fields`: no call but `on_timeout` writes `next_tick`, no call writes `is_hub` or `born`, and no call
  but `leave` writes `leaving` (the `*_tm` lemmas of `MembershipTimerFields`). So no input postpones a tick.
* `pollTimeout_le`: the deadline `poll_timeout` returns is never later than the tick deadline.
* `onTimeout_ticks`: a call of `on_timeout` at or after the tick deadline (on a node that is not leaving) runs the tick
  and sets the next deadline one tick period (`HUB_TICK` for a hub, `NODE_TICK` for a member) after the call;
  `onTimeout_waits`: an earlier call leaves the deadline as it is.
* `tick_window` (the timer schedule): under the host's one obligation (`Timely σ`: each call comes no later than `σ`
  after the deadline `poll_timeout` returned before it), a node that does not leave runs its tick in every window
  `(T, T + period + σ]` that the run outlasts.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership.Cmp
open Pinc.Membership
open Pinc.MemInc

/-! ## `on_timeout` and `poll_timeout` -/

/-- The tick period of a node. -/
def period (n : N) : Nat := if n.isHub then HUB_TICK else NODE_TICK

theorem otTickPre_nextTick (e : Env) (n : N) (now : Nat) :
    (N.otTickPre e n now).nextTick = some (satAdd now (period n)) ∧
    (N.otTickPre e n now).isHub = n.isHub ∧ (N.otTickPre e n now).leaving = n.leaving ∧
    (N.otTickPre e n now).born = n.born := by
  unfold N.otTickPre period
  repeat' split
  all_goals simp_all

/-- `on_timeout` writes none of the role, the start time and the leave flag. -/
theorem onTimeout_fields (e : Env) (n : N) (now : Nat) :
    (N.onTimeout e n now).isHub = n.isHub ∧ (N.onTimeout e n now).born = n.born ∧ (N.onTimeout e n now).leaving = n.leaving := by
  rw [onTimeout_split]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    have h1 := otPre_tm e n now
    split
    · unfold N.otTick
      have h2 := tick_tm e (N.otTickPre e (N.otPre e n now) now) now
      obtain ⟨-, h3, h4, h5⟩ := otTickPre_nextTick e (N.otPre e n now) now
      exact ⟨h2.2.1.trans (h3.trans h1.2.1), h2.2.2.2.trans (h5.trans h1.2.2.2), h2.2.2.1.trans (h4.trans h1.2.2.1)⟩
    · exact ⟨h1.2.1, h1.2.2.2, h1.2.2.1⟩

/-- **The tick runs when its deadline has passed.** A call of `on_timeout` at or after the tick deadline, on a node that
is not leaving, is the tick branch of the code, and the next deadline is one tick period after the call. -/
theorem onTimeout_ticks (e : Env) (n : N) (now : Nat) (hl : n.leaving = false) (hd : n.nextTick.getD 0 ≤ now) :
    N.onTimeout e n now = N.otTick e (N.otPre e n now) now ∧
    (N.onTimeout e n now).nextTick = some (satAdd now (period n)) := by
  have h1 := otPre_tm e n now
  have heq : N.onTimeout e n now = N.otTick e (N.otPre e n now) now := by
    rw [onTimeout_split, if_neg (by simp [hl])]
    dsimp only
    rw [if_pos (by rw [h1.1]; exact hd)]
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold N.otTick
  have h2 := tick_tm e (N.otTickPre e (N.otPre e n now) now) now
  obtain ⟨h3, -⟩ := otTickPre_nextTick e (N.otPre e n now) now
  rw [h2.1, h3]
  unfold period
  rw [h1.2.1]

/-- A call of `on_timeout` before the tick deadline leaves the deadline as it is. -/
theorem onTimeout_waits (e : Env) (n : N) (now : Nat) (hd : now < n.nextTick.getD 0) :
    TM[n, N.onTimeout e n now] := by
  rw [onTimeout_split]
  split
  · simp
  · dsimp only
    have h1 := otPre_tm e n now
    rw [if_neg (by rw [h1.1]; omega)]
    exact h1

/-- The deadline `poll_timeout` returns is never later than the tick deadline (the start time before the first tick). -/
theorem pollTimeout_le (n : N) : N.pollTimeout n ≤ n.nextTick.getD n.born := by
  unfold N.pollTimeout
  dsimp only
  split <;> omega

/-! ## A run of the host's calls -/

/-- A call of the host into the machine, with the instant of the host's clock when it is made. -/
inductive Call where
  | onBytes (e : Env) (now peer : Nat) (fs : List NFrame) (bad : Bool)
  | onFrame (e : Env) (now peer : Nat) (f : NFrame)
  | onTimeout (e : Env) (now : Nat)
  | sessionUp (e : Env) (now peer : Nat) (incoming : Bool)
  | sessionDown (e : Env) (now peer code : Nat)
  | leave (now : Nat)
  | revoke (e : Env) (now member : Nat)
  | addressChanged (now : Nat)
  | snapshotTo (e : Env) (now peer : Nat)
  | setMaxFrame (now mb : Nat)
  | carrierReturn (e : Env) (now member : Nat)
  | carrierGone (e : Env) (now member : Nat)
  | drained (now : Nat)

/-- The instant of a call. -/
def Call.at : Call → Nat
  | .onBytes _ now .. => now
  | .onFrame _ now .. => now
  | .onTimeout _ now => now
  | .sessionUp _ now .. => now
  | .sessionDown _ now .. => now
  | .leave now => now
  | .revoke _ now .. => now
  | .addressChanged now => now
  | .snapshotTo _ now .. => now
  | .setMaxFrame now _ => now
  | .carrierReturn _ now .. => now
  | .carrierGone _ now .. => now
  | .drained now => now

/-- The node after the call (a `revoke` that returns `TableFull` changes nothing). -/
def Call.step : Call → N → N
  | .onBytes e now peer fs bad, n => N.onBytes e n now peer fs bad
  | .onFrame e now peer f, n => N.onFrame e n now peer f
  | .onTimeout e now, n => N.onTimeout e n now
  | .sessionUp e now peer incoming, n => N.sessionUp e n now peer incoming
  | .sessionDown e now peer code, n => N.sessionDown e n now peer code
  | .leave _, n => n.leave
  | .revoke e now member, n => (N.revoke e n now member).getD n
  | .addressChanged now, n => n.addressChanged now
  | .snapshotTo e now peer, n => N.snapshotTo e n now peer
  | .setMaxFrame _ mb, n => n.setMaxFrame mb
  | .carrierReturn e now member, n => N.carrierReturn e n now member
  | .carrierGone e now member, n => N.carrierGone e n now member
  | .drained _, n => n.drained

def Call.isLeave : Call → Bool
  | .leave _ => true
  | _ => false

/-- The node after a sequence of calls. -/
def runCalls (cs : List Call) (n : N) : N := cs.foldl (fun n c => c.step n) n

theorem runCalls_cons (c : Call) (cs : List Call) (n : N) : runCalls (c :: cs) n = runCalls cs (c.step n) := rfl
theorem runCalls_append (a b : List Call) (n : N) : runCalls (a ++ b) n = runCalls b (runCalls a n) := by
  unfold runCalls; rw [List.foldl_append]

/-- **The host's obligation.** Each call comes no later than `σ` after the deadline `poll_timeout` returned after the
previous call: when nothing else happens by then, the host calls `on_timeout`. `σ` is the host's scheduling slack. -/
def Timely (σ : Nat) : N → List Call → Prop
  | _, [] => True
  | n, c :: cs => c.at ≤ N.pollTimeout n + σ ∧ Timely σ (c.step n) cs

theorem Timely.append {σ : Nat} {n : N} {a b : List Call} (h : Timely σ n (a ++ b)) : Timely σ (runCalls a n) b := by
  induction a generalizing n with
  | nil => exact h
  | cons c r ih => exact ih h.2

/-- Every call but `on_timeout` and `leave` keeps the four timer fields. -/
theorem step_tm (c : Call) (n : N) (h1 : ∀ e t, c ≠ .onTimeout e t) (h2 : c.isLeave = false) : TM[n, c.step n] := by
  cases c with
  | onTimeout e t => exact absurd rfl (h1 e t)
  | leave t => simp [Call.isLeave] at h2
  | revoke e now member =>
    simp only [Call.step]
    cases hr : N.revoke e n now member with
    | none => simp
    | some n' => simp only [Option.getD_some]; exact revoke_tm e n n' now member hr
  | _ => simp [Call.step]

/-- Every call but `leave` keeps the role, the start time and the leave flag. -/
theorem step_fields (c : Call) (n : N) (h2 : c.isLeave = false) :
    (c.step n).isHub = n.isHub ∧ (c.step n).born = n.born ∧ (c.step n).leaving = n.leaving := by
  cases c with
  | onTimeout e t => exact onTimeout_fields e n t
  | leave t => simp [Call.isLeave] at h2
  | _ =>
    have := step_tm _ n (fun _ _ h => by cases h) h2
    exact ⟨this.2.1, this.2.2.2, this.2.2.1⟩

theorem runCalls_fields (cs : List Call) (n : N) (h : ∀ c ∈ cs, c.isLeave = false) :
    (runCalls cs n).isHub = n.isHub ∧ (runCalls cs n).born = n.born ∧ (runCalls cs n).leaving = n.leaving := by
  induction cs generalizing n with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c r ih =>
    rw [runCalls_cons]
    obtain ⟨a1, a2, a3⟩ := ih (c.step n) (fun c' hc => h c' (List.mem_cons_of_mem _ hc))
    obtain ⟨b1, b2, b3⟩ := step_fields c n (h c (List.mem_cons_self ..))
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

/-- **The timer schedule over a run.** Along any sequence of calls on which the host keeps its obligation (`Timely σ`)
and the node does not leave, a node whose tick deadline (its start time before the first tick) is at most one tick
period after an instant `T` runs its tick at a call of `on_timeout` at an instant in `(T, T + period + σ]`, provided
the run goes on past that window. No input postpones the tick: every call but `on_timeout` keeps the deadline
(`step_tm`), the deadline `poll_timeout` returns is never later (`pollTimeout_le`), and `on_timeout` at the deadline
runs the tick (`onTimeout_ticks`). The calls before the tick leave a node that is not leaving, has the same role and
whose deadline has passed. -/
theorem tick_window (σ T : Nat) : ∀ (cs : List Call) (n : N), Timely σ n cs → (∀ c ∈ cs, c.isLeave = false) →
    n.leaving = false → n.nextTick.getD n.born ≤ T + period n → (∃ c ∈ cs, T + period n + σ < c.at) →
    ∃ pre e τ post, cs = pre ++ Call.onTimeout e τ :: post ∧ T < τ ∧ τ ≤ T + period n + σ ∧
      (runCalls pre n).leaving = false ∧ (runCalls pre n).isHub = n.isHub ∧ (runCalls pre n).nextTick.getD 0 ≤ τ := by
  intro cs
  induction cs with
  | nil => intro n _ _ _ _ hc; obtain ⟨c, hc, -⟩ := hc; simp at hc
  | cons c cs ih =>
    intro n ht hnl hl hd hc
    obtain ⟨hat, ht'⟩ := ht
    have hpoll := pollTimeout_le n
    have hcat : c.at ≤ T + period n + σ := by omega
    have hrest : ∃ c ∈ cs, T + period n + σ < c.at := by
      obtain ⟨c', hc', hlt⟩ := hc
      rcases List.mem_cons.mp hc' with h | h
      · subst h; omega
      · exact ⟨c', h, hlt⟩
    have hnl' : ∀ c ∈ cs, c.isLeave = false := fun c hc => hnl c (List.mem_cons_of_mem _ hc)
    -- a call that keeps the timer fields: the window carries over to the rest of the run
    have keep : TM[n, c.step n] → ∃ pre e τ post, c :: cs = pre ++ Call.onTimeout e τ :: post ∧ T < τ ∧
        τ ≤ T + period n + σ ∧ (runCalls pre n).leaving = false ∧ (runCalls pre n).isHub = n.isHub ∧
        (runCalls pre n).nextTick.getD 0 ≤ τ := by
      intro htm
      have hp : period (c.step n) = period n := by unfold period; rw [htm.2.1]
      obtain ⟨pre, e, τ, post, h1, h2, h3, h4, h5, h6⟩ := ih (c.step n) ht' hnl' (by rw [htm.2.2.1]; exact hl)
        (by rw [htm.1, htm.2.2.2, hp]; exact hd) (by rw [hp]; exact hrest)
      refine ⟨c :: pre, e, τ, post, by rw [h1]; rfl, h2, by rw [← hp]; exact h3, h4, ?_, h6⟩
      rw [runCalls_cons, h5]; exact htm.2.1
    cases c with
    | onTimeout e t =>
      by_cases hdue : n.nextTick.getD 0 ≤ t
      · by_cases hT : T < t
        · exact ⟨[], e, t, cs, rfl, hT, hcat, hl, rfl, hdue⟩
        · -- the tick ran at or before `T`: the next deadline is within one period of `T`
          obtain ⟨-, hnt⟩ := onTimeout_ticks e n t hl hdue
          obtain ⟨f1, f2, f3⟩ := onTimeout_fields e n t
          have hp : period (N.onTimeout e n t) = period n := by unfold period; rw [f1]
          have hd' : (N.onTimeout e n t).nextTick.getD (N.onTimeout e n t).born ≤ T + period (N.onTimeout e n t) := by
            rw [hnt, hp]
            simp only [Option.getD_some, satAdd]
            omega
          obtain ⟨pre, e', τ, post, h1, h2, h3, h4, h5, h6⟩ := ih (N.onTimeout e n t) ht' hnl'
            (by rw [f3]; exact hl) hd' (by rw [hp]; exact hrest)
          refine ⟨.onTimeout e t :: pre, e', τ, post, by rw [h1]; rfl, h2, by rw [← hp]; exact h3, h4, ?_, h6⟩
          rw [runCalls_cons]; simp only [Call.step]; rw [h5]; exact f1
      · exact keep (onTimeout_waits e n t (by omega))
    | leave t => simp [Call.isLeave] at hnl
    | _ => exact keep (step_tm _ n (fun _ _ h => by cases h) rfl)

end Pinc.Membership.Cmp

#audit_axioms Pinc.Membership.Cmp.step_tm
#audit_axioms Pinc.Membership.Cmp.pollTimeout_le
#audit_axioms Pinc.Membership.Cmp.onTimeout_ticks
#audit_axioms Pinc.Membership.Cmp.tick_window
