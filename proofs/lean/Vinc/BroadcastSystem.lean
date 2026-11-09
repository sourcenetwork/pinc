import Vinc.Axioms

/-!
# The broadcast scenarios at system level

The Lean counterpart of `proofs/tla/BroadcastSystem.tla`, for any number of subscribers (`Subs`, ids from 3 on; the
publisher is 0 and the hubs are 1 and 2), any number of link flips and restarts. A state is the link table, whether
the message was published, which hubs logged it, what each subscriber delivered in its current life (`deliv`) and in
all (`count`), its primary hub, the floors it learned at a restart, what each hub sent it (`sent`) and whether its
first delivery was by the fallback alone (`fbOnly`). The steps are those of the TLA text: `publish`, `pubToHub`
(log, mirror, push to the subscribers whose primary it is), `fallback` (only while the publisher reaches no hub),
`repair` (SUB, HAVE, GET, MSG at the primary), `failover`, `hubAe`, `restart` and `flip`.

Safety, for every reachable state (`Reach`): `atMostOnce` (a subscriber's application hears the message at most once
across its lives unless its first delivery was by the fallback alone) and `floorsCover` (what a hub sent a subscriber
is covered by the floor or a delivery of the current life, which is stronger than the TLA invariant); `fb_twice` is
the concrete run that delivers twice, the `_fb` witness. Liveness, under weak fairness of every step as in
`LSpec`: `late_live` (the late publish: the publisher and every subscriber cut off from both hubs but able to reach
each other), `churn_heals` (once the links stay up), `failover_delivers` (the primary hub lost for good). They are
proved for runs without restarts, which is the config `BroadcastSystem_live.cfg` (`MaxRestarts = 0`).
-/

namespace Vinc.BroadcastSystem

/-- The state of the system. `up a b` is the link `<<a, b>>`. -/
structure St where
  up : Nat → Nat → Bool
  pubd : Bool
  hubLog : Nat → Bool
  deliv : Nat → Bool
  primary : Nat → Nat
  sent : Nat → Nat → Bool
  floor : Nat → Bool
  count : Nat → Nat
  nf : Nat
  nr : Nat
  fbOnly : Nat → Bool

/-- `Init`. -/
def init : St :=
  ⟨fun _ _ => true, false, fun _ => false, fun _ => false, fun _ => 1, fun _ _ => false, fun _ => false,
   fun _ => 0, 0, 0, fun _ => false⟩

/-- Whether `Offer(s)` delivers: neither the dedupe set of this life nor a floor covers the message. -/
def fresh (st : St) (s : Nat) : Bool := !(st.deliv s || st.floor s)

/-- `Offer(s)` on the delivery sets. -/
def offD (st : St) (s : Nat) : Nat → Bool := fun x => if x = s then (st.deliv s || fresh st s) else st.deliv x

/-- `Offer(s)` on the counts. -/
def offC (st : St) (s : Nat) : Nat → Nat := fun x => if x = s && fresh st s then st.count x + 1 else st.count x

/-- A link of the system: hub-hub, publisher-hub, publisher-subscriber, subscriber-hub. -/
def IsLink (Subs : List Nat) (l : Nat × Nat) : Prop :=
  l = (0, 1) ∨ l = (0, 2) ∨ l = (1, 2) ∨ (∃ s ∈ Subs, l = (0, s)) ∨ ∃ s ∈ Subs, ∃ h, (h = 1 ∨ h = 2) ∧ l = (s, h)

/-- Whether a push of the message by hub `h` reaches subscriber `s` (`st'` is the state with the logs updated). -/
def pushed (Subs : List Nat) (st st' : St) (h : Nat) (push : Nat → Bool) (s : Nat) : Bool :=
  Subs.contains s && push s && st'.hubLog (st.primary s) && st.up s (st.primary s) &&
    (st.primary s == h || st.up 1 2)

/-- The state after hub `h` took the message: logged, mirrored over a live hub link, pushed to the subscribers whose
primary it is (a live session may swallow the frame, `push`). -/
def pubStep (Subs : List Nat) (st : St) (h : Nat) (push : Nat → Bool) : St :=
  let log' : Nat → Bool := fun x => if x = h ∨ (x = 3 - h ∧ st.up 1 2 = true) then true else st.hubLog x
  let mid : St := {st with hubLog := log'}
  let pd : Nat → Bool := pushed Subs st mid h push
  {mid with
    deliv := fun s => if pd s = true then offD st s s else st.deliv s,
    count := fun s => if pd s = true then offC st s s else st.count s,
    sent := fun x s => if pd s = true ∧ st.primary s = x then true else st.sent x s}

/-- The state after the publisher handed the message to subscriber `s` over a member link (`fallback_step`). -/
def fallbackSt (st : St) (s : Nat) : St :=
  {st with deliv := offD st s, count := offC st s,
           fbOnly := fun x => if x = s then (st.fbOnly s || !(st.deliv s || st.floor s || st.sent 1 s || st.sent 2 s))
                              else st.fbOnly x}

/-- The state after `s` asked its primary (SUB, HAVE, GET, MSG). -/
def repairSt (st : St) (s : Nat) : St :=
  {st with deliv := offD st s, count := offC st s,
           sent := fun h x => if h = st.primary s ∧ x = s ∧ fresh st s = true then true else st.sent h x}

/-- The state after `s` moved to its other hub. -/
def failoverSt (st : St) (s : Nat) : St :=
  {st with primary := fun x => if x = s then 3 - st.primary s else st.primary x}

/-- The state after the hubs exchanged their ids: hub `h` told the other. -/
def hubAeSt (st : St) (h : Nat) : St := {st with hubLog := fun x => if x = 3 - h then true else st.hubLog x}

/-- The state after subscriber `s` restarted. -/
def restartSt (st : St) (s : Nat) : St :=
  {st with nr := st.nr + 1, deliv := fun x => if x = s then false else st.deliv x,
           floor := fun x => if x = s then (st.floor s || st.sent 1 s || st.sent 2 s) else st.floor x}

/-- The state after a link flipped. -/
def flipSt (st : St) (l : Nat × Nat) : St :=
  {st with nf := st.nf + 1, up := fun a b => if (a, b) = l then !st.up a b else st.up a b}

/-- The steps of the system (`Next`), with the bounds on flips (`F`) and restarts (`R`). -/
inductive Step (Subs : List Nat) (F R : Nat) : St → St → Prop where
  | publish (st : St) (h : st.pubd = false) : Step Subs F R st {st with pubd := true}
  | pubToHub (st : St) (h : Nat) (hh : h = 1 ∨ h = 2) (push : Nat → Bool)
      (g : st.pubd = true ∧ st.up 0 h = true ∧ st.hubLog h = false) :
      Step Subs F R st (pubStep Subs st h push)
  | fallback (st : St) (s : Nat) (hs : s ∈ Subs)
      (g : st.pubd = true ∧ st.up 0 1 = false ∧ st.up 0 2 = false ∧ st.up 0 s = true) :
      Step Subs F R st (fallbackSt st s)
  | repair (st : St) (s : Nat) (hs : s ∈ Subs) (g : st.up s (st.primary s) = true ∧ st.hubLog (st.primary s) = true) :
      Step Subs F R st (repairSt st s)
  | failover (st : St) (s : Nat) (hs : s ∈ Subs)
      (g : st.up s (st.primary s) = false ∧ st.up s (3 - st.primary s) = true) :
      Step Subs F R st (failoverSt st s)
  | hubAe (st : St) (h : Nat) (hh : h = 1 ∨ h = 2)
      (g : st.up 1 2 = true ∧ st.hubLog h = true ∧ st.hubLog (3 - h) = false) :
      Step Subs F R st (hubAeSt st h)
  | restart (st : St) (s : Nat) (hs : s ∈ Subs) (g : st.nr < R) : Step Subs F R st (restartSt st s)
  | flip (st : St) (l : Nat × Nat) (hl : IsLink Subs l) (g : st.nf < F) : Step Subs F R st (flipSt st l)

/-- The reachable states. -/
inductive Reach (Subs : List Nat) (F R : Nat) : St → Prop where
  | init : Reach Subs F R init
  | step {st st' : St} : Reach Subs F R st → Step Subs F R st st' → Reach Subs F R st'

/-! ## Safety -/

/-- The inductive invariant behind `atMostOnce` and `floorsCover`. -/
structure Inv (st : St) : Prop where
  delivCount : ∀ s, st.deliv s = true → 1 ≤ st.count s
  floorCount : ∀ s, st.floor s = true → 1 ≤ st.count s
  sentCovered : ∀ h s, st.sent h s = true → st.deliv s = true ∨ st.floor s = true
  delivSource : ∀ s, st.deliv s = true → st.fbOnly s = true ∨ st.floor s = true ∨ st.sent 1 s = true ∨ st.sent 2 s = true
  countSource : ∀ s, 1 ≤ st.count s → st.fbOnly s = true ∨ st.deliv s = true ∨ st.floor s = true
  once : ∀ s, st.count s ≤ 1 ∨ st.fbOnly s = true
  primHub : ∀ s, st.primary s = 1 ∨ st.primary s = 2
  sentHub : ∀ h s, st.sent h s = true → h = 1 ∨ h = 2

theorem inv_init : Inv init :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init], by simp [init], by simp [init],
   by simp [init]⟩

theorem fresh_iff (st : St) (s : Nat) : fresh st s = true ↔ st.deliv s = false ∧ st.floor s = false := by
  simp [fresh]

theorem offD_true {st : St} {s x : Nat} (h : st.deliv x = true) : offD st s x = true := by
  unfold offD; split <;> simp_all

theorem inv_step {Subs : List Nat} {F R : Nat} {st st' : St} (hi : Inv st) (hs : Step Subs F R st st') : Inv st' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hi
  cases hs with
  | publish h => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  | flip l hl g => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  | hubAe h hh g => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  | failover s hs g =>
    refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8⟩
    intro x; simp only [failoverSt]; split
    · have := h7 s; omega
    · exact h7 x
  | restart s hs g =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, h8⟩ <;> intros <;> simp_all [fallbackSt, repairSt, failoverSt, hubAeSt, restartSt, flipSt, offD, offC, fresh] <;> grind
  | fallback s hs g =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, h8⟩ <;> intros <;> simp_all [fallbackSt, repairSt, failoverSt, hubAeSt, restartSt, flipSt, offD, offC, fresh] <;> grind
  | repair s hs g =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, ?_⟩ <;> intros <;> simp_all [fallbackSt, repairSt, failoverSt, hubAeSt, restartSt, flipSt, offD, offC, fresh] <;> grind
  | pubToHub h hh push g =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, ?_⟩ <;> intros <;> simp_all [pubStep, fallbackSt, repairSt, failoverSt, hubAeSt, restartSt, flipSt, offD, offC, fresh] <;> grind


theorem reach_inv {Subs : List Nat} {F R : Nat} {st : St} (r : Reach Subs F R st) : Inv st := by
  induction r with
  | init => exact inv_init
  | step _ hs ih => exact inv_step ih hs

/-- A subscriber's application hears the message at most once across its lives, unless its first delivery was by the
fallback alone (then no hub has a record of it for the floors of a restart). -/
theorem atMostOnce {Subs : List Nat} {F R : Nat} {st : St} (r : Reach Subs F R st) (s : Nat) :
    st.count s ≤ 1 ∨ st.fbOnly s = true := (reach_inv r).once s

/-- What a hub sent a subscriber is covered by its floor or by a delivery of its current life. -/
theorem floorsCover {Subs : List Nat} {F R : Nat} {st : St} (r : Reach Subs F R st) (h s : Nat)
    (hs : st.sent h s = true) : st.floor s = true ∨ st.deliv s = true :=
  ((reach_inv r).sentCovered h s hs).symm

/-- Right after a restart of `s` every hub's record for it is a floor. -/
theorem restart_floor {Subs : List Nat} {F R : Nat} {st : St} (r : Reach Subs F R st) (s h : Nat)
    (hs : st.sent h s = true) : (restartSt st s).floor s = true := by
  have hh := (reach_inv r).sentHub h s hs
  simp only [restartSt, if_true, Bool.or_eq_true]
  rcases hh with rfl | rfl <;> simp [hs]

/-- The `_fb` witness: a message only the fallback delivered is delivered again after a restart. -/
theorem fb_twice : ∃ st, Reach [5] 3 1 st ∧ st.count 5 = 2 := by
  have r1 := Reach.step (Reach.init (Subs := [5]) (F := 3) (R := 1))
    (Step.flip init (0, 1) (by simp [IsLink]) (by simp [init]))
  have r2 := Reach.step r1 (Step.flip _ (0, 2) (by simp [IsLink]) (by simp [flipSt, init]))
  have r3 := Reach.step r2 (Step.publish _ (by simp [flipSt, init]))
  have r4 := Reach.step r3 (Step.fallback _ 5 (by simp) (by simp [flipSt, init]))
  have r5 := Reach.step r4 (Step.restart _ 5 (by simp) (by simp [fallbackSt, flipSt, init]))
  have r6 := Reach.step r5 (Step.flip _ (0, 1) (by simp [IsLink]) (by simp [restartSt, fallbackSt, flipSt, init]))
  have r7 := Reach.step r6 (Step.pubToHub _ 1 (Or.inl rfl) (fun _ => false)
    (by simp [flipSt, restartSt, fallbackSt, init]))
  have r8 := Reach.step r7 (Step.repair _ 5 (by simp)
    (by simp [pubStep, flipSt, restartSt, fallbackSt, init]))
  exact ⟨_, r8, by decide +kernel⟩

/-! ## Liveness under weak fairness -/

/-- A run: it starts at `init` and each step is a step of the system or a stutter. -/
def Exec (Subs : List Nat) (F R : Nat) (e : Nat → St) : Prop :=
  e 0 = init ∧ ∀ n, Step Subs F R (e n) (e (n + 1)) ∨ e (n + 1) = e n

/-- An action (a set of steps). -/
abbrev Act := St → St → Prop

/-- `A` has a step that changes the state (`ENABLED <A>_vars`). -/
def EnCh (A : Act) (s : St) : Prop := ∃ s', A s s' ∧ s' ≠ s

/-- Weak fairness of `A` on the run `e`: if `A` can change the state at every instant from `n` on, it does at some
instant from `n` on. -/
def WF (A : Act) (e : Nat → St) : Prop :=
  ∀ n, (∀ m, n ≤ m → EnCh A (e m)) → ∃ m, n ≤ m ∧ A (e m) (e (m + 1)) ∧ e (m + 1) ≠ e m

def aPublish : Act := fun s s' => s.pubd = false ∧ s' = {s with pubd := true}
def aPubToHub (Subs : List Nat) : Act := fun s s' =>
  ∃ h push, (h = 1 ∨ h = 2) ∧ (s.pubd = true ∧ s.up 0 h = true ∧ s.hubLog h = false) ∧ s' = pubStep Subs s h push
def aFallback (Subs : List Nat) : Act := fun s s' =>
  ∃ x, x ∈ Subs ∧ (s.pubd = true ∧ s.up 0 1 = false ∧ s.up 0 2 = false ∧ s.up 0 x = true) ∧ s' = fallbackSt s x
def aRepair (Subs : List Nat) : Act := fun s s' =>
  ∃ x, x ∈ Subs ∧ (s.up x (s.primary x) = true ∧ s.hubLog (s.primary x) = true) ∧ s' = repairSt s x
def aFailover (Subs : List Nat) : Act := fun s s' =>
  ∃ x, x ∈ Subs ∧ (s.up x (s.primary x) = false ∧ s.up x (3 - s.primary x) = true) ∧ s' = failoverSt s x
def aHubAe : Act := fun s s' =>
  ∃ h, (h = 1 ∨ h = 2) ∧ (s.up 1 2 = true ∧ s.hubLog h = true ∧ s.hubLog (3 - h) = false) ∧ s' = hubAeSt s h

theorem exec_reach {Subs : List Nat} {F R : Nat} {e : Nat → St} (he : Exec Subs F R e) (n : Nat) :
    Reach Subs F R (e n) := by
  induction n with
  | zero => rw [he.1]; exact Reach.init
  | succ n ih =>
    rcases he.2 n with h | h
    · exact Reach.step ih h
    · rw [h]; exact ih

/-- What every step keeps: the publication, the logs, the counts; and a subscriber's primary changes only by a
failover from a hub it cannot reach. -/
theorem step_facts {Subs : List Nat} {F R : Nat} {st st' : St} (hs : Step Subs F R st st') :
    (st.pubd = true → st'.pubd = true) ∧ (∀ h, st.hubLog h = true → st'.hubLog h = true) ∧
    (∀ s, st.count s ≤ st'.count s) ∧
    (∀ s, st'.primary s = st.primary s ∨ (st.up s (st.primary s) = false ∧ st'.primary s = 3 - st.primary s)) := by
  cases hs <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [pubStep, fallbackSt, repairSt, failoverSt, hubAeSt, restartSt, flipSt, offC, fresh] <;> grind

theorem len_filter_le (l : List Nat) (p q : Nat → Bool) (h : ∀ x ∈ l, q x = true → p x = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    simp only [List.filter_cons]
    cases hq : q a <;> cases hp : p a <;> simp_all <;> omega

theorem len_filter_lt (l : List Nat) (p q : Nat → Bool) (h : ∀ x ∈ l, q x = true → p x = true) (x : Nat)
    (hx : x ∈ l) (hp : p x = true) (hq : q x = false) : (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    have hl := len_filter_le l p q (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have ha := h a (List.mem_cons_self ..)
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [hp, hq]; omega
    · have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hx'
      cases hq' : q a <;> cases hp' : p a <;> simp_all <;> omega

/-- The ranking argument of weak fairness: while the measure is positive the fair action is enabled, and each of
its changing steps lowers it, so it reaches zero. -/
theorem rank_progress {Subs : List Nat} {F R : Nat} (e : Nat → St)
    (hexec : ∀ n, Step Subs F R (e n) (e (n + 1)) ∨ e (n + 1) = e n) (C : St → Prop) (μ : St → Nat) (A : Act)
    (hwf : WF A e) (n0 : Nat) (hC : ∀ m, n0 ≤ m → C (e m))
    (hmono : ∀ s s', C s → Step Subs F R s s' → μ s' ≤ μ s)
    (hen : ∀ s, C s → 0 < μ s → EnCh A s)
    (hdec : ∀ s s', C s → 0 < μ s → A s s' → s' ≠ s → μ s' < μ s) :
    ∃ m, n0 ≤ m ∧ μ (e m) = 0 := by
  refine Classical.byContradiction fun hne => ?_
  have hpos : ∀ m, n0 ≤ m → 0 < μ (e m) := fun m hm =>
    Nat.pos_of_ne_zero fun h => hne ⟨m, hm, h⟩
  have hnon : ∀ m, n0 ≤ m → μ (e (m + 1)) ≤ μ (e m) := by
    intro m hm
    rcases hexec m with h | h
    · exact hmono _ _ (hC m hm) h
    · rw [h]; exact Nat.le_refl _
  have key : ∀ k n, n0 ≤ n → μ (e n) ≤ k → False := by
    intro k
    induction k with
    | zero => intro n hn h; have := hpos n hn; omega
    | succ k ih =>
      intro n hn h
      refine Classical.byContradiction fun _ => ?_
      by_cases hk : ∃ m, n ≤ m ∧ μ (e m) ≤ k
      · obtain ⟨m, hm, hmk⟩ := hk
        exact ih m (Nat.le_trans hn hm) hmk
      · have hall' : ∀ d, μ (e (n + d)) = k + 1 := by
          intro d
          induction d with
          | zero =>
            have : ¬ μ (e n) ≤ k := fun h' => hk ⟨n, Nat.le_refl _, h'⟩
            simp only [Nat.add_zero]; omega
          | succ d ih2 =>
            have h1 := hnon (n + d) (by omega)
            have : ¬ μ (e (n + d + 1)) ≤ k := fun h' => hk ⟨n + d + 1, by omega, h'⟩
            rw [← Nat.add_assoc]
            omega
        have hall : ∀ m, n ≤ m → μ (e m) = k + 1 := by
          intro m hm
          have := hall' (m - n)
          rwa [show n + (m - n) = m by omega] at this
        obtain ⟨m, hm, ham, hch⟩ := hwf n (fun m hm => hen _ (hC m (Nat.le_trans hn hm |> fun h => by omega))
          (hpos m (by omega)))
        have := hdec _ _ (hC m (by omega)) (hpos m (by omega)) ham hch
        have h2 := hall (m + 1) (by omega)
        have h3 := hall m hm
        omega
  exact key _ n0 (Nat.le_refl _) (Nat.le_refl _)

/-- Without restarts: no floor is ever set, and a counted delivery is a delivery of the (only) life. -/
def Inv0 (st : St) : Prop := ∀ s, st.floor s = false ∧ (1 ≤ st.count s → st.deliv s = true)

theorem inv0_init : Inv0 init := fun s => by simp [init]

theorem inv0_step {Subs : List Nat} {F : Nat} {st st' : St} (hi : Inv0 st) (hs : Step Subs F 0 st st') :
    Inv0 st' := by
  cases hs with
  | restart s hs g => exact absurd g (Nat.not_lt_zero _)
  | _ =>
    intro x
    have := hi x
    refine ⟨?_, ?_⟩ <;> intros <;>
    simp_all [pubStep, fallbackSt, repairSt, failoverSt, hubAeSt, flipSt, offD, offC, fresh] <;> grind

theorem reach_inv0 {Subs : List Nat} {F : Nat} {st : St} (r : Reach Subs F 0 st) : Inv0 st := by
  induction r with
  | init => exact inv0_init
  | step _ hs ih => exact inv0_step ih hs

/-- The number of subscribers that have not heard the message. -/
def zeros (Subs : List Nat) (st : St) : Nat := (Subs.filter fun s => st.count s == 0).length

theorem zeros_mono {Subs : List Nat} {F R : Nat} {st st' : St} (hs : Step Subs F R st st') :
    zeros Subs st' ≤ zeros Subs st := by
  have hf := (step_facts hs).2.2.1
  exact len_filter_le Subs _ _ (fun x _ hx => by
    have := hf x
    simp only [beq_iff_eq] at hx ⊢; omega)

theorem exists_zero {Subs : List Nat} {st : St} (h : 0 < zeros Subs st) : ∃ x ∈ Subs, st.count x = 0 := by
  refine Classical.byContradiction fun hn => ?_
  have : Subs.filter (fun s => st.count s == 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hb
    exact hn ⟨a, ha, by simpa using hb⟩
  unfold zeros at h; rw [this] at h; exact Nat.lt_irrefl _ h

/-- An offer to a subscriber that already heard the message changes nothing (without restarts). -/
theorem offer_noop {st : St} (hv : Inv st) (h0 : Inv0 st) (x : Nat) (hc : 1 ≤ st.count x) :
    repairSt st x = st ∧ fallbackSt st x = st := by
  have hd := (h0 x).2 hc
  have hf := (h0 x).1
  have hfr : fresh st x = false := by simp [fresh, hd]
  have eD : offD st x = st.deliv := by
    funext y; unfold offD; split
    · rename_i e; subst e; simp [hd]
    · rfl
  have eC : offC st x = st.count := by
    funext y; unfold offC; simp [hfr]
  constructor
  · cases st
    simp_all [repairSt]
  · cases st
    simp_all [fallbackSt]
    funext a; split <;> simp_all

theorem offer_zero {st : St} (hv : Inv st) (x : Nat) (hc : st.count x = 0) (hd : st.deliv x = false)
    (hf : st.floor x = false) : (repairSt st x).count x = 1 ∧ (fallbackSt st x).count x = 1 := by
  simp [repairSt, fallbackSt, offC, fresh, hd, hf, hc]

theorem count_other (st : St) (x y : Nat) (h : y ≠ x) :
    (repairSt st x).count y = st.count y ∧ (fallbackSt st x).count y = st.count y := by
  simp [repairSt, fallbackSt, offC, h]

/-- A changing repair or fallback step on a state with a subscriber still waiting lowers `zeros`. -/
theorem zeros_dec {Subs : List Nat} {F : Nat} {st st' : St} (r : Reach Subs F 0 st) (x : Nat) (hx : x ∈ Subs)
    (h' : st' = repairSt st x ∨ st' = fallbackSt st x) (hne : st' ≠ st) : zeros Subs st' < zeros Subs st := by
  have hv := reach_inv r
  have h0 := reach_inv0 r
  by_cases hc : 1 ≤ st.count x
  · exfalso
    obtain ⟨e1, e2⟩ := offer_noop hv h0 x hc
    rcases h' with rfl | rfl
    · exact hne e1
    · exact hne e2
  · have hc0 : st.count x = 0 := by omega
    have hd : st.deliv x = false := by
      refine Classical.byContradiction fun hh => ?_
      have := hv.delivCount x (by simpa using hh); omega
    have hf := (h0 x).1
    obtain ⟨o1, o2⟩ := offer_zero hv x hc0 hd hf
    unfold zeros
    apply len_filter_lt Subs _ _ _ x hx (by simpa using hc0)
    · rcases h' with rfl | rfl
      · simp [o1]
      · simp [o2]
    · intro y _ hy
      simp only [beq_iff_eq] at hy ⊢
      rcases h' with rfl | rfl
      · by_cases hyx : y = x
        · subst hyx; omega
        · rw [(count_other st x y hyx).1] at hy; exact hy
      · by_cases hyx : y = x
        · subst hyx; omega
        · rw [(count_other st x y hyx).2] at hy; exact hy

theorem zeros_zero {Subs : List Nat} {st : St} (h : zeros Subs st = 0) : ∀ x ∈ Subs, 1 ≤ st.count x := by
  intro x hx
  refine Classical.byContradiction fun hn => ?_
  have h0 : st.count x = 0 := by omega
  have : 0 < zeros Subs st := by
    unfold zeros
    exact List.length_pos_iff.2 (fun he => by
      have := (List.filter_eq_nil_iff.1 he) x hx
      simp [h0] at this)
  omega

theorem stays {Subs : List Nat} {F R : Nat} {e : Nat → St} (hexec : ∀ n, Step Subs F R (e n) (e (n + 1)) ∨ e (n + 1) = e n)
    (P : St → Prop) (hstep : ∀ s s', Step Subs F R s s' → P s → P s') (m1 : Nat) (h : P (e m1)) :
    ∀ m, m1 ≤ m → P (e m) := by
  have : ∀ d, P (e (m1 + d)) := by
    intro d
    induction d with
    | zero => simpa using h
    | succ d ih =>
      rcases hexec (m1 + d) with hs | hs
      · rw [← Nat.add_assoc]; exact hstep _ _ hs ih
      · rw [← Nat.add_assoc, hs]; exact ih
  intro m hm
  have := this (m - m1)
  rwa [show m1 + (m - m1) = m by omega] at this

theorem enCh_offer {Subs : List Nat} {F : Nat} {s : St} (r : Reach Subs F 0 s) (x : Nat) (hc : s.count x = 0) :
    repairSt s x ≠ s ∧ fallbackSt s x ≠ s := by
  have hv := reach_inv r
  have h0 := reach_inv0 r
  have hd : s.deliv x = false := by
    refine Classical.byContradiction fun hh => ?_
    have := hv.delivCount x (by simpa using hh); omega
  obtain ⟨o1, o2⟩ := offer_zero hv x hc hd (h0 x).1
  exact ⟨fun h => by rw [h] at o1; omega, fun h => by rw [h] at o2; omega⟩

/-- Stage of every liveness proof: once the message is published and the step `A` is enabled for a subscriber that
has not heard it, weak fairness of `A` brings it to every subscriber. -/
theorem all_heard {Subs : List Nat} {F : Nat} (e : Nat → St) (he : Exec Subs F 0 e) (A : Act)
    (hA : ∀ s s', A s s' → ∃ x ∈ Subs, s' = repairSt s x ∨ s' = fallbackSt s x)
    (C : St → Prop) (hwf : WF A e) (n0 : Nat) (hC : ∀ m, n0 ≤ m → C (e m))
    (hen : ∀ s, Reach Subs F 0 s → C s → ∀ x ∈ Subs, s.count x = 0 → EnCh A s) :
    ∃ m, ∀ x ∈ Subs, 1 ≤ (e m).count x := by
  obtain ⟨m, _, hm⟩ := rank_progress (R := 0) e he.2 (fun s => Reach Subs F 0 s ∧ C s) (zeros Subs) A hwf n0
    (fun m hm => ⟨exec_reach he m, hC m hm⟩) (fun _ _ _ hs => zeros_mono hs)
    (fun s hCs hpos => by
      obtain ⟨x, hx, hx0⟩ := exists_zero hpos
      exact hen s hCs.1 hCs.2 x hx hx0)
    (fun s s' hCs hpos hA' hne => by
      obtain ⟨x, hx, h⟩ := hA s s' hA'
      exact zeros_dec hCs.1 x hx h hne)
  exact ⟨m, zeros_zero hm⟩

/-- Every link of the system is up. -/
def Stable (Subs : List Nat) (st : St) : Prop := ∀ l, IsLink Subs l → st.up l.1 l.2 = true

/-- The late publish: the publisher and every subscriber are cut off from both hubs but reach each other. -/
def LateCond (Subs : List Nat) (st : St) : Prop :=
  st.up 0 1 = false ∧ st.up 0 2 = false ∧ ∀ s ∈ Subs, st.up s 1 = false ∧ st.up s 2 = false ∧ st.up 0 s = true

/-- The primary hub lost for good, everything else up. -/
def FailCond (Subs : List Nat) (st : St) : Prop :=
  ∀ l, IsLink Subs l → (st.up l.1 l.2 = true ↔ (l.1 ≠ 1 ∧ l.2 ≠ 1))

/-- The first publication: weak fairness of `publish` publishes. -/
theorem publishes {Subs : List Nat} {F R : Nat} (e : Nat → St) (hexec : ∀ n, Step Subs F R (e n) (e (n + 1)) ∨ e (n + 1) = e n)
    (wf : WF aPublish e) (n0 : Nat) : ∃ m, n0 ≤ m ∧ (e m).pubd = true := by
  obtain ⟨m, hm, h⟩ := rank_progress e hexec (fun _ => True) (fun s => if s.pubd = true then 0 else 1) aPublish wf n0
    (fun _ _ => trivial)
    (fun s s' _ hs => by
      have := (step_facts hs).1
      by_cases h : s.pubd = true <;> by_cases h' : s'.pubd = true <;> simp_all)
    (fun s _ hpos => by
      have h : s.pubd = false := by
        by_cases h : s.pubd = true
        · simp [h] at hpos
        · simpa using h
      exact ⟨{s with pubd := true}, ⟨h, rfl⟩, fun heq => by have := congrArg St.pubd heq; simp [h] at this⟩)
    (fun s s' _ hpos ha _ => by
      obtain ⟨h, rfl⟩ := ha
      simp [h])
  refine ⟨m, hm, ?_⟩
  by_cases hp : (e m).pubd = true
  · exact hp
  · simp [hp] at h

theorem churn_heals {Subs : List Nat} {F : Nat} {e : Nat → St} (he : Exec Subs F 0 e)
    (wfPub : WF aPublish e) (wfHub : WF (aPubToHub Subs) e) (wfAe : WF aHubAe e) (wfRep : WF (aRepair Subs) e)
    (stable : ∃ n0, ∀ m, n0 ≤ m → Stable Subs (e m)) : ∃ m, ∀ x ∈ Subs, 1 ≤ (e m).count x := by
  obtain ⟨n0, hst⟩ := stable
  obtain ⟨m1, hm1, hp1⟩ := publishes e he.2 wfPub n0
  have pub : ∀ m, m1 ≤ m → (e m).pubd = true :=
    stays he.2 (fun s => s.pubd = true) (fun s s' hs h => (step_facts hs).1 h) m1 hp1
  -- some hub logs the message
  obtain ⟨m2, hm2, h2⟩ := rank_progress e he.2 (fun s => Stable Subs s ∧ s.pubd = true)
    (fun s => if s.hubLog 1 = true ∨ s.hubLog 2 = true then 0 else 1) (aPubToHub Subs) wfHub m1
    (fun m hm => ⟨hst m (by omega), pub m hm⟩)
    (fun s s' _ hs => by
      have := (step_facts hs).2.1
      by_cases h : s.hubLog 1 = true ∨ s.hubLog 2 = true
      · rcases h with h | h
        · simp [h, this 1 h]
        · simp [h, this 2 h]
      · simp only [h, if_false]; split <;> omega)
    (fun s hC hpos => by
      have h : s.hubLog 1 = false := by
        by_cases h : s.hubLog 1 = true ∨ s.hubLog 2 = true
        · simp [h] at hpos
        · simp only [not_or] at h; simpa using h.1
      refine ⟨pubStep Subs s 1 (fun _ => false), ⟨1, fun _ => false, Or.inl rfl,
        ⟨hC.2, hC.1 (0, 1) (by simp [IsLink]), h⟩, rfl⟩, fun heq => ?_⟩
      have := congrArg (fun t => t.hubLog 1) heq
      simp [pubStep, h] at this)
    (fun s s' _ hpos ha _ => by
      obtain ⟨h, push, hh, g, rfl⟩ := ha
      have : (pubStep Subs s h push).hubLog h = true := by simp [pubStep]
      rcases hh with rfl | rfl <;> simp [this] <;> exact hpos)
  have logged : (e m2).hubLog 1 = true ∨ (e m2).hubLog 2 = true := by
    by_cases hh : (e m2).hubLog 1 = true ∨ (e m2).hubLog 2 = true
    · exact hh
    · simp [hh] at h2
  have log1 : ∀ m, m2 ≤ m → (e m).hubLog 1 = true ∨ (e m).hubLog 2 = true :=
    stays he.2 (fun s => s.hubLog 1 = true ∨ s.hubLog 2 = true)
      (fun s s' hs h => by
        have := (step_facts hs).2.1
        rcases h with h | h
        · exact Or.inl (this 1 h)
        · exact Or.inr (this 2 h)) m2 logged
  -- both hubs log it
  obtain ⟨m3, hm3, h3⟩ := rank_progress e he.2
    (fun s => Stable Subs s ∧ (s.hubLog 1 = true ∨ s.hubLog 2 = true))
    (fun s => (if s.hubLog 1 = true then 0 else 1) + (if s.hubLog 2 = true then 0 else 1)) aHubAe wfAe m2
    (fun m hm => ⟨hst m (by omega), log1 m hm⟩)
    (fun s s' _ hs => by
      have := (step_facts hs).2.1
      by_cases a1 : s.hubLog 1 = true <;> by_cases a2 : s.hubLog 2 = true <;> by_cases b1 : s'.hubLog 1 = true <;>
        by_cases b2 : s'.hubLog 2 = true <;> simp_all)
    (fun s hC hpos => by
      have hl : (s.hubLog 1 = true ∧ s.hubLog 2 = false) ∨ (s.hubLog 1 = false ∧ s.hubLog 2 = true) := by
        rcases hC.2 with h | h <;> by_cases a : s.hubLog 1 = true <;> by_cases b : s.hubLog 2 = true <;>
          simp_all
      have u := hC.1 (1, 2) (by simp [IsLink])
      rcases hl with ⟨a, b⟩ | ⟨a, b⟩
      · refine ⟨hubAeSt s 1, ⟨1, Or.inl rfl, ⟨u, a, b⟩, rfl⟩, fun heq => ?_⟩
        have := congrArg (fun t => t.hubLog 2) heq
        simp [hubAeSt, b] at this
      · refine ⟨hubAeSt s 2, ⟨2, Or.inr rfl, ⟨u, b, a⟩, rfl⟩, fun heq => ?_⟩
        have := congrArg (fun t => t.hubLog 1) heq
        simp [hubAeSt, a] at this)
    (fun s s' hC hpos ha _ => by
      obtain ⟨h, hh, g, rfl⟩ := ha
      rcases hh with rfl | rfl
      · simp [hubAeSt] at *; simp_all
      · simp [hubAeSt] at *; simp_all)
  have both : (e m3).hubLog 1 = true ∧ (e m3).hubLog 2 = true := by
    by_cases a1 : (e m3).hubLog 1 = true <;> by_cases a2 : (e m3).hubLog 2 = true <;> simp_all
  have both' : ∀ m, m3 ≤ m → (e m).hubLog 1 = true ∧ (e m).hubLog 2 = true :=
    stays he.2 (fun s => s.hubLog 1 = true ∧ s.hubLog 2 = true)
      (fun s s' hs h => ⟨(step_facts hs).2.1 1 h.1, (step_facts hs).2.1 2 h.2⟩) m3 both
  refine all_heard e he (aRepair Subs) (fun s s' ⟨x, hx, _, h⟩ => ⟨x, hx, Or.inl h⟩)
    (fun s => Stable Subs s ∧ s.hubLog 1 = true ∧ s.hubLog 2 = true) wfRep m3
    (fun m hm => ⟨hst m (by omega), (both' m hm).1, (both' m hm).2⟩) ?_
  intro s hr hC x hx hx0
  have hp := (reach_inv hr).primHub x
  have hl : IsLink Subs (x, s.primary x) := Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, s.primary x, hp, rfl⟩)))
  refine ⟨repairSt s x, ⟨x, hx, ⟨hC.1 _ hl, ?_⟩, rfl⟩, (enCh_offer hr x hx0).1⟩
  rcases hp with h | h <;> rw [h] <;> simp [hC.2]

/-- The late publish: with the publisher and every subscriber cut off from both hubs for good, the fallback brings
the message to every subscriber. -/
theorem late_live {Subs : List Nat} {F : Nat} {e : Nat → St} (he : Exec Subs F 0 e) (wfPub : WF aPublish e)
    (wfFb : WF (aFallback Subs) e) (hlate : ∀ n, LateCond Subs (e n)) : ∃ m, ∀ x ∈ Subs, 1 ≤ (e m).count x := by
  obtain ⟨m1, _, hp1⟩ := publishes e he.2 wfPub 0
  have pub : ∀ m, m1 ≤ m → (e m).pubd = true :=
    stays he.2 (fun s => s.pubd = true) (fun s s' hs h => (step_facts hs).1 h) m1 hp1
  refine all_heard e he (aFallback Subs) (fun s s' ⟨x, hx, _, h⟩ => ⟨x, hx, Or.inr h⟩)
    (fun s => s.pubd = true ∧ LateCond Subs s) wfFb m1 (fun m hm => ⟨pub m hm, hlate m⟩) ?_
  intro s hr hC x hx hx0
  exact ⟨fallbackSt s x, ⟨x, hx, ⟨hC.1, hC.2.1, hC.2.2.1, (hC.2.2.2 x hx).2.2⟩, rfl⟩, (enCh_offer hr x hx0).2⟩

theorem stays2 {Subs : List Nat} {F R : Nat} {e : Nat → St}
    (hexec : ∀ n, Step Subs F R (e n) (e (n + 1)) ∨ e (n + 1) = e n) (Q P : St → Prop) (hQ : ∀ n, Q (e n))
    (hstep : ∀ s s', Q s → Step Subs F R s s' → P s → P s') (m1 : Nat) (h : P (e m1)) :
    ∀ m, m1 ≤ m → P (e m) := by
  have : ∀ d, P (e (m1 + d)) := by
    intro d
    induction d with
    | zero => simpa using h
    | succ d ih =>
      rcases hexec (m1 + d) with hs | hs
      · rw [← Nat.add_assoc]; exact hstep _ _ (hQ _) hs ih
      · rw [← Nat.add_assoc, hs]; exact ih
  intro m hm
  have := this (m - m1)
  rwa [show m1 + (m - m1) = m by omega] at this

/-- Hub failover: with the primary hub lost for good and the other hub up, every subscriber moves to the other hub
and has the message. -/
theorem failover_delivers {Subs : List Nat} {F : Nat} {e : Nat → St} (hSubs : ∀ s ∈ Subs, 3 ≤ s)
    (he : Exec Subs F 0 e) (wfPub : WF aPublish e) (wfHub : WF (aPubToHub Subs) e) (wfFo : WF (aFailover Subs) e)
    (wfRep : WF (aRepair Subs) e) (hfail : ∀ n, FailCond Subs (e n)) : ∃ m, ∀ x ∈ Subs, 1 ≤ (e m).count x := by
  obtain ⟨m1, _, hp1⟩ := publishes e he.2 wfPub 0
  have pub : ∀ m, m1 ≤ m → (e m).pubd = true :=
    stays he.2 (fun s => s.pubd = true) (fun s s' hs h => (step_facts hs).1 h) m1 hp1
  have up02 : ∀ s, FailCond Subs s → s.up 0 2 = true := fun s h => (h (0, 2) (by simp [IsLink])).2 (by simp)
  have dn01 : ∀ s, FailCond Subs s → s.up 0 1 = false := fun s h => by
    have := h (0, 1) (by simp [IsLink]); simpa using this
  -- the message reaches hub 2
  obtain ⟨m2, hm2, h2⟩ := rank_progress e he.2 (fun s => FailCond Subs s ∧ s.pubd = true)
    (fun s => if s.hubLog 2 = true then 0 else 1) (aPubToHub Subs) wfHub m1
    (fun m hm => ⟨hfail m, pub m hm⟩)
    (fun s s' _ hs => by
      have := (step_facts hs).2.1 2
      by_cases a : s.hubLog 2 = true <;> by_cases b : s'.hubLog 2 = true <;> simp_all)
    (fun s hC hpos => by
      have h : s.hubLog 2 = false := by
        by_cases h : s.hubLog 2 = true
        · simp [h] at hpos
        · simpa using h
      refine ⟨pubStep Subs s 2 (fun _ => false), ⟨2, fun _ => false, Or.inr rfl, ⟨hC.2, up02 s hC.1, h⟩, rfl⟩,
        fun heq => ?_⟩
      have := congrArg (fun t => t.hubLog 2) heq
      simp [pubStep, h] at this)
    (fun s s' hC hpos ha _ => by
      obtain ⟨h, push, hh, g, rfl⟩ := ha
      rcases hh with rfl | rfl
      · exact absurd g.2.1 (by rw [dn01 s hC.1]; simp)
      · simp [pubStep]; exact hpos)
  have log2 : (e m2).hubLog 2 = true := by
    by_cases a : (e m2).hubLog 2 = true
    · exact a
    · simp [a] at h2
  have log2' : ∀ m, m2 ≤ m → (e m).hubLog 2 = true :=
    stays he.2 (fun s => s.hubLog 2 = true) (fun s s' hs h => (step_facts hs).2.1 2 h) m2 log2
  -- every subscriber moves to hub 2
  obtain ⟨m3, hm3, h3⟩ := rank_progress e he.2 (fun s => Reach Subs F 0 s ∧ FailCond Subs s)
    (fun s => (Subs.filter fun x => s.primary x == 1).length) (aFailover Subs) wfFo m2
    (fun m hm => ⟨exec_reach he m, hfail m⟩)
    (fun s s' hC hs => by
      have hf := (step_facts hs).2.2.2
      apply len_filter_le
      intro x hx hq
      simp only [beq_iff_eq] at hq ⊢
      rcases hf x with h | ⟨h1, h2⟩
      · rw [← h]; exact hq
      · have hp := (reach_inv hC.1).primHub x
        rcases hp with hp | hp
        · exact hp
        · exfalso
          rw [hp] at h1
          have := (hC.2 (x, 2) (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, 2, Or.inr rfl, rfl⟩))))).2
            ⟨by have := hSubs x hx; omega, by omega⟩
          simp at this; rw [this] at h1; cases h1)
    (fun s hC hpos => by
      obtain ⟨x, hx, hx1⟩ : ∃ x ∈ Subs, s.primary x = 1 := by
        refine Classical.byContradiction fun hn => ?_
        have : Subs.filter (fun x => s.primary x == 1) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha hb
          exact hn ⟨a, ha, by simpa using hb⟩
        rw [this] at hpos; exact Nat.lt_irrefl _ hpos
      have u1 := (hC.2 (x, 1) (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, 1, Or.inl rfl, rfl⟩)))))
      have u2 := (hC.2 (x, 2) (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, 2, Or.inr rfl, rfl⟩)))))
      have hx3 := hSubs x hx
      refine ⟨failoverSt s x, ⟨x, hx, ⟨?_, ?_⟩, rfl⟩, fun heq => ?_⟩
      · rw [hx1]; cases hh : s.up x 1
        · rfl
        · have := u1.1 hh; simp at this
      · rw [hx1]; exact u2.2 ⟨by omega, by omega⟩
      · have := congrArg (fun t => t.primary x) heq
        simp [failoverSt, hx1] at this)
    (fun s s' hC hpos ha hne => by
      obtain ⟨x, hx, g, rfl⟩ := ha
      have hp := (reach_inv hC.1).primHub x
      have hx3 := hSubs x hx
      have u2 := (hC.2 (x, 2) (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, 2, Or.inr rfl, rfl⟩))))).2 ⟨by omega, by omega⟩
      have hx1 : s.primary x = 1 := by
        rcases hp with hp | hp
        · exact hp
        · rw [hp] at g; rw [g.1] at u2; cases u2
      apply len_filter_lt Subs _ _ _ x hx (by simpa using hx1) (by simp [failoverSt, hx1])
      intro y _ hy
      simp only [beq_iff_eq] at hy ⊢
      by_cases hyx : y = x
      · subst hyx; simp [failoverSt, hx1] at hy
      · simpa [failoverSt, hyx] using hy)
  have prim2 : ∀ x ∈ Subs, (e m3).primary x = 2 := by
    intro x hx
    have hz : ((Subs.filter fun x => (e m3).primary x == 1)).length = 0 := h3
    have : x ∉ Subs.filter (fun x => (e m3).primary x == 1) := by
      intro hm
      have := List.length_pos_iff.2 (List.ne_nil_of_mem hm)
      omega
    have hne : ¬ (e m3).primary x = 1 := fun h => this (List.mem_filter.2 ⟨hx, by simpa using h⟩)
    rcases (reach_inv (exec_reach he m3)).primHub x with h | h
    · exact absurd h hne
    · exact h
  have prim2' : ∀ m, m3 ≤ m → ∀ x ∈ Subs, (e m).primary x = 2 :=
    stays2 he.2 (fun s => FailCond Subs s) (fun s => ∀ x ∈ Subs, s.primary x = 2) hfail
      (fun s s' hQ hs hP => by
        intro x hx
        have hf := (step_facts hs).2.2.2 x
        rcases hf with h | ⟨h1, h2⟩
        · rw [h]; exact hP x hx
        · rw [hP x hx] at h1
          have := (hQ (x, 2) (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, 2, Or.inr rfl, rfl⟩))))).2
            ⟨by have := hSubs x hx; omega, by omega⟩
          rw [this] at h1; cases h1) m3 prim2
  refine all_heard e he (aRepair Subs) (fun s s' ⟨x, hx, _, h⟩ => ⟨x, hx, Or.inl h⟩)
    (fun s => FailCond Subs s ∧ s.hubLog 2 = true ∧ ∀ x ∈ Subs, s.primary x = 2) wfRep m3
    (fun m hm => ⟨hfail m, log2' m (by omega), prim2' m hm⟩) ?_
  intro s hr hC x hx hx0
  have hx3 := hSubs x hx
  refine ⟨repairSt s x, ⟨x, hx, ⟨?_, ?_⟩, rfl⟩, (enCh_offer hr x hx0).1⟩
  · rw [hC.2.2 x hx]
    exact (hC.1 (x, 2) (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, 2, Or.inr rfl, rfl⟩))))).2 ⟨by omega, by omega⟩
  · rw [hC.2.2 x hx]; exact hC.2.1

#audit_axioms Vinc.BroadcastSystem.reach_inv
#audit_axioms Vinc.BroadcastSystem.atMostOnce
#audit_axioms Vinc.BroadcastSystem.floorsCover
#audit_axioms Vinc.BroadcastSystem.restart_floor
#audit_axioms Vinc.BroadcastSystem.fb_twice
#audit_axioms Vinc.BroadcastSystem.late_live
#audit_axioms Vinc.BroadcastSystem.churn_heals
#audit_axioms Vinc.BroadcastSystem.failover_delivers

end Vinc.BroadcastSystem
