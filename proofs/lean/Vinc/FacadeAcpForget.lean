import Vinc.Axioms

/-!
# The facade's revoke, unrevoke and hook changes against the endpoint's answer cache

The story, in plain words. Peers dial this node. The endpoint decides each session from the answer it cached for the
peer; with none cached it asks the gate (no for a revoked peer, else the application's hook) and caches that answer
for 30 s. This node dials peers too. The application revokes peers, lifts revocations, and edits its hook (an
allowlist). The fix: revoke, unrevoke and `admission_changed` drop the peer's cached answer, so the next session of
that peer is decided by the gate as it stands now, and a dial to a revoked peer is refused before anything is sent.

What must never happen: a session decided on an answer the gate would not give at that moment, such as a deny cached
while the peer was revoked or unlisted refusing it after the lift or the listing (the bug), or an allow cached before
a revoke letting it in after; a cached answer that is not the gate's current one; a revoked peer holding a session this
node dialed.

This is a transcription of `proofs/tla/FacadeAcpForget.tla` over any number of peers and steps. The Rust code is
`crates/vinc-core/src/commands.rs` (`Command::AcpForget`), `crates/vinc-core/src/acp.rs` (`start_acp`, `acp_cached`,
`acp_answer`), `crates/vinc-node/src/node.rs` (`Node::{revoke, unrevoke, forget_access}`),
`crates/vinc/src/engine/ops.rs` (`Core::{revoke, unrevoke, forget_access}`) and `crates/vinc/src/endpoint.rs`
(`Endpoint::{revoke, unrevoke, connect, admission_changed}`).

Main theorems: `inv_reach` (with the code's settings every reachable state keeps the three promises),
`noForgetOnLift_bad` (the code before the fix refuses an unrevoked peer on a stale deny), `noForgetOnRevoke_bad`
(keeping the answer across a revoke lets a revoked peer through on a stale allow), `noRefuseDial_bad` (a dial to a
revoked peer reaches it) and `noForgetOnChange_bad` (a host that lists a peer without telling the endpoint has it
refused on a stale deny).
-/

namespace Vinc.FacadeAcpForget

-- The endpoint's cached answer for a peer: nothing, allow or deny.
inductive Ans where
  | none
  | allow
  | deny
  deriving DecidableEq, Repr

-- A cached answer as a yes or no: only allow lets in.
def asBool : Ans → Bool
  | .allow => true
  | _ => false

-- The cache entry that records the gate's answer `b`.
def cacheOf (b : Bool) : Ans := if b then .allow else .deny

-- Reading back an answer recorded with `cacheOf` gives the answer.
theorem asBool_cacheOf (b : Bool) : asBool (cacheOf b) = b := by cases b <;> rfl

-- The last decision: whether one happened, about whom, what the session got, and what the gate said then.
structure Last where
  done : Bool
  peer : Nat
  ans : Bool
  gate : Bool

-- What does not change: the hook's first answers, and the four switches that give the witnesses.
structure Cfg where
  allowed : Nat → Bool
  forgetOnLift : Bool
  forgetOnRevoke : Bool
  refuseDial : Bool
  forgetOnChange : Bool

-- The state: the hook's answers now, which peers are revoked, the cache, the last decision, and which peers hold a
-- session we dialed.
structure State where
  allowed : Nat → Bool
  revoked : Nat → Bool
  cache : Nat → Ans
  last : Last
  out : Nat → Bool

-- Change one entry of a function.
def set {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

-- The changed entry reads back the new value.
theorem set_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : set f i v i = v := by simp [set]

-- Every other entry is unchanged.
theorem set_other {α : Type} (f : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) : set f i v j = f j := by
  simp [set, h]

-- The gate, for the hook's answers `a` and the revoked set `r`: no for a revoked peer, else the hook's answer.
def gate (a r : Nat → Bool) (p : Nat) : Bool := !r p && a p

-- The start: the hook's first answers, nobody revoked, nothing cached, nothing decided, nothing dialed.
def init (c : Cfg) : State := ⟨c.allowed, fun _ => false, fun _ => .none, ⟨false, 0, false, false⟩, fun _ => false⟩

-- The state after each action of the TLA+ model of the same name.
-- A session of `p` is decided on its cached answer.
def cachedS (s : State) (p : Nat) : State :=
  { s with last := ⟨true, p, asBool (s.cache p), gate s.allowed s.revoked p⟩ }
-- Nothing is cached for `p`: the gate is asked, its answer cached, and the session gets it.
def askS (s : State) (p : Nat) : State :=
  { s with cache := set s.cache p (cacheOf (gate s.allowed s.revoked p)),
           last := ⟨true, p, gate s.allowed s.revoked p, gate s.allowed s.revoked p⟩ }
-- `p` is revoked: with the fix its cached answer goes, and every session with it ends.
def revokeS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with revoked := set s.revoked p true, cache := if c.forgetOnRevoke then set s.cache p .none else s.cache,
           out := set s.out p false }
-- The revocation of `p` is lifted; with the fix its cached answer goes.
def liftS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with revoked := set s.revoked p false, cache := if c.forgetOnLift then set s.cache p .none else s.cache }
-- The cached answer of `p` lapses.
def expireS (s : State) (p : Nat) : State := { s with cache := set s.cache p .none }
-- This node dials `p`: refused up front while `p` is revoked, else the session reaches `p`.
def dialS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with out := if c.refuseDial && s.revoked p then s.out else set s.out p true }
-- A session this node dialed ends for another reason.
def hangupS (s : State) (p : Nat) : State := { s with out := set s.out p false }
-- The host edits its hook's answer for `p` and, with the fix, calls admission_changed for it.
def rehookS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with allowed := set s.allowed p (!s.allowed p),
           cache := if c.forgetOnChange then set s.cache p .none else s.cache }

-- One step of the system, with the guard of each action.
inductive Step (c : Cfg) : State → State → Prop where
  | cached (s : State) (p : Nat) : s.cache p ≠ .none → Step c s (cachedS s p)
  | ask (s : State) (p : Nat) : s.cache p = .none → Step c s (askS s p)
  | revoke (s : State) (p : Nat) : Step c s (revokeS c s p)
  | lift (s : State) (p : Nat) : Step c s (liftS c s p)
  | expire (s : State) (p : Nat) : Step c s (expireS s p)
  | dial (s : State) (p : Nat) : Step c s (dialS c s p)
  | hangup (s : State) (p : Nat) : Step c s (hangupS s p)
  | rehook (s : State) (p : Nat) : Step c s (rehookS c s p)

-- The states the system can reach from the start.
inductive Reach (c : Cfg) : State → Prop where
  | init : Reach c (init c)
  | step (s t : State) : Reach c s → Step c s t → Reach c t

-- Every session is decided with the answer the gate gives at that moment.
abbrev DecideFresh (s : State) : Prop := s.last.done = true → s.last.ans = s.last.gate

-- Every cached answer is the one the gate would give now.
abbrev CacheSound (s : State) : Prop := ∀ q, s.cache q ≠ .none → asBool (s.cache q) = gate s.allowed s.revoked q

-- No revoked peer holds a session this node dialed.
abbrev NoDialRevoked (s : State) : Prop := ∀ q, s.out q = true → s.revoked q = false

-- The three promises together.
abbrev Inv (s : State) : Prop := DecideFresh s ∧ CacheSound s ∧ NoDialRevoked s

/-- The start keeps the three promises. -/
theorem inv_init (c : Cfg) : Inv (init c) := by
  refine ⟨fun h => ?_, fun q h => ?_, fun q h => ?_⟩
  · simp [init] at h
  · simp [init] at h
  · simp [init] at h

/-- Dropping `p`'s cached answer while only `p`'s hook answer and revoked bit may change keeps every cached answer
sound: `p` has none left, and no other peer's answer or bits moved. -/
theorem forget_sound (s : State) (p : Nat) (a r : Nat → Bool) (ha : ∀ q, q ≠ p → a q = s.allowed q)
    (hr : ∀ q, q ≠ p → r q = s.revoked q) (h : CacheSound s) (q : Nat)
    (hq : set s.cache p .none q ≠ .none) : asBool (set s.cache p .none q) = gate a r q := by
  by_cases hqp : q = p
  · subst hqp; rw [set_same] at hq; exact absurd rfl hq
  · rw [set_other _ _ _ _ hqp] at hq ⊢
    unfold gate; rw [ha q hqp, hr q hqp]; exact h q hq

-- A function changed only at `p` agrees with the old one everywhere else.
theorem set_off {α : Type} (f : Nat → α) (p : Nat) (v : α) : ∀ q, q ≠ p → set f p v q = f q :=
  fun q h => set_other f p q v h

/-- With the code's settings every step keeps the three promises. -/
theorem inv_step (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true) (hd : c.refuseDial = true)
    (hh : c.forgetOnChange = true) (s t : State) (hs : Inv s) (st : Step c s t) : Inv t := by
  obtain ⟨hf, hc, ho⟩ := hs
  cases st with
  | cached p hp => exact ⟨fun _ => hc p hp, hc, ho⟩
  | ask p _ =>
    refine ⟨fun _ => rfl, fun q hq => ?_, ho⟩
    simp only [askS] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [set_same]; exact asBool_cacheOf _
    · rw [set_other _ _ _ _ hqp] at hq ⊢; exact hc q hq
  | revoke p =>
    refine ⟨hf, fun q hq => ?_, fun q hq => ?_⟩
    · simp only [revokeS, hr, ite_true] at hq ⊢
      exact forget_sound s p _ _ (fun _ _ => rfl) (set_off _ p true) hc q hq
    · simp only [revokeS] at hq ⊢
      by_cases hqp : q = p
      · subst hqp; rw [set_same] at hq; exact absurd hq (by decide)
      · rw [set_other _ _ _ _ hqp] at hq ⊢; exact ho q hq
  | lift p =>
    refine ⟨hf, fun q hq => ?_, fun q hq => ?_⟩
    · simp only [liftS, hl, ite_true] at hq ⊢
      exact forget_sound s p _ _ (fun _ _ => rfl) (set_off _ p false) hc q hq
    · simp only [liftS] at hq ⊢
      by_cases hqp : q = p
      · subst hqp; rw [set_same]
      · rw [set_other _ _ _ _ hqp]; exact ho q hq
  | expire p =>
    exact ⟨hf, fun q hq => forget_sound s p _ _ (fun _ _ => rfl) (fun _ _ => rfl) hc q hq, ho⟩
  | dial p =>
    refine ⟨hf, hc, fun q hq => ?_⟩
    simp only [dialS, hd, Bool.true_and] at hq ⊢
    cases hrv : s.revoked p with
    | true => simp [hrv] at hq; exact ho q hq
    | false =>
      simp [hrv] at hq
      by_cases hqp : q = p
      · subst hqp; exact hrv
      · rw [set_other _ _ _ _ hqp] at hq; exact ho q hq
  | hangup p =>
    refine ⟨hf, hc, fun q hq => ?_⟩
    simp only [hangupS] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [set_same] at hq; exact absurd hq (by decide)
    · rw [set_other _ _ _ _ hqp] at hq; exact ho q hq
  | rehook p =>
    refine ⟨hf, fun q hq => ?_, ho⟩
    simp only [rehookS, hh, ite_true] at hq ⊢
    exact forget_sound s p _ _ (set_off _ p _) (fun _ _ => rfl) hc q hq

/-- With the code's settings every reachable state keeps the three promises. -/
theorem inv_reach (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true) (hd : c.refuseDial = true)
    (hh : c.forgetOnChange = true) (s : State) (h : Reach c s) : Inv s := by
  induction h with
  | init => exact inv_init c
  | step s t _ st ih => exact inv_step c hl hr hd hh s t ih st

-- The witness settings: the hook admits only peer 1 at the start.
def witness (forgetOnLift forgetOnRevoke refuseDial forgetOnChange : Bool) : Cfg :=
  ⟨fun p => p == 1, forgetOnLift, forgetOnRevoke, refuseDial, forgetOnChange⟩

/-- The code before the fix: peer 1 is revoked and dials, the deny is cached, the revocation is lifted and the deny
kept, so its next dial is refused although the gate now lets it in. -/
theorem noForgetOnLift_bad : ∃ s, Reach (witness false true true true) s ∧ ¬ DecideFresh s := by
  let c := witness false true true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.revoke _ 1)
  have r2 := Reach.step _ _ r1 (Step.ask (c := c) _ 1 (by decide))
  have r3 := Reach.step _ _ r2 (Step.lift (c := c) _ 1)
  have r4 := Reach.step _ _ r3 (Step.cached (c := c) _ 1 (by decide))
  refine ⟨_, r4, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- Keeping the answer across a revoke: peer 1's allow is cached, it is revoked, and its next dial goes through on
the cached allow although the gate now refuses it. -/
theorem noForgetOnRevoke_bad : ∃ s, Reach (witness true false true true) s ∧ ¬ DecideFresh s := by
  let c := witness true false true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.ask _ 1 (by decide))
  have r2 := Reach.step _ _ r1 (Step.revoke (c := c) _ 1)
  have r3 := Reach.step _ _ r2 (Step.cached (c := c) _ 1 (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- A dial that is not refused up front: peer 1 is revoked and this node's dial reaches it. -/
theorem noRefuseDial_bad : ∃ s, Reach (witness true true false true) s ∧ ¬ NoDialRevoked s := by
  let c := witness true true false true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.revoke _ 1)
  have r2 := Reach.step _ _ r1 (Step.dial (c := c) _ 1)
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h 1 (by decide)) (by decide)

/-- A host that edits its hook without telling the endpoint: peer 2 is refused and the deny cached, the host lists
it, and its next dial is refused although the hook now admits it. -/
theorem noForgetOnChange_bad : ∃ s, Reach (witness true true true false) s ∧ ¬ DecideFresh s := by
  let c := witness true true true false
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.ask _ 2 (by decide))
  have r2 := Reach.step _ _ r1 (Step.rehook (c := c) _ 2)
  have r3 := Reach.step _ _ r2 (Step.cached (c := c) _ 2 (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

end Vinc.FacadeAcpForget

#audit_axioms Vinc.FacadeAcpForget.inv_reach
#audit_axioms Vinc.FacadeAcpForget.noForgetOnLift_bad
#audit_axioms Vinc.FacadeAcpForget.noForgetOnRevoke_bad
#audit_axioms Vinc.FacadeAcpForget.noRefuseDial_bad
#audit_axioms Vinc.FacadeAcpForget.noForgetOnChange_bad
