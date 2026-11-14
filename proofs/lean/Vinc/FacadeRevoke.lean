import Vinc.Axioms

/-!
# The facade's access gate: revocation and the access query

The story, in plain words. Peers open sessions with this node, and this node dials peers; a session has a protocol and
a direction, the question the access hook is asked about it. A session that reaches the endpoint waits until the
endpoint decides it: with a cached allow it goes on without a check, with a cached deny it ends, and otherwise a check
asks the gate about the session's protocol in a direction, the facade remembers an allow for exactly that question and
tells the endpoint whether the gate allows the peer anything, and the endpoint caches that. A session the endpoint lets
through comes up at the facade: turned away while its peer is revoked (the backstop), else live if the remembered allow
is for its question or the gate allows it. The gate refuses a revoked peer and otherwise gives the application's hook
answer for the question. The application revokes peers; a revoke ends every live session of that peer in the same
step. It may lift a revocation later. Both answers outlive the revoke and the lift here, so the backstop is shown to
hold on its own. A layer above may ask the access query at any time, also while an endpoint call holds the core.

What must never happen: a live session of a revoked peer; the access query saying yes to a revoked peer or for a
question the hook refuses; more revoked peers than the bound.

This is a transcription of `proofs/tla/FacadeRevoke.tla` over any number of peers, protocols, slots and steps. The Rust
code is `crates/vinc/src/engine/gate.rs` (`Gate::{bar, lift, is_revoked}` and its access query, `Known::covers`),
`crates/vinc/src/engine/ops.rs` (`Core::revoke`), `crates/vinc/src/engine.rs` (`Core::{session_up, session_admitted}`,
the `AcpCheck` arm of `on_event`) and `crates/vinc/src/endpoint.rs` (`Endpoint::revoke`, `unrevoke`, `Endpoint`'s
access query).

Main theorems: `inv_reach` (with the code's settings every reachable state keeps the three promises),
`failOpen_bad` (the old access query, which said yes while the core was borrowed, breaks the query promise) and
`noBackstop_bad` (without the revoked check of `session_admitted`, a revoked peer goes live again on the cached and
the remembered allow).
-/

namespace Vinc.FacadeRevoke

-- Where a session slot stands: free, waiting at the endpoint, live at the facade, or ended.
inductive St where
  | free
  | wait
  | live
  | ended
  deriving DecidableEq, Repr

-- The endpoint's cached answer for a peer.
inductive Ans where
  | none
  | allow
  | deny
  deriving DecidableEq, Repr

-- Which way a session was made: the peer dialed (inbound) or this node did (outbound).
inductive Dir where
  | inb
  | outb
  deriving DecidableEq, Repr

-- A question for the hook: a protocol and a direction.
structure Q where
  proto : Nat
  dir : Dir
  deriving DecidableEq, Repr

-- One session slot: whose session it holds, its question, and where it stands.
structure Sess where
  peer : Nat
  q : Q
  st : St

-- The last access query: whether one happened, about whom and which question, its answer, and whether that peer was
-- revoked then.
structure Last where
  asked : Bool
  peer : Nat
  q : Q
  ans : Bool
  wasRevoked : Bool

-- What does not change: the hook's answers, the questions the facade asks about for the endpoint's answer, the bound,
-- and the two switches that give the witnesses.
structure Cfg where
  hook : Nat → Q → Bool
  listed : List Q
  maxRevoked : Nat
  failOpen : Bool
  backstop : Bool

-- The state: the revoked peers, the endpoint's answer and the facade's remembered allow per peer, the slots, whether
-- the core is borrowed, and the last access query.
structure State where
  revoked : List Nat
  cache : Nat → Ans
  known : Nat → Option Q
  sess : Nat → Sess
  borrowed : Bool
  last : Last

-- Change one entry of a function.
def set {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

-- The changed entry reads back the new value.
theorem set_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : set f i v i = v := by simp [set]

-- Every other entry is unchanged.
theorem set_other {α : Type} (f : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) : set f i v j = f j := by
  simp [set, h]

-- The gate: no for a revoked peer, else the hook's answer for the question.
def gate (c : Cfg) (s : State) (p : Nat) (q : Q) : Bool := decide (p ∉ s.revoked) && c.hook p q

-- The endpoint's answer for a check of `p` that asked `a`: whether the gate allows the peer `a` or a listed question.
def told (c : Cfg) (s : State) (p : Nat) (a : Q) : Bool := gate c s p a || c.listed.any (gate c s p)

-- What the facade remembers after a check of `p` that asked `a`: an allow for exactly `a`, never a refusal.
def knownAfter (c : Cfg) (s : State) (p : Nat) (a : Q) : Option Q := if gate c s p a then some a else none

-- A waiting session comes up at the facade with the remembered allow `kn`: with the backstop a revoked peer's session
-- ends; otherwise it is live when `kn` is for its question or the gate allows it.
def up (c : Cfg) (s : State) (i : Nat) (kn : Option Q) : Nat → Sess :=
  set s.sess i ⟨(s.sess i).peer, (s.sess i).q,
    if c.backstop && decide ((s.sess i).peer ∈ s.revoked) then .ended
    else if decide (kn = some (s.sess i).q) || gate c s (s.sess i).peer (s.sess i).q then .live else .ended⟩

-- The revoked set after revoking `p`: unchanged if `p` is in it already.
def addRevoked (s : State) (p : Nat) : List Nat := if p ∈ s.revoked then s.revoked else p :: s.revoked

-- The slots after revoking `p`: every live session of `p` ends.
def endPeer (s : State) (p : Nat) : Nat → Sess :=
  fun j => if (s.sess j).peer = p ∧ (s.sess j).st = .live then ⟨p, (s.sess j).q, .ended⟩ else s.sess j

-- The start: nobody revoked, nothing cached or remembered, every slot free, the core not borrowed, no access query.
def init : State :=
  ⟨[], fun _ => .none, fun _ => none, fun _ => ⟨0, ⟨0, .inb⟩, .free⟩, false, ⟨false, 0, ⟨0, .inb⟩, false, false⟩⟩

-- The state after each action of the TLA+ model of the same name.
-- A session of `p` with question `q` takes slot `i`, from either side's dial; a revoked peer's is turned away when it
-- comes up.
def arriveS (s : State) (i p : Nat) (q : Q) : State := { s with sess := set s.sess i ⟨p, q, .wait⟩ }
-- A cached allow lets the waiting session of slot `i` come up, with its peer's remembered allow.
def allowS (c : Cfg) (s : State) (i : Nat) : State := { s with sess := up c s i (s.known (s.sess i).peer) }
-- The session of slot `i` ends (a cached deny, or another reason).
def endS (s : State) (i : Nat) : State := { s with sess := set s.sess i ⟨(s.sess i).peer, (s.sess i).q, .ended⟩ }
-- No cached answer: a check asks `a`, the facade remembers an allow for `a`, the endpoint caches what it is told, and
-- the session comes up or ends.
def askS (c : Cfg) (s : State) (i : Nat) (a : Q) : State :=
  { s with
    cache := set s.cache (s.sess i).peer (if told c s (s.sess i).peer a then .allow else .deny),
    known := set s.known (s.sess i).peer (knownAfter c s (s.sess i).peer a),
    sess := if told c s (s.sess i).peer a then up c s i (knownAfter c s (s.sess i).peer a)
            else set s.sess i ⟨(s.sess i).peer, (s.sess i).q, .ended⟩ }
-- `p` is revoked; its live sessions end in the same step.
def revokeS (s : State) (p : Nat) : State := { s with revoked := addRevoked s p, sess := endPeer s p }
-- An ended session gives its slot back.
def freeS (s : State) (i : Nat) : State := { s with sess := set s.sess i ⟨(s.sess i).peer, (s.sess i).q, .free⟩ }
-- The endpoint's answer for `p` lapses.
def expireS (s : State) (p : Nat) : State := { s with cache := set s.cache p .none }
-- The remembered allow of `p` lapses, or the bounded table drops it.
def lapseS (s : State) (p : Nat) : State := { s with known := set s.known p none }
-- An endpoint call takes or gives back the core.
def toggleS (s : State) : State := { s with borrowed := !s.borrowed }
-- The revocation of `p` is lifted (unrevoke).
def liftS (s : State) (p : Nat) : State := { s with revoked := s.revoked.filter (fun q => q != p) }
-- A layer asks the access query about `p` on question `q`; the old code said yes whenever the core was borrowed.
def queryS (c : Cfg) (s : State) (p : Nat) (q : Q) : State :=
  { s with last := ⟨true, p, q, if c.failOpen && s.borrowed then true else gate c s p q, decide (p ∈ s.revoked)⟩ }

-- One step of the system, with the guard of each action.
inductive Step (c : Cfg) : State → State → Prop where
  | arrive (s : State) (i p : Nat) (q : Q) : (s.sess i).st = .free → Step c s (arriveS s i p q)
  | decideAllow (s : State) (i : Nat) : (s.sess i).st = .wait → s.cache (s.sess i).peer = .allow →
      Step c s (allowS c s i)
  | decideDeny (s : State) (i : Nat) : (s.sess i).st = .wait → s.cache (s.sess i).peer = .deny → Step c s (endS s i)
  | decideAsk (s : State) (i : Nat) (a : Q) : (s.sess i).st = .wait → s.cache (s.sess i).peer = .none →
      a.proto = (s.sess i).q.proto → Step c s (askS c s i a)
  | revoke (s : State) (p : Nat) : (p ∈ s.revoked ∨ s.revoked.length < c.maxRevoked) → Step c s (revokeS s p)
  | finish (s : State) (i : Nat) : ((s.sess i).st = .wait ∨ (s.sess i).st = .live) → Step c s (endS s i)
  | free (s : State) (i : Nat) : (s.sess i).st = .ended → Step c s (freeS s i)
  | expire (s : State) (p : Nat) : Step c s (expireS s p)
  | lapse (s : State) (p : Nat) : Step c s (lapseS s p)
  | toggle (s : State) : Step c s (toggleS s)
  | lift (s : State) (p : Nat) : Step c s (liftS s p)
  | query (s : State) (p : Nat) (q : Q) : Step c s (queryS c s p q)

-- The states the system can reach from the start.
inductive Reach (c : Cfg) : State → Prop where
  | init : Reach c init
  | step (s t : State) : Reach c s → Step c s t → Reach c t

-- No live session belongs to a revoked peer.
abbrev NoLiveRevoked (s : State) : Prop := ∀ i, (s.sess i).st = .live → (s.sess i).peer ∉ s.revoked

-- Admit said yes only to a peer that was not revoked at the call, for a question the hook allows.
abbrev AdmitSound (c : Cfg) (s : State) : Prop :=
  s.last.asked = true → s.last.ans = true → s.last.wasRevoked = false ∧ c.hook s.last.peer s.last.q = true

-- The revoked set holds at most the bound.
abbrev RevokedBound (c : Cfg) (s : State) : Prop := s.revoked.length ≤ c.maxRevoked

-- The three promises together.
abbrev Inv (c : Cfg) (s : State) : Prop := NoLiveRevoked s ∧ AdmitSound c s ∧ RevokedBound c s

/-- The start keeps the three promises. -/
theorem inv_init (c : Cfg) : Inv c init := by
  refine ⟨fun i h => ?_, fun h _ => ?_, ?_⟩
  · simp [init] at h
  · simp [init] at h
  · simp [init]

/-- Changing one slot to anything but live keeps every live slot's peer unrevoked. -/
theorem set_notLive (s : State) (i : Nat) (v : Sess) (hv : v.st ≠ .live) (hn : NoLiveRevoked s) (j : Nat)
    (h : (set s.sess i v j).st = .live) : (set s.sess i v j).peer ∉ s.revoked := by
  by_cases hji : j = i
  · subst hji; rw [set_same] at h; exact absurd h hv
  · rw [set_other _ _ _ _ hji] at h ⊢; exact hn j h

/-- A session that `up` makes live does not belong to a revoked peer, with the backstop, whatever the remembered
allow. -/
theorem up_live (c : Cfg) (s : State) (i j : Nat) (kn : Option Q) (hb : c.backstop = true) (hn : NoLiveRevoked s)
    (h : (up c s i kn j).st = .live) : (up c s i kn j).peer ∉ s.revoked := by
  unfold up at h ⊢
  by_cases hji : j = i
  · subst hji
    rw [set_same] at h ⊢
    intro hm
    simp [hb, hm] at h
  · rw [set_other _ _ _ _ hji] at h ⊢; exact hn j h

/-- With the code's settings (the backstop on, the fail-open gone) every step keeps the three promises. -/
theorem inv_step (c : Cfg) (hf : c.failOpen = false) (hb : c.backstop = true) (s t : State) (hs : Inv c s)
    (st : Step c s t) : Inv c t := by
  obtain ⟨hn, ha, hr⟩ := hs
  cases st with
  | arrive i p q _ => exact ⟨set_notLive s i ⟨p, q, .wait⟩ (by simp) hn, ha, hr⟩
  | decideAllow i _ _ => exact ⟨fun j h => up_live c s i j _ hb hn h, ha, hr⟩
  | decideDeny i _ _ => exact ⟨set_notLive s i ⟨(s.sess i).peer, (s.sess i).q, .ended⟩ (by simp) hn, ha, hr⟩
  | finish i _ => exact ⟨set_notLive s i ⟨(s.sess i).peer, (s.sess i).q, .ended⟩ (by simp) hn, ha, hr⟩
  | free i _ => exact ⟨set_notLive s i ⟨(s.sess i).peer, (s.sess i).q, .free⟩ (by simp) hn, ha, hr⟩
  | expire p => exact ⟨hn, ha, hr⟩
  | lapse p => exact ⟨hn, ha, hr⟩
  | toggle => exact ⟨hn, ha, hr⟩
  | lift p =>
    refine ⟨fun j h hm => hn j h (List.mem_filter.mp hm).1, ha, ?_⟩
    exact Nat.le_trans (List.length_filter_le _ _) hr
  | decideAsk i a _ _ _ =>
    refine ⟨fun j h => ?_, ha, hr⟩
    simp only [askS] at h ⊢
    by_cases hg : told c s (s.sess i).peer a = true
    · rw [if_pos hg] at h ⊢; exact up_live c s i j _ hb hn h
    · rw [if_neg hg] at h ⊢; exact set_notLive s i ⟨(s.sess i).peer, (s.sess i).q, .ended⟩ (by simp) hn j h
  | revoke p hg =>
    refine ⟨fun j h => ?_, ha, ?_⟩
    · simp only [revokeS, endPeer] at h ⊢
      by_cases hj : (s.sess j).peer = p ∧ (s.sess j).st = .live
      · rw [if_pos hj] at h; simp at h
      · rw [if_neg hj] at h ⊢
        intro hm
        unfold addRevoked at hm
        by_cases hp : p ∈ s.revoked
        · rw [if_pos hp] at hm; exact hn j h hm
        · rw [if_neg hp] at hm
          rcases List.mem_cons.mp hm with he | hm'
          · exact hj ⟨he, h⟩
          · exact hn j h hm'
    · simp only [RevokedBound, revokeS, addRevoked]
      by_cases hp : p ∈ s.revoked
      · rw [if_pos hp]; exact hr
      · rw [if_neg hp, List.length_cons]
        rcases hg with h | h
        · exact absurd h hp
        · exact h
  | query p q =>
    refine ⟨hn, fun _ hans => ?_, hr⟩
    simp only [queryS, hf, Bool.false_and, gate] at hans ⊢
    simp at hans
    exact ⟨decide_eq_false hans.1, hans.2⟩

/-- With the code's settings every reachable state keeps the three promises. -/
theorem inv_reach (c : Cfg) (hf : c.failOpen = false) (hb : c.backstop = true) (s : State) (h : Reach c s) :
    Inv c s := by
  induction h with
  | init => exact inv_init c
  | step s t _ st ih => exact inv_step c hf hb s t ih st

-- The witness settings: the hook admits only peer 1, on every question; protocol 1 is listed either way; one
-- revocation at most.
def witness (failOpen backstop : Bool) : Cfg :=
  ⟨fun p _ => p == 1, [⟨1, .inb⟩, ⟨1, .outb⟩], 1, failOpen, backstop⟩

-- A session of protocol 1, inbound.
def q1 : Q := ⟨1, .inb⟩

/-- The old access query breaks the query promise: with the core borrowed it says yes to peer 2, which the hook
refuses. -/
theorem failOpen_bad : ∃ s, Reach (witness true true) s ∧ ¬ AdmitSound (witness true true) s := by
  refine ⟨queryS (witness true true) (toggleS init) 2 q1,
    Reach.step _ _ (Reach.step _ _ Reach.init (Step.toggle init)) (Step.query _ 2 q1), ?_⟩
  intro h
  have := (h (by decide) (by decide)).2
  exact absurd this (by decide)

/-- Without the revoked check of `session_admitted` a revoked peer goes live again: peer 1 is allowed, cached and
remembered, revoked, and its next session on the same protocol and direction comes up on the cached allow, which the
remembered allow covers. -/
theorem noBackstop_bad : ∃ s, Reach (witness false false) s ∧ ¬ NoLiveRevoked s := by
  let c := witness false false
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.arrive init 0 1 q1 (by decide))
  have r2 := Reach.step _ _ r1 (Step.decideAsk (c := c) _ 0 q1 (by decide) (by decide) (by decide))
  have r3 := Reach.step _ _ r2 (Step.revoke (c := c) _ 1 (by decide))
  have r4 := Reach.step _ _ r3 (Step.free (c := c) _ 0 (by decide))
  have r5 := Reach.step _ _ r4 (Step.arrive (c := c) _ 0 1 q1 (by decide))
  have r6 := Reach.step _ _ r5 (Step.decideAllow (c := c) _ 0 (by decide) (by decide))
  refine ⟨_, r6, fun h => ?_⟩
  exact h 0 (by decide) (by decide)

end Vinc.FacadeRevoke

#audit_axioms Vinc.FacadeRevoke.inv_reach
#audit_axioms Vinc.FacadeRevoke.failOpen_bad
#audit_axioms Vinc.FacadeRevoke.noBackstop_bad
