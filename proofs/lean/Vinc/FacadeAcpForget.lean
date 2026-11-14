import Vinc.Axioms

/-!
# The facade's access decisions: the hook asked per protocol and direction, against the endpoint's answer per peer

The story, in plain words. Peers dial this node and this node dials them; a session has a protocol and a direction,
the question the access hook is asked about it. The endpoint keeps one answer per peer for 30 s: a session of a peer
with an answer is decided on it, otherwise the endpoint raises a check. The facade asks the hook about the check's
question, remembers an allow for exactly that question as long as the endpoint keeps its answer, and tells the endpoint
"allow" when the gate allows the peer that question or any other it asks about: those of the sessions and unfinished
dials this node holds with the peer, whatever their protocol, and every listed protocol in both directions. A session
the endpoint lets through comes up at the facade: refused while its peer is revoked, else taken up if the remembered
allow is for its own question or the hook allows that question now. A session asks again before its peer's answer runs
out, and a deny then closes every session of the peer. The application revokes peers, lifts revocations and edits its
hook, telling the endpoint through `admission_changed`; each of those drops both answers of the peer, and a dial to a
revoked peer is refused before anything is sent. A dial the gate allows drops a refusal the endpoint holds for its
peer, so the session of that dial asks with its own question. The question a check asks: the first check of a session
this node dialed asks its own; the first check of an accepted session, and a later one, ask its protocol inbound or
outbound (the code asks outbound while a dial of that protocol to the peer waits).

What must never happen: a session taken up on an allow the hook gave for another protocol or direction (issue #440);
a deny held for a peer the gate allows a listed question or the question of a session or dial this node holds with it;
a refusal that closes a session the gate allows; a session decided on answers the gate would not give at that moment;
a cached or remembered allow the gate would not give now; a revoked peer holding a session this node dialed.

This is a transcription of `proofs/tla/FacadeAcpForget.tla` over any number of peers, protocols and steps. The Rust code
is `crates/vinc/src/engine.rs` (`Core::{session_up, session_admitted, admits_other}`, the `AcpCheck` arm of `on_event`),
`crates/vinc/src/engine/gate.rs` (`Known::{covers, remember, forget}`, `direction`), `crates/vinc/src/engine/ops.rs`
(`Core::{connect_start, revoke, unrevoke, forget_access, listen}`), `crates/vinc-core/src/commands.rs`
(`Command::AcpForget`, `Query::PeerSession`, `Query::Access`), `crates/vinc-core/src/acp.rs` (`start_acp`, `ask_acp`,
`acp_answer`), `crates/vinc-node/src/node.rs` (`Node::{revoke, unrevoke, forget_access}`) and
`crates/vinc/src/endpoint.rs` (`Endpoint::{revoke, unrevoke, connect, admission_changed}`).

The promises are proved of every reachable state in `Vinc/FacadeAcpForgetThm.lean` (`inv_reach`,
`noCrossAllow_reach`, `noCrossDeny_reach`, `noCut_reach`), and the settings that break one are in
`Vinc/FacadeAcpForgetBad.lean`. This file holds the model, the promises and the lemmas about one check: `told_false`
(a refusal told to the endpoint means the gate allows none of the questions it must not stand against), `told_of_gate`
(a session the gate allows is never refused by the check it raised) and `told_any` (an allow told is for a peer the gate
allows something).
-/

namespace Vinc.FacadeAcpForget

-- The endpoint's answer for a peer: nothing, allow or deny.
inductive Ans where
  | none
  | allow
  | deny
  deriving DecidableEq, Repr

-- An answer as a yes or no: only allow lets in.
def asBool : Ans → Bool
  | .allow => true
  | _ => false

-- The answer that records `b`.
def cacheOf (b : Bool) : Ans := if b then .allow else .deny

-- Reading back an answer recorded with `cacheOf` gives the answer.
theorem asBool_cacheOf (b : Bool) : asBool (cacheOf b) = b := by cases b <;> rfl

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

-- The last decision: whether one happened, about whom and which question, the endpoint's answer the session got,
-- whether it was taken up, what the gate said then about the question, about the peer and about the questions a
-- refusal must not stand against, and whether the remembered allow covered it.
structure Last where
  done : Bool
  peer : Nat
  q : Q
  ep : Bool
  up : Bool
  gate : Bool
  any : Bool
  held : Bool
  cov : Bool

-- What does not change: the hook's first answers, the protocols the facade lists, those this node dials without
-- listing them (outbound sessions only), and the eight switches that give the witnesses.
structure Cfg where
  hook : Nat → Q → Bool
  listed : List Nat
  dialed : List Nat
  forgetOnLift : Bool
  forgetOnRevoke : Bool
  refuseDial : Bool
  forgetOnChange : Bool
  askEach : Bool
  answerAny : Bool
  askHeld : Bool
  dialAsks : Bool

-- The state: the hook's answers now, which peers are revoked, the endpoint's answer and the facade's remembered allow
-- per peer, the last decision, which peers hold a session we dialed, the questions of the sessions and unfinished
-- dials held with each peer, and whether a refusal closed a session the gate allowed.
structure State where
  hook : Nat → Q → Bool
  revoked : Nat → Bool
  cache : Nat → Ans
  known : Nat → Option Q
  last : Last
  out : Nat → Bool
  sess : Nat → List Q
  cut : Bool

-- Change one entry of a function.
def set {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

-- The changed entry reads back the new value.
theorem set_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : set f i v i = v := by simp [set]

-- Every other entry is unchanged.
theorem set_other {α : Type} (f : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) : set f i v j = f j := by
  simp [set, h]

-- Both directions of each listed protocol: the questions the facade always asks about for the endpoint's answer.
def listedQs (c : Cfg) : List Q := c.listed.flatMap (fun a => [⟨a, .inb⟩, ⟨a, .outb⟩])

-- The questions of sessions: a listed protocol either way, a dialed one outbound.
def qs (c : Cfg) : List Q := listedQs c ++ c.dialed.map (fun a => ⟨a, .outb⟩)

-- The gate: no for a revoked peer, else the hook's answer for the question.
def gate (s : State) (p : Nat) (q : Q) : Bool := !s.revoked p && s.hook p q

-- Whether the gate allows `p` some question a session may have.
def anyB (c : Cfg) (s : State) (p : Nat) : Bool := (qs c).any (gate s p)

-- The questions a refusal for `p` must not stand against when a session with question `q` is at hand: the listed
-- ones, `q`, and those of the sessions and dials held with `p`.
def heldQs (c : Cfg) (s : State) (p : Nat) (q : Q) : List Q := listedQs c ++ (q :: s.sess p)

-- Whether the gate allows `p` one of them.
def heldB (c : Cfg) (s : State) (p : Nat) (q : Q) : Bool := (heldQs c s p q).any (gate s p)

-- The other questions the facade asks about when a check of `p` raised by a session with question `q` is refused
-- (`admits_other`): every listed one and, with the fix, those of the peer's sessions and dials, `q` among them.
def others (c : Cfg) (s : State) (p : Nat) (q : Q) : List Q :=
  listedQs c ++ (bif c.askHeld then q :: s.sess p else [])

-- The endpoint's answer for a check of `p` that asked `a`, raised by a session with question `q`: the gate's answer
-- for `a`, or, with the fix, also an allow when the gate allows the peer another of the questions it asks about.
def told (c : Cfg) (s : State) (p : Nat) (a q : Q) : Bool :=
  gate s p a || (c.answerAny && (others c s p q).any (fun r => decide (r ≠ a) && gate s p r))

-- What the facade remembers after a check of `p` that asked `a`: an allow for exactly `a`, never a refusal.
def knownAfter (c : Cfg) (s : State) (p : Nat) (a : Q) : Option Q := if c.askEach && gate s p a then some a else none

-- The questions a check raised by a session with question `q` may ask; `again` for a later check.
abbrev asked (again : Bool) (q a : Q) : Prop := a.proto = q.proto ∧ (again = true ∨ q.dir = .inb ∨ a = q)

-- Whether the facade takes up a session of `p` with question `q` that the endpoint let through on `ep`, with the
-- remembered allow `kn`: not while revoked, and with each session asked on its own only if `kn` is for `q` or the hook
-- allows `q`; the rule before #440 took up whatever the endpoint let through.
def upOf (c : Cfg) (s : State) (p : Nat) (q : Q) (ep : Bool) (kn : Option Q) : Bool :=
  ep && !s.revoked p && (!c.askEach || decide (kn = some q) || s.hook p q)

-- Whether a dial of `q` to `p` drops the refusal held for `p`: with the fix, when the dial goes out and the gate allows
-- its question.
def dropB (c : Cfg) (s : State) (p : Nat) (q : Q) : Bool :=
  c.dialAsks && !(c.refuseDial && s.revoked p) && decide (s.cache p = .deny) && gate s p q

-- The start: the hook's first answers, nobody revoked, nothing cached or remembered, nothing decided, nothing dialed,
-- no session held, no session closed by a refusal.
def init (c : Cfg) : State :=
  ⟨c.hook, fun _ => false, fun _ => .none, fun _ => none,
   ⟨false, 0, ⟨0, .inb⟩, false, false, false, false, false, false⟩, fun _ => false, fun _ => [], false⟩

-- The state after each action of the TLA+ model of the same name.
-- A session of `p` with question `q` is decided on the endpoint's answer for `p`, and held if it is taken up.
def cachedS (c : Cfg) (s : State) (p : Nat) (q : Q) : State :=
  { s with last := ⟨true, p, q, asBool (s.cache p), upOf c s p q (asBool (s.cache p)) (s.known p), gate s p q,
                    anyB c s p, heldB c s p q, decide (s.known p = some q)⟩,
           sess := set s.sess p (bif upOf c s p q (asBool (s.cache p)) (s.known p) then q :: s.sess p else s.sess p) }
-- No answer for `p`: a check asks `a`, the facade remembers an allow for `a`, the endpoint caches what it is told, and
-- the session is decided on it: held if it is taken up, and a refusal closes every session and dial of `p`.
def askS (c : Cfg) (s : State) (p : Nat) (q a : Q) : State :=
  { s with cache := set s.cache p (cacheOf (told c s p a q)),
           known := set s.known p (knownAfter c s p a),
           last := ⟨true, p, q, told c s p a q, upOf c s p q (told c s p a q) (knownAfter c s p a), gate s p q,
                    anyB c s p, heldB c s p q, decide (knownAfter c s p a = some q)⟩,
           sess := set s.sess p (bif told c s p a q then
                     (bif upOf c s p q (told c s p a q) (knownAfter c s p a) then q :: s.sess p else s.sess p)
                   else []),
           cut := s.cut || (!told c s p a q && (q :: s.sess p).any (gate s p)) }
-- A session of `p` with question `q` asks again and the check asks `a`; a deny closes every session of `p`.
def recheckS (c : Cfg) (s : State) (p : Nat) (q a : Q) : State :=
  { s with cache := set s.cache p (cacheOf (told c s p a q)), known := set s.known p (knownAfter c s p a),
           sess := set s.sess p (bif told c s p a q then s.sess p else []),
           cut := s.cut || (!told c s p a q && (s.sess p).any (gate s p)) }
-- `p` is revoked: with the fix both its answers go, and every session with it ends.
def revokeS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with revoked := set s.revoked p true,
           cache := if c.forgetOnRevoke then set s.cache p .none else s.cache,
           known := if c.forgetOnRevoke then set s.known p none else s.known,
           out := set s.out p false,
           sess := set s.sess p [] }
-- The revocation of `p` is lifted; with the fix both its answers go.
def liftS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with revoked := set s.revoked p false,
           cache := if c.forgetOnLift then set s.cache p .none else s.cache,
           known := if c.forgetOnLift then set s.known p none else s.known }
-- The endpoint's answer for `p` lapses.
def expireS (s : State) (p : Nat) : State := { s with cache := set s.cache p .none }
-- The remembered allow of `p` lapses, or the bounded table drops it.
def lapseS (s : State) (p : Nat) : State := { s with known := set s.known p none }
-- The full table is cleared.
def clearS (s : State) : State := { s with known := fun _ => none }
-- This node dials `p` with question `q`: refused up front while `p` is revoked, else the dial is held and the session
-- reaches `p`; with the fix a dial the gate allows drops a refusal held for `p`, and the remembered allow with it.
def dialS (c : Cfg) (s : State) (p : Nat) (q : Q) : State :=
  { s with out := if c.refuseDial && s.revoked p then s.out else set s.out p true,
           sess := set s.sess p (bif c.refuseDial && s.revoked p then s.sess p else q :: s.sess p),
           cache := bif dropB c s p q then set s.cache p .none else s.cache,
           known := bif dropB c s p q then set s.known p none else s.known }
-- A session this node dialed ends for another reason.
def hangupS (s : State) (p : Nat) : State := { s with out := set s.out p false }
-- A session or a dial with `p` ends.
def endS (s : State) (p : Nat) (q : Q) : State :=
  { s with sess := set s.sess p ((s.sess p).filter (fun r => decide (r ≠ q))) }
-- The host edits its hook's answer for `p` on `q` and, with the fix, calls admission_changed for `p`.
def rehookS (c : Cfg) (s : State) (p : Nat) (q : Q) : State :=
  { s with hook := set s.hook p (fun x => if x = q then !s.hook p q else s.hook p x),
           cache := if c.forgetOnChange then set s.cache p .none else s.cache,
           known := if c.forgetOnChange then set s.known p none else s.known }

-- One step of the system, with the guard of each action. A session this node dialed comes up only after its dial.
inductive Step (c : Cfg) : State → State → Prop where
  | cached (s : State) (p : Nat) (q : Q) : s.cache p ≠ .none → q ∈ qs c → (q.dir = .outb → q ∈ s.sess p) →
      Step c s (cachedS c s p q)
  | ask (s : State) (p : Nat) (q a : Q) : s.cache p = .none → q ∈ qs c → (q.dir = .outb → q ∈ s.sess p) →
      asked false q a → Step c s (askS c s p q a)
  | recheck (s : State) (p : Nat) (q a : Q) : s.cache p = .allow → q ∈ s.sess p → asked true q a →
      Step c s (recheckS c s p q a)
  | revoke (s : State) (p : Nat) : Step c s (revokeS c s p)
  | lift (s : State) (p : Nat) : Step c s (liftS c s p)
  | expire (s : State) (p : Nat) : Step c s (expireS s p)
  | lapse (s : State) (p : Nat) : Step c s (lapseS s p)
  | clear (s : State) : Step c s (clearS s)
  | dial (s : State) (p : Nat) (q : Q) : q ∈ qs c → q.dir = .outb → Step c s (dialS c s p q)
  | hangup (s : State) (p : Nat) : Step c s (hangupS s p)
  | finish (s : State) (p : Nat) (q : Q) : q ∈ s.sess p → Step c s (endS s p q)
  | rehook (s : State) (p : Nat) (q : Q) : Step c s (rehookS c s p q)

-- The states the system can reach from the start.
inductive Reach (c : Cfg) : State → Prop where
  | init : Reach c (init c)
  | step (s t : State) : Reach c s → Step c s t → Reach c t

-- Every session is decided with the answers the gate gives at that moment: it is taken up exactly when the gate allows
-- its own question, the endpoint lets it through only for a peer the gate allows something, and refuses it only when
-- the gate allows none of the questions a refusal must not stand against, its own among them.
abbrev DecideFresh (s : State) : Prop :=
  s.last.done = true →
    s.last.up = s.last.gate ∧ (s.last.ep = true → s.last.any = true) ∧ (s.last.ep = false → s.last.held = false)

-- Every cached allow is for a peer the gate allows something now.
abbrev CacheSound (c : Cfg) (s : State) : Prop := ∀ p, s.cache p = .allow → anyB c s p = true

-- Every remembered allow is one the gate gives now, for exactly that question.
abbrev KnownSound (s : State) : Prop := ∀ p q, s.known p = some q → gate s p q = true

-- No revoked peer holds a session this node dialed.
abbrev NoDialRevoked (s : State) : Prop := ∀ p, s.out p = true → s.revoked p = false

-- No session is taken up on an allow given for another protocol or direction: the gate allows its own question at
-- that moment, or the remembered allow is for exactly its question.
abbrev NoCrossAllow (s : State) : Prop :=
  s.last.done = true → s.last.up = true → s.last.gate = true ∨ s.last.cov = true

-- The endpoint holds a deny only for a peer the gate allows no listed question and no question of a session or dial
-- this node holds with it.
abbrev NoCrossDeny (c : Cfg) (s : State) : Prop :=
  ∀ p, s.cache p = .deny → ∀ q, (q ∈ listedQs c ∨ q ∈ s.sess p) → gate s p q = false

-- No refusal closed a session whose question the gate allowed at that moment.
abbrev NoCut (s : State) : Prop := s.cut = false

-- Every question held is one a session may have.
abbrev SessOK (c : Cfg) (s : State) : Prop := ∀ p q, q ∈ s.sess p → q ∈ qs c

-- The promises together.
abbrev Inv (c : Cfg) (s : State) : Prop :=
  DecideFresh s ∧ CacheSound c s ∧ KnownSound s ∧ NoDialRevoked s ∧ NoCrossDeny c s ∧ NoCut s ∧ SessOK c s

/-- The start keeps the promises. -/
theorem inv_init (c : Cfg) : Inv c (init c) := by
  refine ⟨fun h => ?_, fun p h => ?_, fun p q h => ?_, fun p h => ?_, fun p h => ?_, rfl, fun p q h => ?_⟩
  · simp [init] at h
  · simp [init] at h
  · simp [init] at h
  · simp [init] at h
  · simp [init] at h
  · simp [init] at h

/-- A question is a listed one exactly when its protocol is listed. -/
theorem mem_listedQs (c : Cfg) (q : Q) : q ∈ listedQs c ↔ q.proto ∈ c.listed := by
  unfold listedQs
  constructor
  · intro h
    obtain ⟨a, ha, hq⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact ha
  · intro h
    refine List.mem_flatMap.mpr ⟨q.proto, h, ?_⟩
    cases q with
    | mk pr d => cases d <;> simp

/-- A question of a session is a listed one, or outbound. -/
theorem qs_split (c : Cfg) (q : Q) (hq : q ∈ qs c) : q ∈ listedQs c ∨ q.dir = .outb := by
  unfold qs at hq
  rcases List.mem_append.mp hq with h | h
  · exact Or.inl h
  · obtain ⟨x, _, hx⟩ := List.mem_map.mp h
    rw [← hx]
    exact Or.inr rfl

/-- A listed question is a question of a session. -/
theorem listed_qs (c : Cfg) (q : Q) (hq : q ∈ listedQs c) : q ∈ qs c := by
  unfold qs
  exact List.mem_append.mpr (Or.inl hq)

/-- The first check of a session asks a question a session may have: its own, or its protocol either way when it was
accepted, and an accepted session's protocol is listed. -/
theorem asked_qs (c : Cfg) (q a : Q) (hq : q ∈ qs c) (ha : asked false q a) : a ∈ qs c := by
  rcases ha.2 with h | h | h
  · exact absurd h (by decide)
  · rcases qs_split c q hq with hl | ho
    · have hal : a ∈ listedQs c := by
        rw [mem_listedQs, ha.1]
        exact (mem_listedQs c q).mp hl
      exact listed_qs c a hal
    · rw [h] at ho
      exact absurd ho (by decide)
  · rw [h]
    exact hq

/-- A question of a session the gate allows makes the peer allowed something. -/
theorem any_of_gate (c : Cfg) (s : State) (p : Nat) (q : Q) (hq : q ∈ qs c) (hg : gate s p q = true) :
    anyB c s p = true :=
  List.any_eq_true.mpr ⟨q, hq, hg⟩

/-- With the fix the other questions include every listed one, the asking session's and those held with the peer. -/
theorem mem_others (c : Cfg) (hh : c.askHeld = true) (s : State) (p : Nat) (q r : Q)
    (hr : r ∈ listedQs c ∨ r ∈ q :: s.sess p) : r ∈ others c s p q := by
  unfold others
  rw [hh]
  exact List.mem_append.mpr hr

/-- Each of the other questions is one a session may have, when the asking session's and the held ones are. -/
theorem others_sub (c : Cfg) (s : State) (p : Nat) (q x : Q) (hq : q ∈ qs c) (hs : ∀ r, r ∈ s.sess p → r ∈ qs c)
    (hx : x ∈ others c s p q) : x ∈ qs c := by
  unfold others at hx
  rcases List.mem_append.mp hx with h | h
  · exact listed_qs c x h
  · cases hh : c.askHeld with
    | false =>
      rw [hh] at h
      simp at h
    | true =>
      rw [hh] at h
      rcases List.mem_cons.mp h with e | m
      · rw [e]
        exact hq
      · exact hs x m

/-- With the fix, a refusal told to the endpoint means the gate allows none of the questions it must not stand
against: no listed one, not the asking session's, none held with the peer. -/
theorem told_false (c : Cfg) (hn : c.answerAny = true) (hh : c.askHeld = true) (s : State) (p : Nat) (a q r : Q)
    (ht : told c s p a q = false) (hr : r ∈ listedQs c ∨ r ∈ q :: s.sess p) : gate s p r = false := by
  unfold told at ht
  rw [hn, Bool.true_and] at ht
  have hga : gate s p a = false := by
    cases h : gate s p a with
    | false => rfl
    | true =>
      rw [h, Bool.true_or] at ht
      exact absurd ht (by decide)
  rw [hga, Bool.false_or] at ht
  by_cases hra : r = a
  · rw [hra]
    exact hga
  · cases hg : gate s p r with
    | false => rfl
    | true =>
      have hany : (others c s p q).any (fun x => decide (x ≠ a) && gate s p x) = true :=
        List.any_eq_true.mpr ⟨r, mem_others c hh s p q r hr, by rw [hg, Bool.and_true]; exact decide_eq_true hra⟩
      rw [hany] at ht
      exact absurd ht (by decide)

/-- With the fix, a session the gate allows is never refused by the check it raised. -/
theorem told_of_gate (c : Cfg) (hn : c.answerAny = true) (hh : c.askHeld = true) (s : State) (p : Nat) (a q : Q)
    (hg : gate s p q = true) : told c s p a q = true := by
  cases ht : told c s p a q with
  | true => rfl
  | false =>
    have hf := told_false c hn hh s p a q q ht (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    rw [hg] at hf
    exact absurd hf (by decide)

/-- An allow told to the endpoint is for a peer the gate allows something, when the question asked, the asking
session's and the held ones are questions a session may have. -/
theorem told_any (c : Cfg) (s : State) (p : Nat) (a q : Q) (ha : a ∈ qs c) (hq : q ∈ qs c)
    (hs : ∀ r, r ∈ s.sess p → r ∈ qs c) (ht : told c s p a q = true) : anyB c s p = true := by
  unfold told at ht
  cases hga : gate s p a with
  | true => exact any_of_gate c s p a ha hga
  | false =>
    rw [hga, Bool.false_or, Bool.and_eq_true] at ht
    obtain ⟨x, hx, hxg⟩ := List.any_eq_true.mp ht.2
    rw [Bool.and_eq_true] at hxg
    exact any_of_gate c s p x (others_sub c s p q x hq hs hx) hxg.2

/-- The gate allows none of the questions a refusal must not stand against when it allows no listed one, not the
session's own and none held. -/
theorem heldB_false (c : Cfg) (s : State) (p : Nat) (q : Q)
    (h : ∀ r, (r ∈ listedQs c ∨ r ∈ q :: s.sess p) → gate s p r = false) : heldB c s p q = false := by
  cases hb : heldB c s p q with
  | false => rfl
  | true =>
    unfold heldB heldQs at hb
    obtain ⟨r, hr, hg⟩ := List.any_eq_true.mp hb
    rw [h r (List.mem_append.mp hr)] at hg
    exact absurd hg (by decide)

/-- The gate allows none of the held questions when it allows none of a list they are in. -/
theorem any_false (s : State) (p : Nat) (l : List Q) (h : ∀ r, r ∈ l → gate s p r = false) :
    l.any (gate s p) = false := by
  cases hb : l.any (gate s p) with
  | false => rfl
  | true =>
    obtain ⟨r, hr, hg⟩ := List.any_eq_true.mp hb
    rw [h r hr] at hg
    exact absurd hg (by decide)

/-- What a peer's held questions are after a step that changes only one peer's. -/
theorem sess_at (f g : Nat → List Q) (p : Nat) (l : List Q) (hf : g = set f p l) (x : Nat) (r : Q) (hr : r ∈ g x) :
    (x = p ∧ r ∈ l) ∨ (x ≠ p ∧ r ∈ f x) := by
  rw [hf] at hr
  by_cases hxp : x = p
  · rw [hxp, set_same] at hr
    exact Or.inl ⟨hxp, hr⟩
  · rw [set_other _ _ _ _ hxp] at hr
    exact Or.inr ⟨hxp, hr⟩

/-- A list that grew by at most `q` holds `q` or what it held. -/
theorem mem_grow (b : Bool) (q r : Q) (l : List Q) (h : r ∈ (bif b then q :: l else l)) : r = q ∨ r ∈ l := by
  cases b with
  | true => exact List.mem_cons.mp h
  | false => exact Or.inr h

/-- What the facade remembers is an allow the gate gives, for exactly the question asked. -/
theorem knownAfter_sound (c : Cfg) (s : State) (p : Nat) (a q : Q) (h : knownAfter c s p a = some q) :
    gate s p q = true := by
  unfold knownAfter at h
  split at h
  · rename_i hg
    cases h
    rw [Bool.and_eq_true] at hg
    exact hg.2
  · cases h

/-- With each session asked on its own, the facade takes up a session exactly when the gate allows its question,
given an endpoint answer that is an allow whenever the gate allows the question and a remembered allow the gate
gives. -/
theorem upOf_eq (c : Cfg) (ha : c.askEach = true) (s : State) (p : Nat) (q : Q) (ep : Bool) (kn : Option Q)
    (hep : gate s p q = true → ep = true) (hkn : kn = some q → gate s p q = true) :
    upOf c s p q ep kn = gate s p q := by
  have hk : decide (kn = some q) = true → gate s p q = true := fun h => hkn (of_decide_eq_true h)
  unfold upOf
  unfold gate at hep hk ⊢
  rw [ha]
  revert hep hk
  generalize s.revoked p = r
  generalize s.hook p q = h
  generalize decide (kn = some q) = k
  cases r <;> cases h <;> cases ep <;> cases k <;> decide

/-- With each session asked on its own, a session the facade takes up is one the gate allows, or one the remembered
allow for exactly its question covers. -/
theorem upOf_cross (c : Cfg) (ha : c.askEach = true) (s : State) (p : Nat) (q : Q) (ep : Bool) (kn : Option Q)
    (h : upOf c s p q ep kn = true) : gate s p q = true ∨ decide (kn = some q) = true := by
  unfold upOf at h
  unfold gate
  rw [ha] at h
  revert h
  generalize s.revoked p = r
  generalize s.hook p q = hk
  generalize decide (kn = some q) = k
  cases r <;> cases hk <;> cases ep <;> cases k <;> decide

/-- Two states whose gate agrees on peer `x` agree on whether it is allowed anything. -/
theorem anyB_congr (c : Cfg) (s t : State) (x : Nat) (h : ∀ q, gate t x q = gate s x q) : anyB c t x = anyB c s x := by
  unfold anyB
  exact congrArg _ (funext h)

end Vinc.FacadeAcpForget
