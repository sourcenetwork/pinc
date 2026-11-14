import Vinc.Axioms

/-!
# The facade's access decisions: the hook asked per protocol and direction, against the endpoint's answer per peer

The story, in plain words. Peers dial this node and this node dials them; a session has a protocol and a direction,
the question the access hook is asked about it. The endpoint keeps one answer per peer for 30 s: a session of a peer
with an answer is decided on it, otherwise the endpoint raises a check. The facade asks the hook about the check's
question, remembers an allow for exactly that question as long as the endpoint keeps its answer, and tells the endpoint
"allow" when the gate allows the peer that question or any other of the listed protocols and directions. A session
the endpoint lets through comes up at the facade: refused while its peer is revoked, else taken up if the remembered
allow is for its own question or the hook allows that question now. A live session asks again before its peer's answer
runs out, and a deny then closes every session of the peer. The application revokes peers, lifts revocations and edits
its hook, telling the endpoint through `admission_changed`; each of those drops both answers of the peer, and a dial to
a revoked peer is refused before anything is sent. The question a check asks: the first check of a session this node
dialed asks its own; the first check of an accepted session, and a recheck, ask its protocol inbound or outbound (the
code asks outbound while a dial of that protocol to the peer waits).

What must never happen: a session taken up on an allow the hook gave for another protocol or direction (issue #440);
a deny held for a peer the gate allows a question a session may have, which refuses or closes the sessions of that
question; a session decided on answers the gate would not give at that moment; a cached or remembered answer that is
not the gate's current one; a revoked peer holding a session this node dialed.

This is a transcription of `proofs/tla/FacadeAcpForget.tla` over any number of peers, protocols and steps. The Rust code
is `crates/vinc/src/engine.rs` (`Core::{session_up, session_admitted, admits_other}`, the `AcpCheck` arm of `on_event`),
`crates/vinc/src/engine/gate.rs` (`Known::{covers, remember, forget}`, `direction`), `crates/vinc/src/engine/ops.rs`
(`Core::{revoke, unrevoke, forget_access, listen}`), `crates/vinc-core/src/commands.rs` (`Command::AcpForget`),
`crates/vinc-core/src/acp.rs` (`start_acp`, `ask_acp`, `acp_answer`), `crates/vinc-node/src/node.rs`
(`Node::{revoke, unrevoke, forget_access}`) and `crates/vinc/src/endpoint.rs`
(`Endpoint::{revoke, unrevoke, connect, admission_changed}`).

Main theorems: `inv_reach` (with the code's settings every reachable state keeps the four promises),
`noCrossAllow_reach` (with each session asked on its own, no session is taken up on an allow given for another
question, whatever the host does), `noCrossDeny_reach` (with the code's settings no deny is held for a peer the gate
allows a question a session may have), `noForgetOnLift_bad` (the code before the unrevoke fix refuses an unrevoked peer
on a stale deny), `noForgetOnRevoke_bad` (keeping the answer across a revoke lets a revoked peer through on a stale
allow), `noRefuseDial_bad` (a dial to a revoked peer reaches it), `noForgetOnChange_bad` (a host that allows a peer
without telling the endpoint has it refused on a stale deny), `perPeer_bad` (the rule before #440 takes up a protocol
the hook refuses on an allow given for another), `noAny_bad` (telling the endpoint the asking session's own refusal
denies a peer the hook allows on another protocol) and `unlisted_bad` (found: an outbound session on a protocol this
node does not list is closed at its recheck, which asks the inbound question).
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
-- whether it was taken up, and what the gate said then about the question and about the peer, and whether the
-- remembered allow covered it.
structure Last where
  done : Bool
  peer : Nat
  q : Q
  ep : Bool
  up : Bool
  gate : Bool
  any : Bool
  cov : Bool

-- What does not change: the hook's first answers, the protocols the facade lists, those this node dials without
-- listing them (outbound sessions only), and the six switches that give the witnesses.
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

-- The state: the hook's answers now, which peers are revoked, the endpoint's answer and the facade's remembered allow
-- per peer, the last decision, and which peers hold a session we dialed.
structure State where
  hook : Nat → Q → Bool
  revoked : Nat → Bool
  cache : Nat → Ans
  known : Nat → Option Q
  last : Last
  out : Nat → Bool

-- Change one entry of a function.
def set {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

-- The changed entry reads back the new value.
theorem set_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : set f i v i = v := by simp [set]

-- Every other entry is unchanged.
theorem set_other {α : Type} (f : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) : set f i v j = f j := by
  simp [set, h]

-- Both directions of each listed protocol: the questions the facade asks about for the endpoint's answer.
def listedQs (c : Cfg) : List Q := c.listed.flatMap (fun a => [⟨a, .inb⟩, ⟨a, .outb⟩])

-- The questions of sessions: a listed protocol either way, a dialed one outbound.
def qs (c : Cfg) : List Q := listedQs c ++ c.dialed.map (fun a => ⟨a, .outb⟩)

-- The gate: no for a revoked peer, else the hook's answer for the question.
def gate (s : State) (p : Nat) (q : Q) : Bool := !s.revoked p && s.hook p q

-- Whether the gate allows `p` some question a session may have.
def anyB (c : Cfg) (s : State) (p : Nat) : Bool := (qs c).any (gate s p)

-- The endpoint's answer for a check of `p` that asked `a`: the gate's answer for `a`, or, with the fix, also an allow
-- when the gate allows the peer another listed question.
def told (c : Cfg) (s : State) (p : Nat) (a : Q) : Bool :=
  gate s p a || (c.answerAny && (listedQs c).any (fun q => decide (q ≠ a) && gate s p q))

-- What the facade remembers after a check of `p` that asked `a`: an allow for exactly `a`, never a refusal.
def knownAfter (c : Cfg) (s : State) (p : Nat) (a : Q) : Option Q := if c.askEach && gate s p a then some a else none

-- The questions a check raised by a session with question `q` may ask; `again` for a recheck.
abbrev asked (again : Bool) (q a : Q) : Prop := a.proto = q.proto ∧ (again = true ∨ q.dir = .inb ∨ a = q)

-- Whether the facade takes up a session of `p` with question `q` that the endpoint let through on `ep`, with the
-- remembered allow `kn`: not while revoked, and with each session asked on its own only if `kn` is for `q` or the hook
-- allows `q`; the rule before #440 took up whatever the endpoint let through.
def upOf (c : Cfg) (s : State) (p : Nat) (q : Q) (ep : Bool) (kn : Option Q) : Bool :=
  ep && !s.revoked p && (!c.askEach || decide (kn = some q) || s.hook p q)

-- The start: the hook's first answers, nobody revoked, nothing cached or remembered, nothing decided, nothing dialed.
def init (c : Cfg) : State :=
  ⟨c.hook, fun _ => false, fun _ => .none, fun _ => none, ⟨false, 0, ⟨0, .inb⟩, false, false, false, false, false⟩,
   fun _ => false⟩

-- The state after each action of the TLA+ model of the same name.
-- A session of `p` with question `q` is decided on the endpoint's answer for `p`.
def cachedS (c : Cfg) (s : State) (p : Nat) (q : Q) : State :=
  { s with last := ⟨true, p, q, asBool (s.cache p), upOf c s p q (asBool (s.cache p)) (s.known p), gate s p q,
                    anyB c s p, decide (s.known p = some q)⟩ }
-- No answer for `p`: a check asks `a`, the facade remembers an allow for `a`, the endpoint caches what it is told, and
-- the session is decided on it.
def askS (c : Cfg) (s : State) (p : Nat) (q a : Q) : State :=
  { s with cache := set s.cache p (cacheOf (told c s p a)),
           known := set s.known p (knownAfter c s p a),
           last := ⟨true, p, q, told c s p a, upOf c s p q (told c s p a) (knownAfter c s p a), gate s p q,
                    anyB c s p, decide (knownAfter c s p a = some q)⟩ }
-- A live session of `p` asks again and the check asks `a`; a deny closes every session of `p`.
def recheckS (c : Cfg) (s : State) (p : Nat) (a : Q) : State :=
  { s with cache := set s.cache p (cacheOf (told c s p a)), known := set s.known p (knownAfter c s p a) }
-- `p` is revoked: with the fix both its answers go, and every session with it ends.
def revokeS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with revoked := set s.revoked p true,
           cache := if c.forgetOnRevoke then set s.cache p .none else s.cache,
           known := if c.forgetOnRevoke then set s.known p none else s.known,
           out := set s.out p false }
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
-- This node dials `p`: refused up front while `p` is revoked, else the session reaches `p`.
def dialS (c : Cfg) (s : State) (p : Nat) : State :=
  { s with out := if c.refuseDial && s.revoked p then s.out else set s.out p true }
-- A session this node dialed ends for another reason.
def hangupS (s : State) (p : Nat) : State := { s with out := set s.out p false }
-- The host edits its hook's answer for `p` on `q` and, with the fix, calls admission_changed for `p`.
def rehookS (c : Cfg) (s : State) (p : Nat) (q : Q) : State :=
  { s with hook := set s.hook p (fun x => if x = q then !s.hook p q else s.hook p x),
           cache := if c.forgetOnChange then set s.cache p .none else s.cache,
           known := if c.forgetOnChange then set s.known p none else s.known }

-- One step of the system, with the guard of each action.
inductive Step (c : Cfg) : State → State → Prop where
  | cached (s : State) (p : Nat) (q : Q) : s.cache p ≠ .none → q ∈ qs c → Step c s (cachedS c s p q)
  | ask (s : State) (p : Nat) (q a : Q) : s.cache p = .none → q ∈ qs c → asked false q a →
      Step c s (askS c s p q a)
  | recheck (s : State) (p : Nat) (q a : Q) : s.cache p = .allow → q ∈ qs c → asked true q a →
      Step c s (recheckS c s p a)
  | revoke (s : State) (p : Nat) : Step c s (revokeS c s p)
  | lift (s : State) (p : Nat) : Step c s (liftS c s p)
  | expire (s : State) (p : Nat) : Step c s (expireS s p)
  | lapse (s : State) (p : Nat) : Step c s (lapseS s p)
  | clear (s : State) : Step c s (clearS s)
  | dial (s : State) (p : Nat) : Step c s (dialS c s p)
  | hangup (s : State) (p : Nat) : Step c s (hangupS s p)
  | rehook (s : State) (p : Nat) (q : Q) : Step c s (rehookS c s p q)

-- The states the system can reach from the start.
inductive Reach (c : Cfg) : State → Prop where
  | init : Reach c (init c)
  | step (s t : State) : Reach c s → Step c s t → Reach c t

-- Every session is decided with the answers the gate gives at that moment: the endpoint's for its peer is whether the
-- gate allows the peer anything, and the session is taken up exactly when the gate allows its own question.
abbrev DecideFresh (s : State) : Prop := s.last.done = true → s.last.ep = s.last.any ∧ s.last.up = s.last.gate

-- Every cached answer is the one the gate would give now: whether it allows the peer anything.
abbrev CacheSound (c : Cfg) (s : State) : Prop := ∀ p, s.cache p ≠ .none → asBool (s.cache p) = anyB c s p

-- Every remembered allow is one the gate gives now, for exactly that question.
abbrev KnownSound (s : State) : Prop := ∀ p q, s.known p = some q → gate s p q = true

-- No revoked peer holds a session this node dialed.
abbrev NoDialRevoked (s : State) : Prop := ∀ p, s.out p = true → s.revoked p = false

-- No session is taken up on an allow given for another protocol or direction: the gate allows its own question at
-- that moment, or the remembered allow is for exactly its question.
abbrev NoCrossAllow (s : State) : Prop :=
  s.last.done = true → s.last.up = true → s.last.gate = true ∨ s.last.cov = true

-- The endpoint holds a deny only for a peer the gate allows no question a session may have.
abbrev NoCrossDeny (c : Cfg) (s : State) : Prop := ∀ p, s.cache p = .deny → ∀ q ∈ qs c, gate s p q = false

-- The four promises together.
abbrev Inv (c : Cfg) (s : State) : Prop := DecideFresh s ∧ CacheSound c s ∧ KnownSound s ∧ NoDialRevoked s

/-- The start keeps the four promises. -/
theorem inv_init (c : Cfg) : Inv c (init c) := by
  refine ⟨fun h => ?_, fun q h => ?_, fun p q h => ?_, fun q h => ?_⟩
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

/-- With nothing dialed outside the list, the questions of sessions are the listed ones. -/
theorem qs_nil (c : Cfg) (h : c.dialed = []) : qs c = listedQs c := by simp [qs, h]

/-- A check asks about the protocol of the session that raised it, so, with nothing dialed outside the list, a listed
question. -/
theorem asked_listed (c : Cfg) (hdl : c.dialed = []) (again : Bool) (q a : Q) (hq : q ∈ qs c)
    (ha : asked again q a) : a ∈ listedQs c := by
  rw [qs_nil c hdl, mem_listedQs] at hq
  rw [mem_listedQs, ha.1]
  exact hq

/-- A question of a session the gate allows makes the peer allowed something. -/
theorem any_of_gate (c : Cfg) (s : State) (p : Nat) (q : Q) (hq : q ∈ qs c) (hg : gate s p q = true) :
    anyB c s p = true :=
  List.any_eq_true.mpr ⟨q, hq, hg⟩

/-- With the fix, the endpoint is told whether the gate allows the peer any question a session may have. -/
theorem told_any (c : Cfg) (hn : c.answerAny = true) (hdl : c.dialed = []) (s : State) (p : Nat) (a : Q)
    (ha : a ∈ listedQs c) : told c s p a = anyB c s p := by
  unfold told anyB
  rw [qs_nil c hdl, hn, Bool.true_and]
  cases hg : gate s p a with
  | true =>
    rw [Bool.true_or]
    exact (List.any_eq_true.mpr ⟨a, ha, hg⟩).symm
  | false =>
    rw [Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hxg⟩
      rw [Bool.and_eq_true] at hxg
      exact ⟨x, hx, hxg.2⟩
    · rintro ⟨x, hx, hxg⟩
      refine ⟨x, hx, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨fun hxa => ?_, hxg⟩
      subst hxa
      rw [hg] at hxg
      exact Bool.false_ne_true hxg

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

/-- Dropping the endpoint's answer for `p` while only `p`'s hook answers and revoked bit may change keeps every
cached answer sound: `p` has none left, and no other peer's answer or gate moved. -/
theorem forget_cache (c : Cfg) (s t : State) (p : Nat) (hg : ∀ x, x ≠ p → ∀ q, gate t x q = gate s x q)
    (hcache : t.cache = set s.cache p .none) (hc : CacheSound c s) : CacheSound c t := by
  intro x hx
  rw [hcache] at hx ⊢
  by_cases hxp : x = p
  · subst hxp; rw [set_same] at hx; exact absurd rfl hx
  · rw [set_other _ _ _ _ hxp] at hx ⊢
    rw [anyB_congr c s t x (hg x hxp)]
    exact hc x hx

/-- Dropping the remembered allow of `p` under the same condition keeps every remembered allow sound. -/
theorem forget_known (s t : State) (p : Nat) (hg : ∀ x, x ≠ p → ∀ q, gate t x q = gate s x q)
    (hknown : t.known = set s.known p none) (hk : KnownSound s) : KnownSound t := by
  intro x q hxq
  rw [hknown] at hxq
  by_cases hxp : x = p
  · subst hxp; rw [set_same] at hxq; cases hxq
  · rw [set_other _ _ _ _ hxp] at hxq
    rw [hg x hxp q]
    exact hk x q hxq

/-- Dropping both answers of `p` under the same condition keeps both sound. -/
theorem forget_sound (c : Cfg) (s t : State) (p : Nat) (hg : ∀ x, x ≠ p → ∀ q, gate t x q = gate s x q)
    (hcache : t.cache = set s.cache p .none) (hknown : t.known = set s.known p none) (hc : CacheSound c s)
    (hk : KnownSound s) : CacheSound c t ∧ KnownSound t :=
  ⟨forget_cache c s t p hg hcache hc, forget_known s t p hg hknown hk⟩

/-- A check of `p` that asks a listed question leaves both answers of `p` sound, with the fix. -/
theorem check_sound (c : Cfg) (hn : c.answerAny = true) (hdl : c.dialed = []) (s t : State) (p : Nat) (a : Q)
    (hal : a ∈ listedQs c) (hgt : gate t = gate s) (hcache : t.cache = set s.cache p (cacheOf (told c s p a)))
    (hknown : t.known = set s.known p (knownAfter c s p a)) (hc : CacheSound c s) (hk : KnownSound s) :
    CacheSound c t ∧ KnownSound t := by
  constructor
  · intro x hx
    rw [anyB_congr c s t x (fun q => by rw [hgt])]
    rw [hcache] at hx ⊢
    by_cases hxp : x = p
    · subst hxp; rw [set_same, asBool_cacheOf]; exact told_any c hn hdl s _ a hal
    · rw [set_other _ _ _ _ hxp] at hx ⊢; exact hc x hx
  · intro x q hxq
    rw [hgt]
    rw [hknown] at hxq
    by_cases hxp : x = p
    · subst hxp; rw [set_same] at hxq; exact knownAfter_sound c s _ a q hxq
    · rw [set_other _ _ _ _ hxp] at hxq; exact hk x q hxq

/-- With the code's settings every step keeps the four promises. -/
theorem inv_step (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true) (hd : c.refuseDial = true)
    (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true) (hdl : c.dialed = [])
    (s t : State) (hs : Inv c s) (st : Step c s t) : Inv c t := by
  obtain ⟨hf, hc, hk, ho⟩ := hs
  cases st with
  | cached p q hp hq =>
    refine ⟨fun _ => ⟨hc p hp, ?_⟩, hc, hk, ho⟩
    exact upOf_eq c ha s p q _ _ (fun hg => (hc p hp).trans (any_of_gate c s p q hq hg)) (hk p q)
  | ask p q a _ hq has =>
    have hal := asked_listed c hdl false q a hq has
    have ht := told_any c hn hdl s p a hal
    have hck := check_sound c hn hdl s (askS c s p q a) p a hal rfl rfl rfl hc hk
    refine ⟨fun _ => ⟨ht, ?_⟩, hck.1, hck.2, ho⟩
    exact upOf_eq c ha s p q _ _ (fun hg => ht.trans (any_of_gate c s p q hq hg)) (knownAfter_sound c s p a q)
  | recheck p q a _ hq has =>
    have hal := asked_listed c hdl true q a hq has
    have hck := check_sound c hn hdl s (recheckS c s p a) p a hal rfl rfl rfl hc hk
    exact ⟨hf, hck.1, hck.2, ho⟩
  | revoke p =>
    have hck := forget_sound c s (revokeS c s p) p
      (fun x hxp q => by simp only [gate, revokeS]; rw [set_other _ _ _ _ hxp])
      (by simp [revokeS, hr]) (by simp [revokeS, hr]) hc hk
    refine ⟨hf, hck.1, hck.2, fun q hq => ?_⟩
    simp only [revokeS] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [set_same] at hq; exact absurd hq (by decide)
    · rw [set_other _ _ _ _ hqp] at hq ⊢; exact ho q hq
  | lift p =>
    have hck := forget_sound c s (liftS c s p) p
      (fun x hxp q => by simp only [gate, liftS]; rw [set_other _ _ _ _ hxp])
      (by simp [liftS, hl]) (by simp [liftS, hl]) hc hk
    refine ⟨hf, hck.1, hck.2, fun q hq => ?_⟩
    simp only [liftS] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [set_same]
    · rw [set_other _ _ _ _ hqp]; exact ho q hq
  | expire p => exact ⟨hf, forget_cache c s (expireS s p) p (fun _ _ _ => rfl) rfl hc, hk, ho⟩
  | lapse p => exact ⟨hf, hc, forget_known s (lapseS s p) p (fun _ _ _ => rfl) rfl hk, ho⟩
  | clear => exact ⟨hf, hc, fun x q hxq => by simp [clearS] at hxq, ho⟩
  | dial p =>
    refine ⟨hf, hc, hk, fun q hq => ?_⟩
    simp only [dialS, hd, Bool.true_and] at hq ⊢
    cases hrv : s.revoked p with
    | true => simp [hrv] at hq; exact ho q hq
    | false =>
      simp [hrv] at hq
      by_cases hqp : q = p
      · subst hqp; exact hrv
      · rw [set_other _ _ _ _ hqp] at hq; exact ho q hq
  | hangup p =>
    refine ⟨hf, hc, hk, fun q hq => ?_⟩
    simp only [hangupS] at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [set_same] at hq; exact absurd hq (by decide)
    · rw [set_other _ _ _ _ hqp] at hq; exact ho q hq
  | rehook p y =>
    have hck := forget_sound c s (rehookS c s p y) p
      (fun x hxp q => by simp only [gate, rehookS]; rw [set_other _ _ _ _ hxp])
      (by simp [rehookS, hh]) (by simp [rehookS, hh]) hc hk
    exact ⟨hf, hck.1, hck.2, ho⟩

/-- With the code's settings every reachable state keeps the four promises. -/
theorem inv_reach (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true) (hd : c.refuseDial = true)
    (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true) (hdl : c.dialed = [])
    (s : State) (h : Reach c s) : Inv c s := by
  induction h with
  | init => exact inv_init c
  | step s t _ st ih => exact inv_step c hl hr hd hh ha hn hdl s t ih st

/-- With each session asked on its own, no session is taken up on an allow given for another protocol or direction,
whatever the host does with revoke, unrevoke, `admission_changed` and the protocols it lists. -/
theorem noCrossAllow_reach (c : Cfg) (ha : c.askEach = true) (s : State) (h : Reach c s) : NoCrossAllow s := by
  induction h with
  | init => intro hd; simp [init] at hd
  | step s t _ st ih =>
    cases st with
    | cached p q _ _ => exact fun _ hu => upOf_cross c ha s p q _ _ hu
    | ask p q a _ _ _ => exact fun _ hu => upOf_cross c ha s p q _ _ hu
    | _ => exact ih

/-- With the code's settings the endpoint never holds a deny for a peer the gate allows a question a session may have:
a refusal of one protocol never refuses or closes a session of another the hook allows. -/
theorem noCrossDeny_reach (c : Cfg) (hl : c.forgetOnLift = true) (hr : c.forgetOnRevoke = true)
    (hd : c.refuseDial = true) (hh : c.forgetOnChange = true) (ha : c.askEach = true) (hn : c.answerAny = true)
    (hdl : c.dialed = []) (s : State) (h : Reach c s) : NoCrossDeny c s := by
  intro p hp q hq
  have hcs := (inv_reach c hl hr hd hh ha hn hdl s h).2.1 p (by rw [hp]; decide)
  rw [hp] at hcs
  cases hg : gate s p q with
  | false => rfl
  | true =>
    rw [any_of_gate c s p q hq hg] at hcs
    exact absurd hcs (by decide)

-- The witness settings: the hook allows peer 1 protocol 1 either way and nothing else; protocols 1 and 2 are listed.
def witness (lift revoke dial change each any : Bool) : Cfg :=
  { hook := fun p q => p == 1 && q.proto == 1, listed := [1, 2], dialed := [], forgetOnLift := lift,
    forgetOnRevoke := revoke, refuseDial := dial, forgetOnChange := change, askEach := each, answerAny := any }

-- A session of protocol 1, and one of protocol 2, both inbound.
def q1 : Q := ⟨1, .inb⟩
def q2 : Q := ⟨2, .inb⟩

/-- The code before the unrevoke fix: peer 1 is revoked and dials, the deny is cached, the revocation is lifted and the
deny kept, so its next session is refused although the gate now lets it in. -/
theorem noForgetOnLift_bad : ∃ s, Reach (witness false true true true true true) s ∧ ¬ DecideFresh s := by
  let c := witness false true true true true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.revoke _ 1)
  have r2 := Reach.step _ _ r1 (Step.ask (c := c) _ 1 q1 q1 (by decide) (by decide) (by decide))
  have r3 := Reach.step _ _ r2 (Step.lift (c := c) _ 1)
  have r4 := Reach.step _ _ r3 (Step.cached (c := c) _ 1 q1 (by decide) (by decide))
  refine ⟨_, r4, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- Keeping the answers across a revoke: peer 1's allow is cached, it is revoked, and its next session goes through
the endpoint on the cached allow although the gate now refuses the peer. -/
theorem noForgetOnRevoke_bad : ∃ s, Reach (witness true false true true true true) s ∧ ¬ DecideFresh s := by
  let c := witness true false true true true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.ask _ 1 q1 q1 (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.revoke (c := c) _ 1)
  have r3 := Reach.step _ _ r2 (Step.cached (c := c) _ 1 q1 (by decide) (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- A dial that is not refused up front: peer 1 is revoked and this node's dial reaches it. -/
theorem noRefuseDial_bad : ∃ s, Reach (witness true true false true true true) s ∧ ¬ NoDialRevoked s := by
  let c := witness true true false true true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.revoke _ 1)
  have r2 := Reach.step _ _ r1 (Step.dial (c := c) _ 1)
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h 1 (by decide)) (by decide)

/-- A host that edits its hook without telling the endpoint: peer 2 is refused everything and the deny cached, the
host allows it protocol 1 inbound, and its next session on it is refused although the hook now admits it. -/
theorem noForgetOnChange_bad : ∃ s, Reach (witness true true true false true true) s ∧ ¬ DecideFresh s := by
  let c := witness true true true false true true
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.ask _ 2 q1 q1 (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.rehook (c := c) _ 2 q1)
  have r3 := Reach.step _ _ r2 (Step.cached (c := c) _ 2 q1 (by decide) (by decide))
  refine ⟨_, r3, fun h => ?_⟩
  exact absurd (h (by decide)) (by decide)

/-- The rule before #440: peer 1 dials on protocol 1, the hook allows it and the endpoint caches the allow; its session
on protocol 2, which the hook refuses, comes up on that allow. -/
theorem perPeer_bad : ∃ s, Reach (witness true true true true false false) s ∧ ¬ NoCrossAllow s := by
  let c := witness true true true true false false
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.ask _ 1 q1 q1 (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.cached (c := c) _ 1 q2 (by decide) (by decide))
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h (by decide) (by decide)) (by decide)

/-- Telling the endpoint the asking session's own refusal: peer 1 dials first on protocol 2, which the hook refuses,
and the deny is cached although the hook allows it protocol 1. -/
theorem noAny_bad :
    ∃ s, Reach (witness true true true true true false) s ∧
      ¬ NoCrossDeny (witness true true true true true false) s := by
  let c := witness true true true true true false
  have r1 := Reach.step _ _ (Reach.init (c := c)) (Step.ask _ 1 q2 q2 (by decide) (by decide) (by decide))
  refine ⟨_, r1, fun h => ?_⟩
  exact absurd (h 1 (by decide) q1 (by decide)) (by decide)

-- The finding's settings: protocol 1 is listed, protocol 2 is dialed without being listed, and the hook allows peer 1
-- protocol 2 outbound and nothing else.
def unlisted : Cfg :=
  { hook := fun p q => p == 1 && q == ⟨2, .outb⟩, listed := [1], dialed := [2], forgetOnLift := true,
    forgetOnRevoke := true, refuseDial := true, forgetOnChange := true, askEach := true, answerAny := true }

/-- Found: this node dials peer 1 on protocol 2, which it does not list; the check its dial raised asks protocol 2
outbound and the session comes up. Its recheck asks protocol 2 inbound, as no dial waits any more, which the hook
refuses, and the other questions the facade asks about are the listed protocol's, which the hook refuses too: the
endpoint is told deny, which closes the session the hook allows. -/
theorem unlisted_bad : ∃ s, Reach unlisted s ∧ ¬ NoCrossDeny unlisted s := by
  have r1 := Reach.step _ _ (Reach.init (c := unlisted))
    (Step.ask _ 1 ⟨2, .outb⟩ ⟨2, .outb⟩ (by decide) (by decide) (by decide))
  have r2 := Reach.step _ _ r1 (Step.recheck (c := unlisted) _ 1 ⟨2, .outb⟩ ⟨2, .inb⟩ (by decide) (by decide)
    (by decide))
  refine ⟨_, r2, fun h => ?_⟩
  exact absurd (h 1 (by decide) ⟨2, .outb⟩ (by decide)) (by decide)

end Vinc.FacadeAcpForget

#audit_axioms Vinc.FacadeAcpForget.inv_reach
#audit_axioms Vinc.FacadeAcpForget.noCrossAllow_reach
#audit_axioms Vinc.FacadeAcpForget.noCrossDeny_reach
#audit_axioms Vinc.FacadeAcpForget.noForgetOnLift_bad
#audit_axioms Vinc.FacadeAcpForget.noForgetOnRevoke_bad
#audit_axioms Vinc.FacadeAcpForget.noRefuseDial_bad
#audit_axioms Vinc.FacadeAcpForget.noForgetOnChange_bad
#audit_axioms Vinc.FacadeAcpForget.perPeer_bad
#audit_axioms Vinc.FacadeAcpForget.noAny_bad
#audit_axioms Vinc.FacadeAcpForget.unlisted_bad
