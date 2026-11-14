import Vinc.Axioms

/-!
# A hub's wake for a subscriber it keeps behind

The story. A hub pushes a topic to a subscriber over a stream. When the stream is full the hub keeps the subscriber
behind: it pushes it nothing new and remembers its place in the log (`behind.rs`). The hub serves that place only
when it is woken: the host reports that a full stream took more bytes (`StreamWritable`, vinc-node `events.rs`,
which calls `peer_writable`). The subscriber's session can be replaced. The new stream starts empty, so it was never
full and no host ever reports it writable; the subscriber sends a SUB on it (membership's resubscribe).

What must never happen: a subscriber the hub keeps behind with nothing left that will wake it, because then it is
pushed nothing live again and only a periodic gap repair reaches it.

The fix (`gap.rs` `on_sub`): a SUB from a subscriber the hub keeps behind wakes its catch-up. The finite counterpart
of `proofs/tla/BroadcastPush.tla` (`WakeOrPending`, `LiveAgain`, and the `_noresume` plants). Facts:
- with the fix every step keeps `Inv` (`wake_inv`), and the start satisfies it (`inv_init`);
- without it, a subscriber that falls behind and gets a new session reaches a stuck state (`reach_stuck`), and no
  step ever leaves a stuck state (`stuck_closed`), so it is never served again (`wake_stuck_without`);
- with it, the SUB that follows the new session wakes that same subscriber (`sub_wakes`).
-/

namespace Vinc.BroadcastWake

/-- What the hub knows about one subscriber. -/
structure St where
  -- the hub keeps the subscriber behind (an entry in `behind` and in `lagging`)
  behind : Bool
  -- the subscriber's stream has no room (`Host::backlogged`)
  full : Bool
  -- the host reported that the stream has room, and the hub serves the subscriber's place in the log
  wake : Bool
  -- a SUB from the subscriber's new session is on its way to the hub
  subq : Bool
  deriving DecidableEq, Repr

/-- What can happen to one subscriber. -/
inductive Step where
  -- a push finds the stream full: the hub keeps the subscriber behind (`fall_behind`)
  | fallBehind
  -- the subscriber reads from its stream; a full stream gets room and the host reports it (`StreamWritable`)
  | drain
  -- the stream fills; frames reach it only by pushes, which a behind subscriber gets only while it is served
  | fill
  -- the hub serves a woken subscriber (`peer_writable`); `done` when it sent the newest message (caught up)
  | catchUp (done : Bool)
  -- the session is replaced: an empty stream nobody reports writable, and a SUB on its way
  | swap
  -- the SUB arrives at the hub (`on_sub`)
  | sub
  deriving DecidableEq, Repr

/-- Nothing behind, nothing full, nobody woken, no SUB on its way. -/
def init : St := ⟨false, false, false, false⟩

/-- One step; `resume` is the fix (a SUB wakes a subscriber the hub keeps behind). A step whose condition does not
hold changes nothing. -/
def step (resume : Bool) : Step → St → St
  -- only a full stream refuses a push, and a subscriber already behind is pushed nothing
  | .fallBehind, s => if s.full && !s.behind then { s with behind := true } else s
  -- a full stream gets room; the host's report wakes the hub for a subscriber that is behind
  | .drain, s => if s.full then { s with full := false, wake := s.wake || s.behind } else s
  -- frames reach the stream only while the subscriber is not behind (live pushes) or is served (catch-up)
  | .fill, s => if !s.behind || s.wake then { s with full := true } else s
  -- the hub serves a woken subscriber whose stream has room; once caught up it is no longer behind nor woken
  | .catchUp done, s =>
    if s.wake && s.behind && !s.full then (if done then { s with behind := false, wake := false } else s) else s
  -- a new session: its stream is empty, nothing wakes the hub for it, and the subscriber sends a SUB
  | .swap, s => { s with full := false, wake := false, subq := true }
  -- the SUB arrives; with the fix it wakes a subscriber the hub keeps behind
  | .sub, s => if s.subq then { s with subq := false, wake := s.wake || (resume && s.behind) } else s

/-- A subscriber that is behind is woken, or its stream is full (its drain will wake it), or its SUB is on its way. -/
def Inv (s : St) : Prop := s.behind = true → s.wake = true ∨ s.full = true ∨ s.subq = true

/-- The start satisfies the invariant. -/
theorem inv_init : Inv init := by
  -- nothing is behind at the start
  simp [Inv, init]

/-- With the fix, every step keeps the invariant. -/
theorem wake_inv (st : Step) (s : St) (h : Inv s) : Inv (step true st s) := by
  -- every subscriber state (four flags) and every step, checked one by one
  obtain ⟨b, f, w, q⟩ := s
  cases st <;> cases b <;> cases f <;> cases w <;> cases q <;> simp_all [step, Inv] <;>
    -- the catch-up step also splits on whether it caught the subscriber up
    (try split) <;> simp_all

/-- Behind, not woken, its stream with room: nothing will serve this subscriber unless something wakes it. -/
def Stuck (s : St) : Prop := s.behind = true ∧ s.wake = false ∧ s.full = false

/-- Without the fix, no step leaves a stuck state. -/
theorem stuck_closed (st : Step) (s : St) (h : Stuck s) : Stuck (step false st s) := by
  -- the stuck flags are fixed; the SUB flag can be anything
  obtain ⟨b, f, w, q⟩ := s
  obtain ⟨hb, hw, hf⟩ := h
  simp only at hb hw hf
  subst hb hw hf
  cases st <;> cases q <;> simp [step, Stuck] <;> (try split) <;> simp

/-- Without the fix: the stream fills, the subscriber falls behind, its session is replaced and its SUB arrives. -/
def afterSwap : St := step false .sub (step false .swap (step false .fallBehind (step false .fill init)))

/-- That state is stuck, and the invariant fails there. -/
theorem reach_stuck : Stuck afterSwap ∧ ¬ Inv afterSwap := by
  -- the four steps computed from the start: behind, not woken, room in the stream, no SUB left
  simp [afterSwap, Stuck, Inv, step, init]

/-- Without the fix, whatever happens after those four steps, the subscriber stays stuck: never served again. -/
theorem wake_stuck_without (rest : List Step) :
    Stuck (rest.foldl (fun s st => step false st s) afterSwap) := by
  -- stuck after the four steps, and every further step keeps it stuck
  suffices ∀ (l : List Step) (s : St), Stuck s → Stuck (l.foldl (fun s st => step false st s) s) from
    this rest _ reach_stuck.1
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons x xs ih => intro s h; exact ih _ (stuck_closed x s h)

/-- With the fix, the SUB of the new session wakes the same subscriber. -/
theorem sub_wakes : (step true .sub (step true .swap (step true .fallBehind (step true .fill init)))).wake = true := by
  -- the four steps computed from the start, with the fix
  decide

end Vinc.BroadcastWake

#audit_axioms Vinc.BroadcastWake.wake_inv
#audit_axioms Vinc.BroadcastWake.stuck_closed
#audit_axioms Vinc.BroadcastWake.wake_stuck_without
#audit_axioms Vinc.BroadcastWake.sub_wakes
