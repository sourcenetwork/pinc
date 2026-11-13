import Vinc.ReconcileSession

/-!
# Reconcile drive: the sessions of `drive.rs` as a sans-IO function

`attempt` runs one session of `Initiator::run` against `Responder::serve` over a fresh in-order channel pair, in the
lockstep of `tests/reconcile_common.rs` (`run_with`): the initiator sends, the responder handles the message and
answers with its reply (a cold side answers with its whole stream of chunks), the initiator handles every reply, and
the exchange ends when the initiator is `Done` or `Last`. The channel may reset: `Cut` names the message after which
either end sees `Reset` instead of the message it would have received (the `reset_after` of the test channel). A
protocol error of the responder resets the channel (`fail` in `drive.rs`), which the initiator sees as `Reset`;
a protocol error of the initiator is its own result and resets the channel too.

`runAttempts` is `Initiator::run_retry`: at least one and at most `attempts` attempts, each over a new channel, the
whole session retried after a `Reset`, any other result returned at once, every attempt reset giving `Exhausted`.
The initiator and responder objects are reused across attempts (as in the code): `start` and a fresh responder
message are what clear the previous session.
-/

namespace Vinc.Reconcile

/-- How a driven session ends (`RunError` and success). -/
inductive Run where
  | done (here there : List Item)
  | reset
  | protocol (e : Err)
  | closed
  | exhausted
  deriving DecidableEq, Repr

/-- The message after which each end of a channel sees a reset: the n-th received message of the initiator, of the
responder. -/
structure Cut where
  init : Option Nat := none
  resp : Option Nat := none

/-- A hit: the end that has received `n` messages is about to receive its next one. -/
def Cut.hits (c : Option Nat) (n : Nat) : Bool := c == some (n + 1)

/-- The messages a responder writes for one received message: `handle`, then `resume` while it says `chunk`. -/
def respServe (o : Oracle) (S : List Item) : Nat → Responder → Step → List Nat → List (List Nat) →
    Except Err (List (List Nat) × Responder)
  | 0, r, _, _, acc => .ok (acc, r)
  | fuel + 1, r, step, out, acc =>
    match step with
    | .send | .last => .ok (acc ++ [out], r)
    | .done | .wait => .ok (acc, r)
    | .chunk =>
      match r.resume o S with
      | .error e => .error e
      | .ok (step', out', r') => respServe o S fuel r' step' out' (acc ++ [out])

def respHandle (o : Oracle) (S : List Item) (r : Responder) (tx : List Nat) :
    Except Err (List (List Nat) × Responder) :=
  match r.handle o S tx with
  | .error e => .error e
  | .ok (step, out, r') => respServe o S (S.length + 2) r' step out [] 

/-- The initiator handles the replies in order: the next message to send, the result if the session ended. -/
def initReplies (oI : Oracle) (SI : List Item) (cut : Cut) :
    List (List Nat) → Nat → Initiator → Option (List Nat) →
    (Nat × Initiator × Option (List Nat) × Option Run)
  | [], n, i, pend => (n, i, pend, none)
  | m :: ms, n, i, pend =>
    if Cut.hits cut.init n then (n + 1, i, pend, some .reset)
    else
      match i.handle oI SI m with
      | .error e => (n + 1, i, pend, some (.protocol e))
      | .ok (.send, out, i') => initReplies oI SI cut ms (n + 1) i' (some out)
      | .ok (.last, _, i') => (n + 1, i', pend, some (.done i'.core.here i'.core.there))
      | .ok (.done, _, i') => (n + 1, i', pend, some (.done i'.core.here i'.core.there))
      | .ok (.wait, _, i') => initReplies oI SI cut ms (n + 1) i' pend
      | .ok (.chunk, _, i') => (n + 1, i', pend, some (.protocol (.malformed .state)))

/-- The lockstep loop: the responder receives `tx` (its `nr`-th message), the initiator then its replies. -/
def sessionLoop (oI oR : Oracle) (SI SR : List Item) (cut : Cut) :
    Nat → Nat → Nat → Initiator → Responder → List Nat → (Run × Initiator × Responder)
  | 0, _, _, i, r, _ => (.protocol .tooManyRounds, i, r)
  | fuel + 1, nr, ni, i, r, tx =>
    if Cut.hits cut.resp nr then (.reset, i, r)
    else
      match respHandle oR SR r tx with
      | .error _ => (.reset, i, r)
      | .ok (replies, r') =>
        let (ni', i', pend, res) := initReplies oI SI cut replies ni i none
        match res with
        | some run => (run, i', r')
        | none =>
          match pend with
          | some tx' => sessionLoop oI oR SI SR cut fuel (nr + 1) ni' i' r' tx'
          | none => (.closed, i', r')

/-- One attempt over a fresh channel: `Responder::serve` resets the responder, `Initiator::run` starts. -/
def attempt (oI oR : Oracle) (SI SR : List Item) (ref : Item) (cut : Cut) (fuel : Nat)
    (i : Initiator) (r : Responder) : Run × Initiator × Responder :=
  match i.start oI SI ref with
  | .error e => (.protocol e, i, r)
  | .ok (i0, tx) => sessionLoop oI oR SI SR cut fuel 0 0 i0 { r with side := .fresh } tx

/-- `Initiator::run_retry`: `attempts.max 1` attempts, the cut of attempt `k` is `cuts k`. -/
def runAttempts (oI oR : Oracle) (SI SR : List Item) (ref : Item) (fuel : Nat) (cuts : Nat → Cut) :
    Nat → Nat → Initiator → Responder → (Run × Initiator × Responder)
  | 0, _, i, r => (.exhausted, i, r)
  | n + 1, k, i, r =>
    match attempt oI oR SI SR ref (cuts k) fuel i r with
    | (.reset, i', r') => runAttempts oI oR SI SR ref fuel cuts n (k + 1) i' r'
    | (res, i', r') => (res, i', r')

/-- `attempts.max 1`. -/
def attemptsOf (attempts : Nat) : Nat := max attempts 1

/-! ## Stream resets

A reset at the first message of the responder is a reset of the attempt; an attempt that ends in anything but a reset
ends the run at once; and `attempts` attempts that are all reset end in `Exhausted`. Each attempt begins with
`Initiator::start` and a responder in the `fresh` side, so what an earlier attempt left in the objects is cleared
(`Core.clear`, the `fresh` branch of `Responder.handle`) or written before it is read: `ReconcileStaleRun` proves that
a run on used objects ends as the run on new ones (`runAttempts_fresh`). The trace validation of reused objects
(`TraceReconcile.tla`) and the model with `ResetOn` (`Reconcile_reset.cfg`) check the same on the real code and in
TLC. -/

theorem attempt_reset_first (oI oR : Oracle) (SI SR : List Item) (ref : Item) (cut : Cut) (fuel : Nat)
    (i : Initiator) (r : Responder) (i0 : Initiator) (tx : List Nat)
    (hs : i.start oI SI ref = .ok (i0, tx)) (hc : cut.resp = some 1) (hf : 0 < fuel) :
    (attempt oI oR SI SR ref cut fuel i r).1 = .reset := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp [attempt, hs, sessionLoop, Cut.hits, hc]

/-- An attempt that does not end in a reset is the result of the run: no retry after a protocol error or a result. -/
theorem runAttempts_stops (oI oR : Oracle) (SI SR : List Item) (ref : Item) (fuel : Nat) (cuts : Nat → Cut)
    (n k : Nat) (i : Initiator) (r : Responder) {res : Run} {i' : Initiator} {r' : Responder}
    (ha : attempt oI oR SI SR ref (cuts k) fuel i r = (res, i', r')) (hr : res ≠ .reset) :
    (runAttempts oI oR SI SR ref fuel cuts (n + 1) k i r).1 = res := by
  simp only [runAttempts, ha]

/-- Every attempt reset at the first message of the responder: `Exhausted`, whatever the attempt count and the objects. -/
theorem runAttempts_exhausted (oI oR : Oracle) (SI SR : List Item) (ref : Item) (fuel : Nat) (cuts : Nat → Cut)
    (hf : 0 < fuel) (hc : ∀ k, (cuts k).resp = some 1)
    (hs : ∀ i : Initiator, ∃ i0 tx, i.start oI SI ref = .ok (i0, tx)) :
    ∀ (n k : Nat) (i : Initiator) (r : Responder), (runAttempts oI oR SI SR ref fuel cuts n k i r).1 = .exhausted
  | 0, _, _, _ => rfl
  | n + 1, k, i, r => by
    obtain ⟨i0, tx, h0⟩ := hs i
    have ha := attempt_reset_first oI oR SI SR ref (cuts k) fuel i r i0 tx h0 (hc k) hf
    simp only [runAttempts]
    rcases hh : attempt oI oR SI SR ref (cuts k) fuel i r with ⟨res, i1, r1⟩
    rw [hh] at ha
    simp only at ha
    subst ha
    exact runAttempts_exhausted oI oR SI SR ref fuel cuts hf hc hs n (k + 1) i1 r1

#audit_axioms Vinc.Reconcile.attempt_reset_first
#audit_axioms Vinc.Reconcile.runAttempts_stops
#audit_axioms Vinc.Reconcile.runAttempts_exhausted

end Vinc.Reconcile
