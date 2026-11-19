import Pinc.TransportTimers
import Pinc.Axioms

/-!
# The timers and the closing state: theorems

The properties `proofs/tla/Timers.tla` checks over small bounds, proved for every state, every input and every run
of the model in `Pinc.TransportTimers`:

* `poll_timeout` is exactly the minimum of the deadlines the code combines: the idle deadline and the list `reads`
  (the end of a link outage, the wake wait and, with the link down, recovery while nothing can leave; otherwise the
  handshake retransmit while unconfirmed, the REKEY resend, recovery, the acknowledgement while the path may be sent
  64 bytes, the pacer, the paths, the wake wait, the end of the outage, and on a connected connection the keepalive
  and the MTU timer): it is at most each of them and equal to one (`poll_le_idle`, `poll_le_read`,
  `poll_attained`); it is none exactly once closed and 0 while closing (`poll_none_iff`, `poll_closing`);
* `handle_timeout` does nothing before `poll_timeout` when no probe timeout fires (`timeout_before_poll`), closes silently and does nothing else
  at or after the idle deadline and never before (`timeout_idle`, `timeout_not_idle`), reports an unanswered WAKE
  exactly when its wait ran out (`timeout_wake_due`, `timeout_wake_not_due`), ends a link outage once it lasted its
  bound (`timeout_link_end`), and leaves none of its own deadlines in the past (`timeout_no_stale`); the handshake's
  timer ends a handshaking connection whose handshake ran out of time and a connected one whose peer never confirmed
  the session, each silently and only in its own phase (`timeout_hs`, `timeout_unconf`, `timeout_hs_phase`,
  `timeout_unconf_phase`); at a probe timeout behind a live carrier (`carrier_iff`: a relay path, a carrier heard
  within `cf`, 4 probe timeouts in a row, 4 round trips of silence) it begins a close with a CLOSE unless the path is
  dead or the call ended the connection first (`timeout_carrier_close`), and it begins a close at no other time
  (`timeout_close_only_carrier`);
* at most one CLOSE leaves in any run (`run_closes_le_one`); after a local close of a connected connection the first
  datagram written is the CLOSE and the connection is then closed (`close_then_tx`); a closed connection stays closed,
  has no timer, writes nothing and takes nothing (`closed_inert`, `run_closed`), so a peer's CLOSE, the idle timeout,
  a dead path, a handshake timeout and a session its peer never confirmed, which all end in the closed state with no
  CLOSE to send (`recv_peer_close`, `timeout_idle`, `timeout_dead`, `timeout_hs`, `timeout_unconf`), send nothing ever
  after;
* a heard packet restarts the idle timer and clears the wake wait, anything refused leaves the state as it was
  (`recv_heard`, `recv_unheard`, `recv_refused`); a sleeping peer is held `hold` after its SLEEP (`idle_hold`,
  `sleep_hold`).
-/

namespace Pinc.TransportTimers

/-! ## The minimum `poll_timeout` folds -/

/-- Fold a list of deadlines into the minimum, as the `add` calls of `poll_timeout` do. -/
def foldD (t : Nat) : List (Option Nat) → Nat
  | [] => t
  | x :: xs => foldD (addD t x) xs

/-- The deadlines `poll_timeout` reads besides the idle deadline, in its order, each under its gate. -/
def reads (k : K) (s : S) (c : C) : List (Option Nat) :=
  if suspended s then [linkEnd k s, s.wd] ++ (if s.ld.isSome then [c.recov] else [])
  else (if !c.conf then [c.hs] else []) ++ [c.rekey, c.recov] ++ (if c.amp then [c.ack] else [])
    ++ [c.paced, c.path, s.wd, linkEnd k s] ++ (if s.ph == .conn then [keepDue s, c.mtu] else [])

theorem addD_le (t : Nat) (x : Option Nat) : addD t x ≤ t := by
  cases x <;> simp [addD]; omega

theorem foldD_le (t : Nat) (xs : List (Option Nat)) : foldD t xs ≤ t := by
  induction xs generalizing t with
  | nil => simp [foldD]
  | cons x xs ih => exact Nat.le_trans (ih _) (addD_le t x)

theorem foldD_le_mem (t : Nat) (xs : List (Option Nat)) (y : Nat) (h : some y ∈ xs) : foldD t xs ≤ y := by
  induction xs generalizing t with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst h
      have h1 : addD t (some y) ≤ y := by simp only [addD]; omega
      exact Nat.le_trans (foldD_le (addD t (some y)) xs) h1
    · exact ih _ h

theorem foldD_attained (t : Nat) (xs : List (Option Nat)) : foldD t xs = t ∨ some (foldD t xs) ∈ xs := by
  induction xs generalizing t with
  | nil => simp [foldD]
  | cons x xs ih =>
    rcases ih (addD t x) with h | h
    · cases x with
      | none => simp [foldD, addD] at h ⊢; exact Or.inl h
      | some v =>
        simp only [foldD, addD] at h ⊢
        by_cases hv : t ≤ v
        · left; rw [h]; omega
        · right; rw [h]; simp; omega
    · right; simp [foldD] at h ⊢; exact Or.inr h

theorem poll_open {k : K} {s : S} {c : C} (h : isOpen s = true) :
    poll k s c = some (foldD (idle k s) (reads k s c)) := by
  unfold poll reads
  cases hp : s.ph <;> simp [isOpen, hp] at h ⊢ <;>
    (by_cases hs : suspended s = true <;> by_cases hl : s.ld.isSome = true <;>
      by_cases hc : c.conf = true <;> by_cases ha : c.amp = true <;> simp [hs, hl, hc, ha, foldD])

/-! ## `poll_timeout` is the minimum of the deadlines it names -/

theorem poll_none_iff (k : K) (s : S) (c : C) : poll k s c = none ↔ s.ph = .closed := by
  unfold poll; cases s.ph <;> simp <;> split <;> simp

theorem poll_closing (k : K) (s : S) (c : C) (h : s.ph = .closing) : poll k s c = some 0 := by
  unfold poll; rw [h]

/-- Not later than the idle deadline. -/
theorem poll_le_idle {k : K} {s : S} {c : C} {p : Nat} (ho : isOpen s = true) (hp : poll k s c = some p) :
    p ≤ idle k s := by
  rw [poll_open ho] at hp; cases hp; exact foldD_le _ _

/-- Not later than any deadline it reads. -/
theorem poll_le_read {k : K} {s : S} {c : C} {p y : Nat} (ho : isOpen s = true) (hp : poll k s c = some p)
    (hy : some y ∈ reads k s c) : p ≤ y := by
  rw [poll_open ho] at hp; cases hp; exact foldD_le_mem _ _ _ hy

/-- And equal to one of them. -/
theorem poll_attained {k : K} {s : S} {c : C} {p : Nat} (ho : isOpen s = true) (hp : poll k s c = some p) :
    p = idle k s ∨ some p ∈ reads k s c := by
  rw [poll_open ho] at hp; cases hp; exact foldD_attained _ _

/-- The lifecycle's own clocks are read in both branches. -/
theorem link_read (k : K) (s : S) (c : C) : linkEnd k s ∈ reads k s c := by
  unfold reads; split <;> simp

theorem wake_read (k : K) (s : S) (c : C) : s.wd ∈ reads k s c := by
  unfold reads; split <;> simp

theorem poll_le_link {k : K} {s : S} {c : C} {p d : Nat} (ho : isOpen s = true) (hp : poll k s c = some p)
    (hd : s.ld = some d) : p ≤ d + k.ldm :=
  poll_le_read ho hp (by have := link_read k s c; simp [linkEnd, hd] at this; exact this)

theorem poll_le_wake {k : K} {s : S} {c : C} {p w : Nat} (ho : isOpen s = true) (hp : poll k s c = some p)
    (hw : s.wd = some w) : p ≤ w :=
  poll_le_read ho hp (by have := wake_read k s c; rw [hw] at this; exact this)

/-! ## The parts of `handle_timeout` -/

@[simp] theorem silent_wd (s : S) : (silent s).wd = s.wd := rfl
@[simp] theorem silent_ld (s : S) : (silent s).ld = s.ld := rfl
@[simp] theorem silent_act (s : S) : (silent s).act = s.act := rfl
@[simp] theorem silent_pa (s : S) : (silent s).pa = s.pa := rfl
@[simp] theorem silent_ph (s : S) : (silent s).ph = .closed := rfl
@[simp] theorem silent_close (s : S) : (silent s).close = none := rfl

theorem idle_congr {k : K} {s t : S} (ha : t.act = s.act) (hp : t.pa = s.pa) : idle k t = idle k s := by
  simp [idle, ha, hp]

@[simp] theorem hsStep_wd (s : S) (cc : CC) : (hsStep s cc).s.wd = s.wd := by
  unfold hsStep; split <;> (try split) <;> rfl
@[simp] theorem hsStep_ld (s : S) (cc : CC) : (hsStep s cc).s.ld = s.ld := by
  unfold hsStep; split <;> (try split) <;> rfl
@[simp] theorem hsStep_act (s : S) (cc : CC) : (hsStep s cc).s.act = s.act := by
  unfold hsStep; split <;> (try split) <;> rfl
@[simp] theorem hsStep_pa (s : S) (cc : CC) : (hsStep s cc).s.pa = s.pa := by
  unfold hsStep; split <;> (try split) <;> rfl

@[simp] theorem linkStep_wd (k : K) (s : S) (now : Nat) : (linkStep k s now).wd = s.wd := by
  unfold linkStep; split <;> (try split) <;> rfl
@[simp] theorem linkStep_act (k : K) (s : S) (now : Nat) : (linkStep k s now).act = s.act := by
  unfold linkStep; split <;> (try split) <;> rfl
@[simp] theorem linkStep_pa (k : K) (s : S) (now : Nat) : (linkStep k s now).pa = s.pa := by
  unfold linkStep; split <;> (try split) <;> rfl
@[simp] theorem linkStep_ph (k : K) (s : S) (now : Nat) : (linkStep k s now).ph = s.ph := by
  unfold linkStep; split <;> (try split) <;> rfl
@[simp] theorem linkStep_close (k : K) (s : S) (now : Nat) : (linkStep k s now).close = s.close := by
  unfold linkStep; split <;> (try split) <;> rfl

@[simp] theorem deadStep_wd (r : R) (cc : CC) : (deadStep r cc).s.wd = r.s.wd := by unfold deadStep; split <;> rfl
@[simp] theorem deadStep_ld (r : R) (cc : CC) : (deadStep r cc).s.ld = r.s.ld := by unfold deadStep; split <;> rfl
@[simp] theorem deadStep_act (r : R) (cc : CC) : (deadStep r cc).s.act = r.s.act := by unfold deadStep; split <;> rfl
@[simp] theorem deadStep_pa (r : R) (cc : CC) : (deadStep r cc).s.pa = r.s.pa := by unfold deadStep; split <;> rfl

@[simp] theorem carrierStep_wd (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (carrierStep k r now pr cc).s.wd = r.s.wd := by
  unfold carrierStep beginClose; split <;> (try split) <;> rfl
@[simp] theorem carrierStep_ld (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (carrierStep k r now pr cc).s.ld = r.s.ld := by
  unfold carrierStep beginClose; split <;> (try split) <;> rfl
@[simp] theorem carrierStep_act (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (carrierStep k r now pr cc).s.act = r.s.act := by
  unfold carrierStep beginClose; split <;> (try split) <;> rfl
@[simp] theorem carrierStep_pa (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (carrierStep k r now pr cc).s.pa = r.s.pa := by
  unfold carrierStep beginClose; split <;> (try split) <;> rfl

@[simp] theorem recStep_wd (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (recStep k r now pr cc).s.wd = r.s.wd := by simp [recStep]
@[simp] theorem recStep_ld (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (recStep k r now pr cc).s.ld = r.s.ld := by simp [recStep]
@[simp] theorem recStep_act (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (recStep k r now pr cc).s.act = r.s.act := by simp [recStep]
@[simp] theorem recStep_pa (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) :
    (recStep k r now pr cc).s.pa = r.s.pa := by simp [recStep]

@[simp] theorem wakeStep_ld (r : R) (now : Nat) : (wakeStep r now).s.ld = r.s.ld := by
  unfold wakeStep; split <;> (try split) <;> rfl
@[simp] theorem wakeStep_act (r : R) (now : Nat) : (wakeStep r now).s.act = r.s.act := by
  unfold wakeStep; split <;> (try split) <;> rfl
@[simp] theorem wakeStep_pa (r : R) (now : Nat) : (wakeStep r now).s.pa = r.s.pa := by
  unfold wakeStep; split <;> (try split) <;> rfl
@[simp] theorem wakeStep_ph (r : R) (now : Nat) : (wakeStep r now).s.ph = r.s.ph := by
  unfold wakeStep; split <;> (try split) <;> rfl
@[simp] theorem wakeStep_close (r : R) (now : Nat) : (wakeStep r now).s.close = r.s.close := by
  unfold wakeStep; split <;> (try split) <;> rfl

theorem linkStep_ld (k : K) (s : S) (now : Nat) :
    (linkStep k s now).ld = match s.ld with | some d => if d + k.ldm ≤ now then none else some d | none => none := by
  unfold linkStep; cases h : s.ld <;> simp [h]; split <;> simp [h]

theorem wakeStep_wd (r : R) (now : Nat) :
    (wakeStep r now).s.wd = match r.s.wd with | some w => if w ≤ now then none else some w | none => none := by
  unfold wakeStep; cases h : r.s.wd <;> simp [h]; split <;> simp [h]

theorem wakeStep_unanswered (r : R) (now : Nat) :
    (Ev.unanswered ∈ (wakeStep r now).ev) ↔ (Ev.unanswered ∈ r.ev ∨ ∃ w, r.s.wd = some w ∧ w ≤ now) := by
  unfold wakeStep
  cases h : r.s.wd with
  | none => simp
  | some w => by_cases hw : w ≤ now <;> simp [hw]

theorem wakeStep_ev_mem (r : R) (now : Nat) (x : Ev) (h : x ∈ r.ev) : x ∈ (wakeStep r now).ev := by
  unfold wakeStep
  cases r.s.wd with
  | none => exact h
  | some w => by_cases hw : w ≤ now <;> simp [hw, h]

theorem deadStep_ev (r : R) (cc : CC) (x : Ev) (h : x ∈ (deadStep r cc).ev) : x ∈ r.ev ∨ x = Ev.dead := by
  unfold deadStep at h
  split at h
  · simp at h; exact h
  · exact Or.inl h

theorem carrierStep_ev (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) (x : Ev) (h : x ∈ (carrierStep k r now pr cc).ev) :
    x ∈ r.ev ∨ x = Ev.dead := by
  unfold carrierStep at h
  split at h
  · unfold beginClose at h
    split at h
    · simp at h; exact h
    · simp at h; exact Or.inl h
  · exact Or.inl h

theorem recStep_ev (k : K) (r : R) (now : Nat) (pr : P) (cc : CC) (x : Ev) (h : x ∈ (recStep k r now pr cc).ev) :
    x ∈ r.ev ∨ x = Ev.dead := by
  rcases carrierStep_ev k _ now pr cc x h with h | h
  · exact deadStep_ev r cc x h
  · exact Or.inr h

theorem wakeStep_ev (r : R) (now : Nat) (x : Ev) (h : x ∈ (wakeStep r now).ev) : x ∈ r.ev ∨ x = Ev.unanswered := by
  unfold wakeStep at h
  cases hw : r.s.wd with
  | none => simp [hw] at h; exact Or.inl h
  | some w =>
    by_cases hn : w ≤ now
    · simp [hw, hn] at h; exact h
    · simp [hw, hn] at h; exact Or.inl h

theorem hsStep_ev (s : S) (cc : CC) (x : Ev) (h : x ∈ (hsStep s cc).ev) : x = Ev.hs ∨ x = Ev.unconf := by
  unfold hsStep at h
  split at h
  · simp at h; exact Or.inl h
  · split at h
    · simp at h; exact Or.inr h
    · simp at h

/-- The handshake reports its timeout only for a handshaking connection, when it decided it. -/
theorem hsStep_hs (s : S) (cc : CC) (h : Ev.hs ∈ (hsStep s cc).ev) : cc = .hs ∧ s.ph = .hs := by
  unfold hsStep at h
  split at h
  · rename_i hc; simpa using hc
  · split at h <;> simp at h

/-- And a session its peer never confirmed only for a connected connection, when it decided it. -/
theorem hsStep_unconf (s : S) (cc : CC) (h : Ev.unconf ∈ (hsStep s cc).ev) : cc = .unconf ∧ s.ph = .conn := by
  unfold hsStep at h
  split at h
  · simp at h
  · split at h
    · rename_i hc; simpa using hc
    · simp at h

/-- The events of a call before the idle deadline: the handshake's, a dead path's and an unanswered WAKE. -/
theorem body_ev (k : K) (s : S) (now : Nat) (cc : CC) (pr : P) (x : Ev)
    (h : x ∈ (wakeStep (recStep k ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ now pr cc) now).ev) :
    x ∈ (hsStep s cc).ev ∨ x = Ev.dead ∨ x = Ev.unanswered := by
  rcases wakeStep_ev _ now _ h with h | h
  · rcases recStep_ev k _ now pr cc _ h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem body_no_unanswered (k : K) (s : S) (now : Nat) (cc : CC) (pr : P) :
    Ev.unanswered ∉ (recStep k ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ now pr cc).ev := by
  intro h
  rcases recStep_ev k _ now pr cc _ h with h | h
  · rcases hsStep_ev s cc _ h with h | h <;> cases h
  · cases h

theorem body_no_idle (k : K) (s : S) (now : Nat) (cc : CC) (pr : P) :
    Ev.idle ∉ (wakeStep (recStep k ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ now pr cc) now).ev := by
  intro h
  rcases body_ev k s now cc pr _ h with h | h | h
  · rcases hsStep_ev s cc _ h with h | h <;> cases h
  · cases h
  · cases h

/-- Before the idle deadline `handle_timeout` runs its parts in order. -/
theorem timeout_body {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true) (hi : now < idle k s) :
    timeout k s now cc pr = wakeStep (recStep k ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ now pr cc) now := by
  have hi' : ¬ idle k s ≤ now := by omega
  unfold timeout
  cases hp : s.ph <;> simp [isOpen, hp] at ho ⊢ <;> simp [hi']

/-! ## `handle_timeout` -/

theorem timeout_closing (k : K) (s : S) (now : Nat) (cc : CC) (pr : P) (h : s.ph = .closing) :
    timeout k s now cc pr = ⟨{ s with ph := .closed }, []⟩ := by
  unfold timeout; rw [h]

theorem timeout_closed (k : K) (s : S) (now : Nat) (cc : CC) (pr : P) (h : s.ph = .closed) :
    timeout k s now cc pr = ⟨s, []⟩ := by
  unfold timeout; rw [h]

/-- At or after the idle deadline the connection ends silently and nothing else runs. -/
theorem timeout_idle {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true) (h : idle k s ≤ now) :
    timeout k s now cc pr = ⟨silent s, [.idle]⟩ := by
  unfold timeout
  cases hp : s.ph <;> simp [isOpen, hp, h] at ho ⊢

/-- And never before it: the connection is closed for idleness at the first timer call at or after the deadline. -/
theorem timeout_not_idle {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true) (hi : now < idle k s) :
    Ev.idle ∉ (timeout k s now cc pr).ev := by
  rw [timeout_body cc pr ho hi]; exact body_no_idle k s now cc pr

/-- The deadlines of `handle_timeout` itself are not due: it changes nothing and reports nothing. -/
theorem timeout_early {k : K} {s : S} {now : Nat} (pr : P) (hpr : pr.ping = false) (ho : isOpen s = true)
    (hi : now < idle k s) (hl : ∀ d, s.ld = some d → now < d + k.ldm) (hw : ∀ w, s.wd = some w → now < w) :
    timeout k s now .none pr = ⟨s, []⟩ := by
  rw [timeout_body .none pr ho hi]
  have h1 : hsStep s .none = ⟨s, []⟩ := by simp [hsStep]
  have h2 : linkStep k s now = s := by
    unfold linkStep; cases h : s.ld with
    | none => rfl
    | some d => have := hl d h; simp; omega
  have h3 : recStep k ⟨s, []⟩ now pr .none = ⟨s, []⟩ := by simp [recStep, deadStep, carrierStep, hpr]
  rw [h1]; simp only [h2, h3]
  unfold wakeStep; cases h : s.wd with
  | none => rfl
  | some w => have := hw w h; simp; omega

/-- Nothing happens before `poll_timeout`: a timer call earlier than the time it named changes nothing, unless a
component decides a close of its own in it, and no probe timeout fires (one fires at or after its own deadline, which
`poll_timeout` folds in). -/
theorem timeout_before_poll {k : K} {s : S} {c : C} {p now : Nat} (pr : P) (hpr : pr.ping = false)
    (ho : isOpen s = true) (hp : poll k s c = some p)
    (hn : now < p) : timeout k s now .none pr = ⟨s, []⟩ :=
  timeout_early pr hpr ho (Nat.lt_of_lt_of_le hn (poll_le_idle ho hp))
    (fun _ hd => Nat.lt_of_lt_of_le hn (poll_le_link ho hp hd))
    (fun _ hw => Nat.lt_of_lt_of_le hn (poll_le_wake ho hp hw))

/-- A WAKE whose wait ran out is reported, once. -/
theorem timeout_wake_due {k : K} {s : S} {now w : Nat} (cc : CC) (pr : P) (ho : isOpen s = true) (hi : now < idle k s)
    (hw : s.wd = some w) (hd : w ≤ now) :
    Ev.unanswered ∈ (timeout k s now cc pr).ev ∧ (timeout k s now cc pr).s.wd = none := by
  rw [timeout_body cc pr ho hi]
  refine ⟨(wakeStep_unanswered _ _).2 (Or.inr ⟨w, by simp [hw], hd⟩), ?_⟩
  rw [wakeStep_wd]; simp [hw, hd]

/-- And not before. -/
theorem timeout_wake_not_due {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true)
    (hw : ∀ w, s.wd = some w → now < w) :
    Ev.unanswered ∉ (timeout k s now cc pr).ev ∧ (timeout k s now cc pr).s.wd = s.wd := by
  by_cases hi : idle k s ≤ now
  · rw [timeout_idle cc pr ho hi]; simp
  · rw [timeout_body cc pr ho (by omega)]
    constructor
    · intro hm
      rcases (wakeStep_unanswered _ _).1 hm with h | ⟨w, h1, h2⟩
      · exact body_no_unanswered k s now cc pr h
      · simp at h1; have := hw w h1; omega
    · rw [wakeStep_wd]; simp
      cases h : s.wd with
      | none => rfl
      | some w => have := hw w h; simp; omega

/-- A link outage that lasted its bound ends. -/
theorem timeout_link_end {k : K} {s : S} {now d : Nat} (cc : CC) (pr : P) (ho : isOpen s = true) (hi : now < idle k s)
    (hl : s.ld = some d) (hd : d + k.ldm ≤ now) : (timeout k s now cc pr).s.ld = none := by
  rw [timeout_body cc pr ho hi]; simp [linkStep_ld, hl, hd]

/-- One that did not is kept. -/
theorem timeout_link_keep {k : K} {s : S} {now d : Nat} (cc : CC) (pr : P) (ho : isOpen s = true)
    (hl : s.ld = some d) (hd : now < d + k.ldm) : (timeout k s now cc pr).s.ld = some d := by
  by_cases hi : idle k s ≤ now
  · rw [timeout_idle cc pr ho hi]; simp [hl]
  · rw [timeout_body cc pr ho (by omega)]; simp [linkStep_ld, hl]; omega

/-- No deadline of its own is left in the past by a timer call that leaves the connection open. -/
theorem timeout_no_stale {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true)
    (hr : isOpen (timeout k s now cc pr).s = true) :
    now < idle k (timeout k s now cc pr).s ∧ (∀ d, (timeout k s now cc pr).s.ld = some d → now < d + k.ldm)
      ∧ (∀ w, (timeout k s now cc pr).s.wd = some w → now < w) := by
  by_cases hi : idle k s ≤ now
  · rw [timeout_idle cc pr ho hi] at hr; simp [isOpen] at hr
  · have hi' : now < idle k s := by omega
    rw [timeout_body cc pr ho hi']
    refine ⟨?_, ?_, ?_⟩
    · have he : idle k (wakeStep (recStep k ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ now pr cc) now).s
          = idle k s := idle_congr (by simp) (by simp)
      rw [he]; exact hi'
    · intro d hd
      simp [linkStep_ld] at hd
      cases h : s.ld with
      | none => simp [h] at hd
      | some e =>
        simp [h] at hd
        rcases hd with ⟨h1, h2⟩
        subst h2; omega
    · intro w hw
      rw [wakeStep_wd] at hw; simp at hw
      cases h : s.wd with
      | none => simp [h] at hw
      | some e =>
        simp [h] at hw
        rcases hw with ⟨h1, h2⟩
        subst h2; omega

/-- Recovery gave up: the connection ends silently. -/
theorem timeout_dead {k : K} {s : S} {now : Nat} (pr : P) (ho : isOpen s = true) (hi : now < idle k s) :
    (timeout k s now .dead pr).s.ph = .closed ∧ (timeout k s now .dead pr).s.close = none
      ∧ Ev.dead ∈ (timeout k s now .dead pr).ev := by
  rw [timeout_body .dead pr ho hi]
  have h1 : hsStep s .dead = ⟨s, []⟩ := by simp [hsStep]
  rw [h1]
  have hph : s.ph ≠ .closed := by cases hp : s.ph <;> simp [isOpen, hp] at ho ⊢
  have h2 : recStep k ⟨linkStep k s now, []⟩ now pr .dead = ⟨silent (linkStep k s now), [.dead]⟩ := by
    simp [recStep, deadStep, carrierStep, hph]
  rw [h2]
  exact ⟨by simp, by simp, wakeStep_ev_mem _ _ _ (by simp)⟩

/-- The handshake ran out of time: a handshaking connection ends silently. -/
theorem timeout_hs {k : K} {s : S} {now : Nat} (pr : P) (hp : s.ph = .hs) (hi : now < idle k s) :
    (timeout k s now .hs pr).s.ph = .closed ∧ (timeout k s now .hs pr).s.close = none
      ∧ Ev.hs ∈ (timeout k s now .hs pr).ev := by
  have ho : isOpen s = true := by simp [isOpen, hp]
  rw [timeout_body .hs pr ho hi]
  have h1 : hsStep s .hs = ⟨silent s, [.hs]⟩ := by simp [hsStep, hp]
  rw [h1]
  have h2 : recStep k ⟨linkStep k (silent s) now, [.hs]⟩ now pr .hs = ⟨linkStep k (silent s) now, [.hs]⟩ := by
    have hc : isOpen (linkStep k (silent s) now) = false := by simp [isOpen]
    simp [recStep, deadStep, carrierStep, beginClose, hc]
  rw [h2]
  exact ⟨by simp, by simp, wakeStep_ev_mem _ _ _ (by simp)⟩

/-- A dialing side's session its peer never confirmed within the connect limit after it established (#390): the
connected connection ends silently. -/
theorem timeout_unconf {k : K} {s : S} {now : Nat} (pr : P) (hp : s.ph = .conn) (hi : now < idle k s) :
    (timeout k s now .unconf pr).s.ph = .closed ∧ (timeout k s now .unconf pr).s.close = none
      ∧ Ev.unconf ∈ (timeout k s now .unconf pr).ev := by
  have ho : isOpen s = true := by simp [isOpen, hp]
  rw [timeout_body .unconf pr ho hi]
  have h1 : hsStep s .unconf = ⟨silent s, [.unconf]⟩ := by simp [hsStep, hp]
  rw [h1]
  have h2 : recStep k ⟨linkStep k (silent s) now, [.unconf]⟩ now pr .unconf
      = ⟨linkStep k (silent s) now, [.unconf]⟩ := by
    have hc : isOpen (linkStep k (silent s) now) = false := by simp [isOpen]
    simp [recStep, deadStep, carrierStep, beginClose, hc]
  rw [h2]
  exact ⟨by simp, by simp, wakeStep_ev_mem _ _ _ (by simp)⟩

/-- A connection that a call ends is open before it. -/
theorem timeout_ev_open {k : K} {s : S} {now : Nat} {cc : CC} {pr : P} {x : Ev}
    (h : x ∈ (timeout k s now cc pr).ev) : isOpen s = true := by
  cases hp : s.ph with
  | hs => simp [isOpen, hp]
  | conn => simp [isOpen, hp]
  | closing => rw [timeout_closing k s now cc pr hp] at h; simp at h
  | closed => rw [timeout_closed k s now cc pr hp] at h; simp at h

/-- The handshake's ends keep to their phases: a call reports a handshake timeout only for a handshaking connection
whose handshake decided it ran out of time. -/
theorem timeout_hs_phase {k : K} {s : S} {now : Nat} {cc : CC} {pr : P}
    (h : Ev.hs ∈ (timeout k s now cc pr).ev) : cc = .hs ∧ s.ph = .hs := by
  have ho := timeout_ev_open h
  by_cases hi : idle k s ≤ now
  · rw [timeout_idle cc pr ho hi] at h; simp at h
  · rw [timeout_body cc pr ho (by omega)] at h
    rcases body_ev k s now cc pr _ h with h | h | h
    · exact hsStep_hs s cc h
    · cases h
    · cases h

/-- And a session its peer never confirmed only for a connected connection whose handshake decided it (#390). -/
theorem timeout_unconf_phase {k : K} {s : S} {now : Nat} {cc : CC} {pr : P}
    (h : Ev.unconf ∈ (timeout k s now cc pr).ev) : cc = .unconf ∧ s.ph = .conn := by
  have ho := timeout_ev_open h
  by_cases hi : idle k s ≤ now
  · rw [timeout_idle cc pr ho hi] at h; simp at h
  · rw [timeout_body cc pr ho (by omega)] at h
    rcases body_ev k s now cc pr _ h with h | h | h
    · exact hsStep_unconf s cc h
    · cases h
    · cases h

/-! ## The close behind a live carrier -/

/-- The rule itself: a relay path, a carrier heard less than `cf` ago, 4 probe timeouts in a row, and nothing heard for
4 round trips. -/
theorem carrier_iff (k : K) (now : Nat) (pr : P) :
    carrier k now pr = true ↔
      pr.relay = true ∧ (∃ h, pr.ch = some h ∧ now - h < k.cf) ∧ 4 ≤ pr.pto ∧ 4 * rtt k pr ≤ now - pr.lh := by
  unfold carrier
  cases hch : pr.ch with
  | none => simp
  | some h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨h1, ⟨h, rfl, h2⟩, h3, h4⟩
    · rintro ⟨h1, ⟨h', h5, h2⟩, h3, h4⟩
      cases h5
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- At a probe timeout behind a live carrier the connection begins a close with a CLOSE: error 0, reported as
`PathDead`, never silent. It holds unless the path is dead (`cc = .dead`, which ends it silently first) or the call
ended the connection before the recovery timer ran (the handshake timeout, or a session its peer never confirmed). -/
theorem timeout_carrier_close {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true)
    (hi : now < idle k s) (hd : cc ≠ .dead) (hh : ¬ (cc = .hs ∧ s.ph = .hs)) (hu : ¬ (cc = .unconf ∧ s.ph = .conn))
    (hp : pr.ping = true) (hc : carrier k now pr = true) :
    (timeout k s now cc pr).s.close = some 0 ∧ isOpen (timeout k s now cc pr).s = false
      ∧ Ev.dead ∈ (timeout k s now cc pr).ev := by
  rw [timeout_body cc pr ho hi]
  have h1 : hsStep s cc = ⟨s, []⟩ := by
    unfold hsStep
    split
    · rename_i h; simp at h; exact absurd h hh
    · split
      · rename_i h; simp at h; exact absurd h hu
      · rfl
  have hl : isOpen (linkStep k s now) = true := by simpa [isOpen] using ho
  have hg : (cc != CC.dead && pr.ping && carrier k now pr) = true := by
    cases cc <;> simp [hp, hc] at hd ⊢
  have h2 : recStep k ⟨linkStep k s now, []⟩ now pr cc
      = ⟨(beginClose (linkStep k s now) 0 .dead).s, (beginClose (linkStep k s now) 0 .dead).ev⟩ := by
    simp [recStep, carrierStep, deadStep, hd, hg]
  rw [h1]
  simp only [h2]
  refine ⟨?_, ?_, wakeStep_ev_mem _ _ _ ?_⟩
  · simp [beginClose, hl]
  · have hsph : s.ph = Ph.hs ∨ s.ph = Ph.conn := by simpa [isOpen] using ho
    (simp [isOpen, beginClose, hl, hsph]) <;> (by_cases hk : s.ph = Ph.conn ∧ (linkStep k s now).keys = true <;> simp [hk])
  · simp [beginClose, hl]

/-- And a CLOSE is to leave only then: from an open connection (no CLOSE pending) a timer call before the idle deadline
leaves one to send only at a probe timeout behind a live carrier, on a path that is not dead. -/
theorem timeout_close_only_carrier {k : K} {s : S} {now : Nat} (cc : CC) (pr : P) (ho : isOpen s = true)
    (hi : now < idle k s) (hn : s.close = none) (hc : (timeout k s now cc pr).s.close ≠ none) :
    pr.ping = true ∧ cc ≠ .dead ∧ carrier k now pr = true := by
  rw [timeout_body cc pr ho hi] at hc
  by_cases hg : (cc != CC.dead && pr.ping && carrier k now pr) = true
  · have h := hg
    simp at h
    exact ⟨h.1.2, h.1.1, h.2⟩
  · exfalso
    apply hc
    simp only [wakeStep_close]
    have hr : recStep k ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ now pr cc
        = deadStep ⟨linkStep k (hsStep s cc).s now, (hsStep s cc).ev⟩ cc := by
      simp [recStep, carrierStep, hg]
    rw [hr]
    have hh : (hsStep s cc).s.close = none := by unfold hsStep; split <;> (try split) <;> simp [hn]
    unfold deadStep; split <;> simp [hh]

/-! ## Closing -/

/-- A local close of a connected connection leaves one CLOSE to send; the first datagram `poll_transmit` writes is
that CLOSE, and the connection is closed after it. -/
theorem close_then_tx {s : S} {err now st : Nat} (hp : s.ph = .conn) (hk : s.keys = true) :
    let s1 := (close s err).s
    (close s err).ev = [.local] ∧ s1.ph = .closing ∧ s1.close = some err ∧ canSend s1 = true
      ∧ txClose s1 true = true ∧ (tx s1 now true st).ph = .closed ∧ (tx s1 now true st).close = none := by
  simp [close, beginClose, isOpen, hp, hk, canSend, txClose, tx]

/-- A close of a handshaking connection ends it at once, with nothing to send. -/
theorem close_hs {s : S} {err : Nat} (hp : s.ph = .hs) :
    (close s err).s.ph = .closed ∧ canSend (close s err).s = false := by
  simp [close, beginClose, isOpen, hp, canSend]

/-- A peer's CLOSE ends the connection silently. -/
theorem recv_peer_close {s : S} {now : Nat} (sl : Bool) (ho : isOpen s = true) :
    (recv s now true sl true).s.ph = .closed ∧ (recv s now true sl true).s.close = none
      ∧ Ev.peer ∈ (recv s now true sl true).ev := by
  simp [recv, ho]

theorem closed_canSend (s : S) (h : s.ph = .closed) : canSend s = false := by simp [canSend, h]

/-- A closed connection: no timer, nothing written, nothing taken, and no call but keepalive and pulse changes
anything or reports anything. -/
theorem closed_inert (k : K) (s : S) (c : C) (h : s.ph = .closed) :
    poll k s c = none ∧ canSend s = false ∧ isOpen s = false
      ∧ ∀ op, (∀ ka, op ≠ .keepalive ka) → (∀ n b, op ≠ .pulse n b) → step k s op = (⟨s, []⟩, false) := by
  refine ⟨(poll_none_iff k s c).2 h, closed_canSend s h, by simp [isOpen, h], ?_⟩
  intro op h1 h2
  have ho : isOpen s = false := by simp [isOpen, h]
  cases op with
  | timeout now cc pr => simp [step, timeout_closed k s now cc pr h]
  | recv now hd sl cl => simp [step, recv, ho]
  | bad err => simp [step, bad, beginClose, ho]
  | viol now err => simp [step, viol, ho]
  | close err => simp [step, close, beginClose, ho]
  | tx now sent st => simp [step, tx, h, canSend, txClose]
  | sleep => simp [step, sleep, h]
  | wake now => simp [step, wake, h]
  | link now down => simp [step, link, h]
  | keepalive ka => exact absurd rfl (h1 ka)
  | pulse n b => exact absurd rfl (h2 n b)
  | est now => simp [step, est, h]

/-- A call never takes a closed connection out of the closed state, and never writes on it. -/
theorem step_closed (k : K) (s : S) (op : Op) (h : s.ph = .closed) :
    (step k s op).1.s.ph = .closed ∧ (step k s op).2 = false := by
  have ho : isOpen s = false := by simp [isOpen, h]
  cases op with
  | timeout now cc pr => simp [step, timeout_closed k s now cc pr h, h]
  | recv now hd sl cl => simp [step, recv, ho, h]
  | bad err => simp [step, bad, beginClose, ho, h]
  | viol now err => simp [step, viol, ho, h]
  | close err => simp [step, close, beginClose, ho, h]
  | tx now sent st => simp [step, tx, h, canSend, txClose]
  | sleep => simp [step, sleep, h]
  | wake now => simp [step, wake, h]
  | link now down => simp [step, link, h]
  | keepalive ka => simp [step, keepalive, h]
  | pulse n b => simp [step, pulse, h]
  | est now => simp [step, est, h]

/-- So a run from a closed connection sends no CLOSE and stays closed: after a peer's CLOSE, the idle timeout, a dead
path, a handshake timeout, a session its peer never confirmed, or the CLOSE itself, nothing more ever leaves. -/
theorem run_closed (k : K) (s : S) (ops : List Op) (h : s.ph = .closed) :
    (run k s ops).1.ph = .closed ∧ (run k s ops).2 = 0 := by
  induction ops generalizing s with
  | nil => simp [run, h]
  | cons op ops ih =>
    have hs := step_closed k s op h
    have := ih (step k s op).1.s hs.1
    simp only [run]
    rw [hs.2]; simpa using this

/-- What is left to send: one CLOSE at most until closed, none after. -/
def budget (s : S) : Nat := if s.ph = .closed then 0 else 1

theorem budget_le (s : S) : budget s ≤ 1 := by unfold budget; split <;> simp

/-- The only call that writes the CLOSE is `poll_transmit` on a closing connection, and it is closed after it. -/
theorem step_close_closed (k : K) (s : S) (op : Op) (h : (step k s op).2 = true) :
    (step k s op).1.s.ph = .closed := by
  cases op with
  | tx now sent st =>
    simp only [step] at h ⊢
    have hph : s.ph = .closing := by simp [txClose] at h; exact h.1.1
    have hcl : s.close.isSome = true := by simp [txClose] at h; exact h.1.2
    have hs : (sent && canSend s) = true := by simp [txClose] at h; simp [h.2.1, h.2.2]
    cases hc : s.close with
    | none => simp [hc] at hcl
    | some e => simp [tx, hph, hc, hs]
  | _ => simp [step] at h

theorem step_budget (k : K) (s : S) (op : Op) :
    (if (step k s op).2 then 1 else 0) + budget (step k s op).1.s ≤ budget s := by
  by_cases h : s.ph = .closed
  · have := step_closed k s op h; simp [budget, h, this.1, this.2]
  · have hb : budget s = 1 := by simp [budget, h]
    rw [hb]
    cases hc : (step k s op).2
    · simpa using budget_le _
    · simp [budget, step_close_closed k s op hc]

/-- At most one CLOSE leaves in any run, whatever the calls and the components decide. -/
theorem run_closes_le_one (k : K) (s : S) (ops : List Op) : (run k s ops).2 ≤ 1 := by
  have key : ∀ (s : S) (ops : List Op), (run k s ops).2 + budget (run k s ops).1 ≤ budget s := by
    intro s ops
    induction ops generalizing s with
    | nil => simp [run]
    | cons op ops ih =>
      have h1 := step_budget k s op
      have h2 := ih (step k s op).1.s
      simp only [run]
      revert h1 h2
      cases (step k s op).2 <;> simp <;> omega
  have := key s ops
  have hb := budget_le s
  omega

/-! ## The idle timer and the sleep hold -/

/-- A datagram nothing in which was heard changes nothing. -/
theorem recv_unheard (s : S) (now : Nat) (sl cl : Bool) : recv s now false sl cl = ⟨s, []⟩ := by
  simp [recv]

/-- A closed or closing connection refuses every datagram. -/
theorem recv_refused (s : S) (now : Nat) (hd sl cl : Bool) (ho : isOpen s = false) : recv s now hd sl cl = ⟨s, []⟩ := by
  simp [recv, ho]

theorem idle_ge_act (k : K) (s : S) : s.act + k.idle ≤ idle k s := by
  unfold idle; split <;> omega

/-- A heard packet restarts the idle timer and clears the wake wait. -/
theorem recv_heard {k : K} {s : S} {now : Nat} (sl cl : Bool) (ho : isOpen s = true) :
    (recv s now true sl cl).s.act = now ∧ (recv s now true sl cl).s.wd = none
      ∧ now + k.idle ≤ idle k (recv s now true sl cl).s := by
  have : (recv s now true sl cl).s.act = now ∧ (recv s now true sl cl).s.wd = none := by
    simp [recv, ho]; split <;> simp
  obtain ⟨h1, h2⟩ := this
  have h3 := idle_ge_act k (recv s now true sl cl).s
  rw [h1] at h3
  exact ⟨h1, h2, h3⟩

/-- A peer that announced its sleep is held `hold` after it. -/
theorem idle_hold (k : K) (s : S) (p : Nat) (h : s.pa = some p) : p + k.hold ≤ idle k s := by
  simp [idle, h]; omega

/-- So no timer call within `hold` of the SLEEP closes it for idleness. -/
theorem sleep_hold {k : K} {s : S} {now p : Nat} (cc : CC) (pr : P) (ho : isOpen s = true) (h : s.pa = some p)
    (hn : now < p + k.hold) : Ev.idle ∉ (timeout k s now cc pr).ev :=
  timeout_not_idle cc pr ho (Nat.lt_of_lt_of_le hn (idle_hold k s p h))

/-- WAKE starts the wait for an answer, and the connection counts as heard. -/
theorem wake_starts_wait {k : K} {s : S} {now : Nat} (hp : s.ph = .conn) (hl : s.la = true) :
    (wake k s now).wd = some (now + k.wake) ∧ (wake k s now).act = now ∧ (wake k s now).la = false := by
  simp [wake, resume, hp, hl]

#audit_axioms poll_none_iff
#audit_axioms poll_le_idle
#audit_axioms poll_le_read
#audit_axioms poll_attained
#audit_axioms timeout_idle
#audit_axioms timeout_not_idle
#audit_axioms timeout_before_poll
#audit_axioms timeout_wake_due
#audit_axioms timeout_wake_not_due
#audit_axioms timeout_link_end
#audit_axioms timeout_no_stale
#audit_axioms timeout_dead
#audit_axioms timeout_hs
#audit_axioms timeout_unconf
#audit_axioms timeout_hs_phase
#audit_axioms timeout_unconf_phase
#audit_axioms carrier_iff
#audit_axioms timeout_carrier_close
#audit_axioms timeout_close_only_carrier
#audit_axioms close_then_tx
#audit_axioms recv_peer_close
#audit_axioms closed_inert
#audit_axioms run_closed
#audit_axioms run_closes_le_one
#audit_axioms recv_heard
#audit_axioms sleep_hold

end Pinc.TransportTimers

