import Vinc.Json

/-!
# The mailbox

`mailbox.rs` of `vinc-connect` and the hold and wake step of `relay/route.rs`, as functions on lists. The model is the
one of `proofs/tla/ConnectMailboxOps.tla` (the Lean functions below are the operators `Push`, `Pop`, `Sweep`, `Clear`
and `ShouldWake`), and the Rust test `trace_connect_mailbox` replays the real code against both.

A member holds a queue of messages, oldest first, and the ring state `(head, used, count)` of the code. A message takes
`H + len` bytes (`H` is `ENTRY_HEAD`, 52). The member table is an association list: the table of `table.rs` behaves as a
map (`ConnectTable.lean`). Time is a natural number (`u64` nanoseconds; `saturating_sub` is the truncated `-`). The
counters are `u64`; the theorems read them as naturals, as 2^64 events cannot happen.

Theorems, for every configuration with `0 < B` and every sequence of steps from the empty mailbox (`Reach`):
* `mailbox_bounds`: a member holds at most `B` bytes, the byte count is the sum of the sizes of its messages, the
  message count is its length, the head is inside the ring, and at most `N` members exist.
* `conservation`: stored = delivered + dropped oldest + expired + held, so every loss is counted.
* `fifo_once`: the messages of a member are in increasing sequence number, and no message that was delivered is held.
* `pop_look_out`, `look_keeps`, `remove_front`, `remove_other`: `pop` returns the message `look` returns; a look counts
  no delivery and its message is the front of the member's queue once the old ones are expired; `remove` of the front
  counts one delivery and of any other number changes nothing. A look without a removal is not a step of `Reach`: that
  a refused hand-over keeps its message is checked by TLC (`RefusedKept`), not proven here.
* `age_bound` and `pop_front`: `pop` returns the first message of the member after the old ones are expired, and it
  is younger than the maximum age.
* `drop_oldest`: the quota loop removes a prefix of the queue.
* `wake_first` and `wake_spaced`: the wake rule.
-/

namespace Vinc.ConnectMailbox

structure Cfg where
  H : Nat
  B : Nat
  N : Nat
  maxAge : Nat
  maxPkt : Nat

structure Msg where
  src : Nat
  flag : Nat
  len : Nat
  t : Nat
  seq : Nat
  deriving DecidableEq, Repr

structure Held where
  q : List Msg
  head : Nat
  used : Nat
  count : Nat

structure Stats where
  stored : Nat := 0
  delivered : Nat := 0
  dropped : Nat := 0
  droppedBytes : Nat := 0
  expired : Nat := 0
  oversize : Nat := 0
  members : Nat := 0

structure MB where
  held : List (Nat × Held)
  seq : Nat
  st : Stats

def MB.empty : MB := ⟨[], 0, {}⟩
def Held.new : Held := ⟨[], 0, 0, 0⟩

def sizes (c : Cfg) (q : List Msg) : Nat := (q.map fun m => c.H + m.len).sum

/-! ### The member table (an association list; first match) -/

def lookup (k : Nat) : List (Nat × Held) → Option Held
  | [] => none
  | (a, x) :: r => if a = k then some x else lookup k r

def put (k : Nat) (v : Held) : List (Nat × Held) → List (Nat × Held)
  | [] => [(k, v)]
  | (a, x) :: r => if a = k then (k, v) :: r else (a, x) :: put k v r

def del (k : Nat) : List (Nat × Held) → List (Nat × Held)
  | [] => []
  | (a, x) :: r => if a = k then r else (a, x) :: del k r

def sumC (l : List (Nat × Held)) : Nat := (l.map fun p => p.2.count).sum

theorem sumC_put (k : Nat) (v : Held) : ∀ l : List (Nat × Held),
    sumC (put k v l) + ((lookup k l).map (·.count)).getD 0 = sumC l + v.count := by
  intro l; induction l with
  | nil => simp [put, lookup, sumC]
  | cons p r ih =>
    obtain ⟨a, x⟩ := p
    by_cases h : a = k
    · simp [put, lookup, sumC, h]; omega
    · simp [put, lookup, sumC, h] at *; omega

theorem sumC_del (k : Nat) : ∀ l : List (Nat × Held),
    sumC (del k l) + ((lookup k l).map (·.count)).getD 0 = sumC l := by
  intro l; induction l with
  | nil => simp [del, lookup, sumC]
  | cons p r ih =>
    obtain ⟨a, x⟩ := p
    by_cases h : a = k
    · simp [del, lookup, sumC, h]; omega
    · simp [del, lookup, sumC, h] at *; omega

theorem len_put (k : Nat) (v : Held) : ∀ l : List (Nat × Held),
    (put k v l).length = if (lookup k l).isSome then l.length else l.length + 1 := by
  intro l; induction l with
  | nil => simp [put, lookup]
  | cons p r ih =>
    obtain ⟨a, x⟩ := p
    by_cases h : a = k
    · simp [put, lookup, h]
    · simp [put, lookup, h, ih]; split <;> simp

theorem len_del (k : Nat) : ∀ l : List (Nat × Held), (del k l).length ≤ l.length := by
  intro l; induction l with
  | nil => simp [del]
  | cons p r ih =>
    obtain ⟨a, x⟩ := p
    by_cases h : a = k
    · simp [del, h]
    · simp [del, h]; omega

theorem mem_put {P : Held → Prop} (k : Nat) (v : Held) (hv : P v) :
    ∀ l : List (Nat × Held), (∀ p ∈ l, P p.2) → ∀ p ∈ put k v l, P p.2 := by
  intro l; induction l with
  | nil => intro _ p hp; simp [put] at hp; subst hp; exact hv
  | cons q r ih =>
    obtain ⟨a, x⟩ := q
    intro h p hp
    by_cases e : a = k
    · simp [put, e] at hp
      rcases hp with rfl | hp
      · exact hv
      · exact h p (by simp [hp])
    · simp [put, e] at hp
      rcases hp with rfl | hp
      · exact h _ (by simp)
      · exact ih (fun p hp => h p (by simp [hp])) p hp

theorem mem_del {P : Held → Prop} (k : Nat) :
    ∀ l : List (Nat × Held), (∀ p ∈ l, P p.2) → ∀ p ∈ del k l, P p.2 := by
  intro l; induction l with
  | nil => simp [del]
  | cons q r ih =>
    obtain ⟨a, x⟩ := q
    intro h p hp
    by_cases e : a = k
    · simp [del, e] at hp; exact h p (by simp [hp])
    · simp [del, e] at hp
      rcases hp with rfl | hp
      · exact h _ (by simp)
      · exact ih (fun p hp => h p (by simp [hp])) p hp

theorem lookup_mem (k : Nat) : ∀ (l : List (Nat × Held)) (h : Held), lookup k l = some h → ∃ a, (a, h) ∈ l := by
  intro l; induction l with
  | nil => simp [lookup]
  | cons p r ih =>
    obtain ⟨a, x⟩ := p
    intro h hh
    by_cases e : a = k
    · simp [lookup, e] at hh; exact ⟨a, by simp [hh]⟩
    · simp [lookup, e] at hh
      obtain ⟨b, hb⟩ := ih h hh; exact ⟨b, by simp [hb]⟩

/-! ### The ring operations -/

/-- `Held::skip_front`: the held state and the bytes freed. -/
def skipFront (c : Cfg) (h : Held) : Held × Nat :=
  match h.q with
  | [] => (h, 0)
  | m :: r => (⟨r, (h.head + (c.H + m.len)) % c.B, h.used - (c.H + m.len), h.count - 1⟩, c.H + m.len)

/-- `Mailbox::expire`: drop from the front while the front is at least `maxAge` old (fuel is the queue length). -/
def expireN (c : Cfg) (now : Nat) : Nat → Held → Held × Nat
  | 0, h => (h, 0)
  | n + 1, h =>
    match h.q with
    | [] => (h, 0)
    | m :: _ =>
      if now - m.t < c.maxAge then (h, 0)
      else
        let r := expireN c now n (skipFront c h).1
        (r.1, r.2 + 1)

def expire (c : Cfg) (now : Nat) (h : Held) : Held × Nat := expireN c now h.q.length h

/-- The quota loop of `push`: while `used + size > B` drop the oldest. Returns the state, the counters and the number dropped. -/
def dropN (c : Cfg) (size : Nat) : Nat → Held → Stats → Held × Stats × Nat
  | 0, h, st => (h, st, 0)
  | n + 1, h, st =>
    if h.used + size > c.B then
      let s := skipFront c h
      if s.2 = 0 then (h, st, 0)
      else
        let r := dropN c size n s.1 { st with dropped := st.dropped + 1, droppedBytes := st.droppedBytes + s.2 }
        (r.1, r.2.1, r.2.2 + 1)
    else (h, st, 0)

inductive Res where
  | stored (seq dropped : Nat) (first : Bool)
  | tooLarge
  | noSlot

def push (c : Cfg) (now : Nat) (mb : MB) (k src flag len : Nat) : MB × Res :=
  let size := c.H + len
  if len = 0 ∨ len > c.maxPkt ∨ size > c.B then
    ({ mb with st := { mb.st with oversize := mb.st.oversize + 1 } }, .tooLarge)
  else if (lookup k mb.held).isNone ∧ mb.held.length ≥ c.N then
    ({ mb with st := { mb.st with members := mb.st.members + 1 } }, .noSlot)
  else
    let h0 := (lookup k mb.held).getD Held.new
    let e := expire c now h0
    let first := e.1.count == 0
    let d := dropN c size (e.1.q.length + 1) e.1 { mb.st with expired := mb.st.expired + e.2 }
    let h3 : Held := ⟨d.1.q ++ [⟨src, flag, len, now, mb.seq⟩], d.1.head, d.1.used + size, d.1.count + 1⟩
    ({ held := put k h3 mb.held, seq := mb.seq + 1, st := { d.2.1 with stored := d.2.1.stored + 1 } },
      .stored mb.seq d.2.2 first)

/-- `Mailbox::pop_fitting` (`mx` the longest body the caller can deliver; `pop` is `mx = maxPkt`). -/
def pop (c : Cfg) (now : Nat) (mb : MB) (k mx : Nat) : MB × Option Msg :=
  match lookup k mb.held with
  | none => (mb, none)
  | some h =>
    let e := expire c now h
    let out : Option Msg := match e.1.q with
      | m :: _ => if m.len ≤ mx then some m else none
      | [] => none
    let h2 := if out.isSome then (skipFront c e.1).1 else e.1
    ({ held := if h2.count = 0 then del k mb.held else put k h2 mb.held, seq := mb.seq,
       st := { mb.st with expired := mb.st.expired + e.2, delivered := mb.st.delivered + (if out.isSome then 1 else 0) } },
      out)

/-- `Mailbox::look`: the oldest message left after the old ones expire, if its body is at most `mx` long. It stays
held, in front: nothing leaves but what expired. -/
def look (c : Cfg) (now : Nat) (mb : MB) (k mx : Nat) : MB × Option Msg :=
  match lookup k mb.held with
  | none => (mb, none)
  | some h =>
    let e := expire c now h
    let out : Option Msg := match e.1.q with
      | m :: _ => if m.len ≤ mx then some m else none
      | [] => none
    ({ held := if e.1.count = 0 then del k mb.held else put k e.1 mb.held, seq := mb.seq,
       st := { mb.st with expired := mb.st.expired + e.2 } }, out)

/-- `Mailbox::remove`: the front message leaves, counted delivered, when it is the one numbered `seq`. -/
def remove (c : Cfg) (mb : MB) (k seq : Nat) : MB :=
  match lookup k mb.held with
  | none => mb
  | some h =>
    match h.q with
    | m :: _ =>
      if m.seq = seq then
        let h2 := (skipFront c h).1
        { held := if h2.count = 0 then del k mb.held else put k h2 mb.held, seq := mb.seq,
          st := { mb.st with delivered := mb.st.delivered + 1 } }
      else mb
    | [] => mb

/-- The step of a pass that steps over a message too long for the route: the oldest live message whose body is at most
`mx`, which may stand behind older longer ones. Nothing leaves but what expired (`ConnectRelayOps.tla` `LookFit`). -/
def lookFit (c : Cfg) (now : Nat) (mb : MB) (k mx : Nat) : MB × Option Msg :=
  match lookup k mb.held with
  | none => (mb, none)
  | some h =>
    let e := expire c now h
    ({ held := if e.1.count = 0 then del k mb.held else put k e.1 mb.held, seq := mb.seq,
       st := { mb.st with expired := mb.st.expired + e.2 } }, e.1.q.find? (fun m => decide (m.len ≤ mx)))

/-- The message numbered `seq` leaves wherever it stands in the member's queue, counted delivered; the ring offset is
left as it is (`RemoveSeq`). -/
def removeSeq (c : Cfg) (mb : MB) (k seq : Nat) : MB :=
  match lookup k mb.held with
  | none => mb
  | some h =>
    match h.q.find? (fun m => m.seq == seq) with
    | none => mb
    | some m =>
      let h2 : Held := ⟨h.q.filter (fun x => x.seq != seq), h.head, h.used - (c.H + m.len), h.count - 1⟩
      { held := if h2.count = 0 then del k mb.held else put k h2 mb.held, seq := mb.seq,
        st := { mb.st with delivered := mb.st.delivered + 1 } }

def sweepL (c : Cfg) (now : Nat) : List (Nat × Held) → List (Nat × Held) × Nat
  | [] => ([], 0)
  | (k, h) :: r =>
    let e := expire c now h
    let rr := sweepL c now r
    ((if e.1.count = 0 then rr.1 else (k, e.1) :: rr.1), rr.2 + e.2)

def sweep (c : Cfg) (now : Nat) (mb : MB) : MB :=
  let s := sweepL c now mb.held
  { mb with held := s.1, st := { mb.st with expired := mb.st.expired + s.2 } }

def clear (mb : MB) (k : Nat) : MB :=
  match lookup k mb.held with
  | none => mb
  | some h => { mb with held := del k mb.held, st := { mb.st with expired := mb.st.expired + h.count } }

/-! ### The invariant -/

/-- What every held member satisfies, for messages numbered below `s`. -/
def HI (c : Cfg) (s : Nat) (h : Held) : Prop :=
  h.used = sizes c h.q ∧ h.used ≤ c.B ∧ h.count = h.q.length ∧ h.head < c.B ∧
  (∀ m ∈ h.q, 1 ≤ m.len ∧ m.len ≤ c.maxPkt ∧ m.seq < s) ∧ h.q.Pairwise (fun a b => a.seq < b.seq)

theorem HI_new (c : Cfg) (s : Nat) (hB : 0 < c.B) : HI c s Held.new := by
  simp [HI, Held.new, sizes, hB]

theorem HI_mono {c : Cfg} {s s' : Nat} {h : Held} (hs : s ≤ s') : HI c s h → HI c s' h := by
  rintro ⟨a, b, d, e, f, g⟩
  exact ⟨a, b, d, e, fun m hm => by have := f m hm; omega, g⟩

theorem skip_nil (c : Cfg) (h : Held) (e : h.q = []) : skipFront c h = (h, 0) := by simp [skipFront, e]

theorem skip_cons (c : Cfg) (h : Held) (m : Msg) (r : List Msg) (e : h.q = m :: r) :
    skipFront c h = (⟨r, (h.head + (c.H + m.len)) % c.B, h.used - (c.H + m.len), h.count - 1⟩, c.H + m.len) := by
  simp [skipFront, e]

theorem HI_skip {c : Cfg} {s : Nat} {h : Held} (hB : 0 < c.B) (hi : HI c s h) : HI c s (skipFront c h).1 := by
  by_cases hq : h.q = []
  · rw [skip_nil c h hq]; exact hi
  · obtain ⟨m, r, hmr⟩ := List.exists_cons_of_ne_nil hq
    rw [skip_cons c h m r hmr]
    obtain ⟨a, b, d, e, f, g⟩ := hi
    rw [hmr] at a d f g
    simp only [sizes, List.map_cons, List.sum_cons] at a
    refine ⟨?_, ?_, ?_, Nat.mod_lt _ hB, fun x hx => f x (by simp [hx]), (List.pairwise_cons.mp g).2⟩
    · simp [sizes]; omega
    · simp only; omega
    · simp at d ⊢; omega

theorem skip_q_of (c : Cfg) (h : Held) (m : Msg) (r : List Msg) (e : h.q = m :: r) : (skipFront c h).1.q = r := by
  rw [skip_cons c h m r e]

theorem skip_count_of (c : Cfg) (h : Held) (m : Msg) (r : List Msg) (e : h.q = m :: r) :
    (skipFront c h).1.count = h.count - 1 := by
  rw [skip_cons c h m r e]

theorem HI_expireN {c : Cfg} {s : Nat} (now : Nat) (hB : 0 < c.B) :
    ∀ (n : Nat) (h : Held), HI c s h → HI c s (expireN c now n h).1 := by
  intro n; induction n with
  | zero => intro h hi; simpa [expireN] using hi
  | succ n ih =>
    intro h hi
    cases hq : h.q with
    | nil => simp [expireN, hq]; exact hi
    | cons m r =>
      by_cases hy : now - m.t < c.maxAge
      · simp [expireN, hq, hy]; exact hi
      · simp [expireN, hq, hy]; exact ih _ (HI_skip hB hi)

theorem expireN_count (c : Cfg) (now : Nat) :
    ∀ (n : Nat) (h : Held), h.count = h.q.length → h.q.length ≤ n →
      (expireN c now n h).1.count + (expireN c now n h).2 = h.count ∧
      (expireN c now n h).1.count = (expireN c now n h).1.q.length := by
  intro n; induction n with
  | zero => intro h hc hl; simp [expireN]; omega
  | succ n ih =>
    intro h hc hl
    cases hq : h.q with
    | nil => simp [expireN, hq] at hc ⊢; omega
    | cons m r =>
      rw [hq] at hc hl
      by_cases hy : now - m.t < c.maxAge
      · simp [expireN, hq, hy]; omega
      · have h1 := skip_q_of c h m r hq
        have h2 := skip_count_of c h m r hq
        have := ih (skipFront c h).1 (by rw [h1, h2]; simp at hc ⊢; omega) (by rw [h1]; simp at hl ⊢; omega)
        simp [expireN, hq, hy]
        rw [h2] at this; simp at hc; omega

/-- After expiry the first message, if any, is younger than the maximum age. -/
theorem expireN_front (c : Cfg) (now : Nat) :
    ∀ (n : Nat) (h : Held), h.q.length ≤ n →
      ∀ m r, (expireN c now n h).1.q = m :: r → now - m.t < c.maxAge := by
  intro n; induction n with
  | zero =>
    intro h hl m r hq
    have : h.q = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [expireN, this] at hq
  | succ n ih =>
    intro h hl m r hq
    cases hq0 : h.q with
    | nil => simp [expireN, hq0] at hq
    | cons m0 r0 =>
      by_cases hy : now - m0.t < c.maxAge
      · simp [expireN, hq0, hy] at hq; obtain ⟨rfl, _⟩ := hq; exact hy
      · simp [expireN, hq0, hy] at hq
        exact ih _ (by rw [skip_q_of c h m0 r0 hq0]; rw [hq0] at hl; simp at hl; omega) m r hq

/-- Expiry removes a prefix. -/
theorem expireN_prefix (c : Cfg) (now : Nat) :
    ∀ (n : Nat) (h : Held), ∃ k, (expireN c now n h).1.q = h.q.drop k := by
  intro n; induction n with
  | zero => intro h; exact ⟨0, by simp [expireN]⟩
  | succ n ih =>
    intro h
    cases hq : h.q with
    | nil => exact ⟨0, by simp [expireN, hq]⟩
    | cons m r =>
      by_cases hy : now - m.t < c.maxAge
      · exact ⟨0, by simp [expireN, hq, hy]⟩
      · obtain ⟨k, hk⟩ := ih (skipFront c h).1
        rw [skip_q_of c h m r hq] at hk
        exact ⟨k + 1, by simp [expireN, hq, hy]; exact hk⟩

/-- The quota loop keeps the invariant, removes a prefix, and leaves room for the new message. -/
theorem dropN_room (c : Cfg) {s : Nat} (hB : 0 < c.B) (size : Nat) (hsz : size ≤ c.B)
    (hH : ∀ m : Msg, 0 < c.H + m.len) :
    ∀ (n : Nat) (h : Held) (st : Stats), HI c s h → h.q.length ≤ n →
      HI c s (dropN c size n h st).1 ∧ (dropN c size n h st).1.used + size ≤ c.B ∧
      ∃ k, (dropN c size n h st).1.q = h.q.drop k := by
  intro n; induction n with
  | zero =>
    intro h st hi hl
    have hq : h.q = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hu : h.used = 0 := by rw [hi.1, hq]; simp [sizes]
    simp only [dropN]
    exact ⟨hi, by omega, 0, by simp⟩
  | succ n ih =>
    intro h st hi hl
    by_cases hgt : h.used + size > c.B
    · cases hq : h.q with
      | nil =>
        exfalso
        have : h.used = 0 := by rw [hi.1, hq]; simp [sizes]
        omega
      | cons m r =>
        have hz : (skipFront c h).2 ≠ 0 := by rw [skip_cons c h m r hq]; have := hH m; simp; omega
        have hi' := HI_skip hB hi
        have key := ih (skipFront c h).1 { st with dropped := st.dropped + 1, droppedBytes := st.droppedBytes + (skipFront c h).2 }
          hi' (by rw [skip_q_of c h m r hq]; rw [hq] at hl; simp at hl; omega)
        obtain ⟨a, b, k, hk⟩ := key
        rw [skip_q_of c h m r hq] at hk
        simp only [dropN, hgt, ite_true, hz, ite_false]
        exact ⟨a, b, k + 1, by rw [hk]; simp [hq]⟩
    · simp only [dropN, hgt, ite_false]
      exact ⟨hi, by omega, 0, by simp⟩

/-- The counters of the quota loop: each dropped message is counted, the member count falls by the same number. -/
theorem dropN_acct (c : Cfg) {s : Nat} (hB : 0 < c.B) (size : Nat) (hH : ∀ m : Msg, 0 < c.H + m.len) :
    ∀ (n : Nat) (h : Held) (st : Stats), HI c s h → h.q.length ≤ n →
      (dropN c size n h st).1.count + (dropN c size n h st).2.2 = h.count ∧
      (dropN c size n h st).2.1.dropped = st.dropped + (dropN c size n h st).2.2 ∧
      (dropN c size n h st).2.1.expired = st.expired ∧ (dropN c size n h st).2.1.stored = st.stored ∧
      (dropN c size n h st).2.1.delivered = st.delivered := by
  intro n; induction n with
  | zero => intro h st hi hl; simp [dropN]
  | succ n ih =>
    intro h st hi hl
    by_cases hgt : h.used + size > c.B
    · cases hq : h.q with
      | nil =>
        have hc := hi.2.2.1
        simp [hq] at hc
        have hu : h.used = 0 := by rw [hi.1, hq]; simp [sizes]
        have : ¬ (h.used + size > c.B) ∨ True := Or.inr trivial
        simp only [dropN, hgt, ite_true]
        have hz : (skipFront c h).2 = 0 := by rw [skip_nil c h hq]
        simp [hz]
      | cons m r =>
        have hz : (skipFront c h).2 ≠ 0 := by rw [skip_cons c h m r hq]; have := hH m; simp; omega
        have key := ih (skipFront c h).1 { st with dropped := st.dropped + 1, droppedBytes := st.droppedBytes + (skipFront c h).2 }
          (HI_skip hB hi) (by rw [skip_q_of c h m r hq]; rw [hq] at hl; simp at hl; omega)
        have hc := hi.2.2.1
        have h2 := skip_count_of c h m r hq
        simp only [dropN, hgt, ite_true, hz, ite_false]
        rw [hq] at hc; simp at hc
        simp at key ⊢; omega
    · simp [dropN, hgt]

theorem sizes_append (c : Cfg) (a b : List Msg) : sizes c (a ++ b) = sizes c a + sizes c b := by
  simp [sizes, List.sum_append]

/-- The invariant of the mailbox. -/
def Inv (c : Cfg) (mb : MB) : Prop :=
  mb.held.length ≤ c.N ∧ (∀ p ∈ mb.held, HI c mb.seq p.2 ∧ 0 < p.2.count) ∧
  mb.st.stored = mb.st.delivered + mb.st.dropped + mb.st.expired + sumC mb.held

theorem Inv_empty (c : Cfg) : Inv c MB.empty := by simp [Inv, MB.empty]; simp [sumC]

section steps
variable {c : Cfg} (hB : 0 < c.B) (hH : 0 < c.H)
include hB hH

theorem push_inv (now k src flag len : Nat) (mb : MB) (hi : Inv c mb) : Inv c (push c now mb k src flag len).1 := by
  obtain ⟨h1, h2, h3⟩ := hi
  unfold push
  by_cases h0 : len = 0 ∨ len > c.maxPkt ∨ c.H + len > c.B
  · simp only [h0, ite_true]
    exact ⟨h1, h2, by simpa using h3⟩
  · simp only [h0, ite_false]
    by_cases hf : (lookup k mb.held).isNone ∧ mb.held.length ≥ c.N
    · simp only [hf, ite_true]
      exact ⟨h1, h2, by simpa using h3⟩
    · simp only [hf, ite_false]
      have hl0 : len ≠ 0 := fun h => h0 (Or.inl h)
      have hlm : len ≤ c.maxPkt := Nat.not_lt.mp (fun x => h0 (Or.inr (Or.inl x)))
      have hsB : c.H + len ≤ c.B := Nat.not_lt.mp (fun x => h0 (Or.inr (Or.inr x)))
      have hH' : ∀ m : Msg, 0 < c.H + m.len := fun m => by omega
      have hI0 : HI c mb.seq ((lookup k mb.held).getD Held.new) ∧
          ((lookup k mb.held).getD Held.new).count = ((lookup k mb.held).map (·.count)).getD 0 := by
        cases hl : lookup k mb.held with
        | none => exact ⟨HI_new c mb.seq hB, rfl⟩
        | some h =>
          obtain ⟨a, ha⟩ := lookup_mem k _ h hl
          simp; exact (h2 _ ha).1
      generalize hh0 : (lookup k mb.held).getD Held.new = h0' at hI0
      obtain ⟨hIe0, hcnt0⟩ := hI0
      have hIe := HI_expireN (s := mb.seq) now hB h0'.q.length h0' hIe0
      have hec := expireN_count c now h0'.q.length h0' hIe0.2.2.1 (Nat.le_refl _)
      have hdr := dropN_room c (s := mb.seq) hB (c.H + len) hsB hH' ((expire c now h0').1.q.length + 1) (expire c now h0').1
        { mb.st with expired := mb.st.expired + (expire c now h0').2 } hIe (by omega)
      have hda := dropN_acct c (s := mb.seq) hB (c.H + len) hH' ((expire c now h0').1.q.length + 1) (expire c now h0').1
        { mb.st with expired := mb.st.expired + (expire c now h0').2 } hIe (by omega)
      obtain ⟨hdI, hdroom, hk, hkq⟩ := hdr
      obtain ⟨hda1, hda2, hda3, hda4, hda5⟩ := hda
      generalize hd : dropN c (c.H + len) ((expire c now h0').1.q.length + 1) (expire c now h0').1
        { mb.st with expired := mb.st.expired + (expire c now h0').2 } = d at *
      obtain ⟨dh, ds, dn⟩ := d
      simp only at *
      have hsum := sumC_put k (⟨dh.q ++ [⟨src, flag, len, now, mb.seq⟩], dh.head, dh.used + (c.H + len), dh.count + 1⟩ : Held) mb.held
      have hlen := len_put k (⟨dh.q ++ [⟨src, flag, len, now, mb.seq⟩], dh.head, dh.used + (c.H + len), dh.count + 1⟩ : Held) mb.held
      have hI3 : HI c (mb.seq + 1) (⟨dh.q ++ [⟨src, flag, len, now, mb.seq⟩], dh.head, dh.used + (c.H + len), dh.count + 1⟩ : Held) := by
        obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hdI
        refine ⟨?_, ?_, ?_, u4, ?_, ?_⟩
        · show dh.used + (c.H + len) = sizes c (dh.q ++ [_]); rw [sizes_append, u1]; simp [sizes]
        · simpa using hdroom
        · simp [u3]
        · intro m hm
          simp at hm
          rcases hm with hm | rfl
          · have := (u5 m hm); refine ⟨this.1, this.2.1, by have := this.2.2; omega⟩
          · simp; omega
        · rw [List.pairwise_append]
          refine ⟨u6, by simp, ?_⟩
          intro a ha b hb
          simp at hb; subst hb
          have := (u5 a ha).2.2; omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [hlen]
        by_cases hs : (lookup k mb.held).isSome = true
        · simp [hs]; exact h1
        · have hn : (lookup k mb.held).isNone = true := by cases hl : lookup k mb.held <;> simp_all
          simp [hs]; simp [hn] at hf; omega
      · intro p hp
        have := mem_put (P := fun h => HI c (mb.seq + 1) h ∧ 0 < h.count) k _ ⟨hI3, by simp⟩ mb.held
          (fun p hp => ⟨HI_mono (by omega) (h2 p hp).1, (h2 p hp).2⟩) p hp
        exact this
      · obtain ⟨hec1, _⟩ := hec
        show ds.stored + 1 = ds.delivered + ds.dropped + ds.expired + sumC (put k _ mb.held)
        simp only [] at hsum
        simp only [expire] at hda1 hda3
        omega

theorem finish_inv (mb : MB) (hi : Inv c mb) (k : Nat) (h h2 : Held) (hl : lookup k mb.held = some h)
    (hI2 : HI c mb.seq h2) (ex dv : Nat) (hcnt : h.count = h2.count + ex + dv) :
    Inv c { held := if h2.count = 0 then del k mb.held else put k h2 mb.held, seq := mb.seq,
            st := { mb.st with expired := mb.st.expired + ex, delivered := mb.st.delivered + dv } } := by
  obtain ⟨h1, h2', h3⟩ := hi
  have hd := sumC_del k mb.held
  have hp := sumC_put k h2 mb.held
  have hlen := len_put k h2 mb.held
  have hdl := len_del k mb.held
  rw [hl] at hd hp hlen
  simp only [Option.map_some, Option.getD_some, Option.isSome_some, ite_true] at hd hp hlen
  by_cases hz : h2.count = 0
  · simp only [hz, ite_true]
    exact ⟨by show (del k mb.held).length ≤ c.N; omega, mem_del (P := fun h => HI c mb.seq h ∧ 0 < h.count) k mb.held h2', by show mb.st.stored = (mb.st.delivered + dv) + mb.st.dropped + (mb.st.expired + ex) + sumC (del k mb.held); omega⟩
  · simp only [hz, ite_false]
    refine ⟨by show (put k h2 mb.held).length ≤ c.N; omega, ?_, by show mb.st.stored = (mb.st.delivered + dv) + mb.st.dropped + (mb.st.expired + ex) + sumC (put k h2 mb.held); omega⟩
    exact mem_put (P := fun h => HI c mb.seq h ∧ 0 < h.count) k h2 ⟨hI2, by omega⟩ mb.held h2'

theorem pop_inv (now k mx : Nat) (mb : MB) (hi : Inv c mb) : Inv c (pop c now mb k mx).1 := by
  unfold pop
  cases hl : lookup k mb.held with
  | none => simpa [hl] using hi
  | some h =>
    obtain ⟨a, ha⟩ := lookup_mem k _ h hl
    have hIh := (hi.2.1 _ ha).1
    have hec : (expire c now h).1.count + (expire c now h).2 = h.count ∧ (expire c now h).1.count = (expire c now h).1.q.length :=
      expireN_count c now h.q.length h hIh.2.2.1 (Nat.le_refl _)
    have hIe : HI c mb.seq (expire c now h).1 := HI_expireN now hB _ h hIh
    simp only []
    generalize expire c now h = e at hec hIe
    obtain ⟨e1, e2⟩ := e
    simp only [] at hec hIe ⊢
    cases hq : e1.q with
    | nil => simp only [hq]; simp; exact finish_inv hB hH mb hi k h e1 hl hIe e2 0 (by omega)
    | cons m r =>
      by_cases hm : m.len ≤ mx
      · simp only [hq, hm, ite_true]
        have hq' := skip_count_of c e1 m r hq
        have hs := HI_skip hB hIe
        simp
        exact finish_inv hB hH mb hi k h _ hl hs e2 1 (by rw [hq] at hec; simp at hec; omega)
      · simp only [hq, hm, ite_false]; simp
        exact finish_inv hB hH mb hi k h e1 hl hIe e2 0 (by omega)

theorem clear_inv (mb : MB) (k : Nat) (hi : Inv c mb) : Inv c (clear mb k) := by
  obtain ⟨h1, h2, h3⟩ := hi
  unfold clear
  cases hl : lookup k mb.held with
  | none => exact ⟨h1, h2, h3⟩
  | some h =>
    have hd := sumC_del k mb.held
    rw [hl] at hd
    simp only [Option.map_some, Option.getD_some] at hd
    exact ⟨by show (del k mb.held).length ≤ c.N; have := len_del k mb.held; omega, mem_del (P := fun h => HI c mb.seq h ∧ 0 < h.count) k mb.held h2, by show mb.st.stored = mb.st.delivered + mb.st.dropped + (mb.st.expired + h.count) + sumC (del k mb.held); omega⟩

theorem sweepL_props (now s : Nat) : ∀ l : List (Nat × Held), (∀ p ∈ l, HI c s p.2 ∧ 0 < p.2.count) →
    (∀ p ∈ (sweepL c now l).1, HI c s p.2 ∧ 0 < p.2.count) ∧
    sumC (sweepL c now l).1 + (sweepL c now l).2 = sumC l ∧ (sweepL c now l).1.length ≤ l.length := by
  intro l; induction l with
  | nil => intro _; simp [sweepL, sumC]
  | cons q r ih =>
    obtain ⟨k, h⟩ := q
    intro hl
    obtain ⟨i1, i2, i3⟩ := ih (fun p hp => hl p (by simp [hp]))
    have hh := (hl (k, h) (by simp))
    have hec : (expire c now h).1.count + (expire c now h).2 = h.count ∧ (expire c now h).1.count = (expire c now h).1.q.length :=
      expireN_count c now h.q.length h hh.1.2.2.1 (Nat.le_refl _)
    have hIe : HI c s (expire c now h).1 := HI_expireN now hB h.q.length h hh.1
    simp only [sweepL]
    by_cases hz : (expire c now h).1.count = 0
    · simp only [hz, ite_true]; refine ⟨i1, ?_, by simp; omega⟩; simp [sumC] at i2 hh ⊢; omega
    · simp only [hz, ite_false]
      refine ⟨?_, ?_, by simp; omega⟩
      · intro p hp; simp at hp; rcases hp with rfl | hp
        · exact ⟨hIe, by show 0 < (expire c now h).1.count; omega⟩
        · exact i1 p hp
      · simp [sumC] at i2 ⊢; omega

theorem sweep_inv (now : Nat) (mb : MB) (hi : Inv c mb) : Inv c (sweep c now mb) := by
  obtain ⟨h1, h2, h3⟩ := hi
  obtain ⟨i1, i2, i3⟩ := sweepL_props hB hH now mb.seq mb.held h2
  exact ⟨by simp only [sweep]; omega, i1, by simp only [sweep]; omega⟩

end steps

/-! ### Reachability and the theorems -/

/-- One call of the mailbox. -/
inductive Step (c : Cfg) : MB → MB → Prop
  | push (now k src flag len : Nat) (mb : MB) : Step c mb (push c now mb k src flag len).1
  | pop (now k mx : Nat) (mb : MB) : Step c mb (pop c now mb k mx).1
  | sweep (now : Nat) (mb : MB) : Step c mb (sweep c now mb)
  | clear (k : Nat) (mb : MB) : Step c mb (clear mb k)

inductive Reach (c : Cfg) : MB → Prop
  | init : Reach c MB.empty
  | step {a b : MB} : Reach c a → Step c a b → Reach c b

theorem step_inv {c : Cfg} (hB : 0 < c.B) (hH : 0 < c.H) {a b : MB} (st : Step c a b) (ih : Inv c a) : Inv c b := by
  cases st with
  | push now k src flag len => exact push_inv hB hH now k src flag len _ ih
  | pop now k mx => exact pop_inv hB hH now k mx _ ih
  | sweep now => exact sweep_inv hB hH now _ ih
  | clear k => exact clear_inv hB hH _ k ih

theorem reach_inv {c : Cfg} (hB : 0 < c.B) (hH : 0 < c.H) {mb : MB} (h : Reach c mb) : Inv c mb := by
  induction h with
  | init => exact Inv_empty c
  | step _ st ih => exact step_inv hB hH st ih

/-- The bytes held for a member never exceed `B` and are the sizes of its messages; the count is the length of the
queue; the head is inside the ring; and there are at most `N` members. -/
theorem mailbox_bounds {c : Cfg} (hB : 0 < c.B) (hH : 0 < c.H) {mb : MB} (h : Reach c mb) :
    mb.held.length ≤ c.N ∧ ∀ p ∈ mb.held, p.2.used = sizes c p.2.q ∧ p.2.used ≤ c.B ∧ p.2.count = p.2.q.length ∧
      p.2.head < c.B ∧ 0 < p.2.count := by
  obtain ⟨a, b, _⟩ := reach_inv hB hH h
  exact ⟨a, fun p hp => ⟨(b p hp).1.1, (b p hp).1.2.1, (b p hp).1.2.2.1, (b p hp).1.2.2.2.1, (b p hp).2⟩⟩

/-- Every message is counted: stored = delivered + dropped oldest + expired + held. -/
theorem conservation {c : Cfg} (hB : 0 < c.B) (hH : 0 < c.H) {mb : MB} (h : Reach c mb) :
    mb.st.stored = mb.st.delivered + mb.st.dropped + mb.st.expired + sumC mb.held := (reach_inv hB hH h).2.2

/-- The queue of a member is in increasing sequence number (arrival order), every sequence number is below the
counter, so a number is handed out once, and every message is a legal one (1 to `maxPkt` bytes). -/
theorem fifo_once {c : Cfg} (hB : 0 < c.B) (hH : 0 < c.H) {mb : MB} (h : Reach c mb) :
    ∀ p ∈ mb.held, p.2.q.Pairwise (fun a b => a.seq < b.seq) ∧ ∀ m ∈ p.2.q, m.seq < mb.seq ∧ 1 ≤ m.len ∧ m.len ≤ c.maxPkt := by
  intro p hp
  have := (reach_inv hB hH h).2.1 p hp
  exact ⟨this.1.2.2.2.2.2, fun m hm => ⟨(this.1.2.2.2.2.1 m hm).2.2, (this.1.2.2.2.2.1 m hm).1, (this.1.2.2.2.2.1 m hm).2.1⟩⟩

/-- A push hands out the counter and advances it: sequence numbers are never reused. -/
theorem push_fresh (c : Cfg) (now k src flag len : Nat) (mb : MB) (s d : Nat) (f : Bool)
    (h : (push c now mb k src flag len).2 = .stored s d f) :
    s = mb.seq ∧ (push c now mb k src flag len).1.seq = mb.seq + 1 := by
  unfold push at h ⊢
  by_cases h0 : len = 0 ∨ len > c.maxPkt ∨ c.H + len > c.B
  · simp [h0] at h
  · by_cases hf : (lookup k mb.held).isNone = true ∧ mb.held.length ≥ c.N
    · simp [h0, hf] at h
    · simp only [h0, hf, ite_false] at h ⊢
      simp at h ⊢
      omega

/-- `pop` returns the first message left after the old ones are expired, it is younger than the maximum age, and the
member keeps the rest of its queue. -/
theorem pop_spec (c : Cfg) (now : Nat) (mb : MB) (k mx : Nat) (m : Msg)
    (h : (pop c now mb k mx).2 = some m) :
    ∃ h0 r, lookup k mb.held = some h0 ∧ (expire c now h0).1.q = m :: r ∧ m.len ≤ mx ∧ now - m.t < c.maxAge := by
  unfold pop at h
  cases hl : lookup k mb.held with
  | none => simp [hl] at h
  | some h0 =>
    simp only [hl] at h
    cases hq : (expire c now h0).1.q with
    | nil => simp [hq] at h
    | cons m0 r =>
      by_cases hm : m0.len ≤ mx
      · simp [hq, hm] at h
        subst h
        exact ⟨h0, r, rfl, hq, hm, expireN_front c now h0.q.length h0 (Nat.le_refl _) m0 r hq⟩
      · simp [hq, hm] at h

/-- `pop` returns what `look` returns: the selection rule is one. -/
theorem pop_look_out (c : Cfg) (now : Nat) (mb : MB) (k mx : Nat) :
    (pop c now mb k mx).2 = (look c now mb k mx).2 := by
  unfold pop look
  cases hl : lookup k mb.held with
  | none => simp
  | some h =>
    simp only []

/-- `look` returns the first message left after the old ones are expired, and counts no delivery: the delivered counter
is unchanged and the message is the front of the member's queue once the old ones are expired. -/
theorem look_keeps (c : Cfg) (now : Nat) (mb : MB) (k mx : Nat) (m : Msg)
    (h : (look c now mb k mx).2 = some m) :
    (look c now mb k mx).1.st.delivered = mb.st.delivered ∧
    ∃ h0 r, lookup k mb.held = some h0 ∧ (expire c now h0).1.q = m :: r ∧ m.len ≤ mx ∧ now - m.t < c.maxAge := by
  have hs : (pop c now mb k mx).2 = some m := by rw [pop_look_out]; exact h
  obtain ⟨h0, r, h1, h2, h3, h4⟩ := pop_spec c now mb k mx m hs
  refine ⟨?_, h0, r, h1, h2, h3, h4⟩
  unfold look
  simp [h1]

/-- `remove` of the front message counts it delivered. -/
theorem remove_front (c : Cfg) (mb : MB) (k : Nat) (h0 : Held) (m : Msg) (r : List Msg)
    (hl : lookup k mb.held = some h0) (hq : h0.q = m :: r) :
    (remove c mb k m.seq).st.delivered = mb.st.delivered + 1 := by
  unfold remove
  simp [hl, hq]

/-- `remove` of a number that is not the front's changes nothing. -/
theorem remove_other (c : Cfg) (mb : MB) (k seq : Nat) (h0 : Held) (m : Msg) (r : List Msg)
    (hl : lookup k mb.held = some h0) (hq : h0.q = m :: r) (hne : m.seq ≠ seq) : remove c mb k seq = mb := by
  unfold remove
  simp [hl, hq, hne]

/-- The quota loop removes the oldest messages: what is left is a suffix of the queue (a prefix is dropped), and it
leaves room for the new message. -/
theorem drop_oldest (c : Cfg) {s : Nat} (hB : 0 < c.B) (size : Nat) (hsz : size ≤ c.B) (hH : ∀ m : Msg, 0 < c.H + m.len)
    (n : Nat) (h : Held) (st : Stats) (hi : HI c s h) (hl : h.q.length ≤ n) :
    ∃ k, (dropN c size n h st).1.q = h.q.drop k ∧ (dropN c size n h st).1.used + size ≤ c.B :=
  let r := dropN_room c hB size hsz hH n h st hi hl
  match r.2.2 with | ⟨k, hk⟩ => ⟨k, hk, r.2.1⟩

/-- `first` of a stored push is "the member held nothing once the old messages were expired". -/
theorem push_first (c : Cfg) (now k src flag len : Nat) (mb : MB) (sq d : Nat) (f : Bool)
    (h : (push c now mb k src flag len).2 = .stored sq d f) :
    f = ((expire c now ((lookup k mb.held).getD Held.new)).1.count == 0) := by
  unfold push at h
  by_cases h0 : len = 0 ∨ len > c.maxPkt ∨ c.H + len > c.B
  · simp [h0] at h
  · by_cases hf : (lookup k mb.held).isNone = true ∧ mb.held.length ≥ c.N
    · simp [h0, hf] at h
    · simp only [h0, hf, ite_false] at h
      simp at h
      exact h.2.2.symm

/-- The wake rule of `route.rs` `hold`: a stored message requests a wake-up when it is the first the member holds or
when the last request is at least `rearm` old; a request records the time. -/
def shouldWake (rearm now woke : Nat) (first : Bool) : Bool := first || decide (rearm ≤ now - woke)

def holdWoke (rearm now woke : Nat) (first : Bool) : Nat × Bool :=
  if shouldWake rearm now woke first then (now, true) else (woke, false)

/-- The first held message always requests a wake-up. -/
theorem wake_first (rearm now woke : Nat) : (holdWoke rearm now woke true).2 = true := by
  simp [holdWoke, shouldWake]

/-- Any other request comes at least `rearm` after the previous one, and records its time. -/
theorem wake_spaced (rearm now woke : Nat) (_hr : 0 < rearm) (hw : woke ≤ now)
    (h : (holdWoke rearm now woke false).2 = true) : woke + rearm ≤ now ∧ (holdWoke rearm now woke false).1 = now := by
  unfold holdWoke shouldWake at *
  by_cases hc : rearm ≤ now - woke
  · simp [hc]; omega
  · simp [hc] at h

/-- Within `rearm` of the previous request, no request is made for a non-first message. -/
theorem wake_quiet (rearm now woke : Nat) (h : now - woke < rearm) :
    holdWoke rearm now woke false = (woke, false) := by
  unfold holdWoke shouldWake
  have : ¬ rearm ≤ now - woke := by omega
  simp [this]

end Vinc.ConnectMailbox
