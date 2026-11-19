import Pinc.Axioms
import Pinc.ConnectCarrier

/-!
# The protected carrier: the reader takes whole units, whatever the split

What the model proves about the reader of `ProtectedCarrier`, for every stream, every handshake outcome and every
interleaving of reads and polls:

- a poll decides the next unit exactly when the stream offset by which it can decide is buffered: two length bytes
  for a length of 0 or over the stage's limit, the whole unit otherwise (`poll_idle_iff`); what it decides does not
  depend on any byte past that offset (`poll_extend`), and it never moves the end of the buffer (`poll_wr`);
- a length of 0 or over the limit ends the carrier with `UnitSize` as soon as its two bytes are in (`poll_bad_len`),
  and an ended carrier answers `Closed` and stays ended (`poll_ended`);
- `receive` takes `min(offered, IN_LEN - in_len)` after the release and keeps the buffer bounded (`receive_spec`,
  `receive_bound`);
- after ANY sequence of reads and polls the carrier is the unit-wise reference reader after some number of units,
  and its log of answers is the reference's (`run_ref`); at a quiescent point (the next poll would be idle) or after
  the end, that number is fixed by the bytes taken, so two hosts that took the same bytes, in any split and with any
  polling, agree on the state and on every answer (`split_invariance`).
-/

namespace Pinc.ConnectCarrier
open Pinc.Record (Key Sys sealK openK)

/-! ## Release, receive, transmit -/

/-- The next stream offset the reader takes. -/
def pos (c : C) : Nat := c.rd + c.cons

/-- The buffer holds the unread bytes `[pos, wr)`. -/
def WF (c : C) : Prop := c.rd + c.cons ≤ c.wr

theorem release_fields (c : C) :
    (release c).rd = pos c ∧ (release c).cons = 0 ∧ (release c).wr = c.wr ∧ (release c).st = c.st ∧
    (release c).out = c.out ∧ (release c).spn = c.spn ∧ (release c).rpn = c.rpn ∧ (release c).sk = c.sk ∧
    (release c).rk = c.rk ∧ (release c).kr = c.kr := by
  unfold release pos; split <;> simp_all

theorem release_idem (c : C) : release (release c) = release c := by
  unfold release; split <;> simp_all

/-- The buffer ending at `W` instead. -/
def setW (c : C) (W : Nat) : C := { c with wr := W }

@[simp] theorem setW_wr (c : C) (W : Nat) : (setW c W).wr = W := rfl
@[simp] theorem setW_st (c : C) (W : Nat) : (setW c W).st = c.st := rfl
@[simp] theorem setW_setW (c : C) (a b : Nat) : setW (setW c a) b = setW c b := rfl
theorem pos_setW (c : C) (W : Nat) : pos (setW c W) = pos c := rfl

theorem release_wr (c : C) (W : Nat) : release (setW c W) = setW (release c) W := by
  unfold release setW; split <;> simp_all

theorem receive_spec (k : Konst) (c : C) (n : Nat) :
    (receive k c n).1 = min n (k.inl - (c.wr - pos c)) ∧
    (receive k c n).2 = setW (release c) (c.wr + (receive k c n).1) := by
  obtain ⟨h1, -, h3, -⟩ := release_fields c
  simp [receive, inLen, h1, h3, setW]

/-- The buffer stays within `IN_LEN`. -/
theorem receive_bound (k : Konst) (c : C) (n : Nat) (hwf : WF c) (hb : c.wr - pos c ≤ k.inl) :
    WF (receive k c n).2 ∧ (receive k c n).2.wr - pos (receive k c n).2 ≤ k.inl ∧
    (n ≤ k.inl - (c.wr - pos c) → (receive k c n).1 = n) := by
  obtain ⟨ht, hs⟩ := receive_spec k c n
  obtain ⟨h1, h2, -, -⟩ := release_fields c
  rw [hs]; unfold WF pos setW at *
  dsimp only
  simp only [h1, h2, ht]
  refine ⟨by omega, by omega, fun h => by omega⟩

theorem transmit_spec (c : C) (cap : Nat) :
    (transmit c cap).1 = min cap c.out ∧ (transmit c cap).2 = { c with out := c.out - min cap c.out } := by
  simp [transmit]

/-! ## A poll decides at a fixed offset -/

def maxOf (k : Konst) : Stage → Nat
  | .open_ => k.maxu
  | _ => k.maxm

/-- The stream offset by which the next poll decides: two length bytes for a length of 0 or over the limit, the whole
unit otherwise. -/
def dp (k : Konst) (S : Strm) (c : C) : Nat :=
  if S.hdr (pos c) = 0 ∨ maxOf k c.st < S.hdr (pos c) then pos c + 2 else pos c + 2 + S.hdr (pos c)

theorem endC_wr (c : C) : (endC c).wr = c.wr := rfl

theorem finish_wr (k : Konst) (c : C) (r : DRes) (hs : Hs) : (finish k c r hs).1.wr = c.wr := by
  unfold finish; split <;> simp [endC]

theorem poll_wr (k : Konst) (S : Strm) (c : C) (hs : Hs) : (poll k S c hs).1.wr = c.wr := by
  have hw := (release_fields c).2.2.1
  unfold poll; simp only
  split
  · exact hw
  · unfold pollRecord; split
    · exact hw
    · simp [endC, hw]
    · split
      · simp [endC, hw]
      · split
        · simp [endC, hw]
        · split <;> simp [endC, hw]
  · unfold pollHs; split
    · exact hw
    · simp [endC, hw]
    · rw [finish_wr]; exact hw

/-- On an ended carrier every poll answers `Closed` and the carrier stays ended. -/
theorem poll_ended (k : Konst) (S : Strm) (c : C) (hs : Hs) (h : c.st = .ended) :
    poll k S c hs = (release c, .err .closed) := by
  have := (release_fields c).2.2.2.1
  unfold poll; simp [this, h]

/-- What a poll does with a whole record unit of length `len` (the buffer released): the branch of `poll_record`. -/
def procRec (k : Konst) (S : Strm) (c : C) (len : Nat) : C × Res :=
  if len ≤ k.tag then (endC c, .err .unitSize)
  else match c.rk with
    | none => (endC c, .err .notOpen)
    | some key =>
      match openK key c.rpn (S.opens c.rd c.rpn) with
      | (_, some .authentication) => (endC c, .err .authentication)
      | (_, some .keyRollRequired) => (endC c, .err .keyLimit)
      | (_, some _) => (endC c, .err .record)
      | (key', none) =>
        ({ c with rk := some key', rpn := c.rpn + 1, cons := 2 + len }, if S.fok c.rd then .frame else .err .frame)

/-- What a poll does with a whole handshake unit of length `len`. -/
def procHs (k : Konst) (c : C) (len : Nat) (hs : Hs) : C × Res :=
  let d := hsRun k c.out hs
  finish k { c with cons := 2 + len, out := d.1 } d.2 hs

/-- What a poll does with a whole unit, by stage. -/
def proc (k : Konst) (S : Strm) (c : C) (len : Nat) (hs : Hs) : C × Res :=
  match c.st with
  | .open_ => procRec k S c len
  | _ => procHs k c len hs

theorem pollRecord_eq (k : Konst) (S : Strm) (c : C) :
    pollRecord k S c = match unitLen S c k.maxu with
      | .idle => (c, .idle)
      | .bad => (endC c, .err .unitSize)
      | .unit len => procRec k S c len := rfl

theorem pollHs_eq (k : Konst) (S : Strm) (c : C) (hs : Hs) :
    pollHs k S c hs = match unitLen S c k.maxm with
      | .idle => (c, .idle)
      | .bad => (endC c, .err .unitSize)
      | .unit len => procHs k c len hs := rfl

theorem unitLen_eq (S : Strm) (c : C) (max : Nat) (h0 : c.cons = 0) :
    unitLen S c max =
      if c.wr - pos c < 2 then .idle
      else if S.hdr (pos c) = 0 ∨ max < S.hdr (pos c) then .bad
      else if 2 + S.hdr (pos c) ≤ c.wr - pos c then .unit (S.hdr (pos c)) else .idle := by
  unfold unitLen inLen pos; rw [h0, Nat.add_zero]

/-- A live poll is one decision on the stream offsets: idle until two bytes are in, a length of 0 or over the
stage's limit refused at once, idle again until the whole unit is in, then the unit processed. -/
theorem poll_eq (k : Konst) (S : Strm) (c : C) (hs : Hs) (hne : c.st ≠ .ended) :
    poll k S c hs =
      if c.wr - pos c < 2 then (release c, .idle)
      else if S.hdr (pos c) = 0 ∨ maxOf k c.st < S.hdr (pos c) then (endC (release c), .err .unitSize)
      else if 2 + S.hdr (pos c) ≤ c.wr - pos c then proc k S (release c) (S.hdr (pos c)) hs
      else (release c, .idle) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := release_fields c
  have hp : pos (release c) = pos c := by simp [pos, h1, h2]
  have hu := unitLen_eq S (release c) (maxOf k c.st) h2
  rw [hp, h3] at hu
  unfold poll
  cases hst : c.st with
  | ended => exact absurd hst hne
  | open_ =>
    simp only [maxOf, hst] at hu
    simp only [h4, hst, proc]
    rw [pollRecord_eq, hu]
    by_cases a : c.wr - pos c < 2
    · simp [a]
    · by_cases b : S.hdr (pos c) = 0 ∨ k.maxu < S.hdr (pos c)
      · simp [a, b, maxOf]
      · by_cases d : 2 + S.hdr (pos c) ≤ c.wr - pos c
        · simp [a, b, d, maxOf]
        · simp [a, b, d, maxOf]
  | hs =>
    simp only [maxOf, hst] at hu
    simp only [h4, hst, proc]
    rw [pollHs_eq, hu]
    by_cases a : c.wr - pos c < 2
    · simp [a]
    · by_cases b : S.hdr (pos c) = 0 ∨ k.maxm < S.hdr (pos c)
      · simp [a, b, maxOf]
      · by_cases d : 2 + S.hdr (pos c) ≤ c.wr - pos c
        · simp [a, b, d, maxOf]
        · simp [a, b, d, maxOf]

theorem finish_not_idle (k : Konst) (c : C) (r : DRes) (hs : Hs) : (finish k c r hs).2 ≠ .idle := by
  unfold finish; split <;> (try split) <;> simp

theorem proc_not_idle (k : Konst) (S : Strm) (c : C) (len : Nat) (hs : Hs) : (proc k S c len hs).2 ≠ .idle := by
  unfold proc; split
  · unfold procRec; split
    · simp
    · split
      · simp
      · split <;> (try split) <;> simp
  · exact finish_not_idle _ _ _ _

/-- A live poll is idle exactly when the offset by which it decides is not buffered yet, and then it only
releases. -/
theorem poll_idle_iff (k : Konst) (S : Strm) (c : C) (hs : Hs) (hne : c.st ≠ .ended) :
    ((poll k S c hs).2 = .idle ↔ c.wr < dp k S c) ∧ ((poll k S c hs).2 = .idle → (poll k S c hs).1 = release c) := by
  rw [poll_eq k S c hs hne]
  unfold dp
  have hpn := proc_not_idle k S (release c) (S.hdr (pos c)) hs
  by_cases a : c.wr - pos c < 2
  · have : c.wr < (if S.hdr (pos c) = 0 ∨ maxOf k c.st < S.hdr (pos c) then pos c + 2
        else pos c + 2 + S.hdr (pos c)) := by unfold pos at *; split <;> omega
    simp [a, this]
  · by_cases b : S.hdr (pos c) = 0 ∨ maxOf k c.st < S.hdr (pos c)
    · have : ¬ c.wr < pos c + 2 := by unfold pos at *; omega
      simp [a, b, this]
    · by_cases d : 2 + S.hdr (pos c) ≤ c.wr - pos c
      · have : ¬ c.wr < pos c + 2 + S.hdr (pos c) := by unfold pos at *; omega
        simp [a, b, d, this, hpn]
      · have : c.wr < pos c + 2 + S.hdr (pos c) := by unfold pos at *; omega
        simp [a, b, d, this]

/-- A length of 0 or over the stage's limit ends the carrier with `UnitSize` as soon as its two bytes are buffered,
whatever follows; nothing else changes (no packet number, no key kept, nothing delivered). -/
theorem poll_bad_len (k : Konst) (S : Strm) (c : C) (hs : Hs) (hne : c.st ≠ .ended) (h2 : 2 ≤ c.wr - pos c)
    (hb : S.hdr (pos c) = 0 ∨ maxOf k c.st < S.hdr (pos c)) :
    poll k S c hs = (endC (release c), .err .unitSize) := by
  rw [poll_eq k S c hs hne]
  have : ¬ c.wr - pos c < 2 := by omega
  simp [this, hb]

theorem endC_setW (c : C) (W : Nat) : endC (setW c W) = setW (endC c) W := rfl

theorem finish_setW (k : Konst) (c : C) (r : DRes) (hs : Hs) (W : Nat) :
    finish k (setW c W) r hs = (setW (finish k c r hs).1 W, (finish k c r hs).2) := by
  unfold finish setW; split <;> rfl

theorem proc_setW (k : Konst) (S : Strm) (c : C) (len : Nat) (hs : Hs) (W : Nat) :
    proc k S (setW c W) len hs = (setW (proc k S c len hs).1 W, (proc k S c len hs).2) := by
  obtain ⟨st, rd, wr, cons, out, spn, rpn, sk, rk, kr⟩ := c
  unfold setW
  cases st with
  | open_ =>
    unfold proc procRec; dsimp only
    by_cases a : len ≤ k.tag
    · simp only [a, ite_true]; rfl
    · simp only [a, ite_false]
      cases rk with
      | none => rfl
      | some key => dsimp only; split <;> rfl
  | hs => unfold proc procHs finish; dsimp only; split <;> rfl
  | ended => unfold proc procHs finish; dsimp only; split <;> rfl

/-- What a poll decides does not depend on any byte past the offset by which it decides: with more bytes buffered it
decides the same, and it never moves the end of the buffer. -/
theorem poll_extend (k : Konst) (S : Strm) (c : C) (hs : Hs) (W : Nat) (hne : c.st ≠ .ended)
    (hd : dp k S c ≤ c.wr) (hW : c.wr ≤ W) :
    poll k S (setW c W) hs = (setW (poll k S c hs).1 W, (poll k S c hs).2) := by
  have hne' : (setW c W).st ≠ .ended := hne
  rw [poll_eq k S _ hs hne', poll_eq k S c hs hne, pos_setW, release_wr, setW_st, setW_wr]
  unfold dp at hd
  have a : ¬ c.wr - pos c < 2 := by split at hd <;> omega
  have a' : ¬ W - pos c < 2 := by omega
  simp only [a, a', ite_false]
  by_cases b : S.hdr (pos c) = 0 ∨ maxOf k c.st < S.hdr (pos c)
  · simp only [b, ite_true]; rfl
  · simp only [b, ite_false] at hd ⊢
    have d : 2 + S.hdr (pos c) ≤ c.wr - pos c := by omega
    have d' : 2 + S.hdr (pos c) ≤ W - pos c := by omega
    simp only [d, d', ite_true]
    exact proc_setW k S _ _ hs W

/-! ## Any interleaving of reads and polls is the unit-wise reader -/

/-- The state without the buffer's representation: released, with the end of the buffer forgotten. -/
def view (c : C) : C := setW (release c) 0

theorem view_release (c : C) : view (release c) = view c := by
  simp [view, release_idem]

theorem view_setW (c : C) (W : Nat) : view (setW c W) = view c := by
  simp only [view, release_wr, setW_setW]

theorem poll_release (k : Konst) (S : Strm) (c : C) (hs : Hs) : poll k S (release c) hs = poll k S c hs := by
  unfold poll; rw [release_idem]

theorem release_view (c : C) : release c = setW (view c) c.wr := by
  have := (release_fields c).2.2.1
  simp only [view, setW_setW]
  rw [← this]; rfl

theorem pos_view (c : C) : pos (view c) = pos c := by
  obtain ⟨h1, h2, -⟩ := release_fields c
  simp [pos, view, setW, h1, h2]

theorem st_view (c : C) : (view c).st = c.st := (release_fields c).2.2.2.1

theorem dp_view (k : Konst) (S : Strm) (c : C) : dp k S (view c) = dp k S c := by
  simp only [dp, pos_view, st_view]

/-- The unit-wise reference reader: the next unit (or length) decided with exactly the bytes it needs. -/
def next (k : Konst) (S : Strm) (M : Nat → Hs) (c : C) : C × Res :=
  poll k S (setW c (dp k S c)) (M (pos c))

/-- `n` units of the reference reader from `c`, with its answers; it stops at the end. -/
def refN (k : Konst) (S : Strm) (M : Nat → Hs) : Nat → C → C × List Res
  | 0, c => (c, [])
  | n + 1, c =>
    if c.st = .ended then (c, [])
    else
      let x := next k S M c
      let y := refN k S M n x.1
      (y.1, x.2 :: y.2)

theorem refN_succ (k : Konst) (S : Strm) (M : Nat → Hs) :
    ∀ (j : Nat) (c : C), refN k S M (j + 1) c =
      if (refN k S M j c).1.st = .ended then refN k S M j c
      else ((next k S M (refN k S M j c).1).1, (refN k S M j c).2 ++ [(next k S M (refN k S M j c).1).2])
  | 0, c => by
    by_cases h : c.st = .ended
    · simp [refN, h]
    · simp [refN, h]
  | j + 1, c => by
    by_cases h : c.st = .ended
    · simp [refN, h]
    · have ih := refN_succ k S M j (next k S M c).1
      conv => lhs; unfold refN
      simp only [h, ite_false]
      rw [ih]
      conv => rhs; unfold refN
      simp only [h, ite_false]
      split <;> simp

theorem refN_ended (k : Konst) (S : Strm) (M : Nat → Hs) (j : Nat) (c : C)
    (h : (refN k S M j c).1.st = .ended) : ∀ m, refN k S M (j + m) c = refN k S M j c
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, refN_succ, refN_ended k S M j c h m]
    simp [h]

/-- A host step: offer `n` bytes of the stream (from where the buffer ends), or poll (the handshake machine answers
the unit at the offset being read). The answers logged are those of polls on a live carrier that were not idle. -/
inductive Act where
  | recv (n : Nat)
  | poll

def stepH (k : Konst) (S : Strm) (M : Nat → Hs) (c : C) : Act → C × List Res
  | .recv n => ((receive k c n).2, [])
  | .poll =>
    let x := poll k S c (M (pos c))
    (x.1, if x.2 = .idle ∨ c.st = .ended then [] else [x.2])

def run (k : Konst) (S : Strm) (M : Nat → Hs) : C → List Act → C × List Res
  | c, [] => (c, [])
  | c, a :: as =>
    let x := stepH k S M c a
    let y := run k S M x.1 as
    (y.1, x.2 ++ y.2)

/-- The invariant of every interleaving: the carrier is the reference reader after `j` units, the log is the
reference's, and each of those units was decided within the bytes taken. -/
def RefInv (k : Konst) (S : Strm) (M : Nat → Hs) (c0 c : C) (log : List Res) (j : Nat) : Prop :=
  view c = view (refN k S M j c0).1 ∧ log = (refN k S M j c0).2 ∧
  ∀ i < j, (refN k S M i c0).1.st ≠ .ended → dp k S (refN k S M i c0).1 ≤ c.wr

theorem view_eq_st {a b : C} (h : view a = view b) : a.st = b.st := by
  rw [← st_view a, ← st_view b, h]

theorem view_eq_dp (k : Konst) (S : Strm) {a b : C} (h : view a = view b) : dp k S a = dp k S b := by
  rw [← dp_view k S a, ← dp_view k S b, h]

theorem view_eq_pos {a b : C} (h : view a = view b) : pos a = pos b := by
  rw [← pos_view a, ← pos_view b, h]

theorem stepH_inv (k : Konst) (S : Strm) (M : Nat → Hs) (c0 c : C) (log : List Res) (j : Nat) (a : Act)
    (h : RefInv k S M c0 c log j) :
    ∃ j', RefInv k S M c0 (stepH k S M c a).1 (log ++ (stepH k S M c a).2) j' := by
  obtain ⟨hv, hl, hd⟩ := h
  cases a with
  | recv n =>
    refine ⟨j, ?_, by simp [stepH, hl], fun i hi hne => ?_⟩
    · simp only [stepH]
      rw [(receive_spec k c n).2, view_setW, view_release, hv]
    · have := hd i hi hne
      simp only [stepH]
      rw [(receive_spec k c n).2, setW_wr]; omega
  | poll =>
    obtain ⟨s, hs⟩ : ∃ s, (refN k S M j c0).1 = s := ⟨_, rfl⟩
    rw [hs] at hv
    by_cases he : c.st = .ended
    · refine ⟨j, ?_, by simp [stepH, he, hl], fun i hi hne => ?_⟩
      · simp only [stepH]; rw [poll_ended k S c _ he, view_release, hv, hs]
      · have := hd i hi hne
        simp only [stepH]; rw [poll_ended k S c _ he, (release_fields c).2.2.1]; exact this
    · have hse : s.st ≠ .ended := by rw [← view_eq_st hv]; exact he
      have hdp : dp k S c = dp k S s := view_eq_dp k S hv
      have hpos : pos c = pos s := view_eq_pos hv
      by_cases hw : c.wr < dp k S c
      · -- idle: nothing changes but the release
        have hi := (poll_idle_iff k S c (M (pos c)) he).1.2 hw
        have hc := (poll_idle_iff k S c (M (pos c)) he).2 hi
        refine ⟨j, ?_, by simp [stepH, hi, hl], fun i hi' hne => ?_⟩
        · simp only [stepH]; rw [hc, view_release, hv, hs]
        · have := hd i hi' hne
          simp only [stepH]; rw [hc, (release_fields c).2.2.1]; exact this
      · -- the next unit is decided, as the reference decides it
        have hw' : dp k S s ≤ c.wr := by omega
        have hrel : release c = setW (release (setW s (dp k S s))) c.wr := by
          rw [release_view c, hv, release_wr, setW_setW]
          simp only [view, setW_setW]
        have hX : (release (setW s (dp k S s))).wr = dp k S s := by
          rw [(release_fields _).2.2.1, setW_wr]
        have hXd : dp k S (release (setW s (dp k S s))) = dp k S s := by
          rw [← dp_view, view_release, view_setW, dp_view]
        have hext := poll_extend k S (release (setW s (dp k S s))) (M (pos s)) c.wr
          (by rw [(release_fields _).2.2.2.1, setW_st]; exact hse)
          (by rw [hXd, hX]; exact Nat.le_refl _)
          (by rw [hX]; exact hw')
        have hpoll : poll k S c (M (pos c)) = (setW (next k S M s).1 c.wr, (next k S M s).2) := by
          rw [hpos, ← poll_release, hrel, hext, poll_release]; rfl
        have hsucc := refN_succ k S M j c0
        rw [hs] at hsucc
        simp only [hse, ite_false] at hsucc
        have hni : (next k S M s).2 ≠ .idle := by
          intro hh
          have h1 : (poll k S c (M (pos c))).2 = .idle := by rw [hpoll]; exact hh
          exact hw ((poll_idle_iff k S c _ he).1.1 h1)
        refine ⟨j + 1, ?_, ?_, fun i hi hne => ?_⟩
        · simp only [stepH]; rw [hpoll, view_setW, hsucc]
        · simp only [stepH]; rw [hpoll, hsucc, hl]; simp [hni, he]
        · simp only [stepH]; rw [hpoll, setW_wr]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · exact hd i hi hne
          · subst hi; rw [hs]; exact hw'

/-- After ANY sequence of reads and polls, the carrier is the unit-wise reference reader after some number of units,
with the reference's log of answers, each of those units decided within the bytes taken. -/
theorem run_ref (k : Konst) (S : Strm) (M : Nat → Hs) (c0 : C) :
    ∀ (acts : List Act) (c : C) (log : List Res) (j : Nat), RefInv k S M c0 c log j →
      ∃ j', RefInv k S M c0 (run k S M c acts).1 (log ++ (run k S M c acts).2) j'
  | [], c, log, j, h => ⟨j, by simpa [run] using h⟩
  | a :: as, c, log, j, h => by
    obtain ⟨j1, h1⟩ := stepH_inv k S M c0 c log j a h
    obtain ⟨j2, h2⟩ := run_ref k S M c0 as _ _ j1 h1
    refine ⟨j2, ?_⟩
    simpa [run, List.append_assoc] using h2

theorem refInv_start (k : Konst) (S : Strm) (M : Nat → Hs) (c0 : C) : RefInv k S M c0 c0 [] 0 :=
  ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A state that has taken `W` bytes and decided everything it can: ended, or the next decision needs more. -/
def Settled (k : Konst) (S : Strm) (c : C) : Prop := c.st = .ended ∨ c.wr < dp k S c

theorem settled_unique (k : Konst) (S : Strm) (M : Nat → Hs) (c0 : C) (W : Nat) (j j' : Nat)
    (hj : ∀ i < j, (refN k S M i c0).1.st ≠ .ended → dp k S (refN k S M i c0).1 ≤ W)
    (hj' : ∀ i < j', (refN k S M i c0).1.st ≠ .ended → dp k S (refN k S M i c0).1 ≤ W)
    (sj : (refN k S M j c0).1.st = .ended ∨ W < dp k S (refN k S M j c0).1)
    (sj' : (refN k S M j' c0).1.st = .ended ∨ W < dp k S (refN k S M j' c0).1) :
    refN k S M j c0 = refN k S M j' c0 := by
  rcases Nat.lt_trichotomy j j' with h | h | h
  · rcases sj with e | w
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
      rw [show j + m + 1 = j + (m + 1) by omega, refN_ended k S M j c0 e]
    · by_cases e : (refN k S M j c0).1.st = .ended
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
        rw [show j + m + 1 = j + (m + 1) by omega, refN_ended k S M j c0 e]
      · have := hj' j h e; omega
  · rw [h]
  · rcases sj' with e | w
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
      rw [show j' + m + 1 = j' + (m + 1) by omega, refN_ended k S M j' c0 e]
    · by_cases e : (refN k S M j' c0).1.st = .ended
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
        rw [show j' + m + 1 = j' + (m + 1) by omega, refN_ended k S M j' c0 e]
      · have := hj j' h e; omega

/-- Split invariance: two hosts that drove the same carrier over the same stream with any reads and polls, took the
same bytes and decided everything they could (or saw the end), agree on the state (but for the buffer's
representation) and on every answer, in order. So the answers are a function of the stream alone. -/
theorem split_invariance (k : Konst) (S : Strm) (M : Nat → Hs) (c0 : C) (as bs : List Act)
    (hw : (run k S M c0 as).1.wr = (run k S M c0 bs).1.wr)
    (ha : Settled k S (run k S M c0 as).1) (hb : Settled k S (run k S M c0 bs).1) :
    view (run k S M c0 as).1 = view (run k S M c0 bs).1 ∧ (run k S M c0 as).2 = (run k S M c0 bs).2 := by
  obtain ⟨j, hv, hl, hd⟩ := run_ref k S M c0 as c0 [] 0 (refInv_start k S M c0)
  obtain ⟨j', hv', hl', hd'⟩ := run_ref k S M c0 bs c0 [] 0 (refInv_start k S M c0)
  simp only [List.nil_append] at hl hl'
  have sj : (refN k S M j c0).1.st = .ended ∨ (run k S M c0 as).1.wr < dp k S (refN k S M j c0).1 := by
    rcases ha with e | w
    · left; rw [← view_eq_st hv]; exact e
    · right; rw [← view_eq_dp k S hv]; exact w
  have sj' : (refN k S M j' c0).1.st = .ended ∨ (run k S M c0 as).1.wr < dp k S (refN k S M j' c0).1 := by
    rcases hb with e | w
    · left; rw [← view_eq_st hv']; exact e
    · right; rw [← view_eq_dp k S hv', hw]; exact w
  have hd2 : ∀ i < j', (refN k S M i c0).1.st ≠ .ended → dp k S (refN k S M i c0).1 ≤ (run k S M c0 as).1.wr := by
    intro i hi hne; rw [hw]; exact hd' i hi hne
  have := settled_unique k S M c0 _ j j' hd hd2 sj sj'
  exact ⟨by rw [hv, hv', this], by rw [hl, hl', this]⟩

/-- The host is never stuck: a live carrier whose next poll is idle has room for at least one more byte, because the
input buffer holds a length and the longest unit of either stage (`IN_LEN = 2 + max(MAX_UNIT_LEN,
MAX_MESSAGE_LEN)`). -/
theorem idle_has_room (k : Konst) (S : Strm) (c : C) (hroom : 2 + k.maxm ≤ k.inl ∧ 2 + k.maxu ≤ k.inl)
    (hw : c.wr < dp k S c) : c.wr - pos c < k.inl := by
  have hm : 2 + maxOf k c.st ≤ k.inl := by cases c.st <;> simp [maxOf] <;> omega
  unfold dp at hw
  split at hw <;> omega

#audit_axioms Pinc.ConnectCarrier.receive_bound
#audit_axioms Pinc.ConnectCarrier.poll_idle_iff
#audit_axioms Pinc.ConnectCarrier.poll_bad_len
#audit_axioms Pinc.ConnectCarrier.poll_extend
#audit_axioms Pinc.ConnectCarrier.poll_ended
#audit_axioms Pinc.ConnectCarrier.run_ref
#audit_axioms Pinc.ConnectCarrier.split_invariance
#audit_axioms Pinc.ConnectCarrier.idle_has_room

end Pinc.ConnectCarrier
