import Pinc.ConnectWsEnc

/-!
# The WebSocket framing of the carrier: the reader takes whole frames, whatever the split

The carrier's WebSocket codec is a byte stream reader: the host appends what it reads to a buffer and calls `decode`
until it asks for more, taking the bytes of each frame. Over the stream of frames the encoder wrote (`Good` frames,
`good_of_encode`), for every sequence of reads (of any sizes, never past the end of the stream) and polls:

- the answers the reader has are exactly the answers for the first `j` frames of the stream, it has taken exactly
  their bytes, no message is open, and what it holds is within what was read (`inv_run`);
- at a quiescent point (the next poll changes nothing) the next frame is not whole yet, or there is none
  (`quiescent_iff`), so two hosts that have read the same bytes, in any split and with any polling, have delivered
  the same frames and the same answers (`split_invariance`), as `split_invariance` of the carrier's reader says of
  its units.
-/

namespace Pinc.ConnectWs

/-- A frame the encoder wrote for a decoder of `peer`, and what that decoder returns for it. -/
def Good (mp : Nat) (peer : Peer) (f : List Nat × DRes) : Prop :=
  0 < f.1.length ∧
  (∀ rest N, f.1.length ≤ N → decode mp peer false (bf (f.1 ++ rest)) N = f.2) ∧
  (∀ rest j, j < f.1.length → decode mp peer false (bf (f.1 ++ rest)) j = .idle) ∧
  ∃ k pl st, f.2 = .frame k pl st f.1.length false

/-- The stream of a list of frames. -/
def flat : List (List Nat × DRes) → List Nat
  | [] => []
  | f :: t => f.1 ++ flat t

/-- The offset of the `j`-th frame in the stream. -/
def off : List (List Nat × DRes) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | f :: t, j + 1 => f.1.length + off t j

theorem off_drop (fs : List (List Nat × DRes)) (j : Nat) : (flat fs).drop (off fs j) = flat (fs.drop j) := by
  induction fs generalizing j with
  | nil => simp [flat, off]
  | cons f t ih =>
    cases j with
    | zero => simp [off]
    | succ j => simp [off, flat, List.drop_append, ih]

theorem off_mono (fs : List (List Nat × DRes)) (j : Nat) : off fs j ≤ off fs (j + 1) := by
  induction fs generalizing j with
  | nil => simp [off]
  | cons f t ih => cases j with
    | zero => simp [off]
    | succ j => simp only [off]; have := ih j; omega


theorem off_zero (fs : List (List Nat × DRes)) : off fs 0 = 0 := by cases fs <;> rfl

theorem off_succ (fs : List (List Nat × DRes)) (j : Nat) (h : j < fs.length) :
    off fs (j + 1) = off fs j + (fs[j]'h).1.length := by
  induction fs generalizing j with
  | nil => simp at h
  | cons f t ih => cases j with
    | zero => simp [off, off_zero]
    | succ j => simp only [off, List.getElem_cons_succ]; have := ih j (by simpa using h); omega

theorem off_le_total (fs : List (List Nat × DRes)) (j : Nat) (h : j ≤ fs.length) : off fs j ≤ off fs fs.length := by
  induction fs generalizing j with
  | nil => simp [off]
  | cons f t ih => cases j with
    | zero => simp [off]
    | succ j => simp only [off, List.length_cons]; have := ih j (by simpa using h); omega

/-- The reader of one end: frames taken `j`, bytes read `W`, whether a message is open, the answers so far. -/
structure Rd where
  j : Nat
  W : Nat
  inm : Bool
  log : List DRes

def Rd.init : Rd := ⟨0, 0, false, []⟩

inductive Act where
  | read (k : Nat)
  | poll

/-- One poll: decode at the next frame's offset with the bytes read since; an accepted frame is taken whole. -/
def pollR (mp : Nat) (peer : Peer) (fs : List (List Nat × DRes)) (R : Rd) : Rd :=
  if R.j < fs.length then
    match decode mp peer R.inm (bf ((flat fs).drop (off fs R.j))) (R.W - off fs R.j) with
    | .frame k pl st used inm' => ⟨R.j + 1, R.W, inm', R.log ++ [.frame k pl st used inm']⟩
    | _ => R
  else R

def stepR (mp : Nat) (peer : Peer) (fs : List (List Nat × DRes)) (R : Rd) : Act → Rd
  | .read k => { R with W := min (R.W + k) (off fs fs.length) }
  | .poll => pollR mp peer fs R

def runR (mp : Nat) (peer : Peer) (fs : List (List Nat × DRes)) (R : Rd) (as : List Act) : Rd :=
  as.foldl (stepR mp peer fs) R

def Inv (fs : List (List Nat × DRes)) (R : Rd) : Prop :=
  R.j ≤ fs.length ∧ off fs R.j ≤ R.W ∧ R.W ≤ off fs fs.length ∧ R.inm = false ∧ R.log = (fs.take R.j).map (·.2)

theorem inv_init (fs : List (List Nat × DRes)) : Inv fs Rd.init := by
  refine ⟨Nat.zero_le _, ?_, Nat.zero_le _, rfl, rfl⟩
  cases fs <;> simp [Rd.init, off]

theorem inv_step (mp peer fs) (hg : ∀ f ∈ fs, Good mp peer f) (R : Rd) (a : Act) (h : Inv fs R) :
    Inv fs (stepR mp peer fs R a) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases a with
  | read k =>
    refine ⟨h1, ?_, ?_, h4, h5⟩ <;> simp only [stepR] <;> omega
  | poll =>
    simp only [stepR, pollR]
    by_cases hj : R.j < fs.length
    · rw [ite_cond_eq_true _ _ (by simp [hj])]
      have hd := List.drop_eq_getElem_cons hj
      have hgood := hg _ (List.getElem_mem hj)
      obtain ⟨hpos, hdec, hidle, k, pl, st, hf⟩ := hgood
      have hflat : (flat fs).drop (off fs R.j) = (fs[R.j]).1 ++ flat (fs.drop (R.j + 1)) := by
        rw [off_drop, hd]; rfl
      rw [hflat]
      by_cases hn : (fs[R.j]).1.length ≤ R.W - off fs R.j
      · rw [h4, hdec _ _ hn, hf]
        have hs := off_succ fs R.j hj
        unfold Inv
        dsimp only
        refine ⟨by omega, by omega, h3, rfl, ?_⟩
        rw [h5, List.take_succ, List.map_append, List.getElem?_eq_getElem hj]
        simp [hf]
      · rw [h4, hidle _ _ (by omega)]
        exact ⟨h1, h2, h3, h4, h5⟩
    · simp only [hj, ite_false]; exact ⟨h1, h2, h3, h4, h5⟩

theorem inv_run (mp peer fs) (hg : ∀ f ∈ fs, Good mp peer f) (as : List Act) (R : Rd) (h : Inv fs R) :
    Inv fs (runR mp peer fs R as) := by
  induction as generalizing R with
  | nil => exact h
  | cons a t ih => exact ih _ (inv_step mp peer fs hg R a h)


/-- A poll that changes nothing: the next frame is not whole yet, or there is none. -/
theorem quiescent_iff (mp peer fs) (hg : ∀ f ∈ fs, Good mp peer f) (R : Rd) (h : Inv fs R)
    (hq : pollR mp peer fs R = R) : R.j = fs.length ∨ R.W < off fs (R.j + 1) := by
  by_cases hj : R.j < fs.length
  · right
    refine Classical.byContradiction fun hw => ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hd := List.drop_eq_getElem_cons hj
    obtain ⟨hpos, hdec, hidle, k, pl, st, hf⟩ := hg _ (List.getElem_mem hj)
    have hflat : (flat fs).drop (off fs R.j) = (fs[R.j]).1 ++ flat (fs.drop (R.j + 1)) := by
      rw [off_drop, hd]; rfl
    have hs := off_succ fs R.j hj
    have hn : (fs[R.j]).1.length ≤ R.W - off fs R.j := by omega
    have : pollR mp peer fs R = ⟨R.j + 1, R.W, false, R.log ++ [.frame k pl st (fs[R.j]).1.length false]⟩ := by
      simp only [pollR, hj, ite_true]
      rw [hflat, h4, hdec _ _ hn, hf]
    rw [this] at hq
    have := congrArg Rd.j hq
    simp at this
  · left; have := h.1; omega

theorem off_le_of_le (fs : List (List Nat × DRes)) (a b : Nat) (h : a ≤ b) : off fs a ≤ off fs b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · exact Nat.le_trans (ih hab) (off_mono fs b)
    · have : a = b + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Two readers that have read the same bytes and are quiescent are at the same frame. -/
theorem quiescent_unique (fs : List (List Nat × DRes)) (R1 R2 : Rd) (h1 : Inv fs R1) (h2 : Inv fs R2)
    (hW : R1.W = R2.W) (q1 : R1.j = fs.length ∨ R1.W < off fs (R1.j + 1))
    (q2 : R2.j = fs.length ∨ R2.W < off fs (R2.j + 1)) : R1.j = R2.j := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2
  rcases Nat.lt_trichotomy R1.j R2.j with h | h | h
  · exfalso
    have := off_le_of_le fs (R1.j + 1) R2.j (by omega)
    rcases q1 with q | q <;> omega
  · exact h
  · exfalso
    have := off_le_of_le fs (R2.j + 1) R1.j (by omega)
    rcases q2 with q | q <;> omega

/-- The reader takes whole frames whatever the split: after ANY sequence of reads and polls the answers it has are
those of the first frames of the stream (`Inv`); two hosts that have read the same bytes, in any split and with any
polling, and are quiescent (the next poll changes nothing), have delivered the same frames and answers. -/
theorem split_invariance (mp peer fs) (hg : ∀ f ∈ fs, Good mp peer f) (as bs : List Act)
    (qa : pollR mp peer fs (runR mp peer fs Rd.init as) = runR mp peer fs Rd.init as)
    (qb : pollR mp peer fs (runR mp peer fs Rd.init bs) = runR mp peer fs Rd.init bs)
    (hW : (runR mp peer fs Rd.init as).W = (runR mp peer fs Rd.init bs).W) :
    (runR mp peer fs Rd.init as).log = (runR mp peer fs Rd.init bs).log := by
  have ia := inv_run mp peer fs hg as _ (inv_init fs)
  have ib := inv_run mp peer fs hg bs _ (inv_init fs)
  have hj := quiescent_unique fs _ _ ia ib hW (quiescent_iff mp peer fs hg _ ia qa) (quiescent_iff mp peer fs hg _ ib qb)
  rw [ia.2.2.2.2, ib.2.2.2.2, hj]


/-- The encoder's frames are good frames: a decoder of the right role reads exactly the payload back, takes exactly the
frame, and waits at every proper prefix, whatever bytes follow. -/
theorem good_of_encode (mp : Nat) (peer : Peer) (op : Nat) (pl : List Nat) (mk : Option (List Nat)) (cap : Nat)
    (e : List Nat) (hmp : mp < 65536) (hop : op = 2 ∨ op = 8 ∨ op = 9 ∨ op = 10)
    (hk : ∀ k, mk = some k → k.length = 4) (hm : mk.isSome = true ↔ peer = .client)
    (h : encode mp op pl mk cap = .ok e) :
    Good mp peer (e, .frame (kindOf op) (if op == 8 then [] else pl)
      (if op == 8 && 2 ≤ pl.length then some (pl.getD 0 0 * 256 + pl.getD 1 0) else none) e.length false) := by
  refine ⟨?_, ?_, ?_, _, _, _, rfl⟩
  · obtain ⟨-, -, -, he⟩ := encode_ok mp op pl mk cap e h
    have := encHdr_length op pl.length mk hk
    subst he
    simp only [List.length_append]
    by_cases h125 : pl.length ≤ 125 <;> simp [h125] at this <;> omega
  · intro rest N hN
    exact encode_decode mp peer op pl mk cap e rest N hN hmp hop hk hm h
  · intro rest j hj
    exact encode_prefix mp peer op pl mk cap e rest hmp hop hk hm h j hj

#audit_axioms Pinc.ConnectWs.good_of_encode
#audit_axioms Pinc.ConnectWs.inv_run
#audit_axioms Pinc.ConnectWs.quiescent_iff
#audit_axioms Pinc.ConnectWs.split_invariance

end Pinc.ConnectWs
