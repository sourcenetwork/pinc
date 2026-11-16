import Vinc.TransportStreams

/-!
# The window grant of the stream table (POOL_GRANT, RATE_WINDOW, the 1/8 rule, credit follows consumption)

Unbounded theorems about `Vinc.TransportStreams.grantOne` and `grantRun`, which are `Streams::grant`, and the
window arithmetic of `Streams::new`, `Streams::consume` and `Recv::due`. Sizes are arbitrary (`P`).

* `due_spec`: the limit a window is due to move to is above the old one by at least an eighth of the window, never
  beyond the read position plus the window, and never beyond a fixed final size (the 1/8 rule of flow control).
* `grantOne_ledger`: when a grant raises a limit, the credit granted and not yet received, with the new grant,
  fits in the bytes the pool has left (POOL_GRANT).
* `grantOne_limit_mono`, `grantSlot_eighth` (with `grantOne_proc`, which says a grant that acts is `grantSlot`): a grant
  never lowers a limit, keeps it within one window of the read position, and moves it by an eighth of the window at least.
* `grantOne_defers_only_when_unfit`, `grantOne_not_missed`: a window due to move is moved or deferred, and it is
  deferred only when the ledger says it does not fit.
* `grantRun_first_ok`: after `Streams::grant` for the stream just read from, its window is not due (moved or
  nothing due) or deferred: credit follows consumption, the deferred ones being retried by `regrant`.
* `target_bounds`, `maxStream_le_half`, `maxStream_le_ring`, `span_lt_ring`, `ring_never_overflows`: the window size stays between the initial window
  and the ceiling, which is at most half the pool and `(C - 1)` chunks, so a frame inside the credit never
  reaches `C` chunks beyond the read position (the ring never overflows; RATE_WINDOW).
* `target_own`, `target_idle`: a window grows toward twice what its own reader drained, so a stream that drained
  nothing asks for its initial window (METER, #159). These are about the target alone: that no other stream's
  traffic moves a stream's window is checked by the model (`SizeFollowsOwnRate` in `Streams.tla`).
-/

namespace Vinc.TransportStreams

theorem getD_set_self (l : List Slot) (i : Nat) (x d : Slot) (h : i < l.length) : (l.set i x).getD i d = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne (l : List Slot) (i j : Nat) (x d : Slot) (h : j ≠ i) : (l.set i x).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h.symm]

theorem sum_map_set (f : Slot → Nat) (l : List Slot) (i : Nat) (x : Slot) (h : i < l.length) :
    ((l.set i x).map f).sum + f (l.getD i Slot.new) = (l.map f).sum + f x := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => simp; omega
    | succ k =>
      simp at h
      have := ih k h
      simp at this ⊢
      omega

theorem getD_le_sum (f : Slot → Nat) (l : List Slot) (i : Nat) (h : i < l.length) :
    f (l.getD i Slot.new) ≤ (l.map f).sum := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ k =>
      simp at h
      have := ih k h
      simp at this ⊢
      omega

theorem lt_of_open (l : List Slot) (i : Nat) (h : (l.getD i Slot.new).open_ = true) : i < l.length := by
  by_cases hc : i < l.length
  · exact hc
  · have : l.getD i Slot.new = Slot.new := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ i)]
    rw [this] at h
    simp [Slot.new] at h

@[simp] theorem grown_limit (r : Slot) (t : Nat) : (r.grown t).limit = r.limit := rfl
@[simp] theorem grown_size (r : Slot) (t : Nat) : (r.grown t).size = max r.size t := rfl
@[simp] theorem grown_read (r : Slot) (t : Nat) : (r.grown t).read = r.read := rfl
@[simp] theorem grown_open (r : Slot) (t : Nat) : (r.grown t).open_ = r.open_ := rfl
@[simp] theorem grown_fin (r : Slot) (t : Nat) : (r.grown t).fin = r.fin := rfl
@[simp] theorem raised_limit (r : Slot) (c : Nat) : (r.raised c).limit = c := rfl
@[simp] theorem raised_size (r : Slot) (c : Nat) : (r.raised c).size = r.size := rfl
@[simp] theorem parked_limit (r : Slot) (d : Bool) : (r.parked d).limit = r.limit := rfl
@[simp] theorem parked_size (r : Slot) (d : Bool) : (r.parked d).size = r.size := rfl
@[simp] theorem parked_defer (r : Slot) (d : Bool) : (r.parked d).defer = d := rfl
@[simp] theorem parked_open (r : Slot) (d : Bool) : (r.parked d).open_ = r.open_ := rfl
@[simp] theorem parked_read (r : Slot) (d : Bool) : (r.parked d).read = r.read := rfl
@[simp] theorem parked_fin (r : Slot) (d : Bool) : (r.parked d).fin = r.fin := rfl
@[simp] theorem raised_open (r : Slot) (c : Nat) : (r.raised c).open_ = r.open_ := rfl
@[simp] theorem raised_read (r : Slot) (c : Nat) : (r.raised c).read = r.read := rfl
@[simp] theorem raised_fin (r : Slot) (c : Nat) : (r.raised c).fin = r.fin := rfl
@[simp] theorem raised_defer (r : Slot) (c : Nat) : (r.raised c).defer = false := rfl
@[simp] theorem raised_held (r : Slot) (c : Nat) : (r.raised c).held = r.held := rfl
@[simp] theorem grown_held (r : Slot) (t : Nat) : (r.grown t).held = r.held := rfl

/-! ### The 1/8 rule -/
theorem due_spec (p : P) (r : Slot) (c : Nat) (h : r.due p = some c) :
    r.open_ = true ∧ c > r.limit ∧ c ≥ r.limit + r.size / 8 ∧ c ≤ r.read + r.size ∧
      (∀ f, r.fin = some f → c ≤ f) := by
  unfold Slot.due at h
  cases ho : r.open_ <;> simp only [ho] at h
  · simp at h
  · cases hf : r.fin with
    | none =>
      simp [hf] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h3
      refine ⟨rfl, by omega, by omega, by omega, ?_⟩
      intro f hf'
      simp at hf'
    | some f =>
      simp [hf] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h3
      refine ⟨rfl, by omega, by omega, by omega, ?_⟩
      intro f' hf'
      simp at hf'
      omega

/-- A window with no final size or a final size not yet reached is never due when it is not open. -/
theorem due_closed (p : P) (r : Slot) (h : r.open_ = false) : r.due p = none := by
  simp [Slot.due, h]

/-! ### One step of the grant, on the slot -/
theorem grantSlot_mono (p : P) (tgt g a : Nat) (r : Slot) : r.limit ≤ (grantSlot p tgt g a r).limit := by
  unfold grantSlot
  split
  · simp
  · rename_i c hc
    have hd := due_spec p _ _ hc
    simp only [grown_limit] at hd
    split
    · show r.limit ≤ c
      omega
    · simp

theorem grantSlot_raise (p : P) (tgt g a : Nat) (r : Slot) (h : r.limit < (grantSlot p tgt g a r).limit) :
    ∃ c, (r.grown tgt).due p = some c ∧
      g - r.unreceived p + (r.grown tgt).demandTo p c ≤ a ∧
      grantSlot p tgt g a r = (r.grown tgt).raised c := by
  unfold grantSlot at h ⊢
  split at h
  · simp at h
  · rename_i c hc
    split at h
    · rename_i hf
      refine ⟨c, hc, hf, ?_⟩
      simp [hc, hf]
    · simp at h

theorem grantSlot_ok (p : P) (tgt g a : Nat) (r : Slot) :
    (grantSlot p tgt g a r).defer = true ∨ (grantSlot p tgt g a r).due p = none := by
  unfold grantSlot
  split
  · rename_i hn
    right
    simpa [Slot.due] using hn
  · rename_i c hc
    have hd := due_spec p _ _ hc
    split
    · right
      simp only [Slot.due]
      simp only [Slot.due] at hc
      cases hf : r.fin <;> simp [hf] at hc ⊢ <;> omega
    · left; simp

theorem grantSlot_defers (p : P) (tgt g a : Nat) (r : Slot) (h : (grantSlot p tgt g a r).defer = true) :
    ((r.grown tgt).due p = none) ∨
    ∃ c, (r.grown tgt).due p = some c ∧
      ¬ (g - r.unreceived p + (r.grown tgt).demandTo p c ≤ a) := by
  unfold grantSlot at h
  split at h
  · simp at h
  · rename_i c hc
    split at h
    · simp at h
    · rename_i hf
      right
      exact ⟨c, hc, hf⟩

theorem grantSlot_eighth (p : P) (tgt g a : Nat) (r : Slot) (h : r.limit < (grantSlot p tgt g a r).limit) :
    (grantSlot p tgt g a r).limit ≥ r.limit + (grantSlot p tgt g a r).size / 8 ∧
    (grantSlot p tgt g a r).limit ≤ r.read + (grantSlot p tgt g a r).size ∧
    (∀ f, r.fin = some f → (grantSlot p tgt g a r).limit ≤ f) := by
  obtain ⟨c, hc, -, he⟩ := grantSlot_raise p tgt g a r h
  have hd := due_spec p _ _ hc
  rw [he]
  exact ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩

/-! ### On the table -/
theorem getD_setSlot (T : Tab) (i j : Nat) (r : Slot) (hl : i < T.slots.length) :
    (setSlot T i r).slots.getD j Slot.new = if j = i then r else T.slots.getD j Slot.new := by
  unfold setSlot
  by_cases hj : j = i
  · subst hj; simp only [if_true]; exact getD_set_self _ _ _ _ hl
  · rw [if_neg hj]; exact getD_set_ne _ _ _ _ _ hj

theorem proc_cases (r : Slot) (i first : Nat) :
    (!r.open_ || !(i == first || r.defer)) = true ∨ (r.open_ = true ∧ (i = first ∨ r.defer = true)) := by
  cases ho : r.open_ <;> cases hd : r.defer <;> by_cases h : i = first <;> simp [h]

theorem grantOne_skip (p : P) (first : Nat) (T : Tab) (i : Nat)
    (hs : (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true) :
    grantOne p first T i = T := by
  unfold grantOne
  dsimp only
  rw [if_pos hs]

theorem grantOne_proc (p : P) (first : Nat) (T : Tab) (i : Nat)
    (hs : ¬ (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true) :
    grantOne p first T i = setSlot T i (grantSlot p 0 (gu p T + resv p T) (avail p T) (T.slots.getD i Slot.new)) := by
  unfold grantOne
  dsimp only
  rw [if_neg hs]

theorem proc_open (p : P) (first : Nat) (T : Tab) (i : Nat)
    (hs : ¬ (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true) :
    (T.slots.getD i Slot.new).open_ = true := by
  rcases proc_cases (T.slots.getD i Slot.new) i first with h1 | ⟨h1, -⟩
  · exact absurd h1 hs
  · exact h1

theorem grantOne_limit_mono (p : P) (first : Nat) (T : Tab) (i j : Nat) :
    (T.slots.getD j Slot.new).limit ≤ ((grantOne p first T i).slots.getD j Slot.new).limit := by
  by_cases hs : (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true
  · rw [grantOne_skip p first T i hs]; exact Nat.le_refl _
  · have hl := lt_of_open _ _ (proc_open p first T i hs)
    rw [grantOne_proc p first T i hs, getD_setSlot _ _ _ _ hl]
    split
    · subst_vars; exact grantSlot_mono _ _ _ _ _
    · exact Nat.le_refl _

theorem ledger_arith (SU SU' u pd R SH SH' ext b ch : Nat) (hu : u ≤ SU) (h1 : SU' + u = SU + pd) (h2 : SH' = SH)
    (hfit : SU + R - u + pd ≤ (b - (SH + ext)) * ch) : SU' + R ≤ (b - (SH' + ext)) * ch := by
  subst h2
  omega

/-- Credit never exceeds the ledger: when a grant raises a limit, what is granted and not yet received, with the
windows kept for the credit given to the peer, fits in the pool bytes left. -/
theorem grantOne_ledger (p : P) (first : Nat) (T : Tab) (i : Nat)
    (h : (T.slots.getD i Slot.new).limit < ((grantOne p first T i).slots.getD i Slot.new).limit) :
    gu p (grantOne p first T i) + resv p (grantOne p first T i) ≤ avail p (grantOne p first T i) := by
  by_cases hs : (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true
  · rw [grantOne_skip p first T i hs] at h; exact absurd h (Nat.lt_irrefl _)
  · have hl := lt_of_open _ _ (proc_open p first T i hs)
    rw [grantOne_proc p first T i hs, getD_setSlot _ _ _ _ hl, if_pos rfl] at h
    obtain ⟨c, hc, hfit, he⟩ := grantSlot_raise p 0 (gu p T + resv p T) (avail p T) _ h
    rw [grantOne_proc p first T i hs, he]
    have hsum := sum_map_set (fun s => s.unreceived p) T.slots i
      (((T.slots.getD i Slot.new).grown 0).raised c) hl
    have hup := getD_le_sum (fun s => s.unreceived p) T.slots i hl
    have hheld := sum_map_set (fun s => s.held.length) T.slots i
      (((T.slots.getD i Slot.new).grown 0).raised c) hl
    have hpd : (((T.slots.getD i Slot.new).grown 0).raised c).unreceived p
        = ((T.slots.getD i Slot.new).grown 0).demandTo p c := by
      simp [Slot.unreceived, Slot.demandTo, Slot.chargeTo, poolDemand, Slot.reach, Slot.raised, Slot.grown]
    simp only [hpd] at hsum
    simp only [gu, avail, availC, used, heldTotal, setSlot, resv, creditLeft, admitted] at hsum hup hheld hfit ⊢
    simp only [raised_held, grown_held] at hheld
    refine ledger_arith _ _ _ _ _ _ _ _ _ _ hup hsum ?_ hfit
    omega

theorem grantOne_other (p : P) (first : Nat) (T : Tab) (i j : Nat) (hji : j ≠ i) :
    (grantOne p first T i).slots.getD j Slot.new = T.slots.getD j Slot.new := by
  by_cases hs : (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true
  · rw [grantOne_skip p first T i hs]
  · have hl := lt_of_open _ _ (proc_open p first T i hs)
    rw [grantOne_proc p first T i hs, getD_setSlot _ _ _ _ hl, if_neg hji]

/-- A window due to move is moved or deferred: after a grant step on a slot that is the one asked for or already
deferred (or not open), the slot is deferred or has nothing due. -/
theorem grantOne_not_missed (p : P) (first : Nat) (T : Tab) (i : Nat)
    (h : i = first ∨ (T.slots.getD i Slot.new).defer = true ∨ (T.slots.getD i Slot.new).open_ = false) :
    ((grantOne p first T i).slots.getD i Slot.new).defer = true ∨
      ((grantOne p first T i).slots.getD i Slot.new).due p = none := by
  by_cases hs : (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true
  · rw [grantOne_skip p first T i hs]
    right
    apply due_closed
    have key : ∀ (o d b : Bool), (!o || !(b || d)) = true → (b = true ∨ d = true ∨ o = false) → o = false := by decide
    refine key _ _ (i == first) hs ?_
    rcases h with h | h | h
    · left; simp [h]
    · right; left; exact h
    · right; right; exact h
  · have hl := lt_of_open _ _ (proc_open p first T i hs)
    rw [grantOne_proc p first T i hs, getD_setSlot _ _ _ _ hl, if_pos rfl]
    exact grantSlot_ok _ _ _ _ _

/-- A deferred grant is deferred only because the ledger said it did not fit. -/
theorem grantOne_defers_only_when_unfit (p : P) (first : Nat) (T : Tab) (i : Nat)
    (h : ((grantOne p first T i).slots.getD i Slot.new).defer = true)
    (hp : ¬ (!(T.slots.getD i Slot.new).open_ || !(i == first || (T.slots.getD i Slot.new).defer)) = true) :
    (((T.slots.getD i Slot.new).grown 0).due p = none) ∨
    ∃ c, (((T.slots.getD i Slot.new).grown 0).due p = some c) ∧
      ¬ (gu p T + resv p T - (T.slots.getD i Slot.new).unreceived p
          + ((T.slots.getD i Slot.new).grown 0).demandTo p c ≤ avail p T) := by
  have hl := lt_of_open _ _ (proc_open p first T i hp)
  rw [grantOne_proc p first T i hp, getD_setSlot _ _ _ _ hl, if_pos rfl] at h
  exact grantSlot_defers p _ _ _ _ h

/-- The other slots of the table are left alone by the step on slot `i`, so the slot asked for ends the pass with
its window moved or deferred. -/
theorem foldl_other (p : P) (first : Nat) (l : List Nat) (hf : first ∉ l) (T : Tab) :
    ((l.foldl (grantOne p first) T).slots.getD first Slot.new) = T.slots.getD first Slot.new := by
  induction l generalizing T with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hne : first ≠ a := fun h => hf (h ▸ List.mem_cons_self)
    rw [ih (fun h => hf (List.mem_cons_of_mem _ h)) _, grantOne_other p first T a first hne]

theorem foldl_first_ok (p : P) (first : Nat) (l : List Nat) (hnd : l.Nodup) (hf : first ∈ l) (T : Tab) :
    ((l.foldl (grantOne p first) T).slots.getD first Slot.new).defer = true ∨
      ((l.foldl (grantOne p first) T).slots.getD first Slot.new).due p = none := by
  induction l generalizing T with
  | nil => simp at hf
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    by_cases ha : a = first
    · subst ha
      rw [foldl_other p a t hnd.1]
      exact grantOne_not_missed p a T a (Or.inl rfl)
    · have : first ∈ t := by
        rcases List.mem_cons.mp hf with h | h
        · exact absurd h.symm ha
        · exact h
      exact ih hnd.2 this _

/-- Credit follows consumption: after `Streams::grant` for the stream just read from, its window is deferred
(and `regrant` retries it after every release of pool chunks) or has nothing due; no window due to move is left
unmoved. -/
theorem grantRun_first_ok (p : P) (T : Tab) (first : Nat) (h : first < p.n) :
    ((grantRun p T first).slots.getD first Slot.new).defer = true ∨
      ((grantRun p T first).slots.getD first Slot.new).due p = none :=
  foldl_first_ok p first _ (List.nodup_range) (List.mem_range.mpr h) T

/-! ### Window arithmetic: RATE_WINDOW -/
theorem sw_le_maxStream (p : P) : p.sw ≤ p.maxStream := by
  unfold P.sw; exact Nat.min_le_right _ _

/-- The window size a stream's rate asks for stays between the initial window and the ceiling. -/
theorem target_bounds (p : P) (rate : Nat) :
    p.sw ≤ windowTarget p rate ∧ windowTarget p rate ≤ p.maxStream := by
  have := sw_le_maxStream p
  unfold windowTarget
  constructor <;> omega

/-- METER (#159): the target asks for no more than twice what the stream's own reader drained, or the initial window
when that is smaller: a stream that drained nothing asks for its initial window. -/
theorem target_own (p : P) (rate : Nat) : windowTarget p rate ≤ max (rate * 2) p.sw := by
  unfold windowTarget
  omega

/-- METER (#159): a stream that has drained nothing yet asks for its initial window. -/
theorem target_idle (p : P) : windowTarget p 0 = p.sw := by
  have := sw_le_maxStream p
  unfold windowTarget
  omega

/-- The ceiling is at most half the pool. -/
theorem maxStream_le_half (p : P) : p.maxStream ≤ p.b * p.ch / 2 := by
  unfold P.maxStream P.half
  have h1 : p.b * p.ch / 2 / p.ch * p.ch ≤ p.b * p.ch / 2 := Nat.div_mul_le_self _ _
  omega

theorem maxStream_le_ring (p : P) : p.maxStream ≤ (p.ring - 1) * p.ch := by
  unfold P.maxStream
  omega

theorem span_lt_ring (ch ring read reach : Nat) (hch : 0 < ch) (hring : 1 ≤ ring)
    (h : reach ≤ read + (ring - 1) * ch) : (reach - 1) / ch - read / ch < ring := by
  have h1 : (reach - 1) / ch < read / ch + ring := by
    rw [Nat.div_lt_iff_lt_mul hch]
    have h2 : read < ch * (read / ch + 1) := Nat.lt_mul_div_succ read hch
    obtain ⟨r1, rfl⟩ : ∃ r1, ring = r1 + 1 := ⟨ring - 1, by omega⟩
    have h3 : (read / ch + (r1 + 1)) * ch = ch * (read / ch + 1) + r1 * ch := by
      rw [Nat.add_mul, Nat.succ_mul, Nat.mul_succ, Nat.mul_comm ch (read / ch)]
      omega
    have h4 : r1 + 1 - 1 = r1 := by omega
    rw [h4] at h
    rw [h3]
    omega
  omega

/-- The ring never overflows: a frame inside the credit, with the credit within the ceiling of the read position,
ends at most `ring - 1` chunks past the chunk of the read position, so the check of `Recv::store` cannot fail. -/
theorem ring_never_overflows (p : P) (hch : 0 < p.ch) (hring : 1 ≤ p.ring) (r : Slot) (e : Nat)
    (hlim : r.limit ≤ r.read + p.maxStream) (he : e ≤ r.limit) :
    (e - 1) / p.ch - r.read / p.ch < p.ring := by
  apply span_lt_ring p.ch p.ring r.read e hch hring
  have := maxStream_le_ring p
  omega

end Vinc.TransportStreams
