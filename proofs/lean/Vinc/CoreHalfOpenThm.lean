import Vinc.Axioms
import Vinc.CoreHalfOpen

/-!
# The half-open cap: the count stays under the cap, a refusal changes nothing, a session past its life is gone at the
# next timer call

What the model proves about the half-open bookkeeping of the endpoint, for any number of slots, any cap, any life and
any times (a clock that steps back included):

- between calls the count is the number of counted sessions and at most the cap, a counted session is
  unauthenticated, and an unauthenticated session holds a deadline at most its life after its creation (`Inv`, kept by
  `init_inv`, `arrive_inv`, `establish_inv`, `release_inv`, `settle_inv`, `dial_inv`, `loop_inv`, and by any run of
  calls, `run_inv`);
- so `poll_timeout` is never later than the end of any unauthenticated session, and gives nothing while the event
  queue is stalled (`poll_le`, `poll_stalled`);
- a first flight that makes no session (a stalled queue, a type that starts nothing, the floor or the cap, no slot or
  a failed construction) leaves the table and the count as they were (`arrive_unchanged`); one that makes a session
  was admitted, took a free slot, and made it unauthenticated, counted unless it resumes, with its deadline at most its
  life away, and changed no other slot (`arrive_made`); only a resumption is admitted at the cap (`arrive_cap`);
- a session leaves the count only when it is established (`establish_slot`, `establish_count`), freed
  (`release_slot`, `release_count`), or at a timer call at or after its end or when its connection ended at its timer
  (`loop_left`); no call but an admitted first flight that does not resume adds to the count (`arrive_made`,
  `loop_won`, and the slot lemmas);
- a timer call that the event queue does not stop (as many pops as there are due deadlines, at most the table's size)
  leaves no unauthenticated session at or past its end (`loop_frees`).
-/

namespace Vinc.CoreHalfOpen

/-! ## The table -/

theorem at?_lt : ∀ (l : List (Option Sl)) (j : Nat) (s : Sl), at? l j = some s → j < l.length
  | [], _, _, h => by simp [at?] at h
  | _ :: _, 0, _, _ => by simp
  | _ :: t, n + 1, s, h => by
    simp only [at?] at h
    have := at?_lt t n s h
    simp only [List.length_cons]
    omega

theorem length_put : ∀ (l : List (Option Sl)) (j : Nat) (x : Option Sl), (put l j x).length = l.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: t, n + 1, x => by simp [put, length_put t n x]

theorem at?_put_eq : ∀ (l : List (Option Sl)) (j : Nat) (x : Option Sl), j < l.length → at? (put l j x) j = x
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => rfl
  | _ :: t, n + 1, x, h => by
    simp only [put, at?]
    exact at?_put_eq t n x (by simp at h; omega)

theorem at?_put_ne : ∀ (l : List (Option Sl)) (i j : Nat) (x : Option Sl), i ≠ j → at? (put l j x) i = at? l i
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, i + 1, j + 1, x, h => by
    simp only [put, at?]
    exact at?_put_ne t i j x (by omega)

theorem put_put : ∀ (l : List (Option Sl)) (j : Nat) (x y : Option Sl), put (put l j x) j y = put l j y
  | [], _, _, _ => rfl
  | _ :: _, 0, _, _ => rfl
  | _ :: t, n + 1, x, y => by simp [put, put_put t n x y]

theorem countOf_put : ∀ (l : List (Option Sl)) (j : Nat) (x : Option Sl), j < l.length →
    countOf (put l j x) + cnt (at? l j) = countOf l + cnt x
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp only [put, countOf, at?]; omega
  | _ :: t, n + 1, x, h => by
    simp only [put, countOf, at?]
    have := countOf_put t n x (by simp at h; omega)
    omega

theorem at?_replicate : ∀ (k j : Nat), at? (List.replicate k none) j = none
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | k + 1, j + 1 => by simp only [List.replicate_succ, at?]; exact at?_replicate k j

theorem countOf_replicate : ∀ k, countOf (List.replicate k none) = 0
  | 0 => rfl
  | k + 1 => by simp only [List.replicate_succ, countOf, cnt]; simpa using countOf_replicate k

/-! ## The invariant -/

/-- What one slot must satisfy: a counted session is unauthenticated, and an unauthenticated one holds a deadline at
most its life after its creation. -/
def good (p : P) : Option Sl → Prop
  | some s => (s.counted = true → s.unauth = true) ∧
              (s.unauth = true → ∃ d, s.dl = some d ∧ d ≤ s.created + p.life)
  | none => True

/-- What holds of the table between calls. -/
structure Inv (p : P) (e : E) : Prop where
  exact : e.count = countOf e.slots
  capped : e.count ≤ p.max
  good : ∀ j, good p (at? e.slots j)

theorem init_inv (p : P) (k : Nat) : Inv p (init k) :=
  ⟨by simp [init, countOf_replicate], by simp [init], fun j => by simp [init, at?_replicate, good]⟩

/-- The two halves of `good`, as properties of the table. -/
theorem Inv.counted_unauth {p : P} {e : E} (hI : Inv p e) {j : Nat} {s : Sl} (h : at? e.slots j = some s)
    (hc : s.counted = true) : s.unauth = true := by
  have := hI.good j
  rw [h] at this
  exact this.1 hc

theorem Inv.deadline {p : P} {e : E} (hI : Inv p e) {j : Nat} {s : Sl} (h : at? e.slots j = some s)
    (hu : s.unauth = true) : ∃ d, s.dl = some d ∧ d ≤ s.created + p.life := by
  have := hI.good j
  rw [h] at this
  exact this.2 hu

/-- Replacing one slot by a good one, with the count moved by the change of that slot, keeps the invariant. -/
theorem inv_put {p : P} {e : E} (hI : Inv p e) {j : Nat} (hj : j < e.slots.length) {x : Option Sl} (hx : good p x)
    (c : Nat) (hc : c + cnt (at? e.slots j) = e.count + cnt x) (hcap : c ≤ p.max) :
    Inv p { slots := put e.slots j x, count := c } := by
  refine ⟨?_, hcap, ?_⟩
  · have := countOf_put e.slots j x hj
    have := hI.exact
    simp only
    omega
  · intro i
    simp only
    by_cases hij : i = j
    · subst hij
      rw [at?_put_eq _ _ _ hj]
      exact hx
    · rw [at?_put_ne _ _ _ _ hij]
      exact hI.good i

theorem cnt_le_count {p : P} {e : E} (hI : Inv p e) {j : Nat} {s : Sl} (h : at? e.slots j = some s) :
    cnt (some s) ≤ e.count := by
  have := countOf_put e.slots j none (at?_lt _ _ _ h)
  rw [h] at this
  have := hI.exact
  simp only [cnt] at *
  omega

/-! ## The steps -/

theorem settle_eq (p : P) (e : E) (j d : Nat) (s : Sl) (h : at? e.slots j = some s) :
    settle p e j d = { slots := put e.slots j (some { s with dl := some (if s.unauth then min d (s.created + p.life)
                                                                       else d) }), count := e.count } := by
  simp [settle, h]

theorem settle_none (p : P) (e : E) (j d : Nat) (h : at? e.slots j = none) : settle p e j d = e := by
  simp [settle, h]

theorem settle_inv {p : P} {e : E} (hI : Inv p e) (j d : Nat) : Inv p (settle p e j d) := by
  cases h : at? e.slots j with
  | none => rw [settle_none p e j d h]; exact hI
  | some s =>
    rw [settle_eq p e j d s h]
    have hs := hI.good j
    rw [h] at hs
    refine inv_put hI (at?_lt _ _ _ h) ?_ e.count (by rw [h]; simp [cnt]) hI.capped
    refine ⟨hs.1, fun hu => ?_⟩
    simp only at hu
    simp only [hu, ite_true]
    exact ⟨_, rfl, Nat.min_le_right _ _⟩

theorem establish_inv {p : P} {e : E} (hI : Inv p e) (j : Nat) : Inv p (establish e j) := by
  cases h : at? e.slots j with
  | none => simp only [establish, h]; exact hI
  | some s =>
    simp only [establish, h]
    have hle := cnt_le_count hI h
    refine inv_put hI (at?_lt _ _ _ h) ?_ _ ?_ ?_
    · exact ⟨fun hc => by simp at hc, fun hu => by simp at hu⟩
    · rw [h]
      by_cases hc : s.counted = true
      · simp only [cnt, hc, ite_true] at hle ⊢
        simp only [Bool.false_eq_true, ite_false]
        omega
      · simp [cnt, hc]
    · have := hI.capped
      split <;> omega

theorem release_inv {p : P} {e : E} (hI : Inv p e) (j : Nat) : Inv p (release e j) := by
  cases h : at? e.slots j with
  | none => simp only [release, h]; exact hI
  | some s =>
    simp only [release, h]
    have hle := cnt_le_count hI h
    refine inv_put hI (at?_lt _ _ _ h) ?_ _ ?_ ?_
    · exact trivial
    · rw [h]
      by_cases hc : s.counted = true
      · simp only [cnt, hc, ite_true] at hle ⊢
        omega
      · simp [cnt, hc]
    · have := hI.capped
      split <;> omega

/-- A dial takes a free slot. -/
theorem dial_inv {p : P} {e : E} (hI : Inv p e) {j : Nat} (hj : j < e.slots.length) (hf : at? e.slots j = none)
    (now d : Nat) : Inv p (settle p (dial e j now) j d) := by
  apply settle_inv
  refine inv_put hI hj ?_ e.count (by rw [hf]; simp [cnt]) hI.capped
  exact ⟨fun hc => by simp at hc, fun hu => by simp at hu⟩

/-! ## Slots and the count, step by step -/

theorem establish_slot (e : E) (j : Nat) (s : Sl) (h : at? e.slots j = some s) :
    at? (establish e j).slots j = some { s with unauth := false, counted := false } := by
  simp only [establish, h]
  exact at?_put_eq _ _ _ (at?_lt _ _ _ h)

theorem establish_other (e : E) (i j : Nat) (hij : i ≠ j) : at? (establish e j).slots i = at? e.slots i := by
  unfold establish
  split
  · exact at?_put_ne _ _ _ _ hij
  · rfl

/-- Establishing a session takes it off the count, if it was on it, and changes the count by nothing else. -/
theorem establish_count {p : P} {e : E} (hI : Inv p e) (j : Nat) :
    (establish e j).count + cnt (at? e.slots j) = e.count := by
  cases h : at? e.slots j with
  | none => simp [establish, h, cnt]
  | some s =>
    have := cnt_le_count hI h
    simp only [establish, h, cnt] at *
    split <;> simp_all <;> omega

theorem release_slot (e : E) (j : Nat) (s : Sl) (h : at? e.slots j = some s) : at? (release e j).slots j = none := by
  simp only [release, h]
  exact at?_put_eq _ _ _ (at?_lt _ _ _ h)

theorem release_other (e : E) (i j : Nat) (hij : i ≠ j) : at? (release e j).slots i = at? e.slots i := by
  unfold release
  split
  · exact at?_put_ne _ _ _ _ hij
  · rfl

/-- Freeing a session takes it off the count, if it was on it, and changes the count by nothing else. -/
theorem release_count {p : P} {e : E} (hI : Inv p e) (j : Nat) :
    (release e j).count + cnt (at? e.slots j) = e.count := by
  cases h : at? e.slots j with
  | none => simp [release, h, cnt]
  | some s =>
    have := cnt_le_count hI h
    simp only [release, h, cnt] at *
    split <;> simp_all <;> omega

/-- Moving a deadline changes neither the count nor what a session is. -/
theorem settle_keeps (p : P) (e : E) (j d i : Nat) :
    (settle p e j d).count = e.count ∧ cnt (at? (settle p e j d).slots i) = cnt (at? e.slots i) ∧
    (expired p 0 (at? (settle p e j d).slots i) = expired p 0 (at? e.slots i)) := by
  cases h : at? e.slots j with
  | none => simp [settle_none p e j d h]
  | some s =>
    rw [settle_eq p e j d s h]
    refine ⟨rfl, ?_⟩
    by_cases hij : i = j
    · subst hij
      rw [at?_put_eq _ _ _ (at?_lt _ _ _ h), h]
      simp [cnt, expired]
    · rw [at?_put_ne _ _ _ _ hij]
      simp

/-! ## A first flight for an id no session holds -/

theorem admits_iff (p : P) (count kind len : Nat) (resume : Bool) :
    admits p count kind len resume = true ↔ floor p kind ≤ len ∧ (resume = true ∨ count < p.max) := by
  simp [admits]

/-- A first flight that makes no session changes nothing. -/
theorem arrive_unchanged (p : P) (e : E) (stalled : Bool) (kind len now : Nat) (resume : Bool) (take : Option Nat)
    (d : Nat) (h : ∀ j, (arrive p e stalled kind len now resume take d).1 ≠ .made j) :
    (arrive p e stalled kind len now resume take d).2 = e := by
  unfold arrive at h ⊢
  cases stalled
  · cases hk : isFirst kind
    · simp
    · cases ha : admits p e.count kind len resume
      · simp
      · cases take with
        | none => simp
        | some k =>
          by_cases hf : k < e.slots.length ∧ at? e.slots k = none
          · exact absurd (by simp [hk, ha, hf]) (h k)
          · simp [hf]
  · simp

/-- What a first flight that makes a session did: it was admitted (the queue not stalled, a first message type, the
floor met and the count under the cap unless it resumes) and took a free slot, which now holds an unauthenticated
session made `now`, counted unless it resumes, with its deadline at most its life away; the count rose by one exactly
when it does not resume. -/
theorem arrive_made_eq (p : P) (e : E) (stalled : Bool) (kind len now : Nat) (resume : Bool) (take : Option Nat)
    (d j : Nat) (h : (arrive p e stalled kind len now resume take d).1 = .made j) :
    stalled = false ∧ isFirst kind = true ∧ admits p e.count kind len resume = true ∧
    j < e.slots.length ∧ at? e.slots j = none ∧
    (arrive p e stalled kind len now resume take d).2 =
      { slots := put e.slots j (some { created := now, unauth := true, counted := !resume,
                                       dl := some (min d (now + p.life)) })
        count := if resume then e.count else e.count + 1 } := by
  unfold arrive at h ⊢
  cases stalled
  · cases hk : isFirst kind
    · simp [hk] at h
    · cases ha : admits p e.count kind len resume
      · simp [hk, ha] at h
      · cases take with
        | none => simp [hk, ha] at h
        | some k =>
          by_cases hf : k < e.slots.length ∧ at? e.slots k = none
          · simp [hk, ha, hf] at h
            subst h
            refine ⟨rfl, rfl, rfl, hf.1, hf.2, ?_⟩
            simp only [hf, and_self, ite_true]
            have hm : at? (make e k now resume).slots k =
                some { created := now, unauth := true, counted := !resume, dl := none } := at?_put_eq _ _ _ hf.1
            rw [settle_eq p _ k d _ hm]
            simp [make, put_put]
          · simp [hk, ha, hf] at h
  · simp at h

/-- The slot a first flight made, and the others, which it left alone. -/
theorem arrive_made (p : P) (e : E) (stalled : Bool) (kind len now : Nat) (resume : Bool) (take : Option Nat)
    (d j : Nat) (h : (arrive p e stalled kind len now resume take d).1 = .made j) :
    at? (arrive p e stalled kind len now resume take d).2.slots j =
      some { created := now, unauth := true, counted := !resume, dl := some (min d (now + p.life)) } ∧
    ∀ i, i ≠ j → at? (arrive p e stalled kind len now resume take d).2.slots i = at? e.slots i := by
  obtain ⟨_, _, _, hlt, _, heq⟩ := arrive_made_eq p e stalled kind len now resume take d j h
  rw [heq]
  exact ⟨at?_put_eq _ _ _ hlt, fun i hi => at?_put_ne _ _ _ _ hi⟩

/-- Only a resumption is admitted at the cap. -/
theorem arrive_cap (p : P) (e : E) (stalled : Bool) (kind len now : Nat) (resume : Bool) (take : Option Nat)
    (d j : Nat) (h : (arrive p e stalled kind len now resume take d).1 = .made j) (hc : p.max ≤ e.count) :
    resume = true := by
  have := (arrive_made_eq p e stalled kind len now resume take d j h).2.2.1
  rw [admits_iff] at this
  rcases this.2 with h | h
  · exact h
  · omega

theorem arrive_inv {p : P} {e : E} (hI : Inv p e) (stalled : Bool) (kind len now : Nat) (resume : Bool)
    (take : Option Nat) (d : Nat) : Inv p (arrive p e stalled kind len now resume take d).2 := by
  by_cases hm : ∃ j, (arrive p e stalled kind len now resume take d).1 = .made j
  · obtain ⟨j, hj⟩ := hm
    obtain ⟨_, _, ha, hlt, hfree, heq⟩ := arrive_made_eq p e stalled kind len now resume take d j hj
    rw [heq]
    rw [admits_iff] at ha
    refine inv_put hI hlt ?_ _ ?_ ?_
    · exact ⟨fun _ => rfl, fun _ => ⟨_, rfl, Nat.min_le_right _ _⟩⟩
    · rw [hfree]
      cases resume <;> simp [cnt]
    · have := hI.capped
      cases resume
      · simp only [Bool.false_eq_true, false_or] at ha
        simp only [Bool.false_eq_true, ite_false]
        omega
      · simpa using this
  · have hu := arrive_unchanged p e stalled kind len now resume take d (fun j hj => hm ⟨j, hj⟩)
    rw [hu]
    exact hI

/-! ## `poll_timeout` -/

theorem earliest_le : ∀ (l : List (Option Sl)) (j : Nat) (s : Sl) (d : Nat), at? l j = some s → s.dl = some d →
    ∃ t, earliest l = some t ∧ t ≤ d
  | [], _, _, _, h, _ => by simp [at?] at h
  | o :: t, 0, s, d, h, hd => by
    simp only [at?] at h
    subst h
    simp only [earliest, dlOf, hd]
    cases earliest t with
    | none => exact ⟨d, rfl, Nat.le_refl _⟩
    | some b => exact ⟨min d b, rfl, Nat.min_le_left _ _⟩
  | o :: t, n + 1, s, d, h, hd => by
    simp only [at?] at h
    obtain ⟨u, hu, hle⟩ := earliest_le t n s d h hd
    simp only [earliest, hu]
    cases dlOf o with
    | none => exact ⟨u, rfl, hle⟩
    | some a => exact ⟨min a u, rfl, Nat.le_trans (Nat.min_le_right _ _) hle⟩

/-- `poll_timeout` is never later than the end of any unauthenticated session. -/
theorem poll_le {p : P} {e : E} (hI : Inv p e) {j : Nat} {s : Sl} (h : at? e.slots j = some s)
    (hu : s.unauth = true) : ∃ t, poll e.slots false = some t ∧ t ≤ s.created + p.life := by
  obtain ⟨d, hd, hle⟩ := hI.deadline h hu
  obtain ⟨t, ht, htd⟩ := earliest_le e.slots j s d h hd
  exact ⟨t, ht, Nat.le_trans htd hle⟩

/-- While the event queue is stalled no deadline is given. -/
theorem poll_stalled (l : List (Option Sl)) : poll l true = none := rfl

/-! ## The timer loop -/

/-- Two slots hold the same session, up to its deadline. -/
def keep : Option Sl → Option Sl → Prop
  | some s, some t => t.created = s.created ∧ t.unauth = s.unauth ∧ t.counted = s.counted
  | none, none => True
  | _, _ => False

theorem keep_refl : ∀ a, keep a a
  | some _ => ⟨rfl, rfl, rfl⟩
  | none => trivial

theorem keep_trans : ∀ a b c, keep a b → keep b c → keep a c
  | some _, some _, some _, ⟨h1, h2, h3⟩, ⟨g1, g2, g3⟩ => ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  | none, none, none, _, _ => trivial
  | some _, none, _, h, _ => h.elim
  | none, some _, _, h, _ => h.elim
  | some _, some _, none, _, h => h.elim
  | none, none, some _, _, h => h.elim

theorem keep_expired (p : P) (now : Nat) : ∀ a b, keep a b → expired p now b = expired p now a
  | some _, some _, ⟨h1, h2, _⟩ => by simp [expired, h1, h2]
  | none, none, _ => rfl
  | some _, none, h => h.elim
  | none, some _, h => h.elim

theorem keep_cnt : ∀ a b, keep a b → cnt b = cnt a
  | some _, some _, ⟨_, _, h3⟩ => by simp [cnt, h3]
  | none, none, _ => rfl
  | some _, none, h => h.elim
  | none, some _, h => h.elim

def isDue (now : Nat) (o : Option Sl) : Nat := if (dueAt now o).isSome then 1 else 0

/-- How many deadlines are due at `now`. -/
def dueCount (now : Nat) : List (Option Sl) → Nat
  | [] => 0
  | o :: t => isDue now o + dueCount now t

theorem dueCount_put (now : Nat) : ∀ (l : List (Option Sl)) (j : Nat) (x : Option Sl), j < l.length →
    dueCount now (put l j x) + isDue now (at? l j) = dueCount now l + isDue now x
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp only [put, dueCount, at?]; omega
  | _ :: t, n + 1, x, h => by
    simp only [put, dueCount, at?]
    have := dueCount_put now t n x (by simp at h; omega)
    omega

theorem isDue_le (now : Nat) : ∀ (l : List (Option Sl)) (j : Nat), isDue now (at? l j) ≤ dueCount now l
  | [], _ => by simp [at?, isDue, dueAt]
  | _ :: _, 0 => by simp only [at?, dueCount]; omega
  | _ :: t, n + 1 => by
    simp only [at?, dueCount]
    have := isDue_le now t n
    omega

theorem dueCount_le (now : Nat) : ∀ (l : List (Option Sl)), dueCount now l ≤ l.length
  | [] => by simp [dueCount]
  | o :: t => by
    simp only [dueCount, List.length_cons]
    have := dueCount_le now t
    have : isDue now o ≤ 1 := by unfold isDue; split <;> omega
    omega

theorem pop_some (now : Nat) : ∀ (l : List (Option Sl)) (j : Nat), pop now l = some j →
    (dueAt now (at? l j)).isSome = true
  | [], _, h => by simp [pop] at h
  | o :: t, j, h => by
    simp only [pop] at h
    split at h
    · simp at h
    · rename_i k _ hk
      simp only [Option.some.injEq] at h
      subst h
      simp only [at?]
      exact pop_some now t k hk
    · rename_i a ha _
      simp only [Option.some.injEq] at h
      subst h
      simp [at?, ha]
    · rename_i a k ha hk
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [at?, ha]
      · simp only [Option.some.injEq] at h
        subst h
        simp only [at?]
        exact pop_some now t k hk

theorem pop_none (now : Nat) : ∀ (l : List (Option Sl)), pop now l = none → ∀ j, dueAt now (at? l j) = none
  | [], _, _ => by simp [at?, dueAt]
  | o :: t, h, j => by
    simp only [pop] at h
    split at h
    · rename_i ho ht
      cases j with
      | zero => simpa [at?] using ho
      | succ n => simp only [at?]; exact pop_none now t ht n
    · simp at h
    · simp at h
    · split at h <;> simp at h

/-- Under the invariant an expired session's deadline is due. -/
theorem expired_due {p : P} {e : E} (hI : Inv p e) {now j : Nat} (h : expired p now (at? e.slots j) = true) :
    (dueAt now (at? e.slots j)).isSome = true := by
  cases hs : at? e.slots j with
  | none => rw [hs] at h; simp [expired] at h
  | some s =>
    rw [hs] at h
    simp only [expired, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨d, hd, hle⟩ := hI.deadline hs h.1
    simp only [dueAt, hd]
    have : d ≤ now := Nat.le_trans hle h.2
    simp [this]

/-- One timer of a session in use: the slot is replaced by one that is not due, the count moves by what that slot
held, the slot stays good, and either the session is gone (it was expired, or its connection ended) or it is the same
session with another deadline. -/
theorem runTimer_spec (p : P) (now : Nat) (d : Option Nat) (e : E) (j : Nat) (s : Sl) (h : at? e.slots j = some s)
    (hc : cnt (some s) ≤ e.count) :
    ∃ x c, runTimer p now d e j = { slots := put e.slots j x, count := c } ∧ dueAt now x = none ∧
      c + cnt (some s) = e.count + cnt x ∧ ((s.counted = true → s.unauth = true) → good p x) ∧
      ((x = none ∧ (expired p now (some s) = true ∨ d = none)) ∨ keep (some s) x) := by
  have hlt := at?_lt _ _ _ h
  have h0 : at? (clearDl e j).slots j = some { s with dl := none } := by
    simp only [clearDl, h]
    exact at?_put_eq _ _ _ hlt
  have hc0 : clearDl e j = { slots := put e.slots j (some { s with dl := none }), count := e.count } := by
    simp [clearDl, h]
  have hexp : expired p now (some { s with dl := none }) = expired p now (some s) := by simp [expired]
  have hrel : release (clearDl e j) j =
      { slots := put e.slots j none, count := if s.counted then e.count - 1 else e.count } := by
    simp only [release, h0]
    rw [hc0]
    simp [put_put]
  have hcnt : (if s.counted then e.count - 1 else e.count) + cnt (some s) = e.count + cnt none := by
    simp only [cnt] at hc ⊢
    split <;> simp_all <;> omega
  unfold runTimer
  simp only [h0, hexp]
  by_cases hx : expired p now (some s) = true
  · rw [if_pos hx, hrel]
    exact ⟨none, _, rfl, rfl, hcnt, fun _ => trivial, Or.inl ⟨rfl, Or.inl hx⟩⟩
  · rw [if_neg hx]
    cases d with
    | none =>
      dsimp only
      rw [hrel]
      exact ⟨none, _, rfl, rfl, hcnt, fun _ => trivial, Or.inl ⟨rfl, Or.inr rfl⟩⟩
    | some d =>
      dsimp only
      -- the deadline the connection asks for, kept within the session's life, then moved past now
      let v := if s.unauth then min d (s.created + p.life) else d
      let w := if v ≤ now then now + 1 else v
      have hset : settle p (clearDl e j) j d =
          { slots := put e.slots j (some { s with dl := some v }), count := e.count } := by
        rw [settle_eq p _ j d _ h0, hc0]
        simp [put_put, v]
      have hat : at? (settle p (clearDl e j) j d).slots j = some { s with dl := some v } := by
        rw [hset]
        exact at?_put_eq _ _ _ hlt
      have hb : bump (settle p (clearDl e j) j d) j now =
          { slots := put e.slots j (some { s with dl := some w }), count := e.count } := by
        simp only [bump, hat]
        by_cases hv : v ≤ now
        · simp only [hv, ite_true, w]
          rw [hset]
          simp [put_put]
        · simp only [hv, ite_false, w]
          exact hset
      rw [hb]
      have hnot : ¬ (s.unauth = true ∧ s.created + p.life ≤ now) := by
        intro hh
        apply hx
        simp [expired, hh.1, hh.2]
      refine ⟨_, _, rfl, ?_, by simp [cnt], ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
      · simp only [dueAt]
        by_cases hv : v ≤ now
        · simp [w, hv]
        · simp [w, hv]
      · intro hcu
        refine ⟨hcu, fun hu => ⟨w, rfl, ?_⟩⟩
        have hu' : s.unauth = true := hu
        have hv : v ≤ s.created + p.life := by
          simp only [v, hu', ite_true]
          exact Nat.min_le_right _ _
        by_cases hvn : v ≤ now
        · simp only [w, hvn, ite_true]
          have : ¬ s.created + p.life ≤ now := fun hh => hnot ⟨hu, hh⟩
          omega
        · simp only [w, hvn, ite_false]
          exact hv

/-- A timer call keeps the invariant. -/
theorem loop_inv {p : P} (now : Nat) (ds : Nat → Option Nat) : ∀ (fuel : Nat) (e : E), Inv p e →
    Inv p (loop p now ds fuel e)
  | 0, _, hI => hI
  | fuel + 1, e, hI => by
    simp only [loop]
    split
    · exact hI
    · rename_i j hj
      have hd := pop_some now e.slots j hj
      cases hs : at? e.slots j with
      | none => rw [hs] at hd; simp [dueAt] at hd
      | some s =>
        obtain ⟨x, c, heq, _, hcount, hgood, hgone⟩ := runTimer_spec p now (ds j) e j s hs (cnt_le_count hI hs)
        rw [heq]
        apply loop_inv now ds fuel
        have hg := hI.good j
        rw [hs] at hg
        refine inv_put hI (at?_lt _ _ _ hs) (hgood hg.1) c (by rw [hs]; exact hcount) ?_
        have hle : cnt x ≤ cnt (some s) := by
          rcases hgone with ⟨rfl, _⟩ | hk
          · simp [cnt]
          · exact Nat.le_of_eq (keep_cnt _ _ hk)
        have := hI.capped
        omega

/-- A timer call that the event queue does not stop, with at least as many pops as deadlines are due (the code pops
up to the table's size), leaves no unauthenticated session at or past its end. -/
theorem loop_frees {p : P} (now : Nat) (ds : Nat → Option Nat) : ∀ (fuel : Nat) (e : E), Inv p e →
    dueCount now e.slots ≤ fuel → ∀ j, expired p now (at? (loop p now ds fuel e).slots j) = false
  | 0, e, hI, hf, j => by
    simp only [loop]
    cases hx : expired p now (at? e.slots j)
    · rfl
    · have := expired_due hI hx
      have := isDue_le now e.slots j
      simp only [isDue] at this
      simp_all
  | fuel + 1, e, hI, hf, j => by
    simp only [loop]
    split
    · rename_i hn
      cases hx : expired p now (at? e.slots j)
      · rfl
      · have := expired_due hI hx
        rw [pop_none now e.slots hn j] at this
        simp at this
    · rename_i k hk
      have hd := pop_some now e.slots k hk
      cases hs : at? e.slots k with
      | none => rw [hs] at hd; simp [dueAt] at hd
      | some s =>
        obtain ⟨x, c, heq, hnd, hcount, hgood, hgone⟩ := runTimer_spec p now (ds k) e k s hs (cnt_le_count hI hs)
        rw [heq]
        have hg := hI.good k
        rw [hs] at hg
        have hle : cnt x ≤ cnt (some s) := by
          rcases hgone with ⟨rfl, _⟩ | hk
          · simp [cnt]
          · exact Nat.le_of_eq (keep_cnt _ _ hk)
        have hI' : Inv p { slots := put e.slots k x, count := c } := by
          refine inv_put hI (at?_lt _ _ _ hs) (hgood hg.1) c (by rw [hs]; exact hcount) ?_
          have := hI.capped
          omega
        apply loop_frees now ds fuel _ hI'
        have := dueCount_put now e.slots k x (at?_lt _ _ _ hs)
        rw [hs] at this hd
        simp only [isDue, hd, ite_true, hnd, Option.isSome_none, Bool.false_eq_true, ite_false] at this
        simp only
        omega

/-- What a slot became over a timer call, from what it was: the same session with another deadline, or gone because it
was expired or its connection ended. -/
def rel (p : P) (now : Nat) (ds : Nat → Option Nat) (j : Nat) (a b : Option Sl) : Prop :=
  keep a b ∨ (b = none ∧ (expired p now a = true ∨ ds j = none))

theorem loop_rel {p : P} (now : Nat) (ds : Nat → Option Nat) (e₀ : E) : ∀ (fuel : Nat) (e : E), Inv p e →
    (∀ j, rel p now ds j (at? e₀.slots j) (at? e.slots j)) →
    ∀ j, rel p now ds j (at? e₀.slots j) (at? (loop p now ds fuel e).slots j)
  | 0, _, _, h => h
  | fuel + 1, e, hI, h => by
    simp only [loop]
    split
    · exact h
    · rename_i k hk
      have hd := pop_some now e.slots k hk
      cases hs : at? e.slots k with
      | none => rw [hs] at hd; simp [dueAt] at hd
      | some s =>
        obtain ⟨x, c, heq, _, hcount, hgood, hgone⟩ := runTimer_spec p now (ds k) e k s hs (cnt_le_count hI hs)
        rw [heq]
        have hg := hI.good k
        rw [hs] at hg
        have hle : cnt x ≤ cnt (some s) := by
          rcases hgone with ⟨rfl, _⟩ | hk
          · simp [cnt]
          · exact Nat.le_of_eq (keep_cnt _ _ hk)
        have hI' : Inv p { slots := put e.slots k x, count := c } := by
          refine inv_put hI (at?_lt _ _ _ hs) (hgood hg.1) c (by rw [hs]; exact hcount) ?_
          have := hI.capped
          omega
        apply loop_rel now ds e₀ fuel _ hI'
        intro i
        by_cases hik : i = k
        · subst hik
          simp only
          rw [at?_put_eq _ _ _ (at?_lt _ _ _ hs)]
          have hr := h i
          rw [hs] at hr
          rcases hgone with ⟨rfl, hwhy⟩ | hkx
          · refine Or.inr ⟨rfl, ?_⟩
            rcases hwhy with hx | hn
            · rcases hr with hk0 | ⟨hn0, _⟩
              · exact Or.inl ((keep_expired p now _ _ hk0).symm.trans hx)
              · exact absurd hn0 (by simp)
            · exact Or.inr hn
          · rcases hr with hk0 | ⟨hn0, _⟩
            · exact Or.inl (keep_trans _ _ _ hk0 hkx)
            · exact absurd hn0 (by simp)
        · simp only
          rw [at?_put_ne _ _ _ _ hik]
          exact h i

/-- Over a timer call a slot keeps its session (up to its deadline), or the session is gone because it was at or past
its end or its connection ended at its timer. -/
theorem loop_left {p : P} {e : E} (hI : Inv p e) (now : Nat) (ds : Nat → Option Nat) (fuel j : Nat) :
    keep (at? e.slots j) (at? (loop p now ds fuel e).slots j) ∨
    (at? (loop p now ds fuel e).slots j = none ∧ (expired p now (at? e.slots j) = true ∨ ds j = none)) :=
  loop_rel now ds e fuel e hI (fun _ => Or.inl (keep_refl _)) j

/-- A timer call adds no session to the count. -/
theorem loop_won {p : P} {e : E} (hI : Inv p e) (now : Nat) (ds : Nat → Option Nat) (fuel j : Nat) :
    cnt (at? (loop p now ds fuel e).slots j) ≤ cnt (at? e.slots j) := by
  rcases loop_left hI now ds fuel j with hk | ⟨hn, _⟩
  · exact Nat.le_of_eq (keep_cnt _ _ hk)
  · rw [hn]; simp [cnt]

/-! ## Any run of calls -/

/-- One call of the endpoint, as far as the half-open bookkeeping goes: a first flight for an id no session holds,
the handshake of a session completing (then its deadline `d`), a session freed (its connection ended, a close finished,
a damaged first message superseded), another input moving a session's deadline, a dial of this node, and a timer call. -/
inductive Op where
  | arrive (stalled : Bool) (kind len now : Nat) (resume : Bool) (take : Option Nat) (d : Nat)
  | est (j d : Nat)
  | close (j : Nat)
  | touch (j d : Nat)
  | dial (j now d : Nat)
  | timer (now : Nat) (ds : Nat → Option Nat) (fuel : Nat)

def step (p : P) (e : E) : Op → E
  | .arrive st kind len now r take d => (arrive p e st kind len now r take d).2
  | .est j d => settle p (establish e j) j d
  | .close j => release e j
  | .touch j d => settle p e j d
  | .dial j now d => if j < e.slots.length ∧ at? e.slots j = none then settle p (dial e j now) j d else e
  | .timer now ds fuel => loop p now ds fuel e

theorem step_inv {p : P} {e : E} (hI : Inv p e) : ∀ op, Inv p (step p e op)
  | .arrive st kind len now r take d => arrive_inv hI st kind len now r take d
  | .est j d => settle_inv (establish_inv hI j) j d
  | .close j => release_inv hI j
  | .touch j d => settle_inv hI j d
  | .dial j now d => by
    simp only [step]
    split
    · rename_i h
      exact dial_inv hI h.1 h.2 now d
    · exact hI
  | .timer now ds fuel => loop_inv now ds fuel e hI

/-- Over any run of calls from an empty table, the count is the number of counted sessions and at most the cap, and
every slot is good. -/
theorem run_inv (p : P) : ∀ (ops : List Op) (e : E), Inv p e → Inv p (ops.foldl (step p) e)
  | [], _, hI => hI
  | op :: ops, e, hI => run_inv p ops (step p e op) (step_inv hI op)

end Vinc.CoreHalfOpen

#audit_axioms Vinc.CoreHalfOpen.init_inv
#audit_axioms Vinc.CoreHalfOpen.arrive_inv
#audit_axioms Vinc.CoreHalfOpen.arrive_unchanged
#audit_axioms Vinc.CoreHalfOpen.arrive_made_eq
#audit_axioms Vinc.CoreHalfOpen.arrive_cap
#audit_axioms Vinc.CoreHalfOpen.establish_inv
#audit_axioms Vinc.CoreHalfOpen.establish_count
#audit_axioms Vinc.CoreHalfOpen.release_inv
#audit_axioms Vinc.CoreHalfOpen.release_count
#audit_axioms Vinc.CoreHalfOpen.settle_inv
#audit_axioms Vinc.CoreHalfOpen.poll_le
#audit_axioms Vinc.CoreHalfOpen.loop_inv
#audit_axioms Vinc.CoreHalfOpen.loop_frees
#audit_axioms Vinc.CoreHalfOpen.loop_left
#audit_axioms Vinc.CoreHalfOpen.loop_won
#audit_axioms Vinc.CoreHalfOpen.run_inv
