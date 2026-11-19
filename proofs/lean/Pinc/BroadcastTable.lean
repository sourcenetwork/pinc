import Pinc.Axioms

/-!
# The broadcast seen-set

An unbounded model of `Seen` in `pinc-broadcast/src/table.rs`, the counterpart of the `table.rs Seen` section of
`BroadcastNodeOps.tla` (checked by TLC on small instances). The slot arrays behind the Rust type are an association
`map` from an id to the time it was recorded, plus `order`, the insertion-ordered queue of `(id, time)` records, and
`last`, the newest recorded time. The parameters `ttl` and `cap` are explicit arguments over all of `Nat`; time
subtraction is saturating, as in the Rust and in `Sub` of the TLA+ model.

`contains` is `now - at <= ttl` on the recorded time. `popFront` removes the map entry only when the map still holds
the head record's time (the Rust `pop_front`), so a later record of the same id survives the pop of an older one.
`expire` pops while the head is older than `ttl`; it is a fuel loop with fuel `order.length`, which suffices because
each pop shortens the queue. `push` always succeeds: the Rust `MidMap` refusal (no room for a new id) is unreachable,
because the queue holds at most `cap` records and the map is sized to the same bound, so the model does not have it.
The map walks from the id's home slot to the first free slot and refuses nothing for a long walk: the home is a keyed
hash of the id (`home`), a walk with enough fuel always ends at a free slot when one exists (`probe_some_of_free`), and
every slot before it is taken (`probe_first_free`); the last section states this.
`insert` refuses a full set unless forced, in which case the oldest record is popped first. `insert` does not read
`ttl`, so it takes no `ttl` argument.

Proven for every `ttl`, `cap` and time: the size bound (`insert_len_le`, `expire_len_le`), that `expire` never changes
`contains` (`expire_preserves_contains`), that `popFront` changes `contains` only for the head id
(`popFront_contains_other`), that a forced insert pops only when full (`forced_pop_only_when_full`), the refusal
condition (`insert_refused_iff`), that a stored id is seen for the whole window (`insert_contains`), that a record
with `k` records ahead of it survives `k` forced inserts (`survives_forced`), that an id seen before and not seen
after an insert of another id was the head of a full set (`early_drop`), and the duplicate-record hazard that a
record of an id already held leaves the id forgotten while a record of it remains in the queue (`duplicate_record`),
which is why log eviction records an id only when the set has lost it.
-/

namespace Pinc.BroadcastTable

/-- The seen-set: id to recorded time, the record queue, and the newest recorded time. -/
structure Seen where
  map : Nat → Option Nat
  order : List (Nat × Nat)
  last : Nat

/-- The empty set. -/
def empty : Seen := ⟨fun _ => none, [], 0⟩

/-- `Seen::contains`: the id is recorded and its record is at most `ttl` old. -/
def contains (S : Seen) (ttl mid now : Nat) : Bool :=
  match S.map mid with
  | some t => decide (now - t ≤ ttl)
  | none => false

/-- Number of records. -/
def len (S : Seen) : Nat := S.order.length

/-- The newest recorded time, if any. -/
def newest (S : Seen) : Option Nat := if S.order = [] then none else some S.last

/-- The first instant at which the oldest record is expired, if any. -/
def nextExpiry (S : Seen) (ttl : Nat) : Option Nat :=
  match S.order with
  | [] => none
  | (_, t) :: _ => some (t + ttl + 1)

/-- `pop_front`: drop the oldest record; the map entry goes only if it still holds that record's time. -/
def popFront (S : Seen) : Seen :=
  match S.order with
  | [] => S
  | (m, t) :: r =>
    { S with order := r, map := fun x => if x = m ∧ S.map m = some t then none else S.map x }

/-- The expire loop with a fuel bound. -/
def expireAux (ttl now : Nat) : Nat → Seen → Seen
  | 0, S => S
  | n + 1, S =>
    match S.order with
    | [] => S
    | (_, t) :: _ => if ttl < now - t then expireAux ttl now n (popFront S) else S

/-- `expire`: pop while the oldest record is older than `ttl`. -/
def expire (S : Seen) (ttl now : Nat) : Seen := expireAux ttl now S.order.length S

/-- `push`: append the record, set the map entry and the newest time. -/
def push (S : Seen) (mid now : Nat) : Seen :=
  { map := fun x => if x = mid then some now else S.map x, order := S.order ++ [(mid, now)], last := now }

/-- `insert`: a full set refuses unless forced, which pops the oldest record first. -/
def insert (S : Seen) (cap mid now : Nat) (force : Bool) : Seen × Bool :=
  if cap ≤ S.order.length then
    if force then (push (popFront S) mid now, true) else (S, false)
  else (push S mid now, true)

/-- Forced inserts in sequence, each with its own instant. -/
def forcedAll (S : Seen) (cap : Nat) : List (Nat × Nat) → Seen
  | [] => S
  | (i, t) :: rest => forcedAll (insert S cap i t true).1 cap rest

@[simp] theorem popFront_order (S : Seen) : (popFront S).order = S.order.tail := by
  unfold popFront; split <;> simp_all

@[simp] theorem push_order (S : Seen) (mid now : Nat) : (push S mid now).order = S.order ++ [(mid, now)] := rfl

theorem popFront_len_le (S : Seen) : (popFront S).order.length ≤ S.order.length := by
  simp

/-- Expire never grows the queue (any fuel). -/
theorem expireAux_len_le (ttl now : Nat) : ∀ (n : Nat) (S : Seen),
    (expireAux ttl now n S).order.length ≤ S.order.length := by
  intro n
  induction n with
  | zero => intro S; simp [expireAux]
  | succ n ih =>
    intro S
    unfold expireAux
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_trans (ih _) (popFront_len_le S)
      · exact Nat.le_refl _

theorem expire_len_le (S : Seen) (ttl now : Nat) : (expire S ttl now).order.length ≤ S.order.length :=
  expireAux_len_le ttl now _ S

/-- (1) A forced or unforced insert keeps a set within `cap` (`0 < cap`). -/
theorem insert_len_le (S : Seen) (cap mid now : Nat) (force : Bool) (hcap : 0 < cap)
    (h : S.order.length ≤ cap) : (insert S cap mid now force).1.order.length ≤ cap := by
  unfold insert
  split
  · split
    · simp; omega
    · simpa using h
  · simp; omega

theorem push_contains_ne (S : Seen) (ttl mid mid' now t : Nat) (h : mid ≠ mid') :
    contains (push S mid' now) ttl mid t = contains S ttl mid t := by
  simp [contains, push, h]

/-- (3) `popFront` changes `contains` only for the id of the head record. -/
theorem popFront_contains_other (S : Seen) (ttl m t' mid now : Nat) (r : List (Nat × Nat))
    (hS : S.order = (m, t') :: r) (h : mid ≠ m) :
    contains (popFront S) ttl mid now = contains S ttl mid now := by
  unfold popFront; rw [hS]; simp [contains, h]

/-- Popping an expired head leaves `contains` unchanged, for the head id too. -/
theorem popFront_expired_contains (S : Seen) (ttl m t' mid now : Nat) (r : List (Nat × Nat))
    (hS : S.order = (m, t') :: r) (hage : ttl < now - t') :
    contains (popFront S) ttl mid now = contains S ttl mid now := by
  by_cases h : mid = m
  · subst h
    unfold popFront; rw [hS]
    simp only [contains]
    by_cases hm : S.map mid = some t'
    · simp [hm]; omega
    · simp [hm]
  · exact popFront_contains_other S ttl m t' mid now r hS h

theorem expireAux_contains (ttl now mid : Nat) : ∀ (n : Nat) (S : Seen),
    contains (expireAux ttl now n S) ttl mid now = contains S ttl mid now := by
  intro n
  induction n with
  | zero => intro S; simp [expireAux]
  | succ n ih =>
    intro S
    unfold expireAux
    split
    · rfl
    · rename_i t' r hS
      split
      · rename_i hage
        rw [ih]
        exact popFront_expired_contains S ttl _ t' mid now _ hS hage
      · rfl

/-- (2) Expire never changes `contains` at the instant it runs. -/
theorem expire_preserves_contains (S : Seen) (ttl now mid : Nat) :
    contains (expire S ttl now) ttl mid now = contains S ttl mid now :=
  expireAux_contains ttl now mid _ S

/-- (4) A forced insert on a set with room pops nothing. -/
theorem forced_pop_only_when_full (S : Seen) (cap mid now : Nat) (h : S.order.length < cap) :
    (insert S cap mid now true).1.order = S.order ++ [(mid, now)] ∧ (insert S cap mid now true).2 = true := by
  have h' : ¬cap ≤ S.order.length := by omega
  simp [insert, h']

/-- A forced insert on a full set pops exactly the head. -/
theorem forced_pop_when_full (S : Seen) (cap mid now : Nat) (h : cap ≤ S.order.length) :
    (insert S cap mid now true).1.order = S.order.tail ++ [(mid, now)] := by
  simp [insert, h]

/-- (5) An unforced insert is refused exactly when the set is full; a refusal changes nothing. -/
theorem insert_refused_iff (S : Seen) (cap mid now : Nat) :
    (insert S cap mid now false).2 = false ↔ cap ≤ S.order.length := by
  unfold insert
  by_cases h : cap ≤ S.order.length <;> simp [h]

theorem insert_refused_unchanged (S : Seen) (cap mid now : Nat) (h : cap ≤ S.order.length) :
    (insert S cap mid now false).1 = S := by
  unfold insert; simp [h]

theorem push_contains (S : Seen) (ttl mid now t : Nat) :
    contains (push S mid now) ttl mid t = decide (t - now ≤ ttl) := by
  simp [contains, push]

/-- (6) After a successful insert the id is seen for every instant up to `now + ttl`. -/
theorem insert_contains (S : Seen) (cap mid now : Nat) (force : Bool) (ttl t : Nat)
    (hok : (insert S cap mid now force).2 = true) (ht : t ≤ now + ttl) :
    contains (insert S cap mid now force).1 ttl mid t = true := by
  have key : t - now ≤ ttl := by omega
  unfold insert at hok ⊢
  by_cases h : cap ≤ S.order.length
  · cases force
    · simp [h] at hok
    · simp [h, push_contains, key]
  · simp [h, push_contains, key]

/-- The step of (7): a forced insert moves a held record at most one place forward, and keeps it if it has
a record ahead of it. -/
theorem forced_step (S : Seen) (cap mid now : Nat) (pre post : List (Nat × Nat)) (x : Nat × Nat)
    (hS : S.order = pre ++ x :: post) (hpre : 1 ≤ pre.length) :
    ∃ pre' post', (insert S cap mid now true).1.order = pre' ++ x :: post' ∧ pre.length ≤ pre'.length + 1 := by
  by_cases h : cap ≤ S.order.length
  · rw [forced_pop_when_full S cap mid now h, hS]
    cases pre with
    | nil => simp at hpre
    | cons p ps => exact ⟨ps, post ++ [(mid, now)], by simp, by simp⟩
  · have := (forced_pop_only_when_full S cap mid now (by omega)).1
    exact ⟨pre, post ++ [(mid, now)], by rw [this, hS]; simp, Nat.le_succ _⟩

/-- (7) A record with `pre` records ahead of it is still queued after `k <= pre.length` forced inserts of any
ids at any instants, and it has lost at most `k` records ahead of it. -/
theorem survives_forced (cap : Nat) : ∀ (ids : List (Nat × Nat)) (S : Seen) (pre post : List (Nat × Nat))
    (x : Nat × Nat), S.order = pre ++ x :: post → ids.length ≤ pre.length →
    ∃ pre' post', (forcedAll S cap ids).order = pre' ++ x :: post' ∧ pre.length ≤ pre'.length + ids.length := by
  intro ids
  induction ids with
  | nil => intro S pre post x hS _; exact ⟨pre, post, by simpa [forcedAll] using hS, by simp⟩
  | cons h rest ih =>
    intro S pre post x hS hk
    obtain ⟨i, t⟩ := h
    simp only [List.length_cons] at hk
    obtain ⟨pre', post', h1, h2⟩ := forced_step S cap i t pre post x hS (by omega)
    obtain ⟨pre'', post'', h3, h4⟩ := ih _ pre' post' x h1 (by omega)
    exact ⟨pre'', post'', by simpa [forcedAll] using h3, by simp only [List.length_cons]; omega⟩

/-- (7) The record `(m, t)` pushed after `pre` survives `k <= pre.length` forced inserts. -/
theorem survives_after_push (cap : Nat) (ids : List (Nat × Nat)) (S : Seen) (pre : List (Nat × Nat))
    (m t : Nat) (hS : S.order = pre ++ [(m, t)]) (hk : ids.length ≤ pre.length) :
    (m, t) ∈ (forcedAll S cap ids).order := by
  obtain ⟨pre', post', h, _⟩ := survives_forced cap ids S pre [] (m, t) hS hk
  rw [h]; simp

/-- The record-count statement: an id seen before an insert of another id and not seen after was the head
record of a full set (a forced insert pops it; nothing else drops an id early). -/
theorem early_drop (S : Seen) (cap mid mid' now ttl : Nat) (force : Bool) (hne : mid ≠ mid')
    (hc : contains S ttl mid now = true)
    (hn : contains (insert S cap mid' now force).1 ttl mid now = false) :
    cap ≤ S.order.length ∧ ∃ t r, S.order = (mid, t) :: r := by
  unfold insert at hn
  by_cases hf : cap ≤ S.order.length
  · simp only [hf, ↓reduceIte] at hn
    cases force
    · simp [hc] at hn
    · simp only [↓reduceIte, push_contains_ne _ _ _ _ _ _ hne] at hn
      refine ⟨hf, ?_⟩
      cases hS : S.order with
      | nil => simp [popFront, hS, hc] at hn
      | cons e r =>
        obtain ⟨m, t⟩ := e
        by_cases hm : mid = m
        · exact ⟨t, r, by rw [hm]⟩
        · rw [popFront_contains_other S ttl m t mid now r hS hm, hc] at hn
          simp at hn
  · simp only [hf, ↓reduceIte, push_contains_ne _ _ _ _ _ _ hne, hc] at hn
    simp at hn

/-- (8) The hazard behind the Rust fix: two records of one id at one instant. Popping the first removes the
map entry while the second record is still queued, so the id reads as unseen at every instant. -/
theorem duplicate_record (S : Seen) (ttl mid now : Nat) (rest : List (Nat × Nat))
    (hS : S.order = (mid, now) :: (mid, now) :: rest) (hm : S.map mid = some now) (t : Nat) :
    contains (popFront S) ttl mid t = false ∧ (mid, now) ∈ (popFront S).order := by
  refine ⟨?_, by simp [hS]⟩
  unfold popFront; rw [hS]; simp [contains, hm]

/-! ### The home slot and the walk -/

/-- `IdKey::hash` reduced to a slot: a keyed hash of the id (`hash` is abstract, `key` is the node's secret). The walk
below holds for every `hash`, so a weak key costs time and never correctness. -/
def home (hash : Nat → Nat → Nat) (key slots id : Nat) : Nat := hash key id % slots

/-- The walk: from the home `h`, `d` slots already walked and at most `n` more, the offset of the first free slot, or
`none` when all `n` are taken. `occ` says which slots are taken. -/
def probe (occ : Nat → Bool) (slots h : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, d => if occ ((h + d) % slots) then probe occ slots h n (d + 1) else some d

/-- A walk of `n` slots ends within them. -/
theorem probe_range (occ : Nat → Bool) (slots h : Nat) : ∀ (n d e : Nat),
    probe occ slots h n d = some e → d ≤ e ∧ e < d + n := by
  intro n
  induction n with
  | zero => intro d e hp; simp [probe] at hp
  | succ n ih =>
    intro d e hp
    cases hb : occ ((h + d) % slots) with
    | true =>
      have hp' : probe occ slots h n (d + 1) = some e := by simpa [probe, hb] using hp
      have := ih (d + 1) e hp'
      omega
    | false =>
      have : d = e := by simpa [probe, hb] using hp
      omega

/-- The slot a walk ends at is free. -/
theorem probe_free (occ : Nat → Bool) (slots h : Nat) : ∀ (n d e : Nat),
    probe occ slots h n d = some e → occ ((h + e) % slots) = false := by
  intro n
  induction n with
  | zero => intro d e hp; simp [probe] at hp
  | succ n ih =>
    intro d e hp
    cases hb : occ ((h + d) % slots) with
    | true =>
      have hp' : probe occ slots h n (d + 1) = some e := by simpa [probe, hb] using hp
      exact ih (d + 1) e hp'
    | false =>
      have : d = e := by simpa [probe, hb] using hp
      subst this
      exact hb

/-- The walk ends at the first free slot: every slot from `d` up to the one it ends at is taken, and that one is
free. -/
theorem probe_first_free (occ : Nat → Bool) (slots h : Nat) : ∀ (n d e : Nat),
    probe occ slots h n d = some e →
      (∀ i, d ≤ i → i < e → occ ((h + i) % slots) = true) ∧ occ ((h + e) % slots) = false := by
  intro n
  induction n with
  | zero => intro d e hp; simp [probe] at hp
  | succ n ih =>
    intro d e hp
    cases hb : occ ((h + d) % slots) with
    | true =>
      have hp' : probe occ slots h n (d + 1) = some e := by simpa [probe, hb] using hp
      obtain ⟨H1, H2⟩ := ih (d + 1) e hp'
      refine ⟨fun i hi1 hi2 => ?_, H2⟩
      by_cases hid : i = d
      · subst hid; exact hb
      · exact H1 i (by omega) hi2
    | false =>
      have : d = e := by simpa [probe, hb] using hp
      subst this
      exact ⟨fun i hi1 hi2 => absurd hi2 (by omega), hb⟩

/-- Nothing is refused for a long walk: if any of the `n` slots a walk may read is free, it ends at one. With
`n = slots` and a table at most half full there is always one. -/
theorem probe_some_of_free (occ : Nat → Bool) (slots h : Nat) : ∀ (n d : Nat),
    (∃ i, i < n ∧ occ ((h + d + i) % slots) = false) → ∃ e, probe occ slots h n d = some e := by
  intro n
  induction n with
  | zero => intro d H; obtain ⟨i, hi, _⟩ := H; omega
  | succ n ih =>
    intro d H
    obtain ⟨i, hi, hf⟩ := H
    cases hb : occ ((h + d) % slots) with
    | true =>
      have hi0 : i ≠ 0 := by
        intro h0; subst h0; simp [hb] at hf
      obtain ⟨e, he⟩ := ih (d + 1) ⟨i - 1, by omega, by
        have : h + (d + 1) + (i - 1) = h + d + i := by omega
        rw [this]; exact hf⟩
      exact ⟨e, by simp [probe, hb, he]⟩
    | false => exact ⟨d, by simp [probe, hb]⟩

end Pinc.BroadcastTable
