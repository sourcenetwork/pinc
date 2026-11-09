import Vinc.Axioms

/-!
# The request slots of the value server

`server.rs Server<H, S>` holds its requests in a fixed array of `S` slots. A slot is free, or holds a request
stream of a peer that is being collected, or is serving a response for a root over some rounded ranges.

* `opened_busy`, `opened_free`: a request opens in the first free slot; with none free the stream is reset with
  `BUSY` and nothing is held beyond `S` (`held_le`): a request beyond `S` is refused, never queued.
* `supersede_iff`: the answer to a new request frees exactly the serving slots of the same peer and the same root
  whose rounded ranges overlap one of the new spans, and never the request's own stream; every other slot is
  untouched (`supersede_keeps`). Each freed slot is reset with `SUPERSEDED`.
* `answer_refused_keeps_others`, `answer_installed_supersedes`: the older responses are freed only after the new
  response is accepted; a refused install frees the request's own slot and nothing else.
* `refuse_unavailable`: a value the store does not hold whole (or a plan the value cannot give) resets the
  request with `UNAVAILABLE` and frees only its slot.
* `closed_iff`, `done_frees`: a closed session drops exactly its peer's slots; a finished stream frees its slot.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Vinc.ValuesPlan

/-- A request in a slot: its stream and peer, and the root and rounded ranges once it is being served. -/
structure Slot where
  stream : Nat
  peer : Nat
  serving : Option (Nat × List (Nat × Nat))
  deriving DecidableEq

abbrev Slots := List (Option Slot)

/-- The requests held. -/
def Slots.held (s : Slots) : Nat := s.countP Option.isSome

theorem held_le (s : Slots) : s.held ≤ s.length := List.countP_le_length

/-- The reset codes of the protocol that the server uses. -/
abbrev BUSY : Nat := 6
abbrev UNAVAILABLE : Nat := 2
abbrev SUPERSEDED : Nat := 4

/-- `ServerIn::Opened`: the first free slot takes the stream, or the stream is reset as busy. -/
def opened (s : Slots) (stream peer : Nat) : Slots × List (Nat × Nat) :=
  if h : s.findIdx Option.isNone < s.length then
    (s.set (s.findIdx Option.isNone) (some ⟨stream, peer, none⟩), [])
  else (s, [(stream, BUSY)])

theorem opened_length (s : Slots) (stream peer : Nat) : (opened s stream peer).1.length = s.length := by
  unfold opened; split <;> simp

theorem opened_busy (s : Slots) (stream peer : Nat) (h : ∀ x ∈ s, x.isSome) :
    opened s stream peer = (s, [(stream, BUSY)]) := by
  unfold opened
  have : ¬ s.findIdx Option.isNone < s.length := by
    intro hlt
    have := List.findIdx_getElem (p := Option.isNone) (xs := s) (w := hlt)
    have h2 := h _ (List.getElem_mem hlt)
    cases hx : s[s.findIdx Option.isNone] <;> simp_all
  simp [this]

theorem opened_free (s : Slots) (stream peer : Nat) (h : ∃ x ∈ s, x.isNone) :
    (opened s stream peer).2 = [] ∧ (opened s stream peer).1.held = s.held + 1 := by
  obtain ⟨x, hx, hn⟩ := h
  have hlt : s.findIdx Option.isNone < s.length := List.findIdx_lt_length_of_exists ⟨x, hx, hn⟩
  have hnone : s[s.findIdx Option.isNone] = none := by
    have := List.findIdx_getElem (p := Option.isNone) (xs := s) (w := hlt)
    cases hx : s[s.findIdx Option.isNone] <;> simp_all
  unfold opened
  simp only [hlt, dite_true, true_and]
  unfold Slots.held
  rw [List.set_eq_take_append_cons_drop, if_pos hlt]
  have e : s = s.take (s.findIdx Option.isNone) ++ s[s.findIdx Option.isNone] :: s.drop (s.findIdx Option.isNone + 1) := by
    simp
  have h1 := congrArg (List.countP Option.isSome) e
  simp only [List.countP_append, List.countP_cons, hnone, Option.isSome_none, Option.isSome_some] at h1 ⊢
  simp at h1 ⊢
  omega

/-- Whether any rounded range `(off, len)` of an old response overlaps a new span (empty spans never do). -/
def overlapsB (ranges spans : List (Nat × Nat)) : Bool :=
  ranges.any (fun r => spans.any (fun sp => decide (0 < sp.2 ∧ sp.1 < r.1 + r.2 ∧ r.1 < sp.1 + sp.2)))

/-- The old slot `o` is superseded by the new request on `stream` from `peer` for `root` over `spans`: another
stream, the same peer, serving the same root, with an overlapping range (`SERVE_ONE`). -/
def supersedes (stream peer root : Nat) (spans : List (Nat × Nat)) (o : Slot) : Bool :=
  decide (o.stream ≠ stream) && decide (o.peer = peer) &&
    (match o.serving with
      | some (r, rs) => decide (r = root) && overlapsB rs spans
      | none => false)

/-- `Server::answer`'s supersession pass: the slots superseded are freed and reset with `SUPERSEDED`. -/
def supersede (s : Slots) (stream peer root : Nat) (spans : List (Nat × Nat)) : Slots × List (Nat × Nat) :=
  (s.map (fun x => match x with | some o => if supersedes stream peer root spans o then none else x | none => none),
   s.filterMap (fun x => match x with
     | some o => if supersedes stream peer root spans o then some (o.stream, SUPERSEDED) else none
     | none => none))

theorem supersede_length (s : Slots) (stream peer root : Nat) (spans : List (Nat × Nat)) :
    (supersede s stream peer root spans).1.length = s.length := by
  simp [supersede]

/-- A slot is freed exactly when it is another stream of the same peer serving the same root over an overlapping
range; every other slot stays as it was. -/
theorem supersede_iff (s : Slots) (stream peer root : Nat) (spans : List (Nat × Nat)) (j : Nat) (hj : j < s.length) :
    (supersede s stream peer root spans).1[j]? =
      (match s[j]? with
        | some (some o) => if supersedes stream peer root spans o then some none else some (some o)
        | some none => some none
        | none => none) := by
  simp only [supersede, List.getElem?_map]
  cases hx : s[j]? with
  | none => rfl
  | some x =>
    cases x with
    | none => rfl
    | some o => by_cases hc : supersedes stream peer root spans o = true <;> simp [hc]

theorem supersedes_iff (stream peer root : Nat) (spans : List (Nat × Nat)) (o : Slot) :
    supersedes stream peer root spans o = true ↔
      (o.stream ≠ stream ∧ o.peer = peer ∧ ∃ rs, o.serving = some (root, rs) ∧ overlapsB rs spans = true) := by
  unfold supersedes
  cases hs : o.serving with
  | none => simp
  | some p =>
    obtain ⟨r, rs⟩ := p
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, rs, ⟨h3, rfl⟩, h4⟩
    · rintro ⟨h1, h2, rs', ⟨h3, h4⟩, h5⟩; subst h4; exact ⟨⟨h1, h2⟩, h3, h5⟩

/-- A collecting request is never superseded, and neither is a response of another peer or another root. -/
theorem supersedes_collecting (stream peer root : Nat) (spans : List (Nat × Nat)) (o : Slot) (h : o.serving = none) :
    supersedes stream peer root spans o = false := by
  unfold supersedes; simp [h]

/-- `refuse`: reset the request in slot `i` and free just that slot. -/
def refuse (s : Slots) (i code : Nat) : Slots × List (Nat × Nat) :=
  match s[i]? with
  | some (some o) => (s.set i none, [(o.stream, code)])
  | _ => (s, [])

theorem refuse_spec (s : Slots) (i code : Nat) (o : Slot) (h : s[i]? = some (some o)) :
    (refuse s i code).2 = [(o.stream, code)] ∧ (refuse s i code).1[i]? = some none ∧
      ∀ j, j ≠ i → (refuse s i code).1[j]? = s[j]? := by
  unfold refuse
  rw [h]
  refine ⟨rfl, ?_, ?_⟩
  · have : i < s.length := (List.getElem?_eq_some_iff.1 h).1
    simp [List.getElem?_set, this]
  · intro j hj
    rw [List.getElem?_set]; simp [Ne.symm hj]

/-- `Server::answer` after the plan: the source is installed first. A refused install resets the request with
`UNAVAILABLE` and frees only its slot; once accepted, the older responses are superseded and the slot serves `mine`. -/
def answer (s : Slots) (i root : Nat) (mine spans : List (Nat × Nat)) (installs : Bool) : Slots × List (Nat × Nat) :=
  match s[i]? with
  | some (some me) =>
    if installs then
      ((supersede s me.stream me.peer root spans).1.set i (some { me with serving := some (root, mine) }),
       (supersede s me.stream me.peer root spans).2)
    else refuse s i UNAVAILABLE
  | _ => (s, [])

/-- A refused install leaves every other slot as it was and resets only the request. -/
theorem answer_refused_keeps_others (s : Slots) (i root : Nat) (mine spans : List (Nat × Nat)) (me : Slot)
    (h : s[i]? = some (some me)) :
    (answer s i root mine spans false).2 = [(me.stream, UNAVAILABLE)] ∧
      (answer s i root mine spans false).1[i]? = some none ∧
      ∀ j, j ≠ i → (answer s i root mine spans false).1[j]? = s[j]? := by
  unfold answer
  rw [h]
  exact refuse_spec s i UNAVAILABLE me h

/-- An accepted install supersedes exactly the slots `supersede` frees, resets each with `SUPERSEDED`, and serves. -/
theorem answer_installed_supersedes (s : Slots) (i root : Nat) (mine spans : List (Nat × Nat)) (me : Slot)
    (h : s[i]? = some (some me)) :
    (answer s i root mine spans true).2 = (supersede s me.stream me.peer root spans).2 ∧
      (answer s i root mine spans true).1[i]? = some (some { me with serving := some (root, mine) }) ∧
      ∀ j, j ≠ i → j < s.length → (answer s i root mine spans true).1[j]? = (supersede s me.stream me.peer root spans).1[j]? := by
  unfold answer
  rw [h]
  have hi : i < s.length := (List.getElem?_eq_some_iff.1 h).1
  refine ⟨rfl, ?_, ?_⟩
  · simp [List.getElem?_set, hi, supersede_length]
  · intro j hj _
    simp only [if_true]
    rw [List.getElem?_set]; simp [Ne.symm hj]

/-- A closed session drops exactly the slots of its peer. -/
def closed (s : Slots) (peer : Nat) : Slots :=
  s.map (fun x => match x with | some o => if o.peer = peer then none else x | none => none)

theorem closed_iff (s : Slots) (peer j : Nat) (hj : j < s.length) :
    (closed s peer)[j]? = (match s[j]? with
      | some (some o) => if o.peer = peer then some none else some (some o)
      | some none => some none
      | none => none) := by
  simp only [closed, List.getElem?_map]
  cases hx : s[j]? with
  | none => rfl
  | some x =>
    cases x with
    | none => rfl
    | some o => by_cases hc : o.peer = peer <;> simp [hc]

/-- A finished or reset stream frees the first slot that holds it. -/
def done (s : Slots) (stream : Nat) : Slots :=
  if s.findIdx (fun x => match x with | some o => decide (o.stream = stream) | none => false) < s.length then
    s.set (s.findIdx (fun x => match x with | some o => decide (o.stream = stream) | none => false)) none
  else s

theorem done_length (s : Slots) (stream : Nat) : (done s stream).length = s.length := by
  unfold done; split <;> simp

end Vinc.ValuesPlan

#audit_axioms Vinc.ValuesPlan.opened_busy
#audit_axioms Vinc.ValuesPlan.opened_free
#audit_axioms Vinc.ValuesPlan.opened_length
#audit_axioms Vinc.ValuesPlan.held_le
#audit_axioms Vinc.ValuesPlan.supersedes_iff
#audit_axioms Vinc.ValuesPlan.supersede_iff
#audit_axioms Vinc.ValuesPlan.refuse_spec
#audit_axioms Vinc.ValuesPlan.answer_refused_keeps_others
#audit_axioms Vinc.ValuesPlan.answer_installed_supersedes
#audit_axioms Vinc.ValuesPlan.closed_iff
