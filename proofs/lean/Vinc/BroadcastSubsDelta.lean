import Vinc.Axioms
import Vinc.BroadcastSubs

/-!
# The subscriber list sent as changes: a change applied gives the new list

The unbounded counterpart of `delta` and `apply` in `crates/vinc-broadcast/src/subs.rs`, which
`proofs/tla/BroadcastSubsDelta.tla` takes as given (`Apply(P, a, r)`).

The story. A hub keeps a subscriber list: ids in increasing order, at most `max` of them. When the list changes from
`old` to `new`, the hub sends the change instead of the whole list: `delta old new` is the ids only `new` has (added)
and the ids only `old` has (removed). A member that holds `old` applies it with `apply`: it drops the removed ids,
inserts the added ones in order, and keeps the first `max`. What must hold: the member ends with exactly `new`
(`apply_delta`). Lists here are of numbers standing for node ids; the code orders ids the same way, byte by byte.

Versions. Every list has a version `(e, s)`: the hub's incarnation and the number of the change. A change frame names
the version it makes, `(e, s + 1)`, and a member takes it (`recvDelta`, the DELTA arm of `on_subs`) only when it holds
`(e, s)`, the version just before. What must hold: on that base the member ends with the hub's list at the new version
and holds the new version (`recv_on_base`); on any other base it applies nothing, holds no version (it waits for a
whole list) and asks for one if it held a version (`recv_off_base`); a whole list at version `v` replaces the
member's list with the hub's list at `v` and makes it hold `v`, waiting or not (`recv_full`).

Two more arms. A change at or below the version held, of the same incarnation, is a late copy: it is ignored, and the
member keeps its list and version and asks for nothing (`recv_old`). A member whose limit is under its hub's holds a
cut list (`cut`, `peers_cut` in the code): it is cut by a whole list longer than its limit, or by an applied change
that had to truncate. On a cut list a change that removes an id the member holds is not applied: the id past the cut
that would take its place is not in the change, so the member takes the off-base path and asks for the whole list
(`recv_cut`). A removal of an id the member does not hold changes nothing and is applied.

The member's primary. The source of a member's list is the hub it came from, and only that hub's changes apply
(`from`, in the TLA+ model). In the code a change from the member's primary hub, when the list came from another hub,
makes the primary the source: the member drops its version and asks it for the whole list. That rule is about which
hub a frame came from, not about a list, so it is not stated here; the model has no primary (a change from another hub
is ignored for good there).

Pieces. A whole list travels as ordered pieces of a fixed number of ids, all at one version, each naming its rank
`first` and the `total` of the list. A member gathers them per sending hub (`Part`, `gather` in the code) and never
acts on a partial list (`recvPiece`): a piece that is the whole list is taken now; the first of more starts a
gathering; a later piece joins only the unbroken gathering of the same version and total that has counted exactly
`first` ids; anything else breaks the gathering, changes the list not at all, drops the version held when the sender is
the list's hub (`own`) and asks the hub once per broken gathering. What must hold: any split of a list into non-empty
pieces, fed in order, leaves the member holding the list cut at its limit at that version (`recv_pieces`); a piece that
does not complete the list changes nothing the member holds (`recv_piece_partial`); a piece that does not follow the
gathering takes nothing and asks once (`recv_piece_gap`).

One limit in the model. `apply_delta` needs `new.length ≤ max` for the member's own limit; with the member's limit
under its hub's the new list may be longer than `max`, and `recv_cut` is what keeps such a member right.
-/

namespace Vinc.BroadcastSubsDelta

open Vinc.BroadcastSubs (insSorted mem_insSorted insSorted_sorted)

/-- `delta` in subs.rs: the ids of `new` not in `old` (added), and the ids of `old` not in `new` (removed). The code
finds an id with a binary search of the sorted list; `contains` is the same answer. -/
def delta (old new : List Nat) : List Nat × List Nat :=
  -- added: in new and not in old; removed: in old and not in new
  (new.filter (fun x => !old.contains x), old.filter (fun x => !new.contains x))

/-- The change applied before the cut: drop the removed ids, insert each added id where it belongs (nothing if it is
there). -/
def applyAll (l add rem : List Nat) : List Nat :=
  -- keep what is not removed, insert the added in order
  add.foldl (fun acc n => insSorted n acc) (l.filter (fun x => !rem.contains x))

/-- `apply` in subs.rs: [`applyAll`] cut at the first `max` ids. -/
def apply (l add rem : List Nat) (max : Nat) : List Nat :=
  (applyAll l add rem).take max

/-- Inserting a list of ids one by one into a sorted list keeps it sorted, and it then holds exactly what it held and
the ids inserted. -/
theorem fold_ins (add : List Nat) : ∀ acc : List Nat, acc.Pairwise (· < ·) →
    (add.foldl (fun acc n => insSorted n acc) acc).Pairwise (· < ·) ∧
    ∀ x, x ∈ add.foldl (fun acc n => insSorted n acc) acc ↔ x ∈ acc ∨ x ∈ add := by
  induction add with
  | nil => intro acc h; simp [h]
  | cons a t ih =>
    intro acc h
    -- one insertion, then the rest
    obtain ⟨hs, hm⟩ := ih (insSorted a acc) (insSorted_sorted a acc h)
    refine ⟨by simpa [List.foldl_cons] using hs, fun x => ?_⟩
    simp only [List.foldl_cons, hm, mem_insSorted, List.mem_cons]
    constructor
    · rintro ((h1 | h1) | h1) <;> simp [h1]
    · rintro (h1 | h1 | h1) <;> simp [h1]

/-- Two lists in strictly increasing order that hold the same ids are the same list. -/
theorem eq_of_sorted_mem : ∀ l1 l2 : List Nat, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ h
    cases l2 with
    | nil => rfl
    | cons b u => exact absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | cons a t ih =>
    intro l2 h1 h2 h
    cases l2 with
    | nil => exact absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
    | cons b u =>
      rw [List.pairwise_cons] at h1 h2
      -- the heads are equal: each is the least id of the same set
      have hab : a = b := by
        rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | ha
        · exact e
        rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e | hb
        · exact e.symm
        exact absurd (Nat.lt_trans (h2.1 a ha) (h1.1 b hb)) (Nat.lt_irrefl _)
      subst hab
      -- and the tails hold the same ids, since the head is in neither
      congr 1
      refine ih u h1.2 h2.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
      · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
        · exact absurd (h1.1 x hx) (by omega)
        · exact e
      · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
        · exact absurd (h2.1 x hx) (by omega)
        · exact e

/-- What `delta` sends: an id is added exactly when only the new list has it, removed exactly when only the old one
has it. -/
theorem delta_mem (old new : List Nat) (x : Nat) :
    (x ∈ (delta old new).1 ↔ x ∈ new ∧ x ∉ old) ∧ (x ∈ (delta old new).2 ↔ x ∈ old ∧ x ∉ new) := by
  simp [delta, List.mem_filter]

/-- The change applied to the old list, before any cut, gives exactly the new list: for lists in strictly increasing
order. -/
theorem applyAll_delta (old new : List Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·)) :
    applyAll old (delta old new).1 (delta old new).2 = new := by
  unfold applyAll
  -- what is left of the old list after the removals: sorted, and exactly the ids both lists have
  have hb : (old.filter (fun x => !(delta old new).2.contains x)).Pairwise (· < ·) := ho.filter _
  obtain ⟨hs, hm⟩ := fold_ins (delta old new).1 _ hb
  -- after the insertions the list is sorted and holds exactly the ids of the new list
  refine eq_of_sorted_mem _ _ hs hn (fun x => ?_)
  rw [hm]
  have d := delta_mem old new x
  simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, d.1, d.2]
  by_cases h1 : x ∈ old <;> by_cases h2 : x ∈ new <;> simp [h1, h2]

/-- A member holding the old list that applies the change ends with exactly the new list: for lists in strictly
increasing order, the new one at most `max` long. -/
theorem apply_delta (old new : List Nat) (max : Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·))
    (hl : new.length ≤ max) : apply old (delta old new).1 (delta old new).2 max = new := by
  unfold apply
  rw [applyAll_delta old new ho hn]
  -- the new list is within max, so the cut keeps it whole
  exact List.take_of_length_le hl

/-- What a member holds of a hub's list: the list, its version (`none` while it waits for a whole list), and whether the
list was cut to the member's limit. -/
structure Member where
  peers : List Nat
  ver : Option (Nat × Nat)
  cut : Bool

/-- Whether a change making version `(e, s + 1)` is not newer than the version the member holds: the same incarnation
and a number at or below the held one. -/
def isOld (m : Member) (e s : Nat) : Bool :=
  m.ver.any (fun v => decide (v.1 = e ∧ s + 1 ≤ v.2))

/-- The DELTA arm of `on_subs` for a frame from the member's own hub: the change making version `(e, s + 1)`. A change
not newer than the version held is ignored. On the base `(e, s)` it is applied (unless it removes an id the member
holds from a cut list) and the member holds the new version, cut if the change had to truncate; otherwise nothing is
applied, the member waits, and the second component says whether it sends an ASK (it does when it held a version, so it
asks once). -/
def recvDelta (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) : Member × Bool :=
  -- a late copy: nothing changes
  if isOld m e s then (m, false)
  -- on its base, and not a removal from a cut list: apply and take the new version
  else if decide (m.ver = some (e, s)) && !(m.cut && rem.any (fun r => m.peers.contains r)) then
    (⟨apply m.peers add rem max, some (e, s + 1), m.cut || decide (max < (applyAll m.peers add rem).length)⟩, false)
  -- on another base, or a removal from a cut list: keep the list, drop the version, ask if a version was held
  else (⟨m.peers, none, m.cut⟩, m.ver.isSome)

/-- On a matching base, a member holding the hub's list at `(e, s)` that takes the change from that list to the hub's
list at `(e, s + 1)` holds exactly the new list and the new version, uncut, and asks for nothing. -/
theorem recv_on_base (old new : List Nat) (max e s : Nat) (ho : old.Pairwise (· < ·)) (hn : new.Pairwise (· < ·))
    (hl : new.length ≤ max) :
    recvDelta ⟨old, some (e, s), false⟩ e s (delta old new).1 (delta old new).2 max =
      (⟨new, some (e, s + 1), false⟩, false) := by
  have hc : ¬ max < new.length := Nat.not_lt.2 hl
  simp [recvDelta, isOld, apply_delta old new max ho hn hl, applyAll_delta old new ho hn, hc]

/-- A change at or below the version held, of the same incarnation, changes nothing and asks for nothing. -/
theorem recv_old (m : Member) (e h s : Nat) (add rem : List Nat) (max : Nat) (hv : m.ver = some (e, h))
    (hs : s + 1 ≤ h) : recvDelta m e s add rem max = (m, false) := by
  simp [recvDelta, isOld, hv, hs]

/-- On a cut list, a change on the member's base that removes an id the member holds is not applied: the list is
unchanged, no version is held, and the member asks for the whole list. -/
theorem recv_cut (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) (hv : m.ver = some (e, s)) (hc : m.cut = true)
    (r : Nat) (hr : r ∈ rem) (hp : r ∈ m.peers) :
    recvDelta m e s add rem max = (⟨m.peers, none, true⟩, true) := by
  have hno : ¬ ∀ x : Nat, x ∈ rem → ¬ x ∈ m.peers := fun h => h r hr hp
  simp [recvDelta, isOld, hv, hc, hno]

/-- On any other base a change that is not old is never applied: the list is unchanged, no version is held, and the
member asks for the whole list exactly when it held a version. -/
theorem recv_off_base (m : Member) (e s : Nat) (add rem : List Nat) (max : Nat) (hold : isOld m e s = false)
    (h : m.ver ≠ some (e, s)) :
    (recvDelta m e s add rem max).1.peers = m.peers ∧ (recvDelta m e s add rem max).1.ver = none ∧
      (recvDelta m e s add rem max).2 = m.ver.isSome := by
  simp [recvDelta, hold, h]

/-- The FULL arm of `on_subs` for a member: the whole list at version `v` replaces the member's list and version,
whatever it held, so a waiting member holds a version again; it is cut when the list is longer than the member's limit. -/
def recvFull (_m : Member) (v : Nat × Nat) (list : List Nat) (max : Nat) : Member :=
  -- the list (cut at max, as the code takes at most max ids) and its version replace the member's
  ⟨list.take max, some v, decide (max < list.length)⟩

/-- A whole list at version `v`, the hub's list at `v` (at most `max` long), leaves the member holding exactly that
list and version `v`, uncut, whether it was waiting or held any other version: recovery from a gap. -/
theorem recv_full (m : Member) (v : Nat × Nat) (list : List Nat) (max : Nat) (hl : list.length ≤ max) :
    recvFull m v list max = ⟨list, some v, false⟩ := by
  simp [recvFull, List.take_of_length_le hl, Nat.not_lt.2 hl]

/-- What a member has gathered of one hub's pieces of a whole list (`Part` in subs.rs): the version and total of the
list, how many ids it has counted, the ids kept (at most the member's limit), and whether a piece broke it. -/
structure Part where
  ver : Nat × Nat
  total : Nat
  got : Nat
  ids : List Nat
  broken : Bool

/-- The SUBS piece arm of `on_subs` for a member (`gather` and the member's side of `take_subs`): the piece of ranks
`first` to `first + ids.length` of a list of `total` ids at version `v`, from a hub whose gathering is `p`; `own` says
the hub is the member's list's hub. The result is the member, the gathering, and whether the member asks the hub for
the whole list. A piece that is the whole list replaces the member's list and version and drops the gathering; the
first of more pieces starts the gathering and changes nothing else; a later piece joins the unbroken gathering of the
same version and total that counted exactly `first` ids, and at the last piece the member takes the gathered list
(cut at `max`, cut when `total` is above it) and version; any other piece breaks the gathering, drops the version the
member holds when the hub is its own, and asks once per broken gathering. -/
def recvPiece (own : Bool) (m : Member) (p : Option Part) (v : Nat × Nat) (first total : Nat) (ids : List Nat)
    (max : Nat) : Member × Option Part × Bool :=
  if first = 0 then
    -- the first piece: the whole list, or the start of a gathering
    if ids.length = total then (recvFull m v ids max, none, false)
    else (m, some ⟨v, total, ids.length, ids.take max, false⟩, false)
  else
    -- a piece that does not follow: nothing is taken, the version held is dropped when the hub is the list's hub
    let gapM : Member := if own then { m with ver := none } else m
    let brk : Part := ⟨v, total, 0, [], true⟩
    match p with
    | none => (gapM, some brk, true)
    | some q =>
      if q.ver = v ∧ q.total = total then
        if q.broken then (gapM, some q, false)
        else if q.got = first then
          -- it follows: keep the ids the limit has room for, count all of them
          if q.got + ids.length < total then
            (m, some ⟨v, total, q.got + ids.length, q.ids ++ ids.take (max - q.ids.length), false⟩, false)
          else (⟨q.ids ++ ids.take (max - q.ids.length), some v, decide (max < total)⟩, none, false)
        else (gapM, some brk, true)
      else (gapM, some brk, true)

/-- A piece of the right rank, version and total for an unbroken gathering is joined: the gathering counts it, or at
the last piece the member takes the gathered list at the piece's version. -/
theorem recvPiece_chain (own : Bool) (m : Member) (q : Part) (v : Nat × Nat) (first total max : Nat) (ids : List Nat)
    (hf : first ≠ 0) (hv : q.ver = v) (ht : q.total = total) (hb : q.broken = false) (hg : q.got = first) :
    recvPiece own m (some q) v first total ids max =
      if first + ids.length < total then
        (m, some ⟨v, total, first + ids.length, q.ids ++ ids.take (max - q.ids.length), false⟩, false)
      else (⟨q.ids ++ ids.take (max - q.ids.length), some v, decide (max < total)⟩, none, false) := by
  simp [recvPiece, hf, hv, ht, hb, hg]

/-- A piece that does not complete the list changes nothing the member holds: its list, version and cut flag stay,
it asks for nothing, and the gathering is kept. The piece is the first of more (rank 0, fewer ids than the total), or
it follows an unbroken gathering and leaves ids still due. -/
theorem recv_piece_partial (own : Bool) (m : Member) (p : Option Part) (v : Nat × Nat) (first total max : Nat)
    (ids : List Nat)
    (h : (first = 0 ∧ ids.length < total) ∨
      ∃ q, p = some q ∧ first ≠ 0 ∧ q.ver = v ∧ q.total = total ∧ q.broken = false ∧ q.got = first ∧
        first + ids.length < total) :
    (recvPiece own m p v first total ids max).1 = m ∧ (recvPiece own m p v first total ids max).2.2 = false ∧
      (recvPiece own m p v first total ids max).2.1.isSome = true := by
  rcases h with ⟨h0, hl⟩ | ⟨q, rfl, hf, hv, ht, hb, hg, hl⟩
  · have hne : ids.length ≠ total := Nat.ne_of_lt hl
    simp [recvPiece, h0, hne]
  · rw [recvPiece_chain own m q v first total max ids hf hv ht hb hg, if_pos hl]
    simp

/-- A later piece that does not follow takes nothing: the list and cut flag stay, the version is dropped when the hub
is the list's hub, the gathering is broken at the piece's version and total, and the member asks the hub. This holds
when the hub has no gathering, when it is of another version or total, and when it is unbroken but has not counted
`first` ids. When the gathering is already broken at that version and total, the member asks nothing more. -/
theorem recv_piece_gap (own : Bool) (m : Member) (p : Option Part) (v : Nat × Nat) (first total max : Nat)
    (ids : List Nat) (hf : first ≠ 0) :
    ((p = none ∨ ∃ q, p = some q ∧ (q.ver ≠ v ∨ q.total ≠ total ∨ (q.broken = false ∧ q.got ≠ first))) →
      recvPiece own m p v first total ids max =
        ((if own then { m with ver := none } else m), some ⟨v, total, 0, [], true⟩, true)) ∧
    ((∃ q, p = some q ∧ q.ver = v ∧ q.total = total ∧ q.broken = true) →
      recvPiece own m p v first total ids max = ((if own then { m with ver := none } else m), p, false)) := by
  constructor
  · rintro (rfl | ⟨q, rfl, h⟩)
    · simp [recvPiece, hf]
    · by_cases hv : q.ver = v
      · by_cases ht : q.total = total
        · rcases h with h | h | ⟨hb, hg⟩
          · exact absurd hv h
          · exact absurd ht h
          · simp [recvPiece, hf, hv, ht, hb, hg]
        · simp [recvPiece, hf, hv, ht]
      · simp [recvPiece, hf, hv]
  · rintro ⟨q, rfl, hv, ht, hb⟩
    simp [recvPiece, hf, hv, ht, hb]

/-- Feed the pieces `cs` of a list of `total` ids at version `v` in order to a member, from the rank `k`, through
`recvPiece`; the result is the member and its gathering. -/
def feed (own : Bool) (v : Nat × Nat) (total max : Nat) : Nat → Member → Option Part → List (List Nat) →
    Member × Option Part
  | _, m, p, [] => (m, p)
  | k, m, p, c :: cs =>
    let r := recvPiece own m p v k total c max
    feed own v total max (k + c.length) r.1 r.2.1 cs

/-- Keeping the first `max` ids of a gathering and then what room is left of a piece is cutting the joined list. -/
theorem take_gather (acc c : List Nat) (max : Nat) :
    acc.take max ++ c.take (max - (acc.take max).length) = (acc ++ c).take max := by
  rw [List.take_append, List.length_take]
  have h : max - min max acc.length = max - acc.length := by omega
  rw [h]

/-- Pieces that all hold ids and together hold none are no pieces. -/
theorem rest_empty : ∀ cs : List (List Nat), (∀ c ∈ cs, c ≠ []) → cs.flatten.length = 0 → cs = []
  | [], _, _ => rfl
  | d :: ds, hne, h => by
    have hd : d ≠ [] := hne d (List.mem_cons_self ..)
    have hpos : 0 < d.length := Nat.pos_of_ne_zero (fun h0 => hd (List.eq_nil_of_length_eq_zero h0))
    simp only [List.flatten_cons, List.length_append] at h
    omega

/-- Once a gathering of `acc` (not empty, not the whole list) is joined by the pieces `cs` in order, the member ends
with the list `acc ++ cs.flatten` cut at `max`, at version `v`, uncut when the list fits, and no gathering. -/
theorem feed_go (own : Bool) (v : Nat × Nat) (total max : Nat) :
    ∀ (cs : List (List Nat)) (m : Member) (acc : List Nat),
      (∀ c ∈ cs, c ≠ []) → cs ≠ [] → acc ≠ [] → (acc ++ cs.flatten).length = total →
      feed own v total max acc.length m (some ⟨v, total, acc.length, acc.take max, false⟩) cs =
        (⟨(acc ++ cs.flatten).take max, some v, decide (max < total)⟩, none) := by
  intro cs
  induction cs with
  | nil => intro m acc _ h; exact absurd rfl h
  | cons c cs ih =>
    intro m acc hne _ hacc htot
    have hc : c ≠ [] := hne c (List.mem_cons_self ..)
    have hf : acc.length ≠ 0 := fun h => hacc (List.eq_nil_of_length_eq_zero h)
    have hcpos : 0 < c.length := Nat.pos_of_ne_zero (fun h0 => hc (List.eq_nil_of_length_eq_zero h0))
    have step := recvPiece_chain own m ⟨v, total, acc.length, acc.take max, false⟩ v acc.length total max c hf
      rfl rfl rfl rfl
    by_cases hlt : acc.length + c.length < total
    · -- more pieces are due: this one joins, and the rest end the list
      simp only [feed, step, hlt, ↓reduceIte]
      have hcs : cs ≠ [] := by
        rintro rfl
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append] at htot
        omega
      have := ih m (acc ++ c) (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hcs (by simp [hacc])
        (by simp only [List.length_append, List.flatten_cons] at htot ⊢; omega)
      rw [take_gather acc c max, ← List.length_append, List.flatten_cons, ← List.append_assoc]
      first | exact this | simpa [List.flatten_cons, List.append_assoc] using this
    · -- this piece is the last: no piece follows
      simp only [feed, step, hlt, ↓reduceIte]
      rcases cs with _ | ⟨d, ds⟩
      · simp only [feed, List.flatten_cons, List.flatten_nil, List.append_nil]
        first | (rw [take_gather acc c max]; done) | (rw [take_gather acc c max]; rfl)
      · exfalso
        have hd : d ≠ [] := hne d (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hpos : 0 < d.length := Nat.pos_of_ne_zero (fun h0 => hd (List.eq_nil_of_length_eq_zero h0))
        simp only [List.flatten_cons, List.length_append] at htot
        omega

/-- Any split of a list `l` into non-empty pieces, fed in order from rank 0 to a member that holds nothing of the hub's
pieces, leaves the member holding the list cut at its limit `max`, at version `v`, cut exactly when `l` is longer than
`max`, with no gathering left: the member takes the list whole, as a one-piece FULL. -/
theorem recv_pieces (own : Bool) (m : Member) (v : Nat × Nat) (max : Nat) (l : List Nat) (pcs : List (List Nat))
    (hne : ∀ c ∈ pcs, c ≠ []) (hpcs : pcs ≠ []) (hl : pcs.flatten = l) :
    feed own v l.length max 0 m none pcs = (⟨l.take max, some v, decide (max < l.length)⟩, none) := by
  subst hl
  rcases pcs with _ | ⟨c, cs⟩
  · exact absurd rfl hpcs
  · have hc : c ≠ [] := hne c (List.mem_cons_self ..)
    have hrest : ∀ x ∈ cs, x ≠ [] := fun x hx => hne x (List.mem_cons_of_mem _ hx)
    by_cases h0 : c.length = (c :: cs).flatten.length
    · -- the first piece is the whole list
      have hcs : cs = [] := by
        apply rest_empty cs hrest
        simp only [List.flatten_cons, List.length_append] at h0
        omega
      subst hcs
      simp [feed, recvPiece, recvFull]
    · -- the first of more pieces: a gathering starts, and the rest join it
      have hcs : cs ≠ [] := by
        rintro rfl
        simp at h0
      have step : recvPiece own m none v 0 (c :: cs).flatten.length c max =
          (m, some ⟨v, (c :: cs).flatten.length, c.length, c.take max, false⟩, false) := by
        rw [recvPiece, if_pos rfl, if_neg h0]
      have := feed_go own v (c :: cs).flatten.length max cs m c hrest hcs hc (by simp)
      simp only [feed, step, Nat.zero_add]
      first | exact this | simpa [List.flatten_cons] using this

#audit_axioms Vinc.BroadcastSubsDelta.recv_old
#audit_axioms Vinc.BroadcastSubsDelta.recv_cut
#audit_axioms Vinc.BroadcastSubsDelta.applyAll_delta
#audit_axioms Vinc.BroadcastSubsDelta.recv_full
#audit_axioms Vinc.BroadcastSubsDelta.recv_on_base
#audit_axioms Vinc.BroadcastSubsDelta.recv_off_base
#audit_axioms Vinc.BroadcastSubsDelta.delta_mem
#audit_axioms Vinc.BroadcastSubsDelta.apply_delta
#audit_axioms Vinc.BroadcastSubsDelta.eq_of_sorted_mem
#audit_axioms Vinc.BroadcastSubsDelta.recv_pieces
#audit_axioms Vinc.BroadcastSubsDelta.recv_piece_partial
#audit_axioms Vinc.BroadcastSubsDelta.recv_piece_gap

end Vinc.BroadcastSubsDelta
