import Pinc.ReconcileCorrect
import Pinc.ReconcileWireMsg

/-!
# Reconcile refinement, part 2a: `procPart` split at the head

`tailPart` is `procPart` after its head (tag byte and bounds) is read: the ranks of the bounds and the arm of the part
kind, copied from ReconcileParts.lean. `procPart_eq` shows `procPart` is `readHead` then `tailPart`, so the arm lemmas
work on a decoded head (`readHead_putHead` of the wire proofs).
-/

namespace Pinc.Reconcile

/-- The part rules after the head: ranks of the bounds, then the arm of the kind. -/
def tailPart (o : Oracle) (S : List Item) (c : Core) (kind : Nat) (lo : Item) (hi : Option Item) (r : List Nat)
    (mark : Nat) : Except Err (Core × List Nat) := do
  let lim := c.lim
  let a := rankOf S lo
  let b := match hi with | none => c.n | some h => rankOf S h
  if b < a then throw (.malformed .bound)
  if kind = tFP then
    let (fpb, r) ← lr (readBytes fpLen r)
    if fromBE fpb != fpRange o S a b then
      let items := !c.init || c.exact
      let leaf := if c.init then aleaf else bleaf
      let ok ← if b - a ≤ leaf then leafOk lim S lo hi a b items else pure false
      if ok then
        let c := if c.init then { c with leafed := true } else c
        let out ← if items then itemsPart lim S c.out tFULL lo hi a b else idsPart o lim S c.out lo hi a b
        pure (({ c with out := out }).bump 1, r)
      else
        let (out, cnt) ← splitFit o lim S c.out lo hi a b mark 3
        pure (({ c with out := out }).bump cnt, r)
    else pure (c, r)
  else if kind = tIDS ∧ !c.init then
    let (cc, r) ← lr (count r)
    if cc > aleaf then throw (.malformed .count)
    let (ids, r) ← lr (readBytes (cc * idLen) r)
    let narrow ← if b - a > aleaf then pure true else do pure !(← leafOk lim S lo hi a b true)
    if narrow then
      let (out, cnt) ← splitFit o lim S c.out lo hi a b mark 3
      pure (({ c with out := out }).bump cnt, r)
    else
      let xs ← readRange lim S a (b - a)
      let idl := chunks idLen cc ids
      let (seen, out, extra) := xs.foldl (fun (st : List Nat × Out × Nat) x =>
        match rpos idl (idBytes o x) with
        | some k => (setBit st.1 k, st.2.1, st.2.2)
        | none => (st.1, st.2.1.stageItem x, st.2.2 + 1)) ([0, 0, 0, 0], c.out, 0)
      pure (({ c with out := replyPart out lo hi cc seen extra }).bump 1, r)
  else if kind = tFULL ∧ !c.init then
    let is ← lr (IS.read r)
    let cc := is.left
    if cc > aleaf then throw (.malformed .count)
    let narrow ← if b - a > aleaf then pure true else do pure !(← leafOk lim S lo hi a b true)
    if narrow then
      let r ← lr (drain lim.maxItem (is.left + 1) is)
      let (out, cnt) ← splitFit o lim S c.out lo hi a b mark 3
      pure (({ c with out := out }).bump cnt, r)
    else
      let ((seen, out, extra), r) ← merge lim S a b is (fun m (st : List Nat × Out × Nat) =>
        match m with
        | .both k => .ok (setBit st.1 k, st.2.1, st.2.2)
        | .theirs _ => .ok st
        | .mine x => .ok (st.1, st.2.1.stageItem x, st.2.2 + 1)) ([0, 0, 0, 0], c.out, 0)
      pure (({ c with out := replyPart out lo hi cc seen extra }).bump 1, r)
  else if (kind = tFULL ∨ kind = tCOLD) ∧ c.init then
    let is ← lr (IS.read r)
    let cap := lim.maxReport
    let mf ← c.msgFloor.disjoint lo hi
    let cf ← if kind = tCOLD then c.coldFloor.ascending lo hi else .ok c.coldFloor
    let ((here, there), r) ← merge lim S a b is (fun m (st : List Item × List Item) =>
      match m with
      | .both _ => .ok st
      | .theirs x => if !within x lo hi then .error (.malformed .item) else do pure (← pushItem st.1 (dataLen st.2) cap x, st.2)
      | .mine x => do pure (st.1, ← pushItem st.2 (dataLen st.1) cap x)) (c.here, c.there)
    let c := { c with here := here, there := there, msgFloor := mf, coldFloor := cf }
    let c := if kind = tCOLD then { c with ans := { c.ans with cold := true, coldEnd := !hi.isSome } } else c
    pure (c, r)
  else if kind = tREPLY ∧ c.init then
    let (cc, r) ← lr (count r)
    if cc != b - a ∨ cc > aleaf then throw (.malformed .count)
    let mf ← c.msgFloor.disjoint lo hi
    let (seen, r) ← lr (readBytes ((cc + 7) / 8) r)
    if (cc % 8 != 0) && (match seen.getLast? with | some byte => byte >>> (cc % 8) != 0 | none => false) then
      throw (.malformed .count)
    let there ← unseen lim S a seen cc c.here cc c.there
    let is ← lr (IS.read r)
    let (here, r) ← pushExtras lim S lo hi b there (is.left + 1) is none c.here
    pure ({ c with here := here, there := there, msgFloor := mf }, r)
  else if kind = tCHECK ∧ !c.init then
    let (fpb, r) ← lr (readBytes fpLen r)
    if lo != [] ∨ hi.isSome then throw (.malformed .bound)
    if fromBE fpb != fpRange o S 0 c.n then
      pure (({ c with out := c.out.head tMISS [] none }).bump 1, r)
    else pure (c, r)
  else if kind = tMISS ∧ c.init then
    if lo != [] ∨ hi.isSome then throw (.malformed .bound)
    pure ({ c with ans := { c.ans with miss := true } }, r)
  else throw (.malformed .tag)


theorem procPart_eq (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (mark : Nat) :
    procPart o S c r mark =
      (match readHead c.blast r c.lim.maxItem with
        | .error e => .error (.malformed e)
        | .ok ((kind, lo, hi), l, r1) => tailPart o S { c with blast := l } kind lo hi r1 mark) := by
  unfold procPart readHead
  cases h1 : readU8 r with
  | error e => simp only [lr, h1, Except.mapError, bind, Except.bind]
  | ok p =>
    obtain ⟨t, r⟩ := p
    simp only [lr, h1, Except.mapError, bind, Except.bind]
    cases h2 : readBound c.blast r c.lim.maxItem with
    | error e => simp only [h2, Except.mapError, bind, Except.bind]
    | ok q =>
      obtain ⟨lo, r2⟩ := q
      simp only [h2, Except.mapError, bind, Except.bind]
      by_cases ht : t ≥ 128
      · simp only [ht, decide_true, ite_true, pure, Except.pure, bind, Except.bind]; rfl
      · have ht' : decide (t ≥ 128) = false := by simpa using ht
        cases h3 : readBound lo r2 c.lim.maxItem with
        | error e =>
          simp only [ht', Bool.false_eq_true, ite_false, h3, Except.mapError, bind, Except.bind, pure, Except.pure]
          rw [if_neg ht]
        | ok q2 =>
          obtain ⟨hi, r3⟩ := q2
          simp only [ht', Bool.false_eq_true, ite_false, h3, Except.mapError, bind, Except.bind, pure, Except.pure]
          rw [if_neg ht, Nat.mod_eq_of_lt (by omega : t < 128)]; rfl

end Pinc.Reconcile
