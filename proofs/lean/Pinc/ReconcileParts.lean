import Pinc.ReconcileMachine

/-!
# Reconcile parts: the part rules of `Core::answer`, the reply with rollback, the frames

`procPart` is one iteration of the loop of `answer`: it reads a part head, ranks the bounds in the index and runs the
arm of the part kind. `answerLoop` adds the overflow rollback, `turn` the frame push and the resumption of held frames.
-/

namespace Pinc.Reconcile

/-- A wire error as a step error. -/
def lr {α : Type} (x : Except Reason α) : Except Err α := x.mapError Err.malformed

/-- `Items`: the items of a list, read one at a time. -/
structure IS where
  left : Nat
  r : List Nat

/-- `Items::read`. -/
def IS.read (r : List Nat) : Except Reason IS :=
  match count r with
  | .error e => .error e
  | .ok (n, r) => .ok ⟨n, r⟩

/-- `Items::next_item`. -/
def IS.next (mx : Nat) (s : IS) : Except Reason (Option (Item × IS)) :=
  if s.left = 0 then .ok none
  else
    match count s.r with
    | .error e => .error e
    | .ok (n, r) =>
      if n > mx then .error .item
      else
        match readBytes n r with
        | .error e => .error e
        | .ok (x, r) => .ok (some (x, ⟨s.left - 1, r⟩))

/-- How one item of a merge relates to the two sides. -/
inductive Cmp where
  | both (k : Nat)
  | theirs (x : Item)
  | mine (x : Item)

/-- The loop of `merge` over our items `j..b` and the peer's ascending list, calling `f` for each item of the union. -/
def mergeGo {α : Type} (lim : Limits) (S : List Item) (b : Nat) (f : Cmp → α → Except Err α) :
    Nat → Nat → Nat → Option Item → Option Item → IS → α → Except Err (α × List Nat)
  | 0, _, _, _, _, is, acc => .ok (acc, is.r)
  | fuel + 1, j, k, prev, nxt, is, acc => do
    let m ← if j < b then (readItem lim S j).map some else pure none
    match m, nxt with
    | none, none => pure (acc, is.r)
    | some x, none => mergeGo lim S b f fuel (j + 1) k prev none is (← f (.mine x) acc)
    | m, some t =>
      let adv (j : Nat) (acc : α) : Except Err (α × List Nat) := do
        if let some p := prev then
          if !lexLt p t then throw (.malformed .item)
        match ← lr (is.next lim.maxItem) with
        | none => mergeGo lim S b f fuel j (k + 1) (some t) none is acc
        | some (t', is') => mergeGo lim S b f fuel j (k + 1) (some t) (some t') is' acc
      match m with
      | some x =>
        if lexLt x t then mergeGo lim S b f fuel (j + 1) k prev nxt is (← f (.mine x) acc)
        else if x = t then adv (j + 1) (← f (.both k) acc)
        else adv j (← f (.theirs t) acc)
      | none => adv j (← f (.theirs t) acc)

/-- `merge` of our items `a..b` with the peer's list `is`; returns the accumulator and the reader past the list. -/
def merge {α : Type} (lim : Limits) (S : List Item) (a b : Nat) (is : IS) (f : Cmp → α → Except Err α) (acc : α) :
    Except Err (α × List Nat) := do
  let first ← lr (is.next lim.maxItem)
  match first with
  | none => mergeGo lim S b f ((b - a) + is.left + 2) a 0 none none is acc
  | some (t, is') => mergeGo lim S b f ((b - a) + is.left + 2) a 0 none (some t) is' acc

/-- The reader past the items still unread of `is` (the drain of `while theirs.next_item()?.is_some() {}`). -/
def drain (mx : Nat) : Nat → IS → Except Reason (List Nat)
  | 0, s => .ok s.r
  | fuel + 1, s =>
    match s.next mx with
    | .error e => .error e
    | .ok none => .ok s.r
    | .ok (some (_, s')) => drain mx fuel s'

/-- The bitmap with bit `k` set. -/
def setBit (seen : List Nat) (k : Nat) : List Nat :=
  seen.mapIdx fun i x => if i = k / 8 then x ||| (1 <<< (k % 8)) else x

/-- `reply`: `venc(c)`, the bitmap of the asker's items we have, then the staged extra items. -/
def replyPart (out : Out) (lo : Item) (hi : Option Item) (c : Nat) (seen : List Nat) (extra : Nat) : Out :=
  let out := out.head tREPLY lo hi
  { out with body := out.body ++ venc c ++ seen.take ((c + 7) / 8) ++ venc extra ++ out.stage, stage := [] }

/-- The unseen positions of the reply bitmap: our item `a + j` goes to `there` when bit `j` is clear. -/
def unseen (lim : Limits) (S : List Item) (a : Nat) (seen : List Nat) (cc : Nat) (here : List Item) :
    Nat → List Item → Except Err (List Item)
  | 0, there => .ok there
  | f + 1, there => do
    let j := cc - (f + 1)
    let bit := match seen[j / 8]? with | some byte => decide (byte >>> (j % 8) % 2 = 1) | none => false
    if bit then unseen lim S a seen cc here f there
    else
      let x ← readItem lim S (a + j)
      unseen lim S a seen cc here f (← pushItem there (dataLen here) lim.maxReport x)

/-- The extra items of a reply, each appended to `here`. -/
def pushExtras (lim : Limits) (there : List Item) : Nat → IS → List Item → Except Err (List Item × List Nat)
  | 0, is, here => .ok (here, is.r)
  | f + 1, is, here => do
    match ← lr (is.next lim.maxItem) with
    | none => pure (here, is.r)
    | some (x, is') => pushExtras lim there f is' (← pushItem here (dataLen there) lim.maxReport x)

/-- `rposition` of `x` in the ids. -/
def rpos (ids : List (List Nat)) (x : List Nat) : Option Nat :=
  (ids.zipIdx.filter (fun p => p.1 == x)).getLast?.map (·.2)

/-- The `chunks` of `n` bytes of a list. -/
def chunks (n : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | f + 1, l => if l = [] then [] else l.take n :: chunks n f (l.drop n)

/-- Add `1` to the part count. -/
def Core.bump (c : Core) (n : Nat) : Core := { c with ans := { c.ans with cnt := c.ans.cnt + n } }

/-- One part of `answer`: read it, rank its bounds, run its arm. `mark` is the length of the reply before it. -/
def procPart (o : Oracle) (S : List Item) (c : Core) (r : List Nat) (mark : Nat) :
    Except Err (Core × List Nat) := do
  let lim := c.lim
  let (t, r) ← lr (readU8 r)
  let kind := t % 128
  let inf := decide (t ≥ 128)
  let (lo, r) ← lr (readBound c.blast r lim.maxItem)
  let c := { c with blast := lo }
  let (hi, r, c) ← if inf then pure (none, r, c) else do
    let (h, r) ← lr (readBound c.blast r lim.maxItem)
    pure (some h, r, { c with blast := h })
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
    let ((here, there), r) ← merge lim S a b is (fun m (st : List Item × List Item) =>
      match m with
      | .both _ => .ok st
      | .theirs x => do pure (← pushItem st.1 (dataLen st.2) cap x, st.2)
      | .mine x => do pure (st.1, ← pushItem st.2 (dataLen st.1) cap x)) (c.here, c.there)
    let c := { c with here := here, there := there }
    let c := if kind = tCOLD then { c with ans := { c.ans with cold := true, coldEnd := !hi.isSome } } else c
    pure (c, r)
  else if kind = tREPLY ∧ c.init then
    let (cc, r) ← lr (count r)
    if cc != b - a ∨ cc > aleaf then throw (.malformed .count)
    let (seen, r) ← lr (readBytes ((cc + 7) / 8) r)
    if (cc % 8 != 0) && (match seen.getLast? with | some byte => byte >>> (cc % 8) != 0 | none => false) then
      throw (.malformed .count)
    let there ← unseen lim S a seen cc c.here cc c.there
    let is ← lr (IS.read r)
    let (here, r) ← pushExtras lim there (is.left + 1) is c.here
    pure ({ c with here := here, there := there }, r)
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

end Pinc.Reconcile
