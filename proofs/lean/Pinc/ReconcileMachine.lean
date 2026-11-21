import Pinc.ReconcileWire

/-!
# Reconcile machine: `pinc-reconcile/src/core.rs` and `session.rs`, byte for byte

The engine of both roles (`Core`), the part rules (`procPart`, one arm per part kind), the reply building with
rollback and frames (`answerLoop`, `turn`, `resumeLoop`), the root and cold stream builders, and the handlers of the
initiator and the responder. A message is the list of its bytes; a handler takes the bytes the peer sent and returns
the bytes it writes with the step, or the error. The order of every read, check and write follows the Rust code, so
the error a message gets is the code's.

The item index is a strictly ascending list `S`; the hashes are the oracle `Oracle` (`enc` the 256-bit fingerprint of a
sum and a count of items, `idf` the 64-bit id), so any hash, including a colliding one, is a model. The sum of a list
of items is its signed multiset (`Sum`, the free commutative group on the items, which is what the group sum of the
code is when the discrete logarithm is hard). The one assumption on fingerprints (`EncInj`: `enc` does not collide
on the sums that lists produce) is a hypothesis of the theorems, not part of the model.
-/

namespace Pinc.Reconcile

/-- A sum of items: the signed multiset, the free commutative group on the items, as the coefficient of every item.
Addition and subtraction are pointwise. -/
abbrev Sum := Item → Int

instance : Add Sum := ⟨fun f g y => f y + g y⟩
instance : Sub Sum := ⟨fun f g y => f y - g y⟩

/-- The hashes: `enc` is the 256-bit fingerprint of a sum and of the count of items summed, `idf` the 64-bit id of an
item. -/
structure Oracle where
  enc : Sum → Nat → Nat
  idf : Item → Nat

/-- `Limits`. -/
structure Limits where
  maxItem : Nat
  maxMessage : Nat
  maxReport : Nat
  maxRounds : Nat

def Limits.cap (l : Limits) : Nat := min l.maxMessage frameMax

/-- `Limits::min_message`. -/
def Limits.minMessage (l : Limits) : Nat :=
  let bound := 1 + Varint.encodedLen l.maxItem + l.maxItem
  4 * bound + 2 * (1 + fpLen) + 16

/-- Every failure of a step (`Error<E>`; `index` is the host index failing, `badIndex` an unsorted index). -/
inductive Err where
  | malformed (r : Reason)
  | index
  | badIndex
  | messageTooLarge
  | itemTooLarge
  | reportTooLarge
  | tooManyRounds
  | mismatch
  deriving DecidableEq, Repr

/-- What a step does next (`Step`). -/
inductive Step where
  | send | chunk | last | wait | done
  deriving DecidableEq, Repr

/-! ## The index -/

/-- `rank`: the items strictly below the bound. -/
def rankOf (S : List Item) (b : Item) : Nat := (S.filter (fun x => lexLt x b)).length

/-- `read`: item `i`, or the index failing (out of range, or longer than the buffer of `maxItem` bytes). -/
def readItem (lim : Limits) (S : List Item) (i : Nat) : Except Err Item :=
  match S[i]? with
  | some x => if x.length ≤ lim.maxItem then .ok x else .error .index
  | none => .error .index

/-- The sum of a list of items: how often each item occurs in it. -/
def sumH (xs : List Item) : Sum := fun y => (xs.count y : Int)

/-- `fingerprint(a, b)`: the encoding of the sum over the positions `a..b` and of their count `b - a`. -/
def fpRange (o : Oracle) (S : List Item) (a b : Nat) : Nat := o.enc (sumH ((S.drop a).take (b - a))) (b - a)

/-- The final check the initiator sends: the encoding of the sum of its first `n` items plus the items it lacks minus
the items the peer lacks, and of the count `n + |here| - |there|` (natural subtraction, which stops at zero, as the
code's saturating subtraction does). -/
def checkFp (o : Oracle) (S : List Item) (n : Nat) (here there : List Item) : Nat :=
  o.enc (sumH ((S.drop 0).take n) + sumH here - sumH there) (n + here.length - there.length)

def fpBytes (v : Nat) : List Nat := beBytes fpLen v

/-! ## The message under construction and the state of one side -/

/-- `Out`: the body, the staged items, the previous bound written and its snapshot at the mark. -/
structure Out where
  body : List Nat := []
  stage : List Nat := []
  last : Item := []
  snap : Item := []

def Out.reset (o : Out) : Out := { o with body := [], stage := [], last := [] }

/-- `Out::mark`: remember the end of the message. -/
def Out.mark (o : Out) : Nat × Out := (o.body.length, { o with snap := o.last })

/-- `Out::rollback`: drop everything written since `mark`. -/
def Out.rollback (o : Out) (mark : Nat) : Out := { o with body := o.body.take mark, stage := [], last := o.snap }

def Out.head (o : Out) (kind : Nat) (lo : Item) (hi : Option Item) : Out :=
  let (bs, l) := putHead o.last kind lo hi
  { o with body := o.body ++ bs, last := l }

def Out.stageItem (o : Out) (x : Item) : Out := { o with stage := o.stage ++ venc x.length ++ x }

/-- `Answer`. -/
structure Ans where
  cnt : Nat := 0
  cold : Bool := false
  coldEnd : Bool := false
  miss : Bool := false

/-- A tail of a message that did not fit: its unread bytes, the number of parts, the bound they continue from. -/
structure Frame where
  buf : List Nat
  left : Nat
  last : Item

/-- `Core`. `blast` is the previous bound of the message being read (`Bounds::last`) and `bsnap` its snapshot. -/
structure Core where
  lim : Limits
  n : Nat := 0
  init : Bool
  exact : Bool := false
  leafed : Bool := false
  rounds : Nat := 0
  coldAt : Nat := 0
  coldLo : Item := []
  frames : List Frame := []
  blast : Item := []
  bsnap : Item := []
  out : Out := {}
  ans : Ans := {}
  hdr : List Nat := []
  here : List Item := []
  there : List Item := []

/-- The bytes of an arena (`Arena::data`). -/
def dataLen (xs : List Item) : Nat := (xs.map fun x => (venc x.length).length + x.length).sum

/-- `Core::clear`: forget the previous session. -/
def Core.clear (c : Core) : Core :=
  { c with exact := false, leafed := false, rounds := 0, coldAt := 0, frames := [], here := [], there := [] }

/-- `push`: append `item` to the arena unless the report would pass `max`. -/
def pushItem (arena : List Item) (other max : Nat) (item : Item) : Except Err (List Item) :=
  if dataLen arena + other + item.length + varMax > max then .error .reportTooLarge else .ok (arena ++ [item])

/-! ## Parts of a split, a leaf and a reply -/

/-- `bound_len`: the encoded size of a bound, at most. -/
def boundLen (len : Nat) : Nat := 1 + Varint.encodedLen len + len

/-- `leaf_ok`: whether a leaf part for `a..b` fits a message of its own. -/
def leafOk (lim : Limits) (S : List Item) (lo : Item) (hi : Option Item) (a b : Nat) (items : Bool) :
    Except Err Bool :=
  if b - a ≤ 1 then .ok true
  else
    let base := 1 + boundLen lo.length + (match hi with | some h => boundLen h.length | none => 0)
      + 2 * varMax + aleaf / 8
    if items then
      let rec go (j : Nat) (fuel : Nat) (size : Nat) : Except Err Nat :=
        match fuel with
        | 0 => .ok size
        | f + 1 => match readItem lim S j with
          | .error e => .error e
          | .ok x => go (j + 1) f (size + varMax + x.length)
      match go a (b - a) base with
      | .error e => .error e
      | .ok size => .ok (decide (size ≤ lim.cap))
    else .ok (decide (base + (b - a) * idLen ≤ lim.cap))

/-- The items `a..b` of the index, each read through `read` (so a long item is the index failing). -/
def readRange (lim : Limits) (S : List Item) (a : Nat) : Nat → Except Err (List Item)
  | 0 => .ok []
  | k + 1 => match readItem lim S a with
    | .error e => .error e
    | .ok x => match readRange lim S (a + 1) k with
      | .error e => .error e
      | .ok xs => .ok (x :: xs)

def idBytes (o : Oracle) (x : Item) : List Nat := beBytes idLen (o.idf x)

/-- `ids_part`. -/
def idsPart (o : Oracle) (lim : Limits) (S : List Item) (out : Out) (lo : Item) (hi : Option Item) (a b : Nat) :
    Except Err Out :=
  match readRange lim S a (b - a) with
  | .error e => .error e
  | .ok xs =>
    let out := out.head tIDS lo hi
    .ok { out with body := out.body ++ venc (b - a) ++ (xs.map (idBytes o)).flatten }

/-- `items_part`: a part of kind `kind` (full or cold) carrying the items `a..b`. -/
def itemsPart (lim : Limits) (S : List Item) (out : Out) (kind : Nat) (lo : Item) (hi : Option Item) (a b : Nat) :
    Except Err Out :=
  match readRange lim S a (b - a) with
  | .error e => .error e
  | .ok xs =>
    let out := out.head kind lo hi
    .ok { out with body := out.body ++ venc (b - a) ++ (xs.map fun x => venc x.length ++ x).flatten }

/-- `split`: `a..b` (within `lo..hi`) into `fan` fingerprint parts; the part count. -/
def splitParts (o : Oracle) (lim : Limits) (S : List Item) (out : Out) (lo : Item) (hi : Option Item)
    (a b fan : Nat) : Except Err (Out × Nat) :=
  let step := max 1 (((b - a) + fan - 1) / fan)
  let rec go (x : Nat) (l : Item) (out : Out) (cnt : Nat) (fuel : Nat) : Except Err (Out × Nat) :=
    match fuel with
    | 0 => .ok (out, cnt)
    | f + 1 =>
      if x < b then
        let y := min b (x + step)
        let fpb := fpBytes (fpRange o S x y)
        if y < b then
          match readItem lim S (y - 1), readItem lim S y with
          | .ok p, .ok q =>
            let k := cpl p q + 1
            if k > q.length then .error .badIndex
            else
              let sep := q.take k
              let out := out.head tFP l (some sep)
              go y sep { out with body := out.body ++ fpb } (cnt + 1) f
          | .error e, _ => .error e
          | _, .error e => .error e
        else
          let out := out.head tFP l hi
          go y l { out with body := out.body ++ fpb } (cnt + 1) f
      else .ok (out, cnt)
  go a lo out 0 (b - a + 1)

/-- `split_fit`: `split` into `spl` parts, or into fewer when the parts pass the message limit on their own. -/
def splitFit (o : Oracle) (lim : Limits) (S : List Item) (out : Out) (lo : Item) (hi : Option Item)
    (a b mark : Nat) : Nat → Except Err (Out × Nat)
  | 0 => splitParts o lim S out lo hi a b 2
  | k + 1 =>
    let fan := spl / 2 ^ (2 - k)
    match splitParts o lim S out lo hi a b fan with
    | .error e => .error e
    | .ok (out', cnt) =>
      if out'.body.length ≤ lim.cap ∨ mark > 0 ∨ fan ≤ 2 then .ok (out', cnt)
      else splitFit o lim S (out.rollback mark) lo hi a b mark k

end Pinc.Reconcile
