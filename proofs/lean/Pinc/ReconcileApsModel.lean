import Pinc.ReconcileApsSplit

/-!
# Reconcile APS, part 2: the abstract part system

The abstract part system (APS) of an honest reconciliation between an initiator holding the sorted set `A` and a
responder holding the sorted set `B`, with the hash oracle `o` (`o.H` the fingerprint hash, `o.idf` the id).
Each arm of `Core::answer` is one `Proc` constructor, and the choices the code makes (leaf or split, the fan of a
narrowed split, whether a leaf fits a message) are the nondeterminism of the relation:

* A `Part` is a kind (`fp`, `ids`, `full`, `reply`), the side that processes it next (`toInit`), its interval and its
  depth in the part tree. `fp` and `full` parts go either way; `ids` always to the responder (`toInit = false`),
  `reply` always to the initiator; `reply true` is the answer to ids (collisions possible), `reply false` the exact
  answer to a `full` part.
* `Cfg` fixes the sets, the oracle, the smallest fan a split may use (`minFan`, 2 to 16; the code uses 16 and falls
  back to 8, 4, 2) and `fits`, an arbitrary predicate standing for `leaf_ok` (does the leaf fit a message of its
  own), constrained only by the code's rule that a range of at most one receiver item always fits.
* `Proc c exact p kids ha ta lf`: processing `p` yields the parts `kids`, appends `ha` to `here` and `ta` to
  `there`, and sets `leafed` when `lf`.
* `PStep` processes any pending part (`Perm`), so any order, any message cut and any frame discipline of the byte
  machine is an instance. `PReach` starts from a root (`Init`, the first message of a pass) or from a cold stream.

`splitIvs` (ReconcileApsSplit) is the interval logic of `splitParts`; `idsHere`/`idsThere` the reply of `IDS`
(rposition of the ids, extras = our items with no matching id); `exactHere`/`exactThere` the exact merge.
-/

namespace Pinc.Reconcile

inductive Kind where
  | fp | ids | full | reply (viaIds : Bool)
  deriving DecidableEq

structure Part where
  kind : Kind
  toInit : Bool
  iv : Iv
  d : Nat

structure Cfg where
  o : Oracle
  A : List Item
  B : List Item
  hA : Sorted A
  hB : Sorted B
  minFan : Nat
  hmin : 2 ≤ minFan
  hmax : minFan ≤ 16
  fits : Bool → Bool → Iv → Prop
  fits_small : ∀ s it I, cnt (if s then A else B) I ≤ 1 → fits s it I

/-- The set of the receiver: the initiator's `A` when `toInit`. -/
def Cfg.set (c : Cfg) (toInit : Bool) : List Item := if toInit then c.A else c.B

/-- The fingerprints of the range agree. -/
def Cfg.fpEq (c : Cfg) (I : Iv) : Prop := xorH c.o (I.items c.A) = xorH c.o (I.items c.B)

/-- The exact merge of a range: `B` items `A` lacks, `A` items `B` lacks. -/
def Cfg.exactHere (c : Cfg) (I : Iv) : List Item := (I.items c.B).filter (fun x => !c.A.contains x)
def Cfg.exactThere (c : Cfg) (I : Iv) : List Item := (I.items c.A).filter (fun x => !c.B.contains x)

/-- `rposition` of `v` in the ids. -/
def rposN (ids : List Nat) (v : Nat) : Option Nat :=
  ((ids.zipIdx).filter (fun p => p.1 == v)).getLast?.map (·.2)

def Cfg.ids (c : Cfg) (I : Iv) : List Nat := (I.items c.A).map c.o.idf

/-- The extras of the ids reply: our items whose id is not among the initiator's. -/
def Cfg.idsHere (c : Cfg) (I : Iv) : List Item :=
  (I.items c.B).filter (fun x => !(c.ids I).contains (c.o.idf x))

/-- The initiator items whose position bit is clear in the ids reply. -/
def Cfg.idsThere (c : Cfg) (I : Iv) : List Item :=
  (((I.items c.A).zipIdx).filter (fun p =>
    !((I.items c.B).any (fun x => rposN (c.ids I) (c.o.idf x) == some p.2)))).map (·.1)

def leafOf (toInit : Bool) : Nat := if toInit then aleaf else bleaf

inductive Proc (c : Cfg) (exact : Bool) : Part → List Part → List Item → List Item → Bool → Prop
  | fpEq {d toInit I} (h : c.fpEq I) : Proc c exact ⟨.fp, toInit, I, d⟩ [] [] [] false
  | fpLeafResp {d I} (hne : ¬ c.fpEq I) (hcnt : cnt c.B I ≤ bleaf) (hf : c.fits false true I) :
      Proc c exact ⟨.fp, false, I, d⟩ [⟨.full, true, I, d + 1⟩] [] [] false
  | fpLeafInit {d I} (hne : ¬ c.fpEq I) (hcnt : cnt c.A I ≤ aleaf) (hf : c.fits true exact I) :
      Proc c exact ⟨.fp, true, I, d⟩ [⟨if exact then .full else .ids, false, I, d + 1⟩] [] [] true
  | fpSplit {d toInit I fan} (hne : ¬ c.fpEq I)
      (hno : ¬ (cnt (c.set toInit) I ≤ leafOf toInit ∧ c.fits toInit (!toInit || exact) I))
      (hf1 : c.minFan ≤ fan) (hf2 : fan ≤ 16) :
      Proc c exact ⟨.fp, toInit, I, d⟩
        ((splitIvs (c.set toInit) I fan).map fun J => ⟨.fp, !toInit, J, d + 1⟩) [] [] false
  | respLeaf {d I k} (hk : k = Kind.ids ∨ k = Kind.full)
      (hcnt : cnt c.B I ≤ aleaf) (hf : c.fits false true I) :
      Proc c exact ⟨k, false, I, d⟩ [⟨.reply (decide (k = Kind.ids)), true, I, d + 1⟩] [] [] false
  | respNarrow {d I k fan} (hk : k = Kind.ids ∨ k = Kind.full)
      (hno : ¬ (cnt c.B I ≤ aleaf ∧ c.fits false true I)) (hf1 : c.minFan ≤ fan) (hf2 : fan ≤ 16) :
      Proc c exact ⟨k, false, I, d⟩ ((splitIvs c.B I fan).map fun J => ⟨.fp, true, J, d + 1⟩) [] [] false
  | fullInit {d I} : Proc c exact ⟨.full, true, I, d⟩ [] (c.exactHere I) (c.exactThere I) false
  | replyExact {d I} : Proc c exact ⟨.reply false, true, I, d⟩ [] (c.exactHere I) (c.exactThere I) false
  | replyIds {d I} : Proc c exact ⟨.reply true, true, I, d⟩ [] (c.idsHere I) (c.idsThere I) false

/-- The state of a pass: pending parts, the arenas, the leaf flag, the pass kind, and the processed parts (a ghost). -/
structure St where
  pend : List Part
  here : List Item
  there : List Item
  leafed : Bool
  exact : Bool
  log : List Part

inductive PStep (c : Cfg) : St → St → Prop
  | step {s p rest kids ha ta lf} (hperm : s.pend.Perm (p :: rest)) (hp : Proc c s.exact p kids ha ta lf) :
      PStep c s ⟨kids ++ rest, s.here ++ ha, s.there ++ ta, s.leafed || lf, s.exact, s.log ++ [p]⟩

/-- The first message of a pass: one leaf for a small set, else a split of the whole key space. -/
inductive Init (c : Cfg) (exact : Bool) : St → Prop
  | leaf (hcnt : cnt c.A Iv.top ≤ aleaf) (hf : c.fits true exact Iv.top) :
      Init c exact ⟨[⟨if exact then .full else .ids, false, Iv.top, 1⟩], [], [], true, exact, []⟩
  | split {fan} (hno : ¬ (cnt c.A Iv.top ≤ aleaf ∧ c.fits true exact Iv.top)) (hf1 : c.minFan ≤ fan) (hf2 : fan ≤ 16) :
      Init c exact ⟨(splitIvs c.A Iv.top fan).map (fun J => ⟨.fp, false, J, 1⟩), [], [], false, exact, []⟩

/-- A cold stream: the responder's whole list in chunks (`blocks` any cut of `B` into non-empty pieces). -/
def coldIvs (blocks : List (List Item)) : List Iv := if blocks = [] then [Iv.top] else ivsOf none [] blocks

inductive ColdInit (c : Cfg) : St → Prop
  | mk (blocks : List (List Item)) (hf : blocks.flatten = c.B) (hne : ∀ b ∈ blocks, b ≠ []) :
      ColdInit c ⟨(coldIvs blocks).map (fun J => ⟨.full, true, J, 0⟩), [], [], false, false, []⟩

inductive PReach (c : Cfg) : St → Prop
  | init {exact s} (h : Init c exact s) : PReach c s
  | cold {s} (h : ColdInit c s) : PReach c s
  | step {s s'} (h : PReach c s) (hs : PStep c s s') : PReach c s'

end Pinc.Reconcile
