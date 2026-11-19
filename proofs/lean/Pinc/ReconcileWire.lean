import Pinc.Axioms
import Pinc.Varint

/-!
# Reconcile wire: the byte-level building blocks of `pinc-reconcile/src/wire.rs`

Step for step: the reader primitives (`Reader::read_u8`, `read_bytes`, `read_varint`, `count`), the prefix-compressed
bound (`put_bound`, `read_bound`), the part head (`Out::head`), the framing (`frame_body`, `frame_header`) and the
count field (`put_parts`, `read_parts`). Bytes are `Nat`s below 256; a reader is the list of bytes still unread.

`readBound` carries the canonical check (a bound is accepted only with the shared prefix length the encoder writes,
`min (cpl last b) 255`), so a bound has one encoding.
-/

namespace Pinc.Reconcile

/-- An item, a bound and a set reference: a byte string. -/
abbrev Item := List Nat

/-- A differing range splits into this many sub-ranges. -/
def spl : Nat := 16
/-- The initiator's leaf size, in items. -/
def aleaf : Nat := 32
/-- The responder's leaf size, in items. -/
def bleaf : Nat := 6
/-- The responder streams its whole list when the initiator has fewer than `1 / coldRatio` of its items. -/
def coldRatio : Nat := 10
/-- The most frames a side holds (`MAX_NEST`). -/
def maxNest : Nat := 64
/-- The longest frame body (`FRAME_MAX`). -/
def frameMax : Nat := 0xffffff
/-- The shared prefix length cap of a bound. -/
def cplMax : Nat := 255
/-- Bytes of a range fingerprint, of an item id, and the longest varint. -/
def fpLen : Nat := 16
def idLen : Nat := 8
def varMax : Nat := 9

/-- What is wrong with a message (`Reason`). -/
inductive Reason where
  | frame | truncated | tag | bound | count | item | state
  deriving DecidableEq, Repr

/-- The part kinds (`wire::tag`). -/
def tFP : Nat := 1
def tIDS : Nat := 2
def tFULL : Nat := 3
def tREPLY : Nat := 4
def tCOLD : Nat := 5
def tCHECK : Nat := 6
def tMISS : Nat := 7
def tINF : Nat := 0x80

/-- Lexicographic order on byte strings (`<[u8]>::cmp`): a prefix sorts first. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-- The shared prefix length (`common_prefix`). -/
def cpl : List Nat → List Nat → Nat
  | a :: as, b :: bs => if a = b then cpl as bs + 1 else 0
  | _, _ => 0

/-- `venc`: the varint bytes of a length or a count (always below 2^63 in memory). -/
def venc (v : Nat) : List Nat := Varint.encodeBytes v

/-- Big endian bytes of `v` in `w` bytes, and back. -/
def beBytes : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, v => beBytes w (v / 256) ++ [v % 256]

def fromBE (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-! ## The reader -/

/-- `Reader::read_u8`. -/
def readU8 : List Nat → Except Reason (Nat × List Nat)
  | [] => .error .truncated
  | b :: r => .ok (b, r)

/-- `Reader::read_bytes`. -/
def readBytes (n : Nat) (r : List Nat) : Except Reason (List Nat × List Nat) :=
  if n ≤ r.length then .ok (r.take n, r.drop n) else .error .truncated

/-- `count`: a varint as a `usize`; any varint failure is `Truncated`. -/
def count (r : List Nat) : Except Reason (Nat × List Nat) :=
  match Varint.decode r with
  | .ok (v, used) => .ok (v, r.drop used)
  | .error _ => .error .truncated

/-- `Reader::read_varint` (the same failure mapping as `count`). -/
def readVarint (r : List Nat) : Except Reason (Nat × List Nat) := count r

/-! ## Bounds -/

/-- `put_bound`: `cpl venc(len) suffix` against the previous bound `last`; the bound becomes the new `last`. -/
def putBound (last b : Item) : List Nat × Item :=
  let c := min (cpl last b) cplMax
  ([c] ++ venc (b.length - c) ++ b.drop c, b)

/-- `read_bound` with the canonical check. -/
def readBound (last : Item) (r : List Nat) (mx : Nat) : Except Reason (Item × List Nat) :=
  match readU8 r with
  | .error e => .error e
  | .ok (c, r) =>
    match count r with
    | .error e => .error e
    | .ok (n, r) =>
      if c > last.length ∨ c + n > mx then .error .bound
      else
        match readBytes n r with
        | .error e => .error e
        | .ok (sfx, r) =>
          let noncanon := decide (c < cplMax) && (match last.drop c, sfx with | x :: _, y :: _ => x == y | _, _ => false)
          if noncanon then .error .bound else .ok (last.take c ++ sfx, r)

/-- A part head (`Out::head`): the tag with the infinity bit, the lower bound and, unless infinite, the upper. -/
def putHead (last : Item) (kind : Nat) (lo : Item) (hi : Option Item) : List Nat × Item :=
  let (b1, l1) := putBound last lo
  match hi with
  | none => ((kind ||| tINF) :: b1, l1)
  | some h => let (b2, l2) := putBound l1 h; (kind :: (b1 ++ b2), l2)

/-! ## Framing and the count field -/

/-- `frame_body`: the body, checked against its three-byte length. -/
def frameBody (msg : List Nat) : Except Reason (List Nat) :=
  match msg with
  | a :: b :: c :: body => if (a * 256 + b) * 256 + c = body.length then .ok body else .error .frame
  | _ => .error .truncated

/-- `frame_header`: the three length bytes, or `none` past `FRAME_MAX`. -/
def frameHeader (len : Nat) : Option (List Nat) :=
  if len > frameMax then none else some (beBytes 3 len)

/-- `put_parts`: `venc(cnt << 1 | more)`. -/
def putParts (cnt : Nat) (more : Bool) : List Nat := venc (cnt * 2 + if more then 1 else 0)

/-- `read_parts`: the part count and the `more` flag; an empty message that claims more is `Count`. -/
def readParts (r : List Nat) : Except Reason ((Nat × Bool) × List Nat) :=
  match count r with
  | .error e => .error e
  | .ok (raw, r) =>
    if raw / 2 = 0 ∧ raw % 2 = 1 then .error .count else .ok ((raw / 2, raw % 2 = 1), r)

end Pinc.Reconcile
