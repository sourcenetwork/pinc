import Pinc.VerifyBytes
import Pinc.Sizes

/-!
# `GroupVerifier` of pinc-values at the byte level

`pinc-values/src/verify.rs` `GroupVerifier` checks the same stream as `pinc-dag` `RangeVerifier` but never holds a
group: the bytes of a group go to an incremental hasher as the pieces arrive. This module is that code, call for
call, on the machine integers of `Machine.lean`:

* `feedG` is `feed`, with `feed_pair`, `complete_pair` (`completePairG`) and `feed_group` (`feedGroupG`,
  `finishGroupG`): the 64-byte pair buffer `pair` (its length is `pair_n`), the hasher input `hb` (its length is
  `group_n`; the BLAKE3 `Hasher::update` is incremental, so the hasher state after some updates stands for the
  concatenation of the bytes it took, which is what the symbolic hash `Hash.leaf` is applied to), the stack with its
  64-node cap (`pushG`: `StackOverflow`), the sticky failure, `TooMuchData` for a complete stream with a nonempty
  input, the empty-input no-op;
* `nextItemG`, `nextLenG`, `atBoundaryG`, `isCompleteG`, `failureG`, `skipG` are `next_item`, `next_len`,
  `at_boundary`, `is_complete`, `failure`, `skip_group`;
* `GS.released` is a ghost log (the groups the verifier passed with the bytes of each: those that matched while being
  fed, and those skipped, whose bytes the caller holds); it is not state of the code.

The stack depth bound (`HBnd`, `hbnd_feed`) shows that the 64-node cap is never reached for a value of up to
`u64::MAX` bytes (at most 55 nodes), the same fact that makes `RangeVerifier`'s identical cap unreachable.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.ValuesVerify
open Pinc.Layout Pinc.Tree Pinc.Machine Pinc.VerifyBytes

/-- The errors `GroupVerifier` returns (`TreeError`). -/
inductive Err where
  | parentMismatch
  | groupMismatch
  | tooMuchData
  | outputTooSmall
  | stackOverflow
  deriving DecidableEq

/-- The error of the copying verifier an error of this verifier stands for. -/
def Err.toE : Err → Option E
  | .parentMismatch => some .parentMismatch
  | .groupMismatch => some .groupMismatch
  | .tooMuchData => some .tooMuchData
  | .outputTooSmall => some .outputTooSmall
  | .stackOverflow => none

/-- The verifier state. -/
structure GS (Cv : Type) where
  stack : List (Node Cv)
  released : List (Nat × Bytes)
  pair : Bytes
  hb : Bytes
  failed : Option Err

/-- The outcome of one `feed`: `Ok(Fed { consumed, group })` (the group as byte offset and length), or an error. -/
inductive GR where
  | ok (consumed : Nat) (group : Option (Nat × Nat))
  | err (e : Err)

/-- What `next_item` returns. -/
inductive GItem where
  | pair
  | group (off len : Nat)
  deriving DecidableEq

/-- The depth of the node stack (`STACK`). -/
def stackCap : Nat := 64

section
variable {Cv : Type} [DecidableEq Cv]

/-- `GroupVerifier::new` for a validated request: the root alone on the stack when the range is not empty. -/
def initG (c : Cfg Cv) (root : Cv) : GS Cv :=
  { stack := if c.first < c.last then [⟨root, 0, c.n⟩] else [], released := [], pair := [], hb := [],
    failed := none }

/-- `push`, then `?`: the node goes on the stack, or the verifier fails with `StackOverflow` (and stays failed). -/
def pushG (s : GS Cv) (n : Node Cv) : GS Cv :=
  if s.failed.isSome then s
  else if s.stack.length < stackCap then { s with stack := n :: s.stack }
  else { s with failed := some .stackOverflow }

/-- `complete_pair` on the node `nd` on top of the stack (`rest` below it) and the 64 bytes of the pair, with
`self.pair_n = 0` already done by `feed_pair`. `none` is an arithmetic failure (`absorbed_arith` shows there is none). -/
def completePairG (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (pair : Bytes) : Option (GS Cv) :=
  let raw := c.rd pair
  let s0 : GS Cv := { s with pair := [] }
  if c.H.parent (isRoot c.n nd.lo nd.hi) raw.l raw.r = nd.cv then
    match Machine.sub 64 nd.hi nd.lo with
    | none => none
    | some span =>
      match leftGroupsM Nat.log2 span with
      | none => none
      | some off =>
        match Machine.add 64 nd.lo off with
        | none => none
        | some mid =>
          let s1 : GS Cv := { s0 with stack := rest }
          let s2 := if mid < c.last then pushG s1 ⟨raw.r, mid, nd.hi⟩ else s1
          some (if c.first < mid then pushG s2 ⟨raw.l, nd.lo, mid⟩ else s2)
  else some { s0 with failed := some .parentMismatch }

/-- The end of `feed_pair`: complete the pair, and report `Ok` or the error that failed the verifier. -/
def finishPairG (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (item : Bytes) (take : Nat) :
    Option (GR × GS Cv) :=
  match completePairG c s nd rest item with
  | none => none
  | some s1 => some ((match s1.failed with | some e => GR.err e | none => GR.ok take none), s1)

/-- `feed_pair`. -/
def feedPairG (w : Nat) (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (input : Bytes) :
    Option (GR × GS Cv) :=
  match Machine.sub w 64 s.pair.length with
  | none => none
  | some need =>
    let take := min input.length need
    let head := input.take take
    if s.pair = [] ∧ take = 64 then finishPairG c s nd rest head take
    else
      match Machine.add w s.pair.length take with
      | none => none
      | some e =>
        if 64 < e then some (.err .outputTooSmall, s)
        else if e < 64 then some (.ok take none, { s with pair := s.pair ++ head })
        else finishPairG c s nd rest (s.pair ++ head) take

/-- The end of `feed_group`: the group is complete (`group_n` is reset), its hash is compared with the committed
chaining value; a match releases it. -/
def finishGroupG (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (data : Bytes) (take size : Nat) :
    Option (GR × GS Cv) :=
  let s0 : GS Cv := { s with hb := [] }
  if c.H.leaf (isRoot c.n nd.lo nd.hi) nd.lo data = nd.cv then
    match Machine.mul 64 nd.lo (groupLen c.log) with
    | none => none
    | some off =>
      some (.ok take (some (off, size)),
        { s0 with stack := rest, released := s.released ++ [(nd.lo, data)] })
  else some (.err .groupMismatch, { s0 with failed := some .groupMismatch })

/-- `feed_group`. -/
def feedGroupG (w : Nat) (c : Cfg Cv) (s : GS Cv) (nd : Node Cv) (rest : List (Node Cv)) (input : Bytes) :
    Option (GR × GS Cv) :=
  let size := groupSize c.len c.log nd.lo
  let hb0 := if s.hb.length = 0 then [] else s.hb
  match Machine.sub 64 size s.hb.length with
  | none => none
  | some left =>
    let take := match tryFrom w left with | none => input.length | some n => min n input.length
    let hb1 := hb0 ++ input.take take
    match Machine.add 64 s.hb.length take with
    | none => none
    | some gn =>
      if gn < size then some (.ok take none, { s with hb := hb1 })
      else finishGroupG c s nd rest hb1 take size

/-- `GroupVerifier::feed` on a `w`-bit `usize`. -/
def feedG (w : Nat) (c : Cfg Cv) (s : GS Cv) (input : Bytes) : Option (GR × GS Cv) :=
  match s.failed with
  | some e => some (.err e, s)
  | none =>
    if input = [] then some (.ok 0 none, s)
    else match s.stack with
      | [] => some (.err .tooMuchData, s)
      | nd :: rest =>
        if nd.hi - nd.lo = 1 then feedGroupG w c s nd rest input else feedPairG w c s nd rest input

/-- `next_item`. -/
def nextItemG (c : Cfg Cv) (s : GS Cv) : Option GItem :=
  if s.failed.isSome then none
  else match s.stack with
    | [] => none
    | nd :: _ =>
      some (if nd.hi - nd.lo = 1 then .group (nd.lo * groupLen c.log) (groupSize c.len c.log nd.lo) else .pair)

/-- `next_len`. -/
def nextLenG (c : Cfg Cv) (s : GS Cv) : Option Nat :=
  match nextItemG c s with
  | none => none
  | some .pair => some (64 - s.pair.length)
  | some (.group _ len) => some (len - s.hb.length)

/-- `at_boundary`. -/
def atBoundaryG (s : GS Cv) : Bool := s.pair.length == 0 && s.hb.length == 0

/-- `is_complete`. -/
def isCompleteG (s : GS Cv) : Bool := s.failed.isNone && s.stack.isEmpty

/-- `failure`. -/
def failureG (s : GS Cv) : Option Err := s.failed

/-- `skip_group`: pass over the next group without hashing it; the error is `TooMuchData` and the verifier is
unchanged when the verifier is failed, not at the start of an item, or the next item is not a group. `d` is ghost:
the bytes of the group the caller already holds verified (they are logged, never read by the code). -/
def skipG (c : Cfg Cv) (s : GS Cv) (d : Bytes) : (Except Err (Nat × Nat)) × GS Cv :=
  if s.failed.isSome ∨ atBoundaryG s = false then (.error .tooMuchData, s)
  else match nextItemG c s, s.stack with
    | some (.group off len), nd :: rest => (.ok (off, len), { s with stack := rest, released := s.released ++ [(nd.lo, d)] })
    | _, _ => (.error .tooMuchData, s)

end

end Pinc.ValuesVerify
