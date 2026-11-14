/-!
# The extension frame registry and the dispatch of a received extension frame

The Lean model of `vinc-transport` `frame/ext.rs` (the table `ASSIGNED` and its const check `unique`), of the decoder's
rule for a type from `EXTENSION_BASE` up (`Frame::decode`) and of `send_extension`'s type test, of the `Co::Extension`
arm of `on_conn_event` in `vinc-core` `events.rs` (`route`), and of the type tests of the values server
(`Server::on_event`, `ServerIn::Ext`) and the values fetch (`Fetch::on_ext`) that receive what the endpoint holds for
the application. The numbers are those of the code. Every function is total over unbounded `Nat`.

The table names the layer that takes each type: the sub-session open (`vinc-core` `sub.rs`), `REACH_OUT` (`vinc-core`
`reach.rs`), `PROOF_REQ` (the values server), `PROOF` (the values fetch), and the three types the transport tests send
for opaque payloads (no layer: the application ring).
-/

namespace Vinc.TransportExt

/-- `EXTENSION_BASE`. -/
def base : Nat := 0x40
/-- `ext::SUB_SESSION_OPEN`. -/
def subOpen : Nat := 0x40
/-- `ext::TEST_FIRST` and `ext::TEST_LAST`. -/
def testFirst : Nat := 0x41
def testLast : Nat := 0x43
/-- `ext::REACH_OUT`. -/
def reachOut : Nat := 0x44
/-- `ext::PROOF_REQ`. -/
def proofReq : Nat := 0x49
/-- `ext::PROOF`. -/
def proofFrame : Nat := 0x4f
/-- `REACH_BODY_MAX`: a count byte and eight addresses of 19 bytes. -/
def reachMax : Nat := 1 + 8 * 19

/-- The layer a registered type is for. -/
inductive Who where
  | sub | test | reach | serve | fetch
  deriving DecidableEq, Repr

/-- One entry of `ASSIGNED`, with its layer: the inclusive range `lo ..= hi`. -/
structure Entry where
  lo : Nat
  hi : Nat
  who : Who
  deriving DecidableEq, Repr

/-- `ASSIGNED`. -/
def table : List Entry :=
  [⟨subOpen, subOpen, .sub⟩, ⟨testFirst, testLast, .test⟩, ⟨reachOut, reachOut, .reach⟩,
   ⟨proofReq, proofReq, .serve⟩, ⟨proofFrame, proofFrame, .fetch⟩]

def covers (e : Entry) (t : Nat) : Bool := e.lo ≤ t && t ≤ e.hi

/-- The layer of a type: the first entry of the table that holds it. -/
def owner (t : Nat) : Option Who := (table.find? (covers · t)).map (·.who)

def overlap (a b : Entry) : Bool := a.lo ≤ b.hi && b.lo ≤ a.hi

/-- The range is well formed and at or above the base (the first test of `unique`). -/
def wf (e : Entry) : Bool := !(decide (e.lo > e.hi) || decide (e.lo < base))

/-- `unique` of `ext.rs`: every range well formed and at or above the base, the ranges pairwise disjoint. The loops
over `i` and over `j > i` are the recursion over the head and the `all` over the rest. -/
def uniq : List Entry → Bool
  | [] => true
  | e :: es => wf e && es.all (fun f => !overlap e f) && uniq es

/-- `Frame::decode` takes a type as an extension frame when it is at or above the base (every arm for a type below it
comes first). -/
def decodesExt (t : Nat) : Bool := decide (base ≤ t)

/-- `send_extension` refuses a type below the base (`BadType`). -/
def sendOk (t : Nat) : Bool := decide (base ≤ t)

/-- Where the endpoint puts a received extension frame. -/
inductive Dest where
  | sub | reach | ring | drop
  deriving DecidableEq, Repr

/-- The `Co::Extension` arm of `on_conn_event`: a non-empty sub-session open goes to the sub-session layer; a
`REACH_OUT` of 1 to `REACH_BODY_MAX` bytes to the reach ring (and raises `Event::ReachOut`); any other type, with a
non-empty body and on a session that may release, to the ring the application reads; everything else is dropped.
`len` is the body length, `allowed` the release predicate of the access check (`may_release`: the session is allowed
and its peer's cached answer has not lapsed and is an allow). -/
def route (ty len : Nat) (allowed : Bool) : Dest :=
  if ty = subOpen ∧ 0 < len then .sub
  else if ty = reachOut ∧ 0 < len ∧ len ≤ reachMax then .reach
  else if ty ≠ subOpen ∧ ty ≠ reachOut ∧ 0 < len ∧ allowed = true then .ring
  else .drop

/-- The destination of a type's layer: the endpoint's own layers take theirs, every other layer reads the ring. -/
def destOf : Who → Dest
  | .sub => .sub
  | .reach => .reach
  | _ => .ring

/-- The values server takes a frame of type `PROOF_REQ` and ignores any other. -/
def serveTakes (t : Nat) : Bool := t == proofReq

/-- The values fetch takes a frame of type `PROOF` and ignores any other. -/
def fetchTakes (t : Nat) : Bool := t == proofFrame

end Vinc.TransportExt
