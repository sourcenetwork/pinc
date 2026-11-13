import Vinc.Json
import Vinc.TransportExt

/-!
# Replay of the extension frame dispatch traces

The Lean half of the trace validation of the extension frame registry and its dispatch (`vinc-transport`
`frame/ext.rs`, the `Co::Extension` arm of `vinc-core` `events.rs`), the port of `proofs/tla/TraceExt.tla`. It reads
the `txex` events written by the Rust test `trace_ext`:

* `tbl`: the registry as the code has it (the base, the constants, `REACH_BODY_MAX`, `ASSIGNED`) equals the model's
  numbers and table, and the check of `ext.rs` accepts it;
* `route`: one extension frame carried by real endpoints. What the endpoint did with it must be what `route` says of
  the type, the length and the answer of the access check: one frame in the application ring, with the type and the
  length sent, exactly when `route` is `ring`; the `REACH_OUT` event, with the body length sent, exactly when it is
  `reach`; and the decoder takes the type;
* `sub`: a real second protocol over a session made a child, and neither ring holds anything; the model hands a
  sub-session open to the sub-session layer.

Both files are replayed: the narrow one and the wide one (types up to `2^62 - 1`).
-/

namespace Vinc.TraceExt
open Vinc.Json Vinc.TransportExt

def isTag (t : String) : Bool := t == "txex"

def replayTbl (j : J) : Except String Unit := do
  check ((← natF j "base") == base) "tbl: the base differs"
  check ((← natF j "sub") == subOpen) "tbl: SUB_SESSION_OPEN differs"
  check ((← natF j "reach") == reachOut) "tbl: REACH_OUT differs"
  check ((← natF j "reachmax") == reachMax) "tbl: REACH_BODY_MAX differs"
  check ((← natF j "proofreq") == proofReq) "tbl: PROOF_REQ differs"
  check ((← natF j "proof") == proofFrame) "tbl: PROOF differs"
  check ((← natF j "testfirst") == testFirst) "tbl: TEST_FIRST differs"
  check ((← natF j "testlast") == testLast) "tbl: TEST_LAST differs"
  let a ← pairList (← field j "assigned")
  check (a == table.map fun e => (e.lo, e.hi)) "tbl: ASSIGNED differs from the model's table"
  check (uniq table) "tbl: the check of ext.rs rejects the table"

def replayRoute (j : J) : Except String Unit := do
  let ty ← natF j "ty"
  let len ← natF j "len"
  let allowed ← boolF j "allowed"
  let ring ← natF j "ring"
  let rty ← intF j "rty"
  let rlen ← intF j "rlen"
  let reach ← natF j "reach"
  let reachlen ← intF j "reachlen"
  let d := route ty len allowed
  check (ring == (if d == .ring then 1 else 0)) s!"route: ty {ty} len {len} allowed {allowed}: the ring holds {ring}, the model says {repr d}"
  if d == .ring then
    check (rty == (ty : Int) && rlen == (len : Int)) "route: the frame in the ring is not the one sent"
  else
    check (rty == -1 && rlen == -1) "route: a frame in the ring that the model does not hand it"
  check (reach == (if d == .reach then 1 else 0)) s!"route: ty {ty} len {len}: {reach} REACH_OUT events, the model says {repr d}"
  if d == .reach then
    check (reachlen == (len : Int)) "route: the REACH_OUT body kept is not the one sent"
  else
    check (reachlen == -1) "route: a REACH_OUT body kept that the model does not hand it"
  check (decodesExt ty) "route: the decoder does not take the type"
  if d == .ring then
    check (owner ty != some .sub && owner ty != some .reach) "route: the ring took the type of an endpoint layer"

def replaySub (j : J) : Except String Unit := do
  check ((← natF j "child") == 1) "sub: no child"
  check ((← natF j "ring") == 0 && (← natF j "reach") == 0) "sub: a frame reached a ring"
  check (route subOpen 1 true == .sub) "sub: the model does not hand a sub-session open to the sub-session layer"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "tbl" => replayTbl j
  | "route" => replayRoute j
  | "sub" => replaySub j
  | op => throw s!"unknown extension op {op}"

end Vinc.TraceExt
