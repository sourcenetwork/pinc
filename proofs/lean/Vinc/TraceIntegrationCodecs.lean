import Vinc.Json
import Vinc.RelayNet
import Vinc.StreamTag
import Vinc.ValuesFrames

/-!
# Replay of the small round trips of the integration layer

The replay half of the trace validation of `relay_addr` and `relay_parts`, `write_tag` and `read_tag` and `head_sid`
and `with_sid` (the Rust test `trace_integration_codecs`; the TLA+ half is `TraceIntegrationCodecs.tla`). Every
recorded call is replayed through the Lean functions the codec theorems are about (`RelayNet.relayAddrSock`,
`relayPartsSock`, `StreamTag.writeTag`, `readTag`, `ValuesFrames.headSid`, `withSid`): the model must return what the
code returned. Any difference exits with an error naming the line.
-/

namespace Vinc.TraceIntegrationCodecs
open Vinc.Json Vinc.RelayNet Vinc.StreamTag Vinc.ValuesFrames

/-- Whether an event belongs to this replay. -/
def isTag (t : String) : Bool := ["raddr", "rparts", "wtag", "rtag", "hsid", "wsid"].contains t

/-- The address of an event: four octets or eight segments. -/
def ipOf (v6 : Bool) (s : List Nat) : Except String Ip :=
  match v6, s with
  | false, [a, b, c, d] => pure (.v4 a b c d)
  | true, [s0, s1, s2, s3, s4, s5, s6, s7] => pure (.v6 s0 s1 s2 s3 s4 s5 s6 s7)
  | _, _ => throw "relay: an address of the wrong length"

def segsOf : Ip → List Nat
  | .v4 a b c d => [a, b, c, d]
  | .v6 s0 s1 s2 s3 s4 s5 s6 s7 => [s0, s1, s2, s3, s4, s5, s6, s7]

def raddr (j : J) : Except String Unit := do
  let v6 ← boolF j "v6"
  let a := relayAddrSock v6 (← natF j "relay") (← natF j "peer")
  check (segsOf a.1 == (← natList (← field j "s"))) "relay_addr: different address"
  check (a.1.isV6 == v6) "relay_addr: different family"
  check (a.2 == (← natF j "port")) "relay_addr: a port other than 0"

def rparts (j : J) : Except String Unit := do
  let v6 ← boolF j "v6"
  let ip ← ipOf v6 (← natList (← field j "s"))
  let r := relayPartsSock (ip, ← natF j "port")
  match (← boolF j "some"), r with
  | true, some (relay, peer) =>
    check (relay == (← natF j "relay") && peer == (← natF j "peer")) "relay_parts: different slots"
  | true, none => throw "relay_parts: the model refuses, the code accepts"
  | false, none => pure ()
  | false, some _ => throw "relay_parts: the model accepts, the code refuses"

def wtag (j : J) : Except String Unit := do
  let r := writeTag (← natList (← field j "tag"))
  match j.get? "err", r with
  | some _, none => pure ()
  | some _, some _ => throw "write_tag: the model writes, the code refuses"
  | none, some b => check (b == (← natList (← field j "b"))) "write_tag: different bytes"
  | none, none => throw "write_tag: the model refuses, the code writes"

def rtag (j : J) : Except String Unit := do
  let r := readTag (← natList (← field j "b"))
  match (j.get? "err").bind (·.str?), r with
  | none, .ok tag rest =>
    check (tag == (← natList (← field j "tag"))) "read_tag: different tag"
    check (rest == (← natList (← field j "rest"))) "read_tag: different rest"
  | none, .err e _ => throw s!"read_tag: the model refuses ({repr e}), the code accepts"
  | some "config", .err .config rest =>
    check (rest == (← natList (← field j "rest"))) "read_tag: a refused length byte leaves a different rest"
  | some "eof", .err .eof _ => pure ()
  | some t, .err e _ => throw s!"read_tag: the model refuses with {repr e}, the code with {t}"
  | some t, .ok .. => throw s!"read_tag: the model accepts, the code refuses with {t}"

/-- A stream id from its four 16-bit limbs, least significant first. -/
def limbs (j : J) : Except String Nat := do
  match ← natList (← field j "sid") with
  | [a, b, c, d] => pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw "sid: not four limbs"

def hsid (j : J) : Except String Unit := do
  let r := headSid (← natList (← field j "b"))
  match (← boolF j "ok"), r with
  | true, some v => check (v == (← limbs j)) "head_sid: different id"
  | true, none => throw "head_sid: the model refuses, the code accepts"
  | false, none => pure ()
  | false, some _ => throw "head_sid: the model accepts, the code refuses"

def wsid (j : J) : Except String Unit := do
  let r := withSid (← natList (← field j "b")) (← limbs j)
  match (← boolF j "ok"), r with
  | true, some out => check (out == (← natList (← field j "out"))) "with_sid: different bytes"
  | true, none => throw "with_sid: the model refuses, the code writes"
  | false, none => pure ()
  | false, some _ => throw "with_sid: the model writes, the code refuses"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "t" with
  | "raddr" => raddr j
  | "rparts" => rparts j
  | "wtag" => wtag j
  | "rtag" => rtag j
  | "hsid" => hsid j
  | "wsid" => wsid j
  | t => throw s!"unknown event {t}"

end Vinc.TraceIntegrationCodecs
