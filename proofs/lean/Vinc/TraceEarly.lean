import Vinc.Json
import Vinc.TransportEarly

/-!
# Replay of the early-packet traces

The Lean half of the trace validation of the buffer of packets that arrive before their keys (`conn/recv.rs`,
`drive.rs`, `life.rs`, `stream/datagram.rs`), the port of `proofs/tla/TraceEarly.tla`. It reads the `txea` events
(the real buffer: pushes into pools of one to eight chunks, pops, clears) and the `txeb` events (real connections
handed junk 0-RTT and 1-RTT packets before and after the session is established, and after the close), written by
the Rust test `trace_early`, and replays every step through `Vinc.TransportEarly`: the state the model computes must
be the one recorded, and so must the outcome of each packet.
-/

namespace Vinc.TraceEarly
open Vinc.Json Vinc.TransportEarly

def isTag (t : String) : Bool := t == "txea" || t == "txeb"

structure W where
  c : C := { client := false }
  cap : Nat := 0

def phase (n : Nat) : Ph := if n = 0 then .hs else if n = 1 then .up else .closed

def front (c : C) : Int := match c.q with | [] => -1 | p :: _ => p.id

def junk (id : Nat) (k : Kind) : Pkt := { id, kind := k, fate := .fails }

def outStr : Out → String
  | .held => "held" | .full => "full" | .undec => "undec" | .ok => "ok" | .closed => "closed"

/-- The buffer alone: the length, the packets dropped and the oldest packet held. -/
def sameA (c : C) (j : J) : Except String Unit := do
  let v ← field j "v"
  check (c.q.length == (← natF v "n")) "the number of packets held differs"
  check (c.nd == (← natF v "nd")) "the number of packets dropped differs"
  check (front c == (← intF v "front")) "the oldest packet held differs"

/-- A connection: the phase, the keys, the packets held and the counters. -/
def sameB (c : C) (j : J) : Except String Unit := do
  let v ← field j "v"
  check (c.ph == phase (← natF v "ph")) "the phase differs"
  check (c.er == (← boolF v "er")) "the early keys differ"
  check (c.rv == (← boolF v "rv")) "the 1-RTT keys differ"
  check (c.q.length == (← natF v "n")) "the number of packets held differs"
  check (c.nb == (← natF v "nb")) "early_buffered differs"
  check (c.nd == (← natF v "nd")) "early_dropped differs"
  check (c.nu == (← natF v "nu")) "undecryptable differs"
  check (c.rx == (← natF v "rx")) "bytes_received differs"

def replayEvent (j : J) (w : W) (idx : Nat) : Except String W := do
  let t ← strF j "t"
  let op ← strF j "op"
  if t == "txea" then
    match op with
    | "init" =>
      let c : C := { client := false }
      sameA c j
      pure { c, cap := ← natF j "cap" }
    | "push" =>
      let (out, c2) := holdPkt w.c w.cap (← boolF j "room") (junk (← natF j "id") .s)
      check ((out == .held) == (← boolF j "ok")) "push: the result differs"
      sameA c2 j
      pure { w with c := c2 }
    | "pop" =>
      let c2 := { w.c with q := w.c.q.drop 1 }
      sameA c2 j
      pure { w with c := c2 }
    | "clear" =>
      let c2 := { w.c with q := [] }
      sameA c2 j
      pure { w with c := c2 }
    | op => throw s!"unknown early-buffer op {op}"
  else
    match op with
    | "init" =>
      let v ← field j "v"
      let c : C := { client := ← boolF j "client", rx := ← natF v "rx" }
      sameB c j
      pure { c, cap := ← natF j "cap" }
    | "rx" =>
      let k : Kind := if (← strF j "kind") == "z" then .z else .s
      let (out, c2) := recv w.c w.cap true (junk idx k) (← natF j "dlen")
      check (outStr out == (← strF j "out")) "rx: the outcome differs"
      sameB c2 j
      pure { w with c := c2 }
    | "est" =>
      check (w.c.ph == .hs) "est: not in a handshake"
      let (c1, _) := established w.c
      let c2 := { c1 with rx := c1.rx + (← natF j "real") }
      sameB c2 j
      pure { w with c := c2 }
    | "close" =>
      let c2 := shut w.c
      sameB c2 j
      pure { w with c := c2 }
    | op => throw s!"unknown early-connection op {op}"

end Vinc.TraceEarly
