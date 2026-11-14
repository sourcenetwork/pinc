import Vinc.Json
import Vinc.ConnectCarrier

/-!
# Replay of the protected carrier traces

The Lean half of the trace validation of the protected carrier (`carrier/session.rs`), the port of
`proofs/tla/TraceConnectCarrier.tla`. It reads the `cca` events written by the Rust test `trace_connect_carrier` and
replays every call of the dialer (`d`) and the listener (`a`) through `Vinc.ConnectCarrier`: the stream each end
receives comes first, as its units (offset, length, the index of the other end's record the bytes are, whether its
plaintext decodes); then each call must give the answer the code gave, take and hand out the bytes it did, and leave
the state the public API showed (`free`, `pending_transmit`, `key_request`). A record opens at packet number `pn`
exactly when its bytes are the `pn`-th record the other end sealed. The handshake machine's outcome is an input: what
the step did and how many bytes it queued. The keys use the code's limits (`Record.Limits.default`) and AEAD tag.
-/

namespace Vinc.TraceConnectCarrier
open Vinc.Json Vinc.ConnectCarrier

def isTag (t : String) : Bool := t == "cca"

/-- A stream table: offset, length, the record index (`-1` for none), whether it decodes. -/
abbrev Tab := List (Nat × Nat × Int × Bool)

structure W where
  d : C := {}
  a : C := {}
  td : Tab := []
  ta : Tab := []
  k : Konst := ⟨0, 0, 0, 0, 0, 0, .aes, Record.Limits.default⟩

def look (t : Tab) (o : Nat) : Option (Nat × Int × Bool) :=
  (t.find? (·.1 == o)).map (·.2)

def strmOf (t : Tab) : Strm :=
  { hdr := fun o => ((look t o).map (·.1)).getD 0
    opens := fun o pn => ((look t o).map (fun x => x.2.1 == (pn : Int))).getD false
    fok := fun o => ((look t o).map (·.2.2)).getD false }

def resName : Res → String
  | .idle => "idle"
  | .hs => "hs"
  | .kreq => "kreq"
  | .opened => "open"
  | .frame => "frame"
  | .ok => "ok"
  | .err e => match e with
    | .unitSize => "UnitSize"
    | .authentication => "Authentication"
    | .keyLimit => "KeyLimit"
    | .notOpen => "NotOpen"
    | .outputFull => "OutputFull"
    | .noRoom => "NoRoom"
    | .frame => "Frame"
    | .record => "Record"
    | .closed => "Closed"
    | .handshake => "Handshake"
    | .noKeyRequest => "NoKeyRequest"

def sendName (s : String) : Nat := if s == "d" then 0 else 1

def sends (g : Nat) : List Out := if g = 0 then [] else [.send (g - 2)]

/-- The handshake step the test saw. -/
def hsOf (k : Konst) (side res : String) (g : Nat) : Hs :=
  { herr := res == "Handshake"
    outs := if res == "open" then sends g ++ [.est true]
            else if res == "OutputFull" then sends g ++ [.send k.outn]
            else sends g
    kreq := res == "kreq"
    sb := sendName side
    rb := 1 - sendName side }

def get (w : W) (s : String) : C := if s == "d" then w.d else w.a
def put (w : W) (s : String) (c : C) : W := if s == "d" then { w with d := c } else { w with a := c }
def tabOf (w : W) (s : String) : Tab := if s == "d" then w.td else w.ta

def shows (k : Konst) (c : C) (j : J) (what : String) : Except String Unit := do
  check (free k c == (← natF j "free")) s!"{what}: free() differs: the model has {free k c}"
  check (c.out == (← natF j "pend")) s!"{what}: pending_transmit() differs: the model has {c.out}"
  check ((c.st == .hs && c.kr) == (← boolF j "kr")) s!"{what}: key_request() differs"

def tabList (j : J) : Except String Tab := do
  match j.arr? with
  | some a => a.toList.mapM fun v => do
    match v.arr? with
    | some #[o, h, g, f] =>
      match o.nat?, h.nat?, g.int?, f.bool? with
      | some o, some h, some g, some f => pure (o, h, g, f)
      | _, _, _, _ => throw "a malformed stream unit"
    | _ => throw "a malformed stream unit"
  | none => throw "expected an array of units"

def feOf : String → Except String Fe
  | "ok" => pure .ok
  | "wire" => pure .wire
  | "frame" => pure .frame
  | s => throw s!"unknown encoder outcome {s}"

def replayEvent (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  let side ← strF j "side"
  let c := get w side
  let k := w.k
  match op with
  | "stream" =>
    let t ← tabList (← field j "units")
    pure (if side == "d" then { w with td := t } else { w with ta := t })
  | "init" =>
    let kj ← field j "k"
    let k : Konst := ⟨← natF kj "inl", ← natF kj "maxm", ← natF kj "maxu", ← natF kj "tag", ← natF kj "outn",
      ← natF kj "maxf", .aes, Record.Limits.default⟩
    let c ← match ← strF j "kind" with
      | "dial" =>
        let (c, r) := dial k { herr := false, outs := sends (← natF j "pend"), kreq := ← boolF j "kr", sb := 0, rb := 1 }
        check (r == .ok) "init: dial refused"
        pure c
      | _ => pure accept
    shows k c j "init"
    pure (put { w with k } side c)
  | "recv" =>
    check (c.wr == (← natF j "off")) s!"recv: the host offered from {← natF j "off"}, the model's buffer ends at {c.wr}"
    let (t, c') := receive k c (← natF j "len")
    check (t == (← natF j "took")) s!"recv: the model takes {t}"
    shows k c' j "recv"
    pure (put w side c')
  | "poll" =>
    let res ← strF j "res"
    let t := tabOf w side
    let c1 := release c
    if c1.st != .ended && inLen c1 ≥ 2 then
      check ((look t c1.rd).isSome) s!"poll: the model reads a length at {c1.rd}, which is not a unit of the stream"
    let (c', r) := poll k (strmOf t) c (hsOf k side res (← natF j "grow"))
    check (resName r == res) s!"poll: the model answers {resName r}, the code {res}"
    shows k c' j "poll"
    pure (put w side c')
  | "ans" =>
    let res ← strF j "res"
    let (c', r) := answerSoft k c (hsOf k side res (← natF j "grow"))
    check (resName r == res) s!"ans: the model answers {resName r}, the code {res}"
    shows k c' j "ans"
    pure (put w side c')
  | "tx" =>
    let (n, c') := transmit c (← natF j "cap")
    check (n == (← natF j "n")) s!"tx: the model hands out {n}"
    shows k c' j "tx"
    pure (put w side c')
  | "seal" =>
    let plen ← natF j "plen"
    let cap ← natF j "cap"
    let (c', r, n) ← match ← strF j "how" with
      | "frame" => pure (sealFrame k c plen cap (← feOf (← strF j "fe")))
      | _ => pure (sealBytes k c plen cap)
    check (resName r == (← strF j "res")) s!"seal: the model answers {resName r}"
    check (n == (← natF j "n")) s!"seal: the model's unit is {n} bytes"
    shows k c' j "seal"
    pure (put w side c')
  | op => throw s!"unknown carrier op {op}"

end Vinc.TraceConnectCarrier
