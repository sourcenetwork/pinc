import Pinc.Json
import Pinc.KeyRoll

/-!
# Replay of the key roll traces

The Lean half of the trace validation of `Roll`, `Rekey`, `PacketKey`, `roll_secret` (through the keys) and `due`: it
reads the `kr` events written by the Rust test `trace_keyroll` and replays every one through the functions the
theorems of `Pinc.KeyRoll` and `Pinc.Record` are about (`Roll.start`, `Roll.onRequest`, `Roll.onAnswer`,
`Record.sealK`, `Record.openK`, `Record.rolled`, `KeyRoll.due`, `Rekey.encode`, `Rekey.decode`). It is the port of
`proofs/tla/TraceKeyRoll.tla`.

A run (`begin`) starts two machines, a dialer and an acceptor, and four packet keys. A share, a Diffie-Hellman value
and a sealed packet are recorded as ids. The replay keeps an oracle per kind, a bijection between ids and the
symbolic terms of the model: a share is `pub a` of an atom, the Diffie-Hellman value of two atoms is `Dh` (the
unordered pair), a sealed packet is the pair of the key's secret and its packet number. An id met first as an input
is a share the attacker made; equal ids must be equal terms and equal terms equal ids. So the two sides of a roll
hold the same value, and a packet opens, exactly when the terms say it does.
-/

namespace Pinc.TraceKeyRoll
open Pinc.Json Pinc.KeyRoll

instance : Inhabited Record.Key := ⟨Record.Key.fresh .aes ⟨0, 0⟩ 0⟩
instance : Inhabited Roll := ⟨Roll.new true⟩

/-- The replay state of a run. -/
structure Run where
  run : Nat
  rolls : Array Roll
  ctr : Array Nat
  keys : Array Record.Key
  sOm : List (T × Int)
  dOm : List (T × Int)
  cOm : List ((Record.Sec × Nat) × Int)
  eOm : List (T × Int)

instance : Inhabited Run := ⟨⟨0, #[], #[], #[], [], [], [], []⟩⟩

/-- The replay state of a file: the current run, if any. -/
structure KState where
  r : Option Run := none

def consistent {α : Type} [BEq α] (o : List (α × Int)) (t : α) (id : Int) : Bool :=
  if o.any (fun p => p.1 == t || p.2 == id) then o.contains (t, id) else true

def bind {α : Type} [BEq α] (o : List (α × Int)) (t : α) (id : Int) : Except String (List (α × Int)) :=
  if consistent o t id then pure (if o.contains (t, id) then o else (t, id) :: o)
  else throw s!"id {id} contradicts the oracle"

def idOf {α : Type} [BEq α] (o : List (α × Int)) (t : α) : Option Int := (o.find? (·.1 == t)).map (·.2)

/-- An input share: a known id is its term; a new id is a share the attacker made (node 99). -/
def inShare (o : List (T × Int)) (id : Int) (zero : Bool) : T :=
  match o.find? (·.2 == id) with
  | some p => p.1
  | none => if zero then .junk else .pub ⟨99, id.toNat⟩

/-- An input echo: a known id is its term; a new id is an echo the attacker made, equal to no request's identifier. -/
def inEcho (o : List (T × Int)) (id : Int) : T :=
  match o.find? (·.2 == id) with
  | some p => p.1
  | none => .id (.pub ⟨98, id.toNat⟩)

def pnOf (pn big : Nat) : Nat := if big == 0 then pn else if big == 1 then 2 ^ 62 + pn else 2 ^ 64 - 1

def baseOf (slot : Nat) : Nat := if slot == 0 || slot == 3 then 0 else 1

def pendId (r : Roll) (o : List (T × Int)) : Int :=
  match r.pending with
  | none => -1
  | some m => (idOf o m.share).getD (-2)

def failName : Fail → String
  | .unexpected => "unexpected"
  | .randomness => "randomness"
  | .invalid => "invalid"

def getRun (st : KState) (j : J) : Except String Run := do
  match st.r with
  | none => throw "event outside a run"
  | some r =>
    check (r.run == (← natF j "run")) s!"event of run {← natF j "run"} outside run {r.run}"
    pure r

def natsToList (j : J) : Except String (List Nat) := natList j

def limbsVal (j : J) : Except String Nat := do
  match ← natList j with
  | [a, b, c, d] => pure (a + 65536 * b + 65536 * 65536 * c + 65536 * 65536 * 65536 * d)
  | _ => throw "bad limbs"

def sealName : Option Record.Err → String
  | none => "ok"
  | some .packetNumber => "pn"
  | some .notIncreasing => "inc"
  | some .keyRollRequired => "roll"
  | some _ => "other"

def openName : Option Record.Err → String
  | none => "ok"
  | some .packetNumber => "pn"
  | some .keyRollRequired => "roll"
  | some _ => "auth"

/-- Fresh atom of a node. -/
def freshAtom (r : Run) (n : Nat) : Atom := ⟨n, r.ctr[n]!⟩

def setRoll (r : Run) (n : Nat) (x : Roll) : Run := { r with rolls := r.rolls.set! n x }

/-- One event, against the model state; returns the new state. -/
def replayEvent (j : J) (st : KState) : Except String KState := do
  let op ← strF j "op"
  match op with
  | "begin" =>
    let aead := if (← natF j "aead") == 1 then Record.Aead.aes else Record.Aead.chacha
    let lim : Record.Limits := ⟨← natF j "al", ← natF j "cl"⟩
    pure { r := some ⟨← natF j "run", #[Roll.new true, Roll.new false], #[0, 0],
      #[Record.Key.fresh aead lim 0, Record.Key.fresh aead lim 1, Record.Key.fresh aead lim 1, Record.Key.fresh aead lim 0],
      [], [], [], []⟩ }
  | "start" =>
    let r ← getRun st j
    let n ← natF j "n"
    let fr := freshAtom r n
    let (r1, out) := r.rolls[n]!.start (some fr)
    let res ← strF j "res"
    let (som, ctr) ← match out with
      | .ok m =>
        check (res == "ok") s!"start: model ok, code {res}"
        pure (← bind r.sOm m.share (← intF j "share"), r.ctr[n]! + 1)
      | .error e =>
        check (res == failName e) s!"start: model {failName e}, code {res}"
        check ((← intF j "share") == -1) "start: share of a refusal"
        pure (r.sOm, r.ctr[n]!)
    check ((← intF j "pend") == pendId r1 som) s!"start: pending"
    check ((← boolF j "idle") == r1.isIdle) "start: idle"
    check ((← natF j "rolls") == r1.rolls) "start: rolls"
    pure { r := some { setRoll r n r1 with sOm := som, ctr := r.ctr.set! n ctr } }
  | "onreq" =>
    let r ← getRun st j
    let n ← natF j "n"
    let ans ← boolF j "ans"
    let zero ← boolF j "zero"
    let sid ← intF j "share"
    let sh := inShare r.sOm sid zero
    check (zero == (sh == .junk)) "onreq: zero share"
    let som1 ← bind r.sOm sh sid
    let m : Msg := ⟨ans, sh, 0, .junk, .junk, ← natF j "roll"⟩
    let spn ← natF j "spn"
    let (r1, out) := r.rolls[n]!.onRequest m spn (some (freshAtom r n))
    let res ← strF j "res"
    let drew := !(ans || r.rolls[n]!.isDup m || r.rolls[n]!.blocks m)
    let (som, dom, eom) ← match out with
      | .ok (a, dh) =>
        check (res == "ok") s!"onreq: model ok, code {res}"
        let som2 ← bind som1 a.share (← intF j "oans")
        let eom ← bind r.eOm a.to (← intF j "oecho")
        check ((← natF j "ospn") == a.spn) "onreq: answer switch number"
        match dh with
        | some d => pure (som2, ← bind r.dOm d (← intF j "dh"), eom)
        | none =>
          check ((← intF j "dh") == -1) "onreq: duplicate request gave a value"
          pure (som2, r.dOm, eom)
      | .error e =>
        check (res == failName e) s!"onreq: model {failName e}, code {res}"
        check ((← intF j "oans") == -1 && (← intF j "oecho") == -1 && (← natF j "ospn") == 0 && (← intF j "dh") == -1)
          "onreq: refusal output"
        pure (som1, r.dOm, r.eOm)
    check ((← intF j "pend") == pendId r1 som) "onreq: pending"
    check ((← boolF j "idle") == r1.isIdle) "onreq: idle"
    check ((← natF j "rolls") == r1.rolls) "onreq: rolls"
    pure { r := some { setRoll r n r1 with sOm := som, dOm := dom, eOm := eom, ctr := r.ctr.set! n (r.ctr[n]! + (if drew then 1 else 0)) } }
  | "onans" =>
    let r ← getRun st j
    let n ← natF j "n"
    let ans ← boolF j "ans"
    let zero ← boolF j "zero"
    let sid ← intF j "share"
    let sh := inShare r.sOm sid zero
    check (zero == (sh == .junk)) "onans: zero share"
    let som ← bind r.sOm sh sid
    let eid ← intF j "echo"
    let m : Msg := ⟨ans, sh, ← natF j "spn", if ans then inEcho r.eOm eid else .junk, .junk, ← natF j "roll"⟩
    let (r1, out) := r.rolls[n]!.onAnswer m
    let res ← strF j "res"
    let dom ← match out with
      | .ok (d, pspn) =>
        check (res == "ok") s!"onans: model ok, code {res}"
        check ((← natF j "pspn") == pspn) "onans: switch number"
        bind r.dOm d (← intF j "dh")
      | .error e =>
        check (res == failName e) s!"onans: model {failName e}, code {res}"
        check ((← intF j "dh") == -1 && (← natF j "pspn") == 0) "onans: refusal output"
        pure r.dOm
    check ((← intF j "pend") == pendId r1 som) "onans: pending"
    check ((← boolF j "idle") == r1.isIdle) "onans: idle"
    check ((← natF j "rolls") == r1.rolls) "onans: rolls"
    pure { r := some { setRoll r n r1 with sOm := som, dOm := dom } }
  | "pkroll" =>
    let r ← getRun st j
    let slot ← natF j "slot"
    let dh ← intF j "dh"
    check (r.dOm.any (·.2 == dh)) "pkroll: a value no machine computed"
    let (k1, e) := Record.rolled r.keys[slot]! dh.toNat
    check (e.isNone && (← strF j "res") == "ok") "pkroll: refused"
    check ((← natF j "gen") == k1.generation) "pkroll: generation"
    pure { r := some { r with keys := r.keys.set! slot k1 } }
  | "seal" =>
    let r ← getRun st j
    let slot ← natF j "slot"
    let k := r.keys[slot]!
    let pn := pnOf (← natF j "pn") (← natF j "big")
    let (k1, e) := Record.sealK k pn
    check ((← strF j "res") == sealName e) s!"seal: model {sealName e}, code {← strF j "res"}"
    let com ← match e with
      | none => bind r.cOm (k.secret, pn) (← intF j "ct")
      | some _ =>
        check ((← intF j "ct") == -1) "seal: ct of a refusal"
        pure r.cOm
    check ((← natF j "sealed") == k1.sealed) "seal: sealed"
    check ((← natF j "gen") == k1.generation) "seal: generation"
    pure { r := some { r with keys := r.keys.set! slot k1, cOm := com } }
  | "open" =>
    let r ← getRun st j
    let slot ← natF j "slot"
    let k := r.keys[slot]!
    let pn := pnOf (← natF j "pn") (← natF j "big")
    let ct ← intF j "ct"
    let valid := r.cOm.any fun p => p.2 == ct && p.1 == (k.secret, pn)
    let (k1, e) := Record.openK k pn valid
    check ((← strF j "res") == openName e) s!"open: model {openName e}, code {← strF j "res"}"
    check ((← natF j "failed") == k1.failed) "open: failed"
    check ((← natF j "gen") == k1.generation) "open: generation"
    pure { r := some { r with keys := r.keys.set! slot k1 } }
  | "due" =>
    let lim : Record.Limits := ⟨← natF j "al", ← natF j "cl"⟩
    let mk (a s f : Nat) : Record.Key :=
      { Record.Key.fresh (if a == 1 then .aes else .chacha) lim 0 with sealed := s, failed := f }
    let sk := mk (← natF j "sa") (← natF j "ss") (← natF j "sf")
    let rk := mk (← natF j "ra") (← natF j "rs") (← natF j "rf")
    let age := (← natF j "agem") * 1000000 + (← natF j "ager")
    check (due sk rk age (← natF j "after") == (← boolF j "res")) "due: verdict"
    check (limitReached sk == (← boolF j "lrs") && limitReached rk == (← boolF j "lrr")) "due: limit_reached"
    pure st
  | "enc" =>
    let m : Rekey := ⟨← boolF j "ans", ← natList (← field j "share"), ← natList (← field j "echo"), ← limbsVal (← field j "sl"),
      ← limbsVal (← field j "rl")⟩
    let res ← strF j "res"
    match m.encode with
    | some bs =>
      check (res == "ok") "enc: model ok, code refused"
      check (bs == (← natList (← field j "bytes"))) "enc: bytes"
    | none => check (res == "overflow") "enc: model refused, code ok"
    pure st
  | "dec" =>
    let bytes ← natList (← field j "bytes")
    let res ← strF j "res"
    match Rekey.decode bytes with
    | .ok m =>
      check (res == "ok") "dec: model ok, code refused"
      check (m.answer == (← boolF j "ans") && m.share == (← natList (← field j "share")) &&
        m.echo == (← natList (← field j "echo")) && m.switchPn == (← limbsVal (← field j "sl")) &&
        m.roll == (← limbsVal (← field j "rl"))) "dec: message"
    | .error e =>
      let name := match e with | .kind => "kind" | .trailing => "trailing" | _ => "other"
      check (res == name) s!"dec: model {name}, code {res}"
    pure st
  | _ => throw s!"unknown key roll op {op}"

end Pinc.TraceKeyRoll
