import Vinc.Json
import Vinc.DtnSeal

/-!
# Replay of the one-shot encryption traces

The Lean half of the trace validation of `seal.rs`, `head.rs` and `bundle.rs`: it reads the `ds` events written by
the Rust test `trace_dtn_seal` and replays every one through the functions the theorems of `Vinc.DtnSeal` are
about (`Bun.key`, `decap`, `sealSlice`, `openSlice`, `sealIdx`, `nonce`). It is the port of
`proofs/tla/TraceDtnSeal.tla`.

A public value, a seed and an AEAD key are recorded as ids (one id per distinct byte string, ids are unique across
kinds). The replay keeps one oracle, a bijection between ids and the symbolic terms of the model: a sealing event
binds the ephemeral key, the KEM ciphertext, the bundle id and the key probe to the terms the model computes; a
decapsulation event reads the head fields back through the oracle (an id met first is a value the attacker made, a
`junk` term) and requires the code's verdict to be the model's, and the key the code derived to be the model's key
term, so it equals the sender's exactly when the terms are equal. A slice event requires the code to open a slice
exactly when `openSlice` does.
-/

namespace Vinc.TraceDtnSeal
open Vinc.Json Vinc.DtnSeal Vinc.DtnSeal.T

/-- The replay state: the oracle between ids and terms. -/
structure W where
  om : List (T × Nat) := []

/-- Whether the events of this tag belong to this replay. -/
def isTag (t : String) : Bool := t == "ds"

def consistent (o : List (T × Nat)) (t : T) (id : Nat) : Bool :=
  if o.any (fun p => p.1 == t || p.2 == id) then o.contains (t, id) else true

def bind (o : List (T × Nat)) (t : T) (id : Nat) : Except String (List (T × Nat)) :=
  if consistent o t id then pure (if o.contains (t, id) then o else (t, id) :: o)
  else throw s!"id {id} contradicts the oracle"

/-- The term of an id: a bound id is its term, a new id is a value the attacker made. -/
def termOf (o : List (T × Nat)) (id : Nat) : T :=
  match o.find? (·.2 == id) with
  | some p => p.1
  | none => T.junk id

/-- The names and widths of the fields of `Head::encode` (the fields of `HeadB.fields`). -/
def headWidths : List (String × Nat) :=
  [("id", 32), ("stag", 1), ("src", 32), ("dtag", 1), ("dst", 32), ("wall", 8), ("ctr", 4), ("life", 8),
   ("copies", 2), ("k", 1), ("m", 1), ("log", 1), ("plen", 8), ("root", 32), ("epoch", 4), ("eph", 32), ("kct", 1088)]

/-- The widths add up to `HEAD_LEN`, the length `HeadB.body_length` proves. -/
theorem headWidths_sum : (headWidths.map (·.2)).sum = 32 + 2 * 33 + 12 + 8 + 2 + 2 + 1 + 8 + 32 + 4 + 32 + 1088 := by
  decide

/-- The field a body byte belongs to. -/
def fieldAt (ws : List (String × Nat)) (pos : Nat) : Option String :=
  match ws with
  | [] => none
  | (n, w) :: rest => if pos < w then some n else fieldAt rest (pos - w)

/-- The replayed seed-free slice plaintext. -/
def pt : T := T.pl 0 0

def replayEvent (j : J) (st : W) : Except String W := do
  let e ← strF j "e"
  match e with
  | "begin" => pure {}
  | "enc" =>
    let b : Bun := ⟨← natF j "src", ← natF j "se", ← natF j "sm", ← natF j "kp", ← natF j "dest", ← natF j "ep",
                    ← natF j "wall", ← natF j "ctr"⟩
    let o ← bind st.om b.eph (← natF j "eph")
    let o ← bind o b.ctT (← natF j "ct")
    let o ← bind o b.idT (← natF j "id")
    let o ← bind o b.key (← natF j "kid")
    pure ⟨o⟩
  | "dec" =>
    let own : Own := ⟨← natF j "node", ← natF j "ep", ← natF j "kp"⟩
    let ephId ← natF j "eph"
    let ctId ← natF j "ct"
    let idId ← natF j "id"
    let eph := termOf st.om ephId
    let ct := termOf st.om ctId
    let hsrc ← natF j "hsrc"
    let hwall ← natF j "hwall"
    let hctr ← natF j "hctr"
    let idok ← boolF j "idok"
    let id := if idok then bid hsrc hwall hctr eph else termOf st.om idId
    let lo ← boolF j "lo"
    let h : HeadT := ⟨hsrc, hwall, hctr, ← natF j "dst", ← natF j "hep", eph, ct, id, lo⟩
    let o ← bind st.om eph ephId
    let o ← bind o ct ctId
    let o ← bind o id idId
    let v ← strF j "v"
    let kid ← natF j "kid"
    match decap own h with
    | .wrong =>
      check (v == "wrong" && kid == 0) s!"decap: model refuses the recipient or epoch, code says {v}"
      pure ⟨o⟩
    | .badId =>
      check (v == "badid" && kid == 0) s!"decap: model refuses the bundle id, code says {v}"
      pure ⟨o⟩
    | .crypto =>
      check (v == "crypto" && kid == 0) s!"decap: model fails on the ephemeral key, code says {v}"
      pure ⟨o⟩
    | .ok k =>
      check (v == "ok") s!"decap: model derives a key, code says {v}"
      let o ← bind o k kid
      pure ⟨o⟩
  | "open" =>
    let ka := termOf st.om (← natF j "ka")
    let kb := termOf st.om (← natF j "kb")
    let i ← natF j "i"
    let jj ← natF j "j"
    let tamper ← boolF j "tamper"
    let ok ← boolF j "ok"
    check (st.om.any (·.2 == (← natF j "ka")) && st.om.any (·.2 == (← natF j "kb"))) "open: a key never derived"
    check (i < 2 ^ 64 && jj < 2 ^ 64) "open: index beyond 2^64"
    let model := !tamper && (openSlice kb jj (sealSlice ka i pt)).isSome
    check (model == ok) s!"open: model {model}, code {ok}"
    pure st
  | "nonces" =>
    let k ← natF j "k"
    let data ← natF j "data"
    let bk ← natList (← field j "bk")
    let idxs := sealIdx k (fun b => bk.getD b 0) bk.length
    check (idxs.length == data) s!"nonces: {idxs.length} data indices, code {data}"
    check (decide ((idxs.map nonce).Nodup)) "nonces: the model repeats a nonce"
    check (bk.all (· ≤ k) && decide (0 < k)) "nonces: a block larger than k"
    check (← boolF j "distinct") "nonces: the code repeated a symbol"
    pure st
  | "hgood" =>
    check ((headWidths.map (·.2)).sum == (← natF j "len")) "hgood: the head length differs from the model's"
    check (← boolF j "ok") "hgood: an untouched head must verify"
    pure st
  | "hflip" =>
    let pos ← natF j "pos"
    check (fieldAt headWidths pos == some (← strF j "f")) s!"hflip: byte {pos} is in another field in the model"
    check (← boolF j "rej") "hflip: a changed head must be refused"
    pure st
  | _ => throw s!"unknown dtn seal event {e}"

end Vinc.TraceDtnSeal
