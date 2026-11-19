import Pinc.Json
import Pinc.DtnCustody

/-!
# Replay of the store and custody traces

The replay half of the trace validation of the charged `Ledger` and the `CustodyBook` (the Rust tests
`trace_dtn_store` and `trace_dtn_custody`; the TLA+ halves are `TraceDtnStore.tla` and `TraceDtnCustody.tla`). Every
recorded call is replayed through the model functions the theorems are about (`Pinc.DtnStore.admitItem`, `expire`,
`release`, `reclass`, `accept`, `acceptDue`, `offer`, `onAck`, `delivered`, `bexpire`), with exact `u64` values, and any difference
exits with an error naming the line:

* `dl_new`, `dl_adm`, `dl_exp`, `dl_rel`, `dl_rec`: a plain ledger. The error of an admission, the evicted entries in
  order, the entry released, whether a reclass found its key, and after every call the kept entries in slot order and
  the bytes charged must be the model's.
* `cu_new`, `cu_acc`, `cu_off`, `cu_ack`, `cu_del`, `cu_exp`, `cu_hadm`, `cu_hexp`, `cu_hrel`: a book and its ledger.
  The same observations, plus the held bundles with the node each ack is owed to and the book's length. The offer id
  handed out by `offer` and the previous custodian and offer id of the answer an `accept` owes are recorded and
  checked (`acceptDue`); acks carry the offer id they name. The node an offer was made to and its id are not
  observable; the model has to reproduce them for the later acks to match.

An entry is `(space, id, bytes, class, expires)`; the admission number is not observable.
-/

namespace Pinc.TraceDtnStore
open Pinc.Json Pinc.DtnStore

/-- The replay state: the plain ledger of the current store run, and the book and ledger of the current custody run. -/
structure W where
  led : Ledger := Ledger.empty 0 0
  book : Recs := []
  nx : Nat := 0
  cl : Ledger := Ledger.empty 0 0

instance : Inhabited W := ⟨{}⟩

def isTag (t : String) : Bool := t.startsWith "dl_" || t.startsWith "cu_"

abbrev E := Nat × Nat × Nat × Nat × Nat

def proj (e : Entry) : E := (e.key.space, e.key.id, e.bytes, if e.cls == .custody then 0 else 1, e.expires)

def parseEnt (j : J) : Except String E :=
  do pure (← natF j "s", ← natF j "i", ← natF j "b", ← natF j "c", ← natF j "x")

def parseEnts (j : J) : Except String (List E) :=
  match j.arr? with
  | some a => a.toList.mapM parseEnt
  | none => throw "expected an array of entries"

def clsOf (c : Nat) : Class := if c == 0 then .custody else .transit

/-- After a call: the kept entries in slot order and the bytes charged are the model's. -/
def seen (j : J) (L : Ledger) : Except String Unit := do
  let snap ← parseEnts (← field j "snap")
  check (L.entries.map proj == snap) s!"kept entries: model {L.entries.map proj}, code {snap}"
  check (L.used == (← natF j "used")) s!"bytes charged: model {L.used}, code {← natF j "used"}"

def admErr : AErr → String
  | .dup => "dup" | .expired => "expired" | .custodyRefused => "cust" | .full => "full"

/-- Replay an admission on `L`; returns the new ledger. -/
def replayAdmit (j : J) (L : Ledger) : Except String Ledger := do
  let r := admitItem L ⟨← natF j "s", ← natF j "i"⟩ (← natF j "b") (clsOf (← natF j "c")) (← natF j "x") (← natF j "now")
  let err := match r.err with | none => "ok" | some e => admErr e
  check (err == (← strF j "err")) s!"admitItem: model {err}, code {← strF j "err"}"
  check (r.ev.map proj == (← parseEnts (← field j "ev"))) "admitItem: the evicted entries differ from the model's"
  seen j r.L
  pure r.L

def replayExpire (j : J) (L : Ledger) : Except String Ledger := do
  let r := expire L (← natF j "now")
  check (r.2.map proj == (← parseEnts (← field j "ev"))) "expire: the evicted entries differ from the model's"
  seen j r.1
  pure r.1

def replayRelease (j : J) (L : Ledger) : Except String Ledger := do
  let r := release L ⟨← natF j "s", ← natF j "i"⟩
  let got ← boolF j "got"
  check (r.2.isSome == got) s!"release: model {r.2.isSome}, code {got}"
  if got then
    check (r.2.map proj == some (← parseEnt (← field j "e"))) "release: the entry differs from the model's"
  seen j r.1
  pure r.1

/-- The book's observable state: the held bundles with the node each ack is owed to, and the length. -/
def bookSeen (j : J) (B : Recs) : Except String Unit := do
  let held ← (← field j "held").arr?.getD #[] |>.toList.mapM natList
  let mine := (recs B).map (fun r => [r.bundle, r.previous]) |>.mergeSort (fun a b => decide (a.headD 0 ≤ b.headD 0))
  let theirs := held.mergeSort (fun a b => decide (a.headD 0 ≤ b.headD 0))
  check (mine == theirs) s!"held bundles: model {mine}, code {theirs}"
  check ((recs B).length == (← natF j "blen")) s!"book length: model {(recs B).length}, code {← natF j "blen"}"

def cerrName : CErr → String
  | .store .custodyRefused => "cust" | .store .full => "full" | .store .dup => "dup" | .store .expired => "expired" | .storeUnknown => "storeunknown"
  | .ack => "ack" | .capacity => "cap" | .unknown => "unknown" | .notOffered => "notoffered"

def cuSeen (j : J) (o : COut) : Except String Unit := do
  let err := match o.err with | none => "ok" | some e => cerrName e
  check (err == (← strF j "err")) s!"{← strF j "t"}: model {err}, code {← strF j "err"}"
  seen j o.L
  bookSeen j o.B

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "dl_new" => pure { w with led := Ledger.empty (← natF j "budget") (← natF j "n") }
  | "dl_adm" => pure { w with led := ← replayAdmit j w.led }
  | "dl_exp" => pure { w with led := ← replayExpire j w.led }
  | "dl_rel" => pure { w with led := ← replayRelease j w.led }
  | "dl_rec" =>
    let r := reclass w.led ⟨← natF j "s", ← natF j "i"⟩ (clsOf (← natF j "c"))
    check (r.2 == (← boolF j "ok")) s!"reclass: model {r.2}, code {← boolF j "ok"}"
    seen j r.1
    pure { w with led := r.1 }
  | "cu_new" => pure { w with book := List.replicate (← natF j "n") none, nx := 0, cl := Ledger.empty (← natF j "budget") (← natF j "ln") }
  | "cu_acc" =>
    let o := accept w.book w.cl (← natF j "b") (← natF j "by") (← natF j "x") (← natF j "p") (← natF j "now")
    check (o.ev.map proj == (← parseEnts (← field j "ev"))) "accept: the evicted entries differ from the model's"
    -- the answer owed: the previous custodian and the offer id of the INCOMING offer, on success only
    let due := acceptDue (← natF j "p") (← natF j "o") o
    check (due.isSome == (← boolF j "due")) s!"accept: model {due}, code {← boolF j "due"}"
    let dueRec := (← boolF j "due")
    let ap ← natF j "ap"
    let ao ← natF j "ao"
    let recorded : Option (Nat × Nat) := if dueRec then some (ap, ao) else none
    check (due == recorded) "accept: the answer owed differs"
    cuSeen j o
    pure { w with book := o.B, cl := o.L }
  | "cu_off" =>
    let r := offer w.book w.nx (← natF j "b") (← natF j "to")
    let err := match r.err with | none => "ok" | some _ => "unknown"
    check (err == (← strF j "err")) s!"offer: model {err}, code {← strF j "err"}"
    check (r.err.isSome || r.id == (← natF j "id")) s!"offer: model id {r.id}, code {← natF j "id"}"
    bookSeen j r.B
    pure { w with book := r.B, nx := r.nx }
  | "cu_ack" =>
    let o := onAck w.book w.cl (← natF j "b") (← natF j "c") (← natF j "o") (← boolF j "v")
    cuSeen j o
    pure { w with book := o.B, cl := o.L }
  | "cu_del" =>
    let o := delivered w.book w.cl (← natF j "b")
    cuSeen j o
    pure { w with book := o.B, cl := o.L }
  | "cu_exp" =>
    let o := bexpire w.book w.cl (← natF j "now")
    check (o.ev.map proj == (← parseEnts (← field j "ev"))) "book expire: the evicted entries differ from the model's"
    seen j o.L
    bookSeen j o.B
    pure { w with book := o.B, cl := o.L }
  | "cu_hadm" =>
    let L ← replayAdmit j w.cl
    bookSeen j w.book
    pure { w with cl := L }
  | "cu_hexp" =>
    let L ← replayExpire j w.cl
    bookSeen j w.book
    pure { w with cl := L }
  | "cu_hrel" =>
    let L ← replayRelease j w.cl
    bookSeen j w.book
    pure { w with cl := L }
  | t => throw s!"unknown event {t}"

end Pinc.TraceDtnStore
