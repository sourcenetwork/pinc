import Pinc.Json
import Pinc.TicketsExport
import Pinc.PrekeyCache

/-!
# Replay of the store traces

The replay half of the trace validation of `ClientTickets`, `ServerTickets` and `PrekeyCache` (the Rust test
`trace_stores`, the TLA+ half is `TraceStores.tla`). Every recorded call is replayed through the Lean functions the
theorems are about and any difference exits with an error naming the line:

* `cacc` / `cbad` / `ctake` / `cexp` / `cres`: `Tickets.acceptBatch`, `Tickets.cTake`, `Tickets.exportBytes` (the bytes
  must be those `export` wrote, byte for byte) and `Tickets.restore` (which decodes the recorded bytes itself) on the
  model store of the run. After every call the model's whole content (`exportList` of all tickets, oldest first) must
  equal the content read back from the real store, and the lengths must agree.
* `siss`: `Tickets.issueBatch` with the recorded draws of the generator as the environment.
* `pget` / `pins`: `PrekeyCache.get` / `PrekeyCache.insert`.

Byte strings are ids; the `idef` lines give the bytes of each id.
-/

namespace Pinc.TraceStores
open Pinc.Json Pinc.Tickets

/-- The model state: the id table, the client store, the server store, the prekey cache. -/
structure W where
  defs : Std.HashMap Nat (Nat × List Nat) := {}
  cl : Store := Store.empty 0
  sv : Store := Store.empty 0
  pc : PrekeyCache.Cache := PrekeyCache.Cache.empty 0

instance : Inhabited W := ⟨{}⟩

def hexVal (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
  else throw s!"bad hex digit {c}"

def hexBytes (s : String) : Except String (List Nat) := do
  let rec go : List Char → Except String (List Nat)
    | [] => pure []
    | [_] => throw "odd hex length"
    | a :: b :: r => do
      let v := (← hexVal a) * 16 + (← hexVal b)
      pure (v :: (← go r))
  go s.toList

def lookup (w : W) (id : Nat) : Except String (Nat × List Nat) :=
  match w.defs[id]? with
  | some v => pure v
  | none => throw s!"id {id} has no idef"

/-- A ticket from its recorded ids. -/
def mkTk (w : W) (j : J) : Except String Tk := do
  let (alg, node) ← lookup w (← natF j "p")
  let (_, alpn) ← lookup w (← natF j "a")
  let (_, tid) ← lookup w (← natF j "t")
  let (_, psk) ← lookup w (← natF j "s")
  let (_, credit) ← lookup w (← natF j "cr")
  pure ⟨⟨alg, node⟩, alpn, tid, psk, ← natF j "ae", ← natF j "x", credit⟩

def mkTks (w : W) (j : J) : Except String (List Tk) := do
  match j.arr? with
  | some a => a.toList.mapM (mkTk w)
  | none => throw "expected an array of tickets"

/-- After a client call: the model's content oldest first equals the real store's, and the lengths agree. -/
def clientSeen (w : W) (j : J) (st : Store) : Except String Unit := do
  let snap ← mkTks w (← field j "snap")
  let mine := exportList st.slots 0 st.slots.length
  check (decide (mine = snap)) s!"store content: model has {mine.length} tickets, code {snap.length} (or they differ)"
  check (occ st.slots == (← natF j "len")) s!"store length: model {occ st.slots}, code {← natF j "len"}"

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "idef" =>
    let id ← natF j "id"
    let bytes ← hexBytes (← strF j "b")
    pure { w with defs := w.defs.insert id (← natF j "alg", bytes) }
  | "cnew" => pure { w with cl := Store.empty (← natF j "n") }
  | "cacc" =>
    let now ← natF j "now"
    let bs ← match (← field j "b").arr? with | some a => pure a.toList | none => throw "b"
    let mut tks : List Tk := []
    for e in bs do
      let t ← mkTk w e
      check (t.expiry == expiryOf now (← natF e "lf")) s!"expiry {t.expiry} is not now {now} plus the lifetime"
      tks := tks ++ [t]
    let st := acceptBatch w.cl tks now
    clientSeen w j st
    pure { w with cl := st }
  | "cbad" => do clientSeen w j w.cl; pure w
  | "ctake" =>
    let (alg, node) ← lookup w (← natF j "p")
    let (_, alpn) ← lookup w (← natF j "a")
    let (st, r) := cTake w.cl ⟨alg, node⟩ alpn (← natF j "now")
    match ← boolF j "got" with
    | true =>
      let e ← mkTk w (← field j "e")
      check (r == some e) "take returned a different ticket than the model"
    | false => check r.isNone "take returned a ticket where the model finds none"
    clientSeen w j st
    pure { w with cl := st }
  | "cexp" =>
    let r := exportBytes w.cl.slots (← natF j "now") (← natF j "max") (← natF j "cap")
    match ← boolF j "ok" with
    | true =>
      let bytes ← hexBytes (← strF j "blob")
      check (match r with | .ok b => b == bytes | .error _ => false) "export bytes differ from the model's encoding"
      check (decode bytes == some (← mkTks w (← field j "b"))) "the exported entries differ from the recorded ones"
    | false => check (match r with | .error _ => true | .ok _ => false) "export failed in the code, the model fits the buffer"
    clientSeen w j w.cl
    pure w
  | "cres" =>
    let bytes ← hexBytes (← strF j "blob")
    let now ← natF j "now"
    let (st, n) := restore w.cl bytes now
    let rec_n ← intF j "n"
    match ← boolF j "ok" with
    | true =>
      check (n == some rec_n.toNat && rec_n ≥ 0) s!"restore count: model {n}, code {rec_n}"
      let ents ← mkTks w (← field j "b")
      check (decode bytes == some ents) "the decoded state differs from the recorded entries"
    | false =>
      check (n.isNone && rec_n < 0) "restore accepted a state the code rejected, or the other way round"
      check (decode bytes).isNone "decode accepts a state the code rejected"
    clientSeen w j st
    pure { w with cl := st }
  | "snew" => pure { w with sv := Store.empty (← natF j "n") }
  | "siss" =>
    let ds ← natList (← field j "draws")
    let draw : Nat → Option (List Nat) := fun p => (ds[p]?).map fun d => [d]
    let now ← natF j "now"
    let life ← natF j "lf"
    let mk : List Nat → Tk := fun tid => ⟨⟨0, []⟩, [], tid, [], 0, expiryOf now life, []⟩
    let (st, r) := issueBatch w.sv mk now draw (← natF j "cnt")
    match ← boolF j "ok" with
    | true =>
      let b ← natList (← field j "batch")
      check (match r with | .ok ids => ids == b.map fun d => [d] | .error _ => false) "issued batch differs from the model"
    | false =>
      check (match r with | .error .ticketId => true | _ => false) "issue_batch failed in the code, not in the model (or not with the ticket id failure)"
    check (occ st.slots == (← natF j "len")) s!"server store length: model {occ st.slots}, code {← natF j "len"}"
    pure { w with sv := st }
  | "pnew" => pure { w with pc := PrekeyCache.Cache.empty (← natF j "n") }
  | "pget" =>
    let (st, r) := PrekeyCache.get w.pc [← natF j "h"]
    match ← boolF j "hit" with
    | true => check (r == some (← natF j "v")) s!"cache get: model {r}, code hit with {← natF j "v"}"
    | false => check r.isNone "cache get hit in the model, miss in the code"
    check (PrekeyCache.occE st.slots == (← natF j "len")) "cache length"
    pure { w with pc := st }
  | "pins" =>
    let st := PrekeyCache.insert w.pc [← natF j "h"] (← natF j "v")
    check (PrekeyCache.occE st.slots == (← natF j "len")) s!"cache length after insert: model {PrekeyCache.occE st.slots}, code {← natF j "len"}"
    pure { w with pc := st }
  | t => throw s!"unknown store event {t}"

/-- The tags this module replays. -/
def isStoreTag (t : String) : Bool :=
  ["idef", "cnew", "cacc", "cbad", "ctake", "cexp", "cres", "snew", "siss", "pnew", "pget", "pins"].contains t

end Pinc.TraceStores
