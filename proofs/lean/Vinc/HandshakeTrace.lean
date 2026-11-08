import Vinc.Json
import Vinc.HandshakeModel

/-!
# Replay of the handshake traces

The Lean half of the trace validation of `Initiator` and `Responder`: it reads the `hs` events written by the Rust
test `trace_handshake` (one per step of either machine, see `tests/trace_handshake.rs`) and replays every step
through the step functions of `Vinc.HandshakeModel` (`IBeginFull`, `IBeginResume`, `IHandle`, `IKey`, `RHandle`,
`RKey`), which are the transcription of `proofs/tla/HsOps.tla`. It is the port of `proofs/tla/TraceHandshake.tla`.

For each step the replay checks, against the model's result: the outcome (`ok`, `drop`, `fatal`), the events, the
number and type of the messages sent, the key request raised, and for an established session the peer and the
resumed flag. An input message is the model message of an earlier output (found by message id), or that message
with the recorded field replaced by a value the attacker made (`forge`). The oracle `om` is a bijection between the
symbolic terms the code hashes or derives (ephemeral publics, prekey and its hash, ciphertexts, transcript hashes,
ticket ids, keys) and their recorded ids: equal ids must be equal terms and equal terms equal ids, so the code
absorbs into each transcript exactly the fields the model does and both sides derive equal keys exactly when the
model says so. A world (`begin` event) starts from empty stores.
-/

namespace Vinc.HandshakeTrace
open Vinc.Json Vinc.Hs

/-- The nodes of a world: the initiator's, and the two responders'. -/
def iNode : Nat := 1
def r1 : Nat := 2
def r2 : Nat := 3
def rNode (rn : Nat) : Nat := if rn == 1 then r1 else r2

/-- The ticket slots of a recorded responder store (the real store never evicts in these runs). -/
def emptyStore : Store := { pkc := [], tks := List.replicate 16 NoSlot, clk := 0 }

/-- The model state of one world. -/
structure W where
  ist : List (Nat × IState) := []
  rst : List ((Nat × Nat) × RState) := []
  sto : List (Nat × Store) := []
  cli : List Tk := []
  msgs : List (Nat × Msg) := []
  om : List (Term × Int) := []

def W.getI (w : W) (s : Nat) : IState := (w.ist.lookup s).getD {}
def W.setI (w : W) (s : Nat) (st : IState) : W := { w with ist := (s, st) :: w.ist.filter (·.1 != s) }
def W.getR (w : W) (rn s : Nat) : RState := (w.rst.lookup (rn, s)).getD {}
def W.setR (w : W) (rn s : Nat) (st : RState) : W := { w with rst := ((rn, s), st) :: w.rst.filter (·.1 != (rn, s)) }
def W.getS (w : W) (rn : Nat) : Store := (w.sto.lookup rn).getD emptyStore
def W.setS (w : W) (rn : Nat) (st : Store) : W := { w with sto := (rn, st) :: w.sto.filter (·.1 != rn) }

/-! ## The oracle -/

def consistent (o : List (Term × Int)) (t : Term) (id : Int) : Bool :=
  if o.any (fun p => p.1 == t || p.2 == id) then o.contains (t, id) else true

/-- Fold `(term, id)` pairs into the oracle; `none` if one contradicts it. Negative ids mean "not recorded". -/
def foldOm (o : List (Term × Int)) : List (Term × Int) → Option (List (Term × Int))
  | [] => some o
  | (t, id) :: r =>
    if id < 0 then foldOm o r
    else if consistent o t id then foldOm (if o.contains (t, id) then o else (t, id) :: o) r
    else none

/-! ## Messages -/

def tyName : MTy → String
  | .init => "Init" | .prej => "PRej" | .reply => "Reply" | .fin => "Fin"
  | .hello => "Hello" | .rreply => "RReply" | .rrej => "RRej" | .nil => "None"

def evName : Ev → String
  | .early => "early" | .est => "est" | .rejected => "rejected" | .failed => "failed"

def errName : Err → String
  | .ok => "ok" | .drop => "drop" | .fatal => "fatal"

/-- A tampered message: the original with the recorded field replaced by a value the attacker made. -/
def forge (b : Msg) (fld : String) (mid : Nat) : Except String Msg :=
  match fld with
  | "prm" => pure { b with prm := Term.bad }
  | "e" => pure { b with e := Term.pub ⟨4, att, mid⟩ }
  | "pk" => pure { b with pk := if b.form == .full then Term.ek (1000000 + mid) else Term.hash (Term.ek (1000000 + mid)) }
  | "ct" => pure { b with ct := Term.ct ⟨3, att, mid⟩ att }
  | "sealed" => pure { b with sealed := BadBlob }
  | "tid" => pure { b with tid := Term.tid 1000000 mid }
  | "binder" => pure { b with binder := Term.bad }
  | "conf" => pure { b with conf := Term.bad }
  | "tids" => pure { b with tids := Term.one (Term.tid 1000000 mid) }
  | "rprm" => pure { b with rprm := Term.bad }
  | "echo" => pure { b with echo := Term.bad }
  | _ => throw s!"unknown tampered field {fld}"

def msgOf (w : W) (mid : Int) : Except String Msg :=
  match mid with
  | .ofNat n => match w.msgs.lookup n with
    | some m => pure m
    | none => throw s!"message id {mid} was never sent"
  | _ => throw s!"bad message id {mid}"

def inputMsg (w : W) (ev : J) : Except String Msg := do
  let ibase ← intF ev "ibase"
  let imid ← natF ev "imid"
  if ibase == -1 then msgOf w imid else forge (← msgOf w ibase) (← strF ev "ifld") imid

def inputKnown (w : W) (ev : J) : Except String Bool := do
  let ibase ← intF ev "ibase"
  let imid ← natF ev "imid"
  let imal ← boolF ev "imal"
  pure (imal || (if ibase == -1 then w.msgs.any (·.1 == imid)
                 else match ibase with | .ofNat b => w.msgs.any (·.1 == b) | _ => false))

/-- The ids the code recorded for a message it sent, paired with the model terms. -/
def mpairs (m : Msg) (rec : J) : Except String (List (Term × Int)) := do
  let tids ← (← field rec "tids").arr?.elim (throw "tids is not an array")
    (fun a => a.toList.mapM fun v => match v.int? with | some n => pure n | none => throw "tid is not a number")
  let ts := tidsList m.tids
  check (ts.length == tids.length) s!"the message carries {ts.length} tickets in the model, {tids.length} recorded"
  let e ← intF rec "e"
  let c ← intF rec "ct"
  let t ← intF rec "tid"
  let echo ← intF rec "echo"
  let hpk ← intF rec "hpk"
  let pk ← intF rec "pk"
  pure ([(m.e, e), (m.ct, c), (m.tid, t), (m.echo, echo)]
        ++ (if m.ty == .init then [(rHpk m, hpk), (m.pk, pk)] else [])
        ++ ts.zip tids)

/-! ## The checks common to every step -/

/-- What a step of either machine reports, in one shape. -/
structure View where
  err : Err
  ev : List Ev
  out : List Msg
  req : String
  est : Bool
  peer : Nat
  resumed : Bool
  signTh : Term
  send : Term
  recv : Term
  res : Term
  early : Term
  tidTerms : List Term
  isI : Bool

def reqI (old new : IState) : String :=
  if new.ph == .decap && old.ph != .decap then "decap" else if new.ph == .sign && old.ph != .sign then "sign" else "none"
def reqR (old new : RState) : String := if new.ph == .sign && old.ph != .sign then "sign" else "none"

def viewI (old : IState) (r : IRes) : View :=
  { err := r.err, ev := r.ev, out := r.out, req := reqI old r.st, est := r.st.est, peer := r.st.peer,
    resumed := r.st.resumed, signTh := r.st.th4, send := r.st.send, recv := r.st.recv, res := r.st.res,
    early := r.st.early, tidTerms := tidsList r.st.tids, isI := true }
def viewR (old : RState) (r : RRes) : View :=
  { err := r.err, ev := r.ev, out := r.out, req := reqR old r.st, est := r.st.est, peer := r.st.peer,
    resumed := r.st.resumed, signTh := r.st.th2, send := r.st.send, recv := r.st.recv, res := r.st.res,
    early := r.st.early, tidTerms := [r.st.mytid], isI := false }

/-- Every check of a step but the state update: returns the new oracle and message table. -/
def stepOK (ev : J) (w : W) (v : View) : Except String (List (Term × Int) × List (Nat × Msg)) := do
  check (errName v.err == (← strF ev "res")) s!"outcome: model {errName v.err}, code {← strF ev "res"}"
  let evs ← (← field ev "evs").arr?.elim (throw "evs is not an array") (fun a => a.toList.mapM fun x => match x.str? with
    | some s => pure s | none => throw "event is not a string")
  let mev := v.ev.map evName
  check (evs.all mev.contains && mev.all evs.contains) s!"events: model {mev}, code {evs}"
  let outs ← (← field ev "outs").arr?.elim (throw "outs is not an array") (fun a => pure a.toList)
  check (outs.length == v.out.length) s!"messages sent: model {v.out.length}, code {outs.length}"
  check (v.req == (← strF ev "req")) s!"key request: model {v.req}, code {← strF ev "req"}"
  let est := v.ev.contains .est
  if est then
    check (v.est && v.peer == (if v.isI then r1 else iNode) && v.resumed == (← boolF ev "resumed"))
      s!"the established session differs: peer {v.peer}, resumed {v.resumed}"
    let n := (← natList (← field ev "etids")).length
    check (n == (if v.isI then v.tidTerms.length else 1)) "the ticket count of the established session differs"
  else check ((← strF ev "peer") == "none") "a peer is reported without Established"
  let first? := match outs, v.out with | o :: _, m :: _ => some (o, m) | _, _ => none
  let p1 ← match first? with | some (o, m) => mpairs m o | none => pure []
  let rth ← intF ev "rth"
  let send ← intF ev "send"
  let recv ← intF ev "recv"
  let rsm ← intF ev "rsm"
  let early ← intF ev "early"
  let etids ← natList (← field ev "etids")
  let p2 : List (Term × Int) := if v.req == "sign" then [(v.signTh, rth)] else []
  let p3 : List (Term × Int) := if est then [(v.send, send), (v.recv, recv), (v.res, rsm)] else []
  let p4 : List (Term × Int) := if v.ev.contains .early then [(v.early, early)] else []
  let p5 : List (Term × Int) := if est then v.tidTerms.zip (etids.map Int.ofNat) else []
  let some om' := foldOm w.om (p1 ++ p2 ++ p3 ++ p4 ++ p5) | throw "the recorded ids contradict the term oracle"
  match first? with
  | none => pure (om', w.msgs)
  | some (o, m) =>
    let mid ← natF o "mid"
    check ((← strF o "ty") == tyName m.ty) s!"message type: model {tyName m.ty}"
    check (w.msgs.all fun p => (p.1 == mid) == (p.2 == m)) s!"message id {mid} is reused for a different message"
    pure (om', if w.msgs.any (·.1 == mid) then w.msgs else (mid, m) :: w.msgs)

/-! ## Replaying one event -/

def replayEvent (ev : J) (w : W) : Except String W := do
  let op ← strF ev "op"
  if op == "begin" then return {}
  match op with
  | "start" =>
    let s ← natF ev "s"
    let mode ← strF ev "mode"
    check ((w.getI s).ph == .none) "the session started twice"
    let x := atom 0 iNode s
    let (r, cli') ← if mode == "resume" then do
        let tid ← intF ev "tid"
        match w.cli.find? (fun t => w.om.contains (t.tid, tid)) with
        | some tk => pure (IBeginResume iNode x tk, w.cli.erase tk)
        | none => throw "resumption with a ticket the client does not hold"
      else pure (IBeginFull iNode x r1 (mode == "short") Term.nil Term.nil, w.cli)
    let (om', msgs') ← stepOK ev w (viewI {} r)
    pure { (w.setI s r.st) with om := om', msgs := msgs', cli := cli' }
  | "recv" =>
    let who ← strF ev "who"
    let s ← natF ev "s"
    let known ← inputKnown w ev
    check known "an input message that was never sent and is not marked malformed"
    let imal ← boolF ev "imal"
    if who == "I" then
      let old := w.getI s
      let r ← if imal then pure (Drop old) else do pure (IHandle old iNode (← inputMsg w ev))
      let (om', msgs') ← stepOK ev w (viewI old r)
      pure { (w.setI s r.st) with om := om', msgs := msgs' }
    else
      let rn ← natF ev "rn"
      let old := w.getR rn s
      let sto := w.getS rn
      let r ← if imal then pure (RDrop old sto) else do pure (RHandle old (rNode rn) s sto (← inputMsg w ev))
      let (om', msgs') ← stepOK ev w (viewR old r)
      pure { ((w.setR rn s r.st).setS rn r.sto) with om := om', msgs := msgs' }
  | "key" =>
    let who ← strF ev "who"
    let s ← natF ev "s"
    let kind : KRes := if (← strF ev "kind") == "ok" then .ok else .fail
    if who == "I" then
      let old := w.getI s
      let r := IKey old iNode kind
      let (om', msgs') ← stepOK ev w (viewI old r)
      pure { (w.setI s r.st) with om := om', msgs := msgs' }
    else
      let rn ← natF ev "rn"
      let old := w.getR rn s
      let sto := w.getS rn
      let r := RKey old (rNode rn) s sto kind
      let (om', msgs') ← stepOK ev w (viewR old r)
      pure { ((w.setR rn s r.st).setS rn r.sto) with om := om', msgs := msgs' }
  | "accept" =>
    let s ← natF ev "s"
    let st := w.getI s
    let rr := w.getR (← natF ev "rn") (← natF ev "rs")
    let some tid := if st.resumed then (tidsList st.tids).head? else some rr.mytid | throw "no ticket to accept"
    check (st.ph == .done && (st.resumed || (rr.ph == .done && rr.thf == st.thf)))
      "tickets accepted from a session that did not finish with the same transcript"
    let some om' := foldOm w.om [(tid, ← intF ev "tid")] | throw "the ticket id contradicts the term oracle"
    pure { w with om := om', cli := ⟨tid, Term.psk st.res tid, st.peer⟩ :: w.cli }
  | _ => throw s!"unknown handshake op {op}"

end Vinc.HandshakeTrace
