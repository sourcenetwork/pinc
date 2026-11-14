import Vinc.Json
import Vinc.HandshakeSys

/-!
# Replay of the handshake traces

The Lean half of the trace validation of `Initiator`, `Responder` and `ClientTickets`: it reads the `hs` events
written by the Rust test `trace_handshake` (one per step of either machine, and one per client-store operation) and
replays every step through the step functions of `Vinc.HandshakeModel` and `Vinc.HandshakeSys` (`INew`, `IHandle`,
`IKey`, `IRetransmit`, `IShed`, `RHandle`, `RKey`, `RRetransmit`, `RShed`, `CTake`, `CInsertAll`, `CExport`,
`KeepSeq`, `acceptTks`), which are the transcription of `proofs/tla/HsOps.tla`. It is the port of
`proofs/tla/TraceHandshake.tla`, operator by operator.

For each step the replay checks, against the model's result: the outcome (`ok`, `drop`, `fatal`), the events, the
number, type and length of the messages sent, the key request raised, and for an established session the peer, the
resumed flag, the ticket ids and the ALPN. An input message is the model message of an earlier output (found by
message id), or that message with the recorded field replaced by a value the attacker made (`forge`). The oracle
`om` is a bijection between the symbolic terms the code hashes or derives (ephemeral publics, prekey and its hash,
ciphertexts, transcript hashes, session keys) and their recorded ids: equal ids must be equal terms and equal terms
equal ids, so the code absorbs into each transcript exactly the fields the model does and both sides derive equal
keys exactly when the model says so. Ticket ids are the recorded ids themselves (the generator is the environment).
A world (`begin` event) starts from empty stores of the recorded capacities. A prekey reject is delivered after the
reject gap exactly when the recorded clock (whole seconds, the gap being 500 ms) moved on since the full Initial last
sent for a reject of that session (`rts`, as in TraceHandshake.tla).
-/

namespace Vinc.HandshakeTrace
open Vinc.Json Vinc.Hs Term

/-- The nodes of a world: the initiator's, and the two honest responders'; the third responder is the attacker's. -/
def iNode : Nat := 1
def r1 : Nat := 2
def r2 : Nat := 3
def rNode (rn : Nat) : Nat := if rn == 1 then r1 else if rn == 2 then r2 else att
def peerNode (c : String) : Nat := if c == "R1" then r1 else if c == "R2" then r2 else att

/-- A value no honest node makes: the "bad" field of a tampered message. -/
def badT : Term := junk 0 nil

/-- The model state of one world (the variables `ist rst sto cli snap msgs om inode rts` of TraceHandshake.tla). -/
structure W where
  ist : List (Nat × IState) := []
  rst : List ((Nat × Nat) × RState) := []
  sto : List (Nat × Store) := []
  cli : List Slot := []
  snap : List Tk := []
  msgs : List (Nat × Msg) := []
  om : List (Term × Int) := []
  inode : Nat := iNode
  /-- Per initiator session, the clock of the full Initial it last sent for a prekey reject. -/
  rts : List (Nat × Nat) := []

def W.getI (w : W) (s : Nat) : IState := (w.ist.lookup s).getD {}
def W.setI (w : W) (s : Nat) (st : IState) : W := { w with ist := (s, st) :: w.ist.filter (·.1 != s) }
def W.getR (w : W) (rn s : Nat) : RState := (w.rst.lookup (rn, s)).getD {}
def W.setR (w : W) (rn s : Nat) (st : RState) : W := { w with rst := ((rn, s), st) :: w.rst.filter (·.1 != (rn, s)) }
def W.getS (w : W) (rn : Nat) : Store := (w.sto.lookup rn).getD {}
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

/-- A tampered message (HsOps `Forge`): the original with the recorded field replaced by a value the attacker made. -/
def forge (b : Msg) (fld : String) (mid : Nat) : Except String Msg :=
  match fld with
  | "ver" => pure { b with ver := badT }
  | "al" => pure { b with al := badAlp }
  | "dc" => pure { b with dc := cid 3 att mid }
  | "sc" => pure { b with sc := cid 3 att mid }
  | "of" => pure { b with of := off att }
  | "cr" => pure { b with cr := crd att }
  | "e" => pure { b with e := pub ⟨4, att, mid⟩ }
  | "pk" => pure { b with pk := if b.form == .full then ek (1000000 + mid) else hash (ek (1000000 + mid)) }
  | "ct" => pure { b with ct := ct ⟨3, att, mid⟩ (ek att) }
  | "sealed" => pure { b with sealed := BadBlob }
  | "tid" => pure { b with tid := tidT (1000000 + mid) }
  | "binder" => pure { b with binder := badT }
  | "conf" => pure { b with conf := badT }
  | "tids" => pure { b with tids := [tidT (1000000 + mid)] }
  | "echo" => pure { b with echo := badT }
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

/-- TraceHandshake `TidsOK`: the model's ticket ids are the recorded ids. -/
def tidsOK (tids : List Term) (ids : List Nat) : Bool :=
  tids.length == ids.length && (tids.zip ids).all fun p => p.1 == tidT p.2

/-- TraceHandshake `HpkOf`. -/
def hpkOf (m : Msg) : Term := if m.form == .full then hash m.pk else m.pk

/-- TraceHandshake `MPairs`: the ids the code recorded for a message it sent, paired with the model terms. -/
def mpairs (m : Msg) (rec : J) : Except String (List (Term × Int)) := do
  let e ← intF rec "e"
  let c ← intF rec "ct"
  let echo ← intF rec "echo"
  let hpk ← intF rec "hpk"
  let pk ← intF rec "pk"
  pure ([(m.e, e), (m.ct, c), (m.echo, echo)] ++ (if m.ty == .init then [(hpkOf m, hpk), (m.pk, pk)] else []))

/-- TraceHandshake `MsgOK`. -/
def msgOK (m : Msg) (rec : J) : Except String Unit := do
  check ((← strF rec "ty") == tyName m.ty) s!"message type: model {tyName m.ty}, code {← strF rec "ty"}"
  if m.ty == .init || m.ty == .hello || m.ty == .rreply then
    check ((Int.ofNat m.len) == (← intF rec "len")) s!"message length: model {m.len}, code {← intF rec "len"}"
  if m.tid != nil then
    let t ← intF rec "tid"
    check (t ≥ 0 && m.tid == tidT t.toNat) "the ticket id of the message differs"
  if m.ty == .rreply then
    check (tidsOK m.tids (← natList (← field rec "tids"))) "the ticket ids of the reply differ"

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
  cid : Term
  early : Term
  tids : List Term
  al : Term

/-- TraceHandshake `ReqOf` for the initiator. -/
def reqI (old new : IState) : String :=
  if new.ph == .decap && old.ph != .decap then "decap" else if new.ph == .sign && old.ph != .sign then "sign" else "none"
/-- TraceHandshake `ReqOf` for the responder. -/
def reqR (old new : RState) : String := if new.ph == .sign && old.ph != .sign then "sign" else "none"

def viewI (old : IState) (r : IRes) : View :=
  { err := r.err, ev := r.ev, out := r.out, req := reqI old r.st, est := r.st.est, peer := r.st.peer,
    resumed := r.st.resumed, signTh := r.st.th4, send := r.st.send, recv := r.st.recv, res := r.st.res,
    cid := r.st.cid, early := r.st.early, tids := r.st.tids, al := r.st.al }
def viewR (old : RState) (r : RRes) : View :=
  { err := r.err, ev := r.ev, out := r.out, req := reqR old r.st, est := r.st.est, peer := r.st.peer,
    resumed := r.st.resumed, signTh := r.st.th2, send := r.st.send, recv := r.st.recv, res := r.st.res,
    cid := r.st.cid, early := r.st.early, tids := r.st.mytids, al := r.st.al }

/-- The ALPN index of a served ALPN (anything else cannot be an established session's). -/
def alpIdx : Term → Int
  | alp i => i
  | _ => -2

/-- TraceHandshake `StepOK`: every check of a step but the state update; returns the new oracle and message table.
`peer` is the node the established session must name. -/
def stepOK (ev : J) (w : W) (v : View) (peer : Nat) : Except String (List (Term × Int) × List (Nat × Msg)) := do
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
    check (v.est && v.peer == peer && v.resumed == (← boolF ev "resumed"))
      s!"the established session differs: peer {v.peer}, resumed {v.resumed}"
    check (tidsOK v.tids (← natList (← field ev "etids"))) "the ticket ids of the established session differ"
    check (alpIdx v.al == (← intF ev "alpn")) "the ALPN of the established session differs"
  else check ((← strF ev "op") == "start" || (← strF ev "peer") == "none") "a peer is reported without Established"
  let first? := match outs, v.out with | o :: _, m :: _ => some (o, m) | _, _ => none
  let p1 ← match first? with | some (o, m) => mpairs m o | none => pure []
  let p2 : List (Term × Int) ← if v.req == "sign" then do pure [(v.signTh, ← intF ev "rth")] else pure []
  let p3 : List (Term × Int) ←
    if est then do pure [(v.send, ← intF ev "send"), (v.recv, ← intF ev "recv"), (v.res, ← intF ev "rsm"), (v.cid, ← intF ev "cid")]
    else pure []
  let p4 : List (Term × Int) ← if v.ev.contains .early then do pure [(v.early, ← intF ev "early")] else pure []
  let some om' := foldOm w.om (p1 ++ p2 ++ p3 ++ p4) | throw "the recorded ids contradict the term oracle"
  match first? with
  | none => pure (om', w.msgs)
  | some (o, m) =>
    let mid ← natF o "mid"
    msgOK m o
    check (w.msgs.all fun p => (p.1 == mid) == (p.2 == m)) s!"message id {mid} is reused for a different message"
    pure (om', if w.msgs.any (·.1 == mid) then w.msgs else (mid, m) :: w.msgs)

/-! ## The store operations of the trace -/

/-- TraceHandshake `MarkExpired`: the ticket with this id passed its expiry. -/
def markExpired (sl : List Slot) (tid : Nat) : List Slot :=
  sl.map fun s => if s.occ && s.tid == tidT tid then { s with exp := true } else s

/-- TraceHandshake `DropIdx`: the indices of the entries of an export that are not among the kept ids. -/
def dropIdx (sq : List Tk) (kept : List Nat) : List Nat :=
  (List.range sq.length).filter fun j => match sq[j]? with
    | some t => !(kept.map tidT).contains t.tid
    | none => false

/-- The id draws of the ticket batch an established responder session issued: the recorded ids. -/
def drawsOf (etids : List Nat) : List (List Nat) := etids.map fun t => [t]

/-- TraceHandshake `SlotsOK`: the slot table of the ticket store of the responder's node after a step, as the code
holds it. Slot by slot the ticket id, and whether the code's clock passed the expiry (the expiry in seconds `sx`
against the time `ts` of the step), must be the model's; an empty slot is -1. -/
def slotsOK (sl : List Slot) (ev : J) : Except String Unit := do
  let slots ← intList (← field ev "slots")
  let sx ← intList (← field ev "sx")
  let ts ← intF ev "ts"
  check (slots.length == sl.length && sx.length == sl.length) "the slot table has another size than the model's"
  for (s, (id, x)) in sl.zip (slots.zip sx) do
    if s.occ then
      check (id ≥ 0 && s.tid == tidT id.toNat) "the ticket id of a slot differs from the model's"
      check (s.exp == decide (x < ts)) "the expiry of a slot differs from the model's"
    else check (id == -1 && x == -1) "a slot the model has empty holds a ticket"

/-- A resumed responder bounds the Reply it sends again for a full Initial under the answered ids by this many times
the Initial's length (`RInitial`); the code records the bound it computed, and -1 for any other message. -/
def resendFactor : Nat := 3

/-- TraceHandshake `CapOK`. -/
def capOK (old : RState) (ev : J) (m? : Option Msg) : Except String Unit := do
  let cap ← intF ev "rcap"
  match m? with
  | some m =>
    if m.ty == .init && old.ph == .resumed && old.dc == m.dc && old.sc == m.sc then
      check (cap == Int.ofNat resendFactor * (← intF ev "ilen")) s!"the bound on the repeated Reply is {cap}, not {resendFactor} times the Initial"
    else check (cap == -1) "a bound on a repeated Reply is reported for a message that has none"
  | none => check (cap == -1) "a bound on a repeated Reply is reported for a malformed message"

/-! ## Replaying one event -/

def replayEvent (ev : J) (w : W) : Except String W := do
  let op ← strF ev "op"
  match op with
  | "begin" =>
    let tk ← natF ev "tk"
    let ck ← natF ev "ck"
    let ia ← boolF ev "ia"
    let es : Store := { pkc := [], tks := List.replicate tk NoSlot }
    pure { sto := [(1, es), (2, es), (3, es)], cli := List.replicate ck NoSlot, inode := if ia then att else iNode }
  | "start" =>
    let s ← natF ev "s"
    let mode ← strF ev "mode"
    let peer := peerNode (← strF ev "peer")
    let al := alp (← natF ev "alpn")
    let c : CTakeRes := if (← boolF ev "take") then CTake w.cli peer al else ⟨w.cli, none⟩
    let r := INew w.inode s peer al (mode == "short") c.tk
    check ((w.getI s).ph == .none) "the session started twice"
    check ((mode == "resume") == c.tk.isSome) "resumption and the client store's ticket disagree"
    if let some tk := c.tk then
      let t ← intF ev "tid"
      check (t ≥ 0 && tk.tid == tidT t.toNat) "the ticket the client store gave is not the recorded one"
    let (om', msgs') ← stepOK ev w (viewI {} r) peer
    pure { (w.setI s r.st) with om := om', msgs := msgs', cli := c.sl }
  | "recv" =>
    let who ← strF ev "who"
    let s ← natF ev "s"
    check (← inputKnown w ev) "an input message that was never sent and is not marked malformed"
    let imal ← boolF ev "imal"
    if who == "I" then
      let old := w.getI s
      let ts ← natF ev "ts"
      -- a prekey reject is delivered after the gap when the clock moved on since the last full Initial for one
      let gapOver := (w.rts.lookup s).any (fun t => decide (t < ts))
      let m? ← if imal then pure none else do
        let m0 ← inputMsg w ev
        pure (some (if m0.ty == .prej then { m0 with gap := gapOver } else m0))
      let r := match m? with | some m => IHandle old w.inode m | none => Drop old
      let (om', msgs') ← stepOK ev w (viewI old r) old.peer
      let rts' := match m? with
        | some m => if m.ty == .prej && !r.out.isEmpty then (s, ts) :: w.rts.filter (·.1 != s) else w.rts
        | none => w.rts
      pure { (w.setI s r.st) with om := om', msgs := msgs', rts := rts' }
    else
      let rn ← natF ev "rn"
      let old := w.getR rn s
      let sto := w.getS rn
      let cs := drawsOf (← natList (← field ev "etids"))
      let m? ← if imal then pure none else do pure (some (← inputMsg w ev))
      let r := match m? with | some m => RHandle old (rNode rn) s sto m cs | none => RDrop old sto
      let (om', msgs') ← stepOK ev w (viewR old r) w.inode
      slotsOK r.sto.tks ev
      capOK old ev m?
      pure { ((w.setR rn s r.st).setS rn r.sto) with om := om', msgs := msgs' }
  | "key" =>
    let who ← strF ev "who"
    let s ← natF ev "s"
    let kind : KRes := if (← strF ev "kind") == "ok" then .ok else .fail
    if who == "I" then
      let old := w.getI s
      let r := IKey old w.inode kind
      let (om', msgs') ← stepOK ev w (viewI old r) old.peer
      pure { (w.setI s r.st) with om := om', msgs := msgs' }
    else
      let rn ← natF ev "rn"
      let old := w.getR rn s
      let sto := w.getS rn
      let r := RKey old (rNode rn) s sto kind
      let (om', msgs') ← stepOK ev w (viewR old r) w.inode
      slotsOK r.sto.tks ev
      pure { ((w.setR rn s r.st).setS rn r.sto) with om := om', msgs := msgs' }
  | "retx" =>
    let who ← strF ev "who"
    let s ← natF ev "s"
    if who == "I" then
      let old := w.getI s
      let r := IRetransmit w.inode old
      let (om', msgs') ← stepOK ev w (viewI old r) old.peer
      pure { (w.setI s r.st) with om := om', msgs := msgs' }
    else
      let rn ← natF ev "rn"
      let old := w.getR rn s
      let r := RRetransmit old (w.getS rn)
      let (om', msgs') ← stepOK ev w (viewR old r) w.inode
      slotsOK r.sto.tks ev
      pure { w with om := om', msgs := msgs' }
  | "shed" =>
    let who ← strF ev "who"
    let s ← natF ev "s"
    if who == "I" then pure (w.setI s (IShed (w.getI s)))
    else
      let rn ← natF ev "rn"
      pure (w.setR rn s (RShed (w.getR rn s)))
  | "accept" =>
    let s ← natF ev "s"
    let st := w.getI s
    let rr := w.getR (← natF ev "rn") (← natF ev "rs")
    let tids := if st.resumed then st.tids else rr.mytids
    check (st.ph == .done && (st.resumed || ((rr.ph == .done || rr.ph == .resumed) && rr.thf == st.thf)))
      "tickets accepted from a session that did not finish with the same transcript"
    check (tidsOK tids (← natList (← field ev "tids"))) "the accepted ticket ids differ from the session's"
    pure { w with cli := CInsertAll w.cli (acceptTks st tids) }
  | "expire" =>
    let tid ← natF ev "tid"
    if (← strF ev "scope") == "srv" then
      let rn ← natF ev "rn"
      let sto := w.getS rn
      pure (w.setS rn { sto with tks := markExpired sto.tks tid })
    else pure { w with cli := markExpired w.cli tid }
  | "export" =>
    let out := CExport w.cli (← natF ev "max")
    check (tidsOK (out.map (·.tid)) (← natList (← field ev "tids"))) "the exported tickets differ"
    pure { w with snap := out }
  | "restore" =>
    let kept ← natList (← field ev "kept")
    if (← boolF ev "ok") then
      let drop := dropIdx w.snap kept
      check ((← natF ev "stored") == kept.length) "the stored count differs from the kept entries"
      check (w.snap.length - drop.length == kept.length) "the entries kept by the restore differ from the model's"
      pure { w with cli := CInsertAll w.cli (KeepSeq w.snap drop 0) }
    else pure w
  | "restart" => pure { w with cli := List.replicate w.cli.length NoSlot }
  | _ => throw s!"unknown handshake op {op}"

end Vinc.HandshakeTrace
