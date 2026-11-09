import Vinc.DtnForwardWitness
import Vinc.DtnCustodySys

/-!
# Scenarios: many nodes, each a forwarder, a custody book and a ledger, joined by a network

The system model of `proofs/tla/DtnScenario.tla` for any number of nodes. A node is the forwarder of
`Vinc.DtnForward` (`vinc-dtn/src/forward.rs`), the custody book and the charged ledger of `Vinc.DtnStore`
(`custody.rs`, `store.rs`); the system adds only the host glue, which the Rust test `tests/trace_dtn_scenario.rs`
implements with the real crate types:

* a contact `a < b` sets the link of each side; a tick advances every forwarder to `t + 1` and then every book
  expires its ledger at `t + 1`;
* a poll that sends makes a network message; a handover of copies that is not a retransmission is offered custody
  (`offer`) when `offerable`; a poll that releases calls `delivered` on the book;
* a bundle message reaching the destination is a delivery and is answered by an ack; at a relay the book accepts
  custody (the ledger may refuse: the copies are dropped and nothing is answered), then the forwarder holds the copies
  (a repeated hold ignores them) and an ack is answered; an ack at its addressee is `Acked` to the forwarder and
  `on_ack` to the book (the signature check is the boolean `valid = true`; an ack that fails it moves nothing: the
  `bad` event);
* a message may be lost; the mailbox layer may add an item to the shared ledger (`press`), and a bundle it evicts is
  forgotten by the forwarder.

The model has any list of node ids (`Cfg.ids`, without repeats), so every theorem is for every number of nodes and every
capacity. Ghost variables (not in the code) count the copies dropped (`dropped`) and released (`released`), and record
`delivered` (the destination received the bundle), `replayed` (a retransmitted hold was accepted: possible only after
the first copy of the message was lost, since a node that held or finished the bundle refuses the hold,
`DtnForwardWitness`), `acc` (the nodes that accepted custody) and `fin` (a node was told of the delivery by an ack).

The custody part of every node evolves only through `Vinc.DtnStore.step` (`ledgerEv`), so the single-node theorems of
`DtnCustodySys` hold at every node of every reachable system (`DtnScenarioNode`).
-/

namespace Vinc.DtnScenario

open Vinc.DtnForward (F Input Err Act)

/-- The constants of a system. Node ids are the numbers of `ids`; `src` creates the bundle (id 1) and `dest` is its
destination. `tight` is the node whose ledger has no room (0: none). `ranked`: custody is offered only to a higher id. -/
structure Cfg where
  ids : List Nat
  src : Nat
  dest : Nat
  copies : Nat
  exp : Nat
  retry : Nat
  maxSends : Nat
  fb : Nat
  fl : Nat
  ft : Nat
  fd : Nat
  lbud : Nat
  lslots : Nat
  bslots : Nat
  tight : Nat
  pb : Nat
  ranked : Bool

/-- The bundle all of this is about. -/
def bid : Nat := 1

/-- One node. -/
structure Node where
  f : F
  B : DtnStore.Recs
  L : DtnStore.Ledger
  /-- The book's offer counter (`next_offer`). -/
  nx : Nat

/-- A network message: a bundle message (`fresh` unless it is a retransmission) or a custody ack. -/
inductive Msg where
  | bun (id from_ to copies : Nat) (fresh : Bool) (off : Nat)
  | ack (id from_ to off : Nat)
  deriving DecidableEq, Repr

/-- The message id (unique: the sequence number at creation). -/
def Msg.id : Msg → Nat
  | .bun id .. => id
  | .ack id .. => id

/-- The whole system. -/
structure Sys where
  cfg : Cfg
  nodes : Nat → Node
  msgs : List Msg
  t : Nat
  seq : Nat
  /-- The host's memory of the offer id last made by a node to each peer, repeated by a retransmission. -/
  lo : Nat → Nat → Nat
  dropped : Nat
  released : Nat
  delivered : Bool
  replayed : Bool
  fin : Bool
  acc : List Nat

/-- The events of the network and the host. -/
inductive Ev where
  | contact (a b : Nat) (up : Bool)
  | tick
  | poll (n : Nat)
  | bun (m : Msg)
  | ack (m : Msg)
  | lose (m : Msg)
  | press (n k : Nat)
  | bad

/-- A node with nothing in it. -/
def Node.empty (c : Cfg) (n : Nat) : Node :=
  ⟨F.new c.retry c.maxSends 0 c.fb c.fl c.ft c.fd, List.replicate c.bslots none,
   DtnStore.Ledger.empty (if n = c.tight then 0 else c.lbud) c.lslots, 0⟩

/-- The origin accepts custody (previous node 0) and holds the copies. -/
def originAcc (c : Cfg) : DtnStore.COut :=
  DtnStore.accept (Node.empty c c.src).B (Node.empty c c.src).L bid 1 c.exp 0 0

def originHold (c : Cfg) : F × Err :=
  DtnForward.step (Node.empty c c.src).f 0 (.hold bid c.dest c.exp c.copies)

/-- Whether custody of a handover from `n` to `p` is offered. -/
def offerable (c : Cfg) (n p : Nat) : Bool := if c.ranked then decide (n < p) else true

/-- The initial system: the origin holds the bundle. -/
def Sys.init (c : Cfg) : Sys where
  cfg := c
  nodes := fun n =>
    if n = c.src then ⟨(originHold c).1, (originAcc c).B, (originAcc c).L, 0⟩ else Node.empty c n
  msgs := []
  t := 0
  seq := 0
  lo := fun _ _ => 0
  dropped := 0
  released := 0
  delivered := false
  replayed := false
  fin := false
  acc := [c.src]

/-- Replace one node. -/
def Sys.set (s : Sys) (n : Nat) (x : Node) : Sys :=
  { s with nodes := fun m => if m = n then x else s.nodes m }

/-- Whether some forwarder of the system holds a bundle that knows it was delivered. -/
def Sys.anyFlag (s : Sys) : Bool :=
  s.cfg.ids.any fun n => (s.nodes n).f.bs.any fun o => o.any (·.delivered)

/-- The `DtnStore` event a system event applies to node `n`'s book and ledger, if any. -/
def ledgerEv (s : Sys) : Ev → Nat → Option DtnStore.Ev
  | .tick, _ => some (.bexpire (s.t + 1))
  | .poll n, m =>
    if m = n then
      match DtnForward.poll (s.nodes n).f with
      | (_, .send p _ c r) => if c > 0 && !r && offerable s.cfg n p then some (.offer bid p) else none
      | (_, .release _) => some (.delivered bid)
      | _ => none
    else none
  | .bun (.bun _ from_ r _ _ _), m =>
    if m = r ∧ r ≠ s.cfg.dest then some (.accept bid 1 s.cfg.exp from_ s.t) else none
  | .ack (.ack _ c p o), m => if m = p then some (.ack bid c o true) else none
  | .press n k, m =>
    if m = n ∧ (DtnStore.admitItem (s.nodes n).L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t).err = none
    then some (.hostAdmit ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t) else none
  | _, _ => none

/-- The book and ledger of node `m` after the event. -/
def ledgerAfter (s : Sys) (ev : Ev) (m : Nat) : DtnStore.Sys :=
  match ledgerEv s ev m with
  | some e => DtnStore.step ⟨(s.nodes m).B, (s.nodes m).L, (s.nodes m).nx⟩ e
  | none => ⟨(s.nodes m).B, (s.nodes m).L, (s.nodes m).nx⟩

/-- The forwarder's `heldSum` of the bundle. -/
def heldOf (f : F) : Nat := DtnForward.heldSum f bid

/-- One event, without the `fin` ghost. -/
def exec0 (s : Sys) : Ev → Sys
  | .contact a b up =>
    let fa := (DtnForward.step (s.nodes a).f s.t (if up then .linkUp b else .linkDown b)).1
    let fb := (DtnForward.step (s.nodes b).f s.t (if up then .linkUp a else .linkDown a)).1
    (s.set a { s.nodes a with f := fa }).set b { s.nodes b with f := fb }
  | .tick =>
    { s with
      nodes := fun m =>
        if m ∈ s.cfg.ids then
          { f := (DtnForward.step (s.nodes m).f (s.t + 1) .tick).1
            B := (ledgerAfter s .tick m).B, L := (ledgerAfter s .tick m).L, nx := (s.nodes m).nx }
        else s.nodes m
      t := s.t + 1 }
  | .poll n =>
    let x := s.nodes n
    let r := DtnForward.poll x.f
    let post := ledgerAfter s (.poll n) n
    let y : Node := { f := r.1, B := post.B, L := post.L, nx := post.nx }
    match r.2 with
    | .none => s.set n y
    | .send p _ c retr =>
      -- a fresh handover that is offered custody gets the id the book handed out; a retransmission repeats the id
      -- last made to the peer
      let offered := c > 0 && !retr && offerable s.cfg n p
      let ok := offered && (DtnStore.offer x.B x.nx bid p).err = none
      let off := if retr then s.lo n p else if ok then x.nx else 0
      { s.set n y with msgs := Msg.bun s.seq n p c (!retr) off :: s.msgs, seq := s.seq + 1,
                       lo := if ok then fun a q => if a = n ∧ q = p then x.nx else s.lo a q else s.lo }
    | .release _ => { s.set n y with released := s.released + heldOf x.f }
  | .bun m =>
    match m with
    | .ack .. => s
    | .bun _ from_ r c fresh off =>
      let rest := s.msgs.erase m
      if r = s.cfg.dest then
        { s with msgs := Msg.ack s.seq r from_ off :: rest, seq := s.seq + 1, delivered := true }
      else
        let x := s.nodes r
        let a := DtnStore.accept x.B x.L bid 1 s.cfg.exp from_ s.t
        let post := ledgerAfter s (.bun m) r
        match a.err with
        | some _ =>
          { s.set r { x with B := post.B, L := post.L, nx := post.nx } with
            msgs := rest, dropped := s.dropped + (if fresh then c else 0) }
        | none =>
          let h := DtnForward.step x.f s.t (.hold bid s.cfg.dest s.cfg.exp c)
          { s.set r ⟨h.1, post.B, post.L, post.nx⟩ with
            msgs := Msg.ack s.seq r from_ off :: rest, seq := s.seq + 1,
            dropped := s.dropped + (if h.2 != .ok && fresh then c else 0),
            replayed := s.replayed || (h.2 == .ok && !fresh), acc := r :: s.acc }
  | .ack m =>
    match m with
    | .bun .. => s
    | .ack _ c p _ =>
      let x := s.nodes p
      let post := ledgerAfter s (.ack m) p
      { s.set p ⟨(DtnForward.step x.f s.t (.acked c bid)).1, post.B, post.L, post.nx⟩ with msgs := s.msgs.erase m }
  | .lose m =>
    { s with msgs := s.msgs.erase m,
             dropped := s.dropped + (match m with | .bun _ _ _ c true _ => c | _ => 0) }
  | .press n k =>
    let x := s.nodes n
    let a := DtnStore.admitItem x.L ⟨2, k⟩ s.cfg.pb .transit (s.cfg.exp + 100) s.t
    match a.err with
    | some _ => s
    | none =>
      let gone := a.ev.any fun e => e.key.space == 1
      let f' := if gone then (DtnForward.step x.f s.t (.forget bid)).1 else x.f
      { s.set n ⟨f', x.B, a.L, x.nx⟩ with released := s.released + (if gone then heldOf x.f else 0) }
  | .bad => s

/-- One event: `exec0`, then the `fin` ghost learns of every delivery flag. -/
def exec (s : Sys) (ev : Ev) : Sys :=
  let s' := exec0 s ev
  { s' with fin := s'.fin || s'.anyFlag }

/-- Which events the environment may choose in `s`: nodes of the system, messages in the network. -/
def En (s : Sys) : Ev → Prop
  | .contact a b _ => a ∈ s.cfg.ids ∧ b ∈ s.cfg.ids ∧ a < b
  | .tick => True
  | .poll n => n ∈ s.cfg.ids
  | .bun m => m ∈ s.msgs ∧ match m with | .bun _ _ r _ _ _ => r ∈ s.cfg.ids | .ack .. => False
  | .ack m => m ∈ s.msgs ∧ match m with | .ack _ _ p _ => p ∈ s.cfg.ids | .bun .. => False
  | .lose m => m ∈ s.msgs
  | .press n _ => n ∈ s.cfg.ids
  | .bad => True

/-- The reachable systems. -/
inductive Reach : Sys → Prop where
  | init (c : Cfg) (hn : c.ids.Nodup) (hsrc : c.src ∈ c.ids) (hmax : c.lbud ≤ DtnStore.MAX)
      (hacc : (originAcc c).err = none) (hhold : (originHold c).2 = .ok) : Reach (Sys.init c)
  | step {s : Sys} (ev : Ev) : Reach s → En s ev → Reach (exec s ev)

end Vinc.DtnScenario
