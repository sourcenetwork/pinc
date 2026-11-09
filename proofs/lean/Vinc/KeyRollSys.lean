import Vinc.KeyRoll

/-!
# The key roll as a two-node system

The Lean counterpart of the system part of `proofs/tla/KeyRoll.tla`, transcribed operator by operator: the
`Roll` machine of `keyroll.rs` (`Vinc.KeyRoll.Roll`) driven by the flip/hold layer of `conn/keys.rs` (staged
keys, the switch of the sending key, the reactive switch of the answerer, the previous key held for one probe
timeout, the floors), for two connections over a network that loses, reorders and duplicates every packet.

* `Node` is one connection: `roll`, the fresh-atom counter `ctr`, the sending key `sk` with its phase bit `sph` and
  the staged sending key `stg`, the pending REKEY message `out` and the time `reqAt` of the last send of the
  request, and the receive side: current key `cur`, phase bit `rph`, `first` number of the phase, previous key
  `prev` with its deadline, staged next key `nxt` with its floor, the next packet number `npn` and the packet
  numbers seen.
* `Node.recvKeys` (`RecvKeys`), `rekeyRx` (`RekeyRx`), `Begin`, `SendPkt`, `Deliver`, `Tick` are the TLA+ operators.
  The network is the list `net` of every packet ever sent: any packet can be delivered any number of times, at any
  time, in any order (loss is a packet never delivered), and, with `forgeOn`, with its phase bit flipped.
  Time is explicit: `Tick` adds one to `now`; the probe timeout `pto` is a parameter. The finite bounds `MaxTime`
  and `Sat` of the TLC model are not needed (time is unbounded, counters saturate at `u64::MAX`); the caps `cap`
  (how many fresh atoms a node may draw) and `maxPn` stay as parameters, so every theorem holds for every value.
  The generation counter is a `Nat` (the `GenerationExhausted` refusal of `PacketKey::rolled` at `u32::MAX` is the
  subject of `Vinc.Record`, not of this model, as in the TLA+ model).
* The switches `gateFirst` (the code as read: a request is refused while a next key is staged, before the
  duplicate-request check) and `bindAnswers` (the network only delivers an answer to the request it answers) are
  explicit fields of `Params`; the theorems that need one say so in their hypotheses.
* GHOST state, never read by the machine, only by the statements and the invariants: `Node.ders` (every derivation
  of new keys at this node, in order: whether it was a staging as answerer, the request share, the
  Diffie-Hellman value, the depth of the key the request arrived under), `Node.promAt` (the last promotion time),
  and the logs of the system `slog` (every seal), `comp` (every completed answer), `stl` (every staging: the
  answerer, its answer and the position in its derivations) and `breq` (every request begun with the number of
  derivations of the node at that time). They exist to state the properties.

Node `false` is the dialer, node `true` the acceptor.
-/

namespace Vinc.KeyRollSys
open Vinc.KeyRoll

/-- The parameters of the system (the constants of the TLA+ model). -/
structure Params where
  /-- The probe timeout. -/
  pto : Nat
  /-- How many fresh atoms (rolls started or answered) a node may draw. -/
  cap : Bool → Nat
  /-- The largest packet number sealed. -/
  maxPn : Nat
  /-- `GateFirst`: a request is refused while a next key is staged, before the duplicate-request check. -/
  gateFirst : Bool
  /-- `BindAnswers`: an answer is only delivered to a requester whose current request it answers. -/
  bindAnswers : Bool
  /-- `ForgeOn`: the attacker may deliver a packet with its phase bit flipped. -/
  forgeOn : Bool

/-- The node number as a term index. -/
def nid (n : Bool) : Nat := if n then 1 else 0

/-- `Atom(n, k)`. -/
def atomOf (n : Bool) (k : Nat) : Atom := ⟨nid n, k⟩

/-- One key of the connection with its failed-open counter (`NewK`). -/
structure PK where
  sec : T
  g : Nat
  fc : Nat
  deriving DecidableEq

def PK.new (sec : T) (g : Nat) : PK := ⟨sec, g, 0⟩

/-- The previous key with its hold deadline. -/
structure Prev where
  k : PK
  dl : Nat
  deriving DecidableEq

/-- The staged next key with its floor. -/
structure Nxt where
  k : PK
  floor : Nat
  deriving DecidableEq

/-- Ghost: one derivation of new keys at a node. `stg` tells a staging (the node answered a request) from a
completion (the node took the answer to its own request); `rid` is the request share of the roll, `dh` the
Diffie-Hellman value, `lvl` for a staging the depth of the secret the request packet was sealed under. -/
structure Der where
  stg : Bool
  rid : T
  dh : T
  lvl : Nat
  deriving DecidableEq

/-- The keys and the machine of one connection. -/
structure Node where
  roll : Roll
  ctr : Nat
  sk : PK
  sph : Bool
  stg : Option PK
  out : Option Msg
  reqAt : Option Nat
  cur : PK
  rph : Bool
  first : Nat
  prev : Option Prev
  nxt : Option Nxt
  npn : Nat
  seen : List Nat
  /-- Ghost: the derivations of new keys, in order. -/
  ders : List Der
  /-- Ghost: when the last promotion happened. -/
  promAt : Option Nat

/-- Ghost: how many times this node derived new keys (the `chg` of the TLA+ model). -/
def Node.chg (s : Node) : Nat := s.ders.length

/-- `NodeInit(n)`. -/
def Node.init (n : Bool) : Node where
  roll := Roll.new (!n)
  ctr := 0
  sk := PK.new (.base (nid n)) 0
  sph := false
  stg := none
  out := none
  reqAt := none
  cur := PK.new (.base (nid (!n))) 0
  rph := false
  first := 0
  prev := none
  nxt := none
  npn := 0
  seen := []
  ders := []
  promAt := none

/-- `Expire`: the previous key is dropped once its deadline passed. -/
def Node.expire (s : Node) (t : Nat) : Node :=
  match s.prev with
  | some p => if p.dl ≤ t then { s with prev := none } else s
  | none => s

/-- `Select`: the key slot a packet with phase bit `ph` and number `pn` is opened with (after `expire`). -/
def Node.select (s : Node) (ph : Bool) (pn : Nat) : Sel :=
  if ph == s.rph then .cur
  else match s.nxt with
    | some x => if x.floor ≤ pn then .next else if pn < s.first && s.prev.isSome then .prev else .err
    | none => if pn < s.first && s.prev.isSome then .prev else .err

/-- `SlotKey(s, sel).sec`. -/
def Node.slotSec (s : Node) : Sel → Option T
  | .cur => some s.cur.sec
  | .next => s.nxt.map (·.k.sec)
  | .prev => s.prev.map (·.k.sec)
  | .err => none

/-- `BumpFC`: a failed open counts against the key it was tried with. -/
def Node.bumpFC (s : Node) : Sel → Node
  | .cur => { s with cur := { s.cur with fc := Record.inc s.cur.fc } }
  | .prev => { s with prev := s.prev.map fun x => { x with k := { x.k with fc := Record.inc x.k.fc } } }
  | .next => { s with nxt := s.nxt.map fun x => { x with k := { x.k with fc := Record.inc x.k.fc } } }
  | .err => s

/-- `Promote`: the staged key becomes current, the old one is held until `t + pto`. -/
def Node.promote (s : Node) (pn t pto : Nat) : Node :=
  match s.nxt with
  | some x => { s with prev := some ⟨s.cur, t + pto⟩, cur := x.k, rph := !s.rph, first := pn, nxt := none,
                       promAt := some t }
  | none => s

/-- `UpdateSend`: the staged sending key becomes the sending key. -/
def Node.updateSend (s : Node) : Node :=
  match s.stg with
  | some k => { s with sk := k, sph := !s.sph, stg := none }
  | none => s

/-- A packet on the network: the sender, the phase bit, the packet number, the secret it was sealed under and the
REKEY message it carries. -/
structure Pkt where
  src : Bool
  ph : Bool
  pn : Nat
  sec : T
  pl : Option Msg
  deriving DecidableEq

/-- The outcome of `RecvKeys`: the new keys state, whether the packet opened and the slot it was tried with. -/
structure Rx where
  s : Node
  acc : Bool
  sel : Sel

/-- `RecvKeys`, up to the opening. `forged`: the phase bit of the packet was flipped by the attacker, so the tag
verifies under no key. -/
def Node.recvKeys (s : Node) (p : Pkt) (forged : Bool) (t pto : Nat) : Rx :=
  let s1 := s.expire t
  let sel := s1.select (if forged then !p.ph else p.ph) p.pn
  let ok := !forged && decide (s1.slotSec sel = some p.sec)
  match sel with
  | .err => ⟨s1, false, .err⟩
  | .cur => if ok then ⟨{ s1 with first := if p.pn < s1.first then p.pn else s1.first }, true, .cur⟩
            else ⟨s1.bumpFC .cur, false, .cur⟩
  | .next => if ok then ⟨(s1.promote p.pn t pto).updateSend, true, .next⟩ else ⟨s1.bumpFC .next, false, .next⟩
  | .prev => if ok then ⟨s1, true, .prev⟩ else ⟨s1.bumpFC .prev, false, .prev⟩

/-- `IsDupMsg`: a request whose share is the share of the last request answered. -/
def isDupMsg (s : Node) (m : Msg) : Bool := !m.answer && s.roll.isDup m

/-- `Gated`: `Keys::on_request` is refused while a next key is staged; with `gateFirst = false` a duplicate request
is answered before that check. -/
def gated (P : Params) (s : Node) (m : Msg) : Bool := s.nxt.isSome && (P.gateFirst || !isDupMsg s m)

/-- `CanRx`: a fresh atom is drawn for every request that is not a duplicate. -/
def canRx (P : Params) (s : Node) (m : Msg) (me : Bool) : Bool :=
  m.answer || isDupMsg s m || gated P s m || decide (s.ctr < P.cap me) || (s.roll.dialer && !s.roll.isIdle)

/-- Ghost: a completed answer: the node, the Diffie-Hellman value it computed, the one the answerer used, the
request the answer answers and the request that was out. -/
structure Comp where
  n : Bool
  dh : T
  gdh : T
  to : T
  req : T

/-- Ghost: a staging: the answerer, its answer and the number of its derivations before it. -/
structure StRec where
  n : Bool
  ans : Msg
  pos : Nat

/-- The outcome of `RekeyRx`: the node and the ghost log entries the step adds. -/
structure Rk where
  s : Node
  comp : Option Comp
  st : Option StRec

/-- The answer switches the sending key (`RekeyRx`, answer taken): the roll `r` after the answer, the
Diffie-Hellman value `dh` and the peer's switch number `pspn`; `rid` is the request that was out. -/
def Node.consumed (s : Node) (r : Roll) (dh : T) (pspn : Nat) (rid : T) : Node :=
  { s with roll := r, nxt := some ⟨PK.new (.roll s.cur.sec dh) (s.cur.g + 1), pspn⟩,
           sk := PK.new (.roll s.sk.sec dh) (s.sk.g + 1), sph := !s.sph, reqAt := none,
           ders := s.ders ++ [⟨false, rid, dh, 0⟩] }

/-- A request is answered with fresh keys (`RekeyRx`, request staged): the roll `r` after the request, the answer
`ans`, the Diffie-Hellman value `dh`; `rid` the request share and `lvl` the depth of its packet's secret. -/
def Node.staged (s : Node) (r : Roll) (ans : Msg) (dh : T) (rid : T) (lvl : Nat) : Node :=
  { s with roll := r, out := some ans, ctr := s.ctr + 1, ders := s.ders ++ [⟨true, rid, dh, lvl⟩],
           stg := some (PK.new (.roll s.sk.sec dh) (s.sk.g + 1)),
           nxt := some ⟨PK.new (.roll s.cur.sec dh) (s.cur.g + 1), 0⟩ }

/-- `RekeyRx` (`Connection::on_rekey_body` for a body that parsed): the answer switches the sending key, a request
stages the keys. `lvl` is the depth of the secret of the packet the body arrived in (ghost). -/
def rekeyRx (P : Params) (s : Node) (m : Msg) (me : Bool) (lvl : Nat) : Rk :=
  if m.answer then
    match s.roll.onAnswer m, s.roll.pending with
    | (r, .ok (dh, pspn)), some rq => ⟨s.consumed r dh pspn rq.share, some ⟨me, dh, m.gdh, m.to, rq.share⟩, none⟩
    | (r, _), _ => ⟨{ s with roll := r }, none, none⟩
  else if gated P s m then ⟨s, none, none⟩
  else
    match s.roll.onRequest m s.npn (some (atomOf me s.ctr)) with
    | (r, .error _) => ⟨{ s with roll := r }, none, none⟩
    | (_, .ok (ans, none)) => ⟨{ s with out := some ans }, none, none⟩
    | (r, .ok (ans, some dh)) => ⟨s.staged r ans dh m.share lvl, none, some ⟨me, ans, s.ders.length⟩⟩

/-- A seal: node, secret, generation, packet number (the ghost log `slog`). -/
structure Seal where
  n : Bool
  sec : T
  g : Nat
  pn : Nat
  deriving DecidableEq

/-- Ghost: a begun request: the node, the request share and the number of derivations of the node then. -/
structure BReq where
  n : Bool
  sh : T
  j : Nat
  deriving DecidableEq

/-- The system: the two nodes, the network, the time and the ghost logs. -/
structure Sys where
  nd : Bool → Node
  net : List Pkt
  now : Nat
  slog : List Seal
  comp : List Comp
  stl : List StRec
  breq : List BReq

/-- Function update. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β := fun x => if x = a then b else f x

/-- Replace the node `n` of the system. -/
def Sys.setNode (S : Sys) (n : Bool) (s' : Node) : Sys := { S with nd := upd S.nd n s' }

/-- Add an optional entry to a log. -/
def addOpt {α : Type} : Option α → List α → List α
  | some x, l => x :: l
  | none, l => l

def Sys.init : Sys where
  nd := Node.init
  net := []
  now := 0
  slog := []
  comp := []
  stl := []
  breq := []

/-- `Begin(n)` (`roll_tick`): a due roll starts, when none is under way and nothing is staged. Guard and update. -/
def beginOk (P : Params) (S : Sys) (n : Bool) : Bool :=
  let s := S.nd n
  decide (s.ctr < P.cap n) && s.stg.isNone && s.nxt.isNone && s.roll.isIdle

def beginUpd (S : Sys) (n : Bool) : Sys :=
  let s := S.nd n
  let r := s.roll.start (some (atomOf n s.ctr))
  { (S.setNode n { s with roll := r.1, out := (match r.2 with | .ok m => some m | .error _ => none),
                          reqAt := none, ctr := s.ctr + 1 }) with
    breq := ⟨n, .pub (atomOf n s.ctr), s.chg⟩ :: S.breq }

/-- `poll_rekey`: the pending request is due again (never sent, or a probe timeout passed since the last send). -/
def Node.pollDue (s : Node) (now pto : Nat) : Bool :=
  match s.reqAt with | none => true | some a => decide (now ≥ a + pto)

/-- `Poll` (`poll_rekey`): the message waiting, or the pending request again once a probe timeout passed. -/
def Node.poll (s : Node) (now pto : Nat) : Option Msg × Node :=
  match s.out with
  | some m => (some m, { s with out := none, reqAt := if m.answer then s.reqAt else some now })
  | none =>
    match s.roll.pending with
    | some r => if s.pollDue now pto then (some r, { s with reqAt := some now }) else (none, s)
    | none => (none, s)

/-- `SendPkt(n, withPl)`: a packet sealed under the sending key, carrying the polled REKEY message if any. -/
def sendQ (P : Params) (S : Sys) (n : Bool) (withPl : Bool) : Option Msg × Node :=
  if withPl then (S.nd n).poll S.now P.pto else (none, S.nd n)

def sendOk (P : Params) (S : Sys) (n : Bool) (withPl : Bool) : Bool :=
  let q := sendQ P S n withPl
  decide (q.2.npn ≤ P.maxPn) && (!withPl || q.1.isSome) && (withPl || ((S.nd n).poll S.now P.pto).1.isNone)

def sendPkt (P : Params) (S : Sys) (n : Bool) (withPl : Bool) : Pkt :=
  let q := sendQ P S n withPl
  ⟨n, q.2.sph, q.2.npn, q.2.sk.sec, q.1⟩

def sendUpd (P : Params) (S : Sys) (n : Bool) (withPl : Bool) : Sys :=
  let q := sendQ P S n withPl
  { (S.setNode n { q.2 with npn := q.2.npn + 1 }) with
    net := sendPkt P S n withPl :: S.net
    slog := ⟨n, q.2.sk.sec, q.2.sk.g, q.2.npn⟩ :: S.slog }

/-- What `Deliver` does to the receiving node before the REKEY body is looked at: the keys layer, and the packet
number set. Returns the node, whether the packet was accepted and new (`proc`). -/
def Node.afterRecv (P : Params) (s0 : Node) (p : Pkt) (forged : Bool) (now : Nat) : Node × Bool :=
  let k := s0.recvKeys p forged now P.pto
  let proc := k.acc && decide (p.pn ∉ s0.seen)
  (if proc then { k.s with seen := p.pn :: k.s.seen } else k.s, proc)

/-- The guard of `Deliver(n, p, forged)`: the packet is on the network, comes from the peer, a forged one only
when the attacker is on; the network only delivers an answer to the request it answers (`bindAnswers`); a request
is only delivered to a node that can draw a fresh atom (`CanRx`). -/
def deliverOk (P : Params) (S : Sys) (n : Bool) (p : Pkt) (forged : Bool) : Bool :=
  let r := (S.nd n).afterRecv P p forged S.now
  S.net.contains p && decide (p.src = !n) && (!forged || P.forgeOn) &&
    (match p.pl with
     | none => true
     | some m =>
       !r.2 ||
         ((!(P.bindAnswers && m.answer && !r.1.roll.isIdle) ||
             (match r.1.roll.pending with | some rq => decide (m.to = rq.share) | none => false)) &&
          (m.answer || canRx P r.1 m n)))

def deliverUpd (P : Params) (S : Sys) (n : Bool) (p : Pkt) (forged : Bool) : Sys :=
  let r := (S.nd n).afterRecv P p forged S.now
  let rk : Rk := match p.pl with
    | some m => if r.2 then rekeyRx P r.1 m n p.sec.depth else ⟨r.1, none, none⟩
    | none => ⟨r.1, none, none⟩
  { (S.setNode n rk.s) with comp := addOpt rk.comp S.comp, stl := addOpt rk.st S.stl }

def tickUpd (S : Sys) : Sys := { S with now := S.now + 1 }

/-- One step of the system. -/
inductive Step (P : Params) : Sys → Sys → Prop
  | begin (S : Sys) (n : Bool) : beginOk P S n = true → Step P S (beginUpd S n)
  | send (S : Sys) (n w : Bool) : sendOk P S n w = true → Step P S (sendUpd P S n w)
  | deliver (S : Sys) (n : Bool) (p : Pkt) (f : Bool) : deliverOk P S n p f = true → Step P S (deliverUpd P S n p f)
  | tick (S : Sys) : Step P S (tickUpd S)

/-- The reachable states. -/
inductive Reach (P : Params) : Sys → Prop
  | init : Reach P Sys.init
  | step (S S' : Sys) : Reach P S → Step P S S' → Reach P S'

end Vinc.KeyRollSys
