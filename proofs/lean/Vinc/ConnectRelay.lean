import Vinc.Json
import Vinc.ConnectMailbox
import Vinc.ConnectTable

/-!
# The relay

`relay/{mod,clients,route,records,discovery}.rs` of `vinc-connect` as functions, step for step the operators of
`proofs/tla/ConnectRelayOps.tla` (same state, same order of effects). The model works in nanoseconds, with the
constants of `relay::rule`; the trace carries whole seconds and the replay multiplies by `10^9`. Node ids are naturals,
`0` meaning none. The session table is the exact `Table` model of `ConnectTable.lean` (so the sweep order is the real
slot order); the other tables are association lists that refuse a new key at capacity, which is all the code observes of
them (`ConnectTable.lean`, `ConnectTable.tla`). The mailbox is `ConnectMailbox.lean`.

Seams, stated: a signature is an oracle (the call says whether the record or notice verifies for this relay); a record
is identified by its node, sequence number and home; the record and lookup answers, the relay's own record and the
republish timer are not part of this model. The recursion fuels (`sweepC`, `dhLoop`) are the iteration bounds of the
loops they model (the sweep visits at most `2C` slots; a mailbox holds at most `B` messages).
-/

namespace Vinc.ConnectRelay
open Vinc

inductive V where
  | s (x : String)
  | n (x : Nat)
  deriving BEq, Repr, DecidableEq

abbrev Ef := List (List V)

def sec : Nat := 1000000000

/-- The rule constants of `relay::rule` in nanoseconds, and the sizes of the carrier. -/
def fresh : Nat := 20 * sec
def stale : Nat := 15 * sec
def fwdBack : Nat := 30 * sec
def sleepWin : Nat := 10 * sec
def goneTtl : Nat := 600 * sec
def sweepNs : Nat := 1 * sec
def recTtl : Nat := 3 * (1800 * sec)
def wakeRearm : Nat := 30 * sec
def skewMs : Nat := 10000
def maxTun : Nat := 1452 - 28
def maxPkt : Nat := 1452
def aliasMax : Nat := 32
def maxPeers : Nat := 32

structure CF where
  me : Nat := 0
  C : Nat := 1
  R : Nat := 1
  MN : Nat := 1
  MB : Nat := 1
  bytes : Nat := 0
  window : Nat := 1
  sessT : Nat := 1
  age : Nat := 1

def mc (cf : CF) : ConnectMailbox.Cfg := ⟨52, cf.MB, cf.MN, cf.age, maxPkt⟩

/-! ### Association lists -/

def aget {α : Type} (l : List (Nat × α)) (k : Nat) : Option α := (l.find? (·.1 == k)).map (·.2)
/-- Replace the entry of `k`, or add it at the end (keys are unique, so first match is the only one). -/
def aput {α : Type} : List (Nat × α) → Nat → α → List (Nat × α)
  | [], k, v => [(k, v)]
  | (a, x) :: t, k, v => if a == k then (k, v) :: t else (a, x) :: aput t k v
def adel {α : Type} (l : List (Nat × α)) (k : Nat) : List (Nat × α) := l.filter (·.1 != k)
def acan {α : Type} (l : List (Nat × α)) (k cap : Nat) : Bool := l.any (·.1 == k) || decide (l.length < cap)

/-! ### Alias tables -/

structure AT where
  len : Nat
  sl : List Nat

def AT.new : AT := ⟨0, List.replicate aliasMax 0⟩

def AT.assign (a : AT) (node : Nat) : AT × Bool × Nat :=
  match (List.range a.len).find? (fun i => a.sl.getD i 0 == node) with
  | some i => (a, true, i)
  | none =>
    let a1 := if a.len ≥ aliasMax then AT.new else a
    (⟨a1.len + 1, a1.sl.set a1.len node⟩, false, a1.len)

def AT.learn (a : AT) (al node : Nat) : AT := if al < aliasMax then { a with sl := a.sl.set al node } else a
def AT.resolve (a : AT) (al : Nat) : Nat := if al < aliasMax then a.sl.getD al 0 else 0

structure Client where
  id : Nat
  opened : Nat
  lastRx : Nat
  ws : Nat
  wb : Nat
  tx : AT
  rx : AT

structure FB where
  n : Nat
  rel : Nat
  at_ : Nat

structure Sl where
  at_ : Nat
  woke : Nat

structure Rc where
  seq : Nat
  home : Nat
  rcv : Nat

structure RS where
  bk : List (Nat × Nat) := []
  tb : ConnectTable.T := ConnectTable.T.new 1
  cd : List (Nat × Client) := []
  gone : List (Nat × Nat) := []
  sl : List (Nat × Sl) := []
  udp : List (Nat × Nat) := []
  fb : List FB := []
  peers : List Nat := List.replicate maxPeers 0
  recs : List (Nat × Rc) := []
  mb : ConnectMailbox.MB := ConnectMailbox.MB.empty
  ns : Nat := 0
  ls : Nat := 0

def RS.new (cf : CF) : RS :=
  { tb := ConnectTable.T.new cf.C, fb := List.replicate cf.C ⟨0, 0, 0⟩ }

structure Out where
  r : RS
  res : String
  ef : Ef

def RS.bkf (r : RS) (k : Nat) : Nat := (aget r.bk k).getD 0
def hasC (cf : CF) (r : RS) (n : Nat) : Bool := (ConnectTable.find cf.C r.bkf r.tb n).isSome
def isPeer (r : RS) (n : Nat) : Bool := r.peers.contains n
def cget (r : RS) (n : Nat) : Client := (aget r.cd n).getD ⟨0, 0, 0, 0, 0, AT.new, AT.new⟩
def setC (r : RS) (n : Nat) (c : Client) : RS := { r with cd := aput r.cd n c }

def routedE (s d : Nat) (rt : String) (b : Nat) : List V := [.s "t", .s "routed", .n s, .n d, .s rt, .n b]
def rejE (why : String) (node : Nat) : List V := [.s "t", .s "rej", .s why, .n node]
def localEf (from_ me len : Nat) : Ef := [routedE from_ me "local" len, [.s "local", .n from_, .n len]]
def fail (r : RS) (why : String) (node : Nat) : Out := ⟨r, why, [rejE why node]⟩
def okOut (r : RS) (ef : Ef) : Out := ⟨r, "ok", ef⟩

/-- The UDP session of `dst` was heard less than 20 s ago. -/
def tunnelFresh (r : RS) (now dst : Nat) : Bool :=
  match aget r.udp dst with | some h => decide (now - h < fresh) | none => false

def tunnelDown (r : RS) (now dst src flag len : Nat) : Bool × Ef :=
  if !tunnelFresh r now dst || len == 0 || 35 + len > maxTun then (false, [])
  else (true, [[.s "udp", .n dst, .s "spl", .n src, .n flag, .n len], routedE src dst "tunnel" len])

def deliverClient (cf : CF) (r : RS) (now src dst flag len : Nat) (staleCopy : Bool) : RS × Bool × Ef :=
  if !hasC cf r dst then (r, false, [])
  else
    let c := cget r dst
    let st := decide (now - c.lastRx > stale)
    let (a, known, al) := c.tx.assign src
    let r1 := setC r dst { c with tx := a }
    let fe : List V := if known then [.s "car", .n dst, .s "ra", .n al, .n flag, .n len]
      else [.s "car", .n dst, .s "rn", .n src, .n al, .n flag, .n len]
    let t := if staleCopy && st then tunnelDown r1 now dst src flag len else (false, [])
    (r1, true, [fe, routedE src dst "carrier" len] ++ t.2)

def hold (cf : CF) (r : RS) (now dst src flag len : Nat) : Out :=
  let (mb, res) := ConnectMailbox.push (mc cf) now r.mb dst src flag len
  match res with
  | .stored seq dropped first =>
    let s : Sl := (aget r.sl dst).getD ⟨0, 0⟩
    let rearm := ConnectMailbox.shouldWake wakeRearm now s.woke first
    let r1 := { r with mb := mb, sl := if rearm then aput r.sl dst { s with woke := now } else r.sl }
    okOut r1 ([routedE src dst "mailbox" len, [.s "t", .s "mstored", .n dst, .n seq, .n dropped]] ++
      (if rearm then [[.s "t", .s "wakereq", .n dst], [.s "wake", .n dst]] else []))
  | _ => ⟨{ r with mb := mb }, "mbrefused", [rejE "mbrefused" src]⟩

/-- The reply route (`FWD_BACK`) for `dst`: the relay that forwarded its packets, if within 30 s and not this relay; else 0. -/
def backOf (cf : CF) (r : RS) (now dst : Nat) : Nat :=
  let slot := r.fb.getD (r.bkf dst) ⟨0, 0, 0⟩
  if slot.n == dst && now - slot.at_ < fwdBack && slot.rel != cf.me then slot.rel else 0

/-- The home relay `forward` sends to: the reply route if there is one, else the home of the stored record; 0 if none. -/
def homeOf (cf : CF) (r : RS) (now dst : Nat) : Nat :=
  if backOf cf r now dst != 0 then backOf cf r now dst else (aget r.recs dst).elim 0 (·.home)

def forward (cf : CF) (r : RS) (now src dst flag len : Nat) : Out :=
  if homeOf cf r now dst == 0 || homeOf cf r now dst == cf.me then fail r "noroute" src
  else if !isPeer r (homeOf cf r now dst) then fail r "nopeer" src
  else okOut r [[.s "peer", .n (homeOf cf r now dst), .s "fwd", .n src, .n dst, .n flag, .n len], routedE src dst "peer" len]

/-- The origin of a packet: from a member's carrier, forwarded by a peer relay, or from a member's UDP session. -/
inductive Origin where
  | client | peer | tunnel
  deriving DecidableEq

def route (cf : CF) (r : RS) (now src dst flag len : Nat) (origin : Origin) : Out :=
  if dst == cf.me then okOut r (localEf src cf.me len)
  else if (deliverClient cf r now src dst flag len true).2.1 then
    okOut (deliverClient cf r now src dst flag len true).1 (deliverClient cf r now src dst flag len true).2.2
  else if (tunnelDown r now dst src flag len).1 then okOut r (tunnelDown r now dst src flag len).2
  else if (aget r.sl dst).isSome then hold cf r now dst src flag len
  else if origin == .peer then fail r "noroute" src
  else forward cf r now src dst flag len

def dhLoop (cf : CF) (now node : Nat) (op : Bool) (fit : Nat) : Nat → RS → Ef → RS × Ef
  | 0, r, acc => (r, acc)
  | fuel + 1, r, acc =>
    let (mb, got) := ConnectMailbox.pop (mc cf) now r.mb node fit
    let r1 := { r with mb := mb }
    match got with
    | none => (r1, acc)
    | some m =>
      let sent := if op then deliverClient cf r1 now m.src node m.flag m.len false
        else (r1, (tunnelDown r1 now node m.src m.flag m.len).1, (tunnelDown r1 now node m.src m.flag m.len).2)
      let e := sent.2.2 ++ (if sent.2.1 then [[.s "t", .s "mdeliv", .n node, .n m.seq]] else [rejE "notunnel" node])
      dhLoop cf now node op fit fuel sent.1 (acc ++ e)

def pendingCount (mb : ConnectMailbox.MB) (k : Nat) : Nat :=
  match ConnectMailbox.lookup k mb.held with | some h => h.count | none => 0

def deliverHeld (cf : CF) (r : RS) (now node : Nat) : RS × Ef :=
  if pendingCount r.mb node == 0 then (r, [])
  else
    let op := hasC cf r node
    let fr := tunnelFresh r now node
    if !op && !fr then (r, [])
    else dhLoop cf now node op (if op then maxPkt else maxTun - 35) (cf.MB + 1) r []

def carrierOpened (cf : CF) (r : RS) (now node : Nat) : Out :=
  let id := r.ns
  let pre : Ef := if hasC cf r node then [[.s "close", .n node, .n (cget r node).id, .s "replaced"]] else []
  let (t, ins) := ConnectTable.insert cf.C r.bkf r.tb node 0
  match ins with
  | .full => ⟨r, "full", pre ++ [rejE "full" node]⟩
  | .ok _ =>
    let cl : Client := ⟨id, now, now, now, 0, AT.new, AT.new⟩
    let r1 := { r with tb := t, cd := aput r.cd node cl, ns := id + 1, gone := adel r.gone node, sl := adel r.sl node }
    let (r2, ef) := deliverHeld cf r1 now node
    okOut r2 (pre ++ [[.s "t", .s "opened", .n node, .n id]] ++ ef)

def carrierClosed (cf : CF) (r : RS) (now node sid : Nat) : Out :=
  if !hasC cf r node || (cget r node).id != sid then okOut r []
  else
    let (t, _) := ConnectTable.remove cf.C r.bkf r.tb node
    let gone1 := if acan r.gone node cf.C then aput r.gone node now else r.gone
    let asleep := (aget gone1 node).isSome && (match aget r.sl node with | some s => decide (s.at_ ≥ now - sleepWin) | none => false)
    okOut { r with tb := t, cd := adel r.cd node, gone := gone1 } [[.s "t", .s "closed", .n node, .n (if asleep then 1 else 0)]]

/-- The client with its byte window restarted when the window length has passed. -/
def chargeC (cf : CF) (c : Client) (now : Nat) : Client := if now - c.ws ≥ cf.window then { c with ws := now, wb := 0 } else c

def charge (cf : CF) (r : RS) (now node bytes : Nat) : RS × Bool × Ef :=
  if (chargeC cf (cget r node) now).wb + bytes > cf.bytes then
    (setC r node (chargeC cf (cget r node) now), false, [[.s "t", .s "quota", .n node]])
  else (setC r node { chargeC cf (cget r node) now with wb := (chargeC cf (cget r node) now).wb + bytes }, true, [])

def accept (cf : CF) (r : RS) (now k seq home : Nat) (origin : String) : Out :=
  match aget r.recs k with
  | some s =>
    if seq < s.seq || (seq == s.seq && home != s.home) then fail r "stalerec" k
    else if seq == s.seq then okOut { r with recs := aput r.recs k { s with rcv := now } } []
    else okOut { r with recs := aput r.recs k ⟨seq, home, now⟩ } [[.s "t", .s "rstored", .n k, .n seq, .s origin]]
  | none =>
    if r.recs.length ≥ cf.R then fail r "storefull" k
    else okOut { r with recs := aput r.recs k ⟨seq, home, now⟩ } [[.s "t", .s "rstored", .n k, .n seq, .s origin]]

def replicate (r : RS) (rlen : Nat) : Ef :=
  (r.peers.filter (· != 0)).map fun p => [.s "peer", .n p, .s "sync", .n rlen]

def publish (cf : CF) (r : RS) (now node k seq home rlen : Nat) : Out :=
  if node != k then fail r "wrongowner" node
  else
    let a := accept cf r now k seq home "publish"
    if a.res != "ok" then a else okOut a.r (a.ef ++ replicate a.r rlen)

/-- The notice's clock is 10 s or more away from the relay's, in milliseconds (`abs_diff`). -/
def skewed (now ts : Nat) : Bool := decide ((now / 1000000).max ts - (now / 1000000).min ts ≥ skewMs)

def sleepNotice (cf : CF) (r : RS) (now k ts good sender : Nat) : Out :=
  if sender != 0 && sender != k then fail r "wrongsender" k
  else if skewed now ts then fail r "skew" k
  else if !(hasC cf r k || (aget r.gone k).isSome) then fail r "unknown" k
  else if good == 0 then fail r "sig" k
  else if !acan r.sl k cf.C then fail r "full" k
  else okOut { r with sl := aput r.sl k ⟨now, ((aget r.sl k).map (·.woke)).getD 0⟩ } [[.s "t", .s "sleepok", .n k]]

def weight : List V → Nat
  | [.s "send", _, _, .n l] => l
  | [.s "sendnew", _, _, _, .n l] => l
  | [.s "sendalias", _, _, .n l] => l
  | [.s "selfsend", .n l] => l
  | [.s "other", .n l] => l
  | [.s "pub", _, _, _, .n l] => l
  | [.s "sleep", _, _, _, .n l] => l
  | _ => 0

def dispatch (cf : CF) (r : RS) (now node : Nat) (f : List V) : Out :=
  match f with
  | [.s "send", .n dst, .n flag, .n len] => route cf r now node dst flag len .client
  | [.s "sendnew", .n dst, .n al, .n flag, .n len] =>
    let c := cget r node
    route cf (setC r node { c with rx := c.rx.learn al dst }) now node dst flag len .client
  | [.s "sendalias", .n al, .n flag, .n len] =>
    let dst := (cget r node).rx.resolve al
    if dst == 0 then fail r "unkalias" node else route cf r now node dst flag len .client
  | [.s "selfsend", .n len] => okOut r (localEf node cf.me len)
  | [.s "ping"] => okOut r [[.s "t", .s "pulse", .n node], [.s "car", .n node, .s "pong"]]
  | [.s "pong"] => okOut r []
  | [.s "pub", .n k, .n seq, .n home, .n rlen] => publish cf r now node k seq home rlen
  | [.s "sleep", .n k, .n ts, .n good, _] => sleepNotice cf r now k ts good node
  | _ => fail r "unexpected" node

def carrierFrame (cf : CF) (r : RS) (now node sid : Nat) (f : List V) : Out :=
  if !hasC cf r node || (cget r node).id != sid then fail r "stale" node
  else
    let r1 := setC r node { cget r node with lastRx := now }
    let w := weight f
    let (r2, ok, ef) := charge cf r1 now node w
    if w > 0 && !ok then ⟨r2, "quota", ef⟩
    else dispatch cf (if w > 0 then r2 else r1) now node f

def peerFrame (cf : CF) (r : RS) (now from_ : Nat) (f : List V) : Out :=
  if !isPeer r from_ then fail r "unauth" from_
  else
    match f with
    | [.s "fwd", .n src, .n dst, .n flag, .n len] =>
      let learn := !hasC cf r src
      let r1 := if learn then { r with fb := r.fb.set (r.bkf src) ⟨src, from_, now⟩ } else r
      let rt := route cf r1 now src dst flag len .peer
      ⟨rt.r, rt.res, (if learn then [[.s "t", .s "fwdback", .n src, .n from_]] else []) ++ rt.ef⟩
    | [.s "sync", .n k, .n seq, .n home, _] => accept cf r now k seq home "replica"
    | [.s "ping"] => okOut r [[.s "peer", .n from_, .s "pong"]]
    | [.s "pong"] => okOut r []
    | _ => fail r "unexpected" from_

def addPeer (r : RS) (p : Nat) : RS × Bool :=
  if isPeer r p then (r, true)
  else match r.peers.findIdx? (· == 0) with
    | some i => ({ r with peers := r.peers.set i p }, true)
    | none => (r, false)

def removePeer (r : RS) (p : Nat) : RS := { r with peers := r.peers.map fun x => if x == p then 0 else x }

def udpHeard (cf : CF) (r : RS) (node at_ : Nat) : Out :=
  if acan r.udp node cf.C then okOut { r with udp := aput r.udp node at_ } [] else ⟨r, "full", []⟩

def udpGone (r : RS) (node : Nat) : RS := { r with udp := adel r.udp node }

def memberReturned (cf : CF) (r : RS) (now node : Nat) : Out :=
  let (r2, ef) := deliverHeld cf { r with sl := adel r.sl node } now node
  okOut r2 ef

def spu (cf : CF) (r : RS) (now m dst flag len : Nat) : Out :=
  if len == 0 || 35 + len > maxTun then fail r "baddg" m
  else
    let r1 := if m != 0 && acan r.udp m cf.C then { r with udp := aput r.udp m now } else r
    if m == 0 then fail r1 "unauth" 0
    else if dst == cf.me then fail r1 "noroute" m
    else route cf r1 now m dst flag len .tunnel

def sweepC (cf : CF) (now : Nat) : Nat → Nat → RS → Ef → RS × Ef
  | 0, _, r, acc => (r, acc)
  | fuel + 1, i, r, acc =>
    if i ≥ cf.C then (r, acc)
    else
      let k := (ConnectTable.getS r.tb.s i).k
      if k == 0 then sweepC cf now fuel (i + 1) r acc
      else
        let c := cget r k
        if now - c.opened < cf.sessT then sweepC cf now fuel (i + 1) r acc
        else
          let r1 := { r with tb := ConnectTable.removeAt cf.C r.bkf r.tb i, cd := adel r.cd k,
                             gone := if acan r.gone k cf.C then aput r.gone k now else r.gone }
          sweepC cf now fuel i r1 (acc ++ [[.s "t", .s "expired", .n k], [.s "close", .n k, .n c.id, .s "session"]])

def timeout (cf : CF) (r : RS) (now : Nat) : Out :=
  if now - r.ls < sweepNs then okOut r []
  else
    let (r1, ef) := sweepC cf now (2 * cf.C + 2) 0 r []
    let gone2 := r1.gone.filter (fun p => now - p.2 < goneTtl)
    let sl2 := r1.sl.filter (fun p => now - p.2.at_ < goneTtl)
    let recs2 := r1.recs.filter (fun p => now - p.2.rcv < recTtl)
    let mb2 := ConnectMailbox.sweep (mc cf) now r1.mb
    okOut { r1 with ls := now, gone := gone2, sl := sl2, recs := recs2, mb := mb2 } ef

end Vinc.ConnectRelay
