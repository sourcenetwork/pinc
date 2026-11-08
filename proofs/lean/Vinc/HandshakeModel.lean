import Vinc.Axioms

/-!
# The handshake model: symbolic terms and the step functions

A line-by-line transcription of `proofs/tla/HsOps.tla` (the TLA+ model that the trace check ties to the Rust code),
over unbounded node, session and ticket identifiers.

Perfect cryptography is the stated hypothesis of this model, and it is built into the term algebra: `Term` is a free
inductive type, so a hash, a key derivation or a MAC is a constructor tagged with its purpose, and two terms are equal
iff their constructors and arguments are (collision resistance and separation of the derivations). `Known` is the
Dolev-Yao deduction of the attacker from its own secrets: a Diffie-Hellman secret needs one of the two secrets, a KEM
secret needs the coin or the key owner, the hybrid chain keys need both inputs, every other derived key needs its key
argument. Nothing else about the primitives is assumed, and nothing is declared beyond definitions and theorems.

Naming follows HsOps.tla (`Th0`, `IHandle`, `RHello`, ...). Nodes are naturals and node `att = 0` is the attacker's;
secret atoms are naturals `atom tag node k`, so the owner of an atom is its node and the Diffie-Hellman secret of two
atoms is the unordered pair (`Dh`). Each step returns the new local state, the messages sent, the events raised, the
verdict (`ok`, `drop`: input dropped and nothing changes, `fatal`: the machine stopped) and the signatures made.
-/

namespace Vinc.Hs

/-- The attacker's node. -/
def att : Nat := 0

/-- A secret atom: a tag (0 initiator ephemeral, 1 fallback ephemeral, 2 responder ephemeral, 3 KEM coin), the node
that owns it and a counter. -/
structure Atom where
  t : Nat
  n : Nat
  k : Nat
  deriving DecidableEq, Repr

def atom (t n k : Nat) : Atom := ⟨t, n, k⟩
/-- The node that owns an atom. -/
def owner (a : Atom) : Nat := a.n

/-- A total order on atoms, to name the unordered pair of a Diffie-Hellman secret. -/
def Atom.lt (a b : Atom) : Bool := a.t < b.t || (a.t == b.t && (a.n < b.n || (a.n == b.n && a.k < b.k)))

/-- Symbolic terms; a free algebra (perfect primitives). -/
inductive Term where
  | nil | ok | bad
  | pub (a : Atom)
  | ek (n : Nat)
  | hash (t : Term)
  | ct (coin : Atom) (o : Nat)
  | dh (a b : Atom)
  | kem (coin : Atom) (o : Nat)
  | junk (n : Nat) (c : Term)
  | ck1 (a b : Term)
  | ck1r (a b : Term)
  | hs (k : Term) (dir : Bool) (th : Term)
  | ck2 (k th : Term)
  | app (k : Term) (dir : Bool) (th : Term)
  | res (k th : Term)
  | cfk (k th : Term)
  | psk (r tid : Term)
  | ckpsk (p : Term)
  | early (c th : Term)
  | binder (p th : Term)
  | conf (c t : Term)
  | sig (id : Nat) (resp : Bool) (th : Term)
  | th0 (prm e hpk : Term)
  | th1 (t rprm e ct : Term)
  | th2 (t : Term) (id : Nat)
  | th3 (t sg : Term)
  | th4 (t : Term) (id : Nat)
  | th5 (t sg : Term)
  | thH (prm tid e : Term)
  | thR (h b rprm e : Term)
  | thT (t tids : Term)
  | tid (n k : Nat)
  | one (t : Term)
  deriving DecidableEq, Repr

open Term

/-- The attacker can compute `t` from its own secrets. -/
def Known : Term → Prop
  | dh a b => owner a = att ∨ owner b = att
  | kem c o => owner c = att ∨ o = att
  | junk _ _ => False
  | ck1 a b => Known a ∧ Known b
  | ck1r a b => Known a ∧ Known b
  | hs k _ _ => Known k
  | ck2 k _ => Known k
  | app k _ _ => Known k
  | res k _ => Known k
  | cfk k _ => Known k
  | psk k _ => Known k
  | ckpsk k => Known k
  | early k _ => Known k
  | binder k _ => Known k
  | conf k _ => Known k
  | _ => False

/-- The Diffie-Hellman secret of two atoms (unordered). -/
def Dh (a b : Atom) : Term := if Atom.lt b a then dh b a else dh a b

theorem Dh_comm (a b : Atom) : Dh a b = Dh b a := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [Dh, Atom.lt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  by_cases h1 : (b1 < a1 ∨ b1 = a1 ∧ (b2 < a2 ∨ b2 = a2 ∧ b3 < a3))
  · have h2 : ¬ (a1 < b1 ∨ a1 = b1 ∧ (a2 < b2 ∨ a2 = b2 ∧ a3 < b3)) := by omega
    simp [h1, h2]
  · by_cases h2 : (a1 < b1 ∨ a1 = b1 ∧ (a2 < b2 ∨ a2 = b2 ∧ a3 < b3))
    · simp [h1, h2]
    · have : a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by omega
      obtain ⟨rfl, rfl, rfl⟩ := this
      rfl

/-- The atom behind an ephemeral public value (an unknown shape is the attacker's). -/
def atomOf : Term → Atom
  | pub a => a
  | _ => ⟨0, 0, 0⟩

/-- The node behind a prekey term. -/
def ekNode : Term → Nat
  | ek o => o
  | _ => 0

/-- The list of ticket ids a term carries. -/
def tidsList : Term → List Term
  | one t => [t]
  | _ => []

structure Blob where
  k : Term
  ad : Term
  id : Nat
  sig : Term
  deriving DecidableEq, Repr

def BadBlob : Blob := ⟨nil, nil, 0, nil⟩

inductive MTy | nil | init | prej | reply | fin | hello | rreply | rrej
  deriving DecidableEq, Repr
inductive Form | nil | full | short
  deriving DecidableEq, Repr

/-- A handshake message; one record shape, unused fields are `nil`. -/
structure Msg where
  ty : MTy := .nil
  form : Form := .nil
  prm : Term := ok
  e : Term := nil
  pk : Term := nil
  rprm : Term := ok
  ct : Term := nil
  sealed : Blob := BadBlob
  tid : Term := nil
  binder : Term := nil
  tids : Term := nil
  conf : Term := nil
  echo : Term := nil
  deriving DecidableEq, Repr

inductive Ev | early | est | rejected | failed
  deriving DecidableEq, Repr
inductive Err | ok | drop | fatal
  deriving DecidableEq, Repr
inductive KRes | ok | fail
  deriving DecidableEq, Repr
inductive IPh | none | reply | resume | decap | sign | done | failed
  deriving DecidableEq, Repr
inductive RPh | idle | sign | finish | done | failed
  deriving DecidableEq, Repr
inductive Mode | nil | short | full | resume | fallback
  deriving DecidableEq, Repr

/-- A signature made: the signer, whether it is the responder's, the transcript. -/
structure SigE where
  id : Nat
  resp : Bool
  th : Term
  deriving DecidableEq, Repr

/-- A ticket as issued: id, pre-shared key, and the peer it was issued to (or, in a client store, issued by). -/
structure Tk where
  tid : Term
  psk : Term
  peer : Nat
  deriving DecidableEq, Repr

/-- The initiator's local state (INil of HsOps.tla). -/
structure IState where
  ph : IPh := .none
  peer : Nat := 0
  x : Atom := ⟨0, 0, 0⟩
  short : Bool := false
  th0 : Term := nil
  mode : Mode := .nil
  ckpsk : Term := nil
  thh : Term := nil
  binder : Term := nil
  early : Term := nil
  tid : Term := nil
  reply : Msg := {}
  th1 : Term := nil
  ssx : Term := nil
  hsi : Term := nil
  ck1 : Term := nil
  th2 : Term := nil
  th3 : Term := nil
  th4 : Term := nil
  send : Term := nil
  recv : Term := nil
  res : Term := nil
  ath : Term := nil
  thf : Term := nil
  tids : Term := nil
  auth : Bool := false
  est : Bool := false
  resumed : Bool := false
  fell : Bool := false
  acc : Bool := false
  deriving DecidableEq, Repr

structure IRes where
  st : IState
  out : List Msg := []
  ev : List Ev := []
  err : Err := .ok
  sg : List SigE := []
  deriving DecidableEq, Repr

def Drop (st : IState) : IRes := { st := st, err := .drop }
def Fatal (st : IState) : IRes := { st := { st with ph := .failed }, ev := [.failed], err := .fatal }
def Ok (st : IState) (out : List Msg) (ev : List Ev) : IRes := { st := st, out := out, ev := ev }

/-- Initiator::begin_full: a fresh ephemeral `x`, the short or the full Initial. -/
def IBeginFull (n : Nat) (x : Atom) (peer : Nat) (short : Bool) (thh early : Term) : IRes :=
  let e := pub x
  let hpk := hash (ek n)
  Ok { ph := .reply, peer := peer, x := x, short := short, th0 := th0 ok e hpk,
       mode := if short then .short else .full, thh := thh, early := early }
    [if short then { ty := .init, form := .short, e := e, pk := hpk }
     else { ty := .init, form := .full, e := e, pk := ek n }] []

/-- Initiator::begin_resume with a ticket. -/
def IBeginResume (n : Nat) (x : Atom) (tk : Tk) : IRes :=
  let e := pub x
  let thh := thH ok tk.tid e
  let b := binder tk.psk thh
  let ckp := ckpsk tk.psk
  Ok { ph := .resume, peer := tk.peer, x := x, mode := .resume, ckpsk := ckp, thh := thh, binder := b,
       early := early ckp thh, tid := tk.tid }
    [{ ty := .hello, e := e, tid := tk.tid, binder := b }] [.early]

/-- Resumption reply: the transcript, chain and confirmation the initiator computes. -/
def rrThr (st : IState) (m : Msg) : Term := thR st.thh st.binder m.rprm m.e
def rrCk2 (st : IState) (m : Msg) : Term := ck2 (ck1r st.ckpsk (Dh st.x (atomOf m.e))) (rrThr st m)

/-- The state after the initiator accepts a resumption reply. -/
def rrDone (st : IState) (m : Msg) : IState :=
  { st with ph := .done, send := app (rrCk2 st m) true (rrThr st m), recv := app (rrCk2 st m) false (rrThr st m),
            res := res (rrCk2 st m) (rrThr st m), ath := rrThr st m, thf := rrThr st m, tids := m.tids,
            auth := true, est := true, resumed := true }

/-- The state after a resume reject: a fresh full handshake. -/
def rrFall (st : IState) (n : Nat) : IState :=
  { (IBeginFull n (atom 1 st.x.n st.x.k) st.peer false st.thh nil).st with mode := .fallback, fell := true }
/-- Initiator::handle for a message `m` received by node `n`. -/
def IHandle (st : IState) (n : Nat) (m : Msg) : IRes :=
  if st.ph = .failed then Drop st
  else match m.ty with
    | .reply =>
      if st.ph ≠ .reply then Drop st
      else if m.rprm ≠ ok then Fatal st
      else Ok { st with ph := .decap, reply := m, th1 := th1 st.th0 m.rprm m.e m.ct,
                        ssx := Dh st.x (atomOf m.e) } [] []
    | .prej =>
      if ¬(st.ph = .reply ∧ st.short = true) ∨ m.echo ≠ st.th0 then Drop st
      else Ok { st with short := false } [{ ty := .init, form := .full, e := pub st.x, pk := ek n }] []
    | .rreply =>
      if st.ph ≠ .resume then Drop st
      else if m.conf ≠ conf (cfk (rrCk2 st m) (rrThr st m)) (thT (rrThr st m) m.tids) then Fatal st
      else Ok (rrDone st m) [] [.est]
    | .rrej =>
      if st.ph ≠ .resume ∨ m.echo ≠ st.thh then Drop st
      else Ok (rrFall st n) (IBeginFull n (atom 1 st.x.n st.x.k) st.peer false st.thh nil).out [.rejected]
    | _ => Drop st

/-- The KEM secret node `n` obtains by decapsulating `c`: the real one if the ciphertext is to its prekey, else an
unrelated value only `n` knows. -/
def Decap (n : Nat) (c : Term) : Term :=
  match c with
  | ct coin o => if o = n then kem coin o else junk n c
  | _ => junk n c

/-- The KEM secret the initiator decapsulates. -/
def ikSsk (st : IState) (n : Nat) : Term := Decap n st.reply.ct
def ikCk1 (st : IState) (n : Nat) : Term := ck1 (ikSsk st n) st.ssx

def ikSignSt (st : IState) (n : Nat) : IState :=
  { st with ph := .sign, hsi := hs (ikCk1 st n) true st.th1, ck1 := ikCk1 st n,
            th2 := th2 st.th1 st.reply.sealed.id,
            th3 := th3 (th2 st.th1 st.reply.sealed.id) st.reply.sealed.sig,
            th4 := th4 (th3 (th2 st.th1 st.reply.sealed.id) st.reply.sealed.sig) n,
            ath := th2 st.th1 st.reply.sealed.id, auth := true }

def ikSig (st : IState) (n : Nat) : Term := sig n false st.th4
def ikT5 (st : IState) (n : Nat) : Term := th5 st.th4 (ikSig st n)
def ikCk2 (st : IState) (n : Nat) : Term := ck2 st.ck1 (ikT5 st n)
def ikDoneSt (st : IState) (n : Nat) : IState :=
  { st with ph := .done, send := app (ikCk2 st n) true (ikT5 st n), recv := app (ikCk2 st n) false (ikT5 st n),
            res := res (ikCk2 st n) (ikT5 st n), thf := ikT5 st n, est := true }
/-- Initiator::on_key_response. -/
def IKey (st : IState) (n : Nat) (kind : KRes) : IRes :=
  if st.ph = .decap ∧ kind = .ok then
    let b := st.reply.sealed
    if b.k ≠ hs (ikCk1 st n) false st.th1 ∨ b.ad ≠ st.th1 then Fatal st
    else if b.id ≠ st.peer then Fatal st
    else if b.sig ≠ sig b.id true (th2 st.th1 b.id) then Fatal st
    else Ok (ikSignSt st n) [] []
  else if st.ph = .sign ∧ kind = .ok then
    { st := ikDoneSt st n, out := [{ ty := .fin, sealed := ⟨st.hsi, st.th3, n, ikSig st n⟩ }], ev := [.est],
      sg := [⟨n, false, st.th4⟩] }
  else if (st.ph = .decap ∨ st.ph = .sign) ∧ kind = .fail then Fatal st
  else Drop st

/-- The responder's local state (RNil). -/
structure RState where
  ph : RPh := .idle
  th0 : Term := nil
  hpk : Term := nil
  ek : Term := nil
  fresh : Bool := false
  ct : Term := nil
  th1 : Term := nil
  th2 : Term := nil
  th3 : Term := nil
  hsr : Term := nil
  hsi : Term := nil
  ck1 : Term := nil
  reply : Msg := {}
  send : Term := nil
  recv : Term := nil
  res : Term := nil
  ath : Term := nil
  thf : Term := nil
  th4 : Term := nil
  peer : Nat := 0
  tid : Term := nil
  thh : Term := nil
  early : Term := nil
  mytid : Term := nil
  sgn : Bool := false
  auth : Bool := false
  est : Bool := false
  resumed : Bool := false
  deriving DecidableEq, Repr

/-- A ticket slot of the responder's store. -/
structure Slot where
  occ : Bool := false
  tid : Term := nil
  psk : Term := nil
  peer : Nat := 0
  exp : Bool := false
  stamp : Nat := 0
  deriving DecidableEq, Repr

def NoSlot : Slot := {}

/-- The shared state of one responder node: the prekey cache (hashes), the ticket slots, the stamp clock. -/
structure Store where
  pkc : List Term := []
  tks : List Slot := []
  clk : Nat := 0
  deriving DecidableEq, Repr

/-- The index of the slot with the lowest stamp (the first, on a tie). -/
def argmin : List Slot → Nat → Nat → Nat → Nat
  | [], _, best, _ => best
  | s :: l, i, best, bs => if s.stamp < bs then argmin l (i + 1) i s.stamp else argmin l (i + 1) best bs

/-- ServerTickets victim: the first empty slot, else the first expired one, else the oldest. -/
def Victim (tks : List Slot) : Nat :=
  match tks.findIdx? (fun s => !s.occ) with
  | some i => i
  | none =>
    match tks.findIdx? (fun s => s.exp) with
    | some i => i
    | none => match tks with
      | [] => 0
      | s :: l => argmin l 1 0 s.stamp

/-- issue_batch for one ticket. -/
def IssueTicket (sto : Store) (t p : Term) (peer : Nat) : Store :=
  let slot : Slot := { occ := true, tid := t, psk := p, peer := peer, exp := false, stamp := sto.clk + 1 }
  { sto with tks := sto.tks.set (Victim sto.tks) slot, clk := sto.clk + 1 }

def RemoveSlot (sto : Store) (i : Nat) : Store := { sto with tks := sto.tks.set i NoSlot }

structure RRes where
  st : RState
  out : List Msg := []
  ev : List Ev := []
  err : Err := .ok
  sto : Store
  iss : List Tk := []
  sg : List SigE := []
  deriving DecidableEq, Repr

def RDrop (st : RState) (sto : Store) : RRes := { st := st, err := .drop, sto := sto }
def RFatal (st : RState) (sto : Store) : RRes :=
  { st := { st with ph := .failed }, ev := [.failed], err := .fatal, sto := sto }
def ROk (st : RState) (out : List Msg) (ev : List Ev) (sto : Store) : RRes :=
  { st := st, out := out, ev := ev, sto := sto }

/-- The responder session `s = (n, k)`: its ephemeral atom, coin and ticket id. -/
def ry (n k : Nat) : Atom := atom 2 n k
def rcoin (n k : Nat) : Atom := atom 3 n k

def rHpk (m : Msg) : Term := if m.form = .full then hash m.pk else m.pk
def rEk (m : Msg) : Term := if m.form = .full then m.pk else (match rHpk m with | Term.hash t => t | _ => nil)
def rT0 (m : Msg) : Term := th0 m.prm m.e (rHpk m)
def rC (n k : Nat) (m : Msg) : Term := ct (rcoin n k) (ekNode (rEk m))
def rT1 (n k : Nat) (m : Msg) : Term := th1 (rT0 m) ok (pub (ry n k)) (rC n k m)
def rCk1 (n k : Nat) (m : Msg) : Term := ck1 (kem (rcoin n k) (ekNode (rEk m))) (Dh (ry n k) (atomOf m.e))
def rInitSt (st : RState) (n k : Nat) (m : Msg) : RState :=
  { st with ph := .sign, th0 := rT0 m, hpk := rHpk m, ek := rEk m, fresh := decide (m.form = .full), ct := rC n k m,
            th1 := rT1 n k m, th2 := th2 (rT1 n k m) n, ath := th2 (rT1 n k m) n,
            hsr := hs (rCk1 n k m) false (rT1 n k m), hsi := hs (rCk1 n k m) true (rT1 n k m), ck1 := rCk1 n k m }

def rfT4 (st : RState) (m : Msg) : Term := th4 st.th3 m.sealed.id
def rfT5 (st : RState) (m : Msg) : Term := th5 (rfT4 st m) m.sealed.sig
def rfCk2 (st : RState) (m : Msg) : Term := ck2 st.ck1 (rfT5 st m)
def rfRes (st : RState) (m : Msg) : Term := res (rfCk2 st m) (rfT5 st m)
def rfSto (st : RState) (n k : Nat) (sto : Store) (m : Msg) : Store :=
  let sto1 := IssueTicket sto (tid n k) (psk (rfRes st m) (tid n k)) m.sealed.id
  if st.fresh then { sto1 with pkc := st.hpk :: sto1.pkc } else sto1
def rfSt (st : RState) (n k : Nat) (m : Msg) : RState :=
  { st with ph := .done, peer := m.sealed.id, th4 := rfT4 st m, send := app (rfCk2 st m) false (rfT5 st m),
            recv := app (rfCk2 st m) true (rfT5 st m), res := rfRes st m, thf := rfT5 st m, mytid := tid n k,
            auth := true, est := true }
def rhSlot (sto : Store) (i0 : Nat) : Slot := sto.tks.getD i0 NoSlot
def rhThh (m : Msg) : Term := thH m.prm m.tid m.e
def rhThr (n k : Nat) (m : Msg) : Term := thR (rhThh m) m.binder ok (pub (ry n k))
def rhCk2 (n k : Nat) (sto : Store) (i0 : Nat) (m : Msg) : Term :=
  ck2 (ck1r (ckpsk (rhSlot sto i0).psk) (Dh (ry n k) (atomOf m.e))) (rhThr n k m)
def rhSt (st : RState) (n k : Nat) (sto : Store) (i0 : Nat) (m : Msg) : RState :=
  { st with ph := .done, peer := (rhSlot sto i0).peer, tid := m.tid, thh := rhThh m,
            early := early (ckpsk (rhSlot sto i0).psk) (rhThh m),
            send := app (rhCk2 n k sto i0 m) false (rhThr n k m), recv := app (rhCk2 n k sto i0 m) true (rhThr n k m),
            res := res (rhCk2 n k sto i0 m) (rhThr n k m), ath := rhThr n k m, thf := rhThr n k m, mytid := tid n k,
            sgn := true, auth := true, est := true, resumed := true }
def rhSto (n k : Nat) (sto : Store) (i0 : Nat) (m : Msg) : Store :=
  IssueTicket (RemoveSlot sto i0) (tid n k) (psk (res (rhCk2 n k sto i0 m) (rhThr n k m)) (tid n k)) (rhSlot sto i0).peer

def rhMsg (n k : Nat) (sto : Store) (i0 : Nat) (m : Msg) : Msg :=
  { ty := .rreply, e := pub (ry n k), tids := one (tid n k),
    conf := conf (cfk (rhCk2 n k sto i0 m) (rhThr n k m)) (thT (rhThr n k m) (one (tid n k))) }
def rkSig (st : RState) (n : Nat) : Term := sig n true st.th2
def rkReply (st : RState) (n k : Nat) : Msg :=
  { ty := .reply, e := pub (ry n k), ct := st.ct, sealed := ⟨st.hsr, st.th1, n, rkSig st n⟩ }
def rkSt (st : RState) (n k : Nat) : RState :=
  { st with ph := .finish, th3 := th3 st.th2 (rkSig st n), reply := rkReply st n k, sgn := true }

/-- Responder::on_initial. -/
def RInitial (st : RState) (n k : Nat) (sto : Store) (m : Msg) : RRes :=
  if st.ph = .failed then RDrop st sto
  else if st.ph = .finish then (if st.th0 = rT0 m then ROk st [st.reply] [] sto else RDrop st sto)
  else if st.ph ≠ .idle then RDrop st sto
  else if m.prm ≠ ok then RFatal st sto
  else if m.form = .short ∧ rHpk m ∉ sto.pkc then ROk st [{ ty := .prej, echo := rT0 m }] [] sto
  else ROk (rInitSt st n k m) [] [] sto

/-- Responder::on_key_response: the host's signature of the Reply. -/
def RKey (st : RState) (n k : Nat) (sto : Store) (kind : KRes) : RRes :=
  if st.ph = .sign ∧ kind = .ok then
    { st := rkSt st n k, out := [rkReply st n k], sto := sto, sg := [⟨n, true, st.th2⟩] }
  else if st.ph = .sign ∧ kind = .fail then RFatal st sto
  else RDrop st sto

/-- Responder::on_finish. -/
def RFinish (st : RState) (n k : Nat) (sto : Store) (m : Msg) : RRes :=
  if st.ph = .failed then RDrop st sto
  else if st.ph ≠ .finish then RDrop st sto
  else if m.sealed.k ≠ st.hsi ∨ m.sealed.ad ≠ st.th3 then RFatal st sto
  else if m.sealed.sig ≠ sig m.sealed.id false (rfT4 st m) then RFatal st sto
  else { st := rfSt st n k m, ev := [.est], sto := rfSto st n k sto m,
         iss := [⟨tid n k, psk (rfRes st m) (tid n k), m.sealed.id⟩] }

/-- Responder::on_hello. -/
def RHello (st : RState) (n k : Nat) (sto : Store) (m : Msg) : RRes :=
  let found := sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid)
  let i0 := found.getD 0
  let usable := found.isSome ∧ (rhSlot sto i0).exp = false ∧ binder (rhSlot sto i0).psk (rhThh m) = m.binder
  let stoRej := if found.isSome ∧ (rhSlot sto i0).exp = true then RemoveSlot sto i0 else sto
  if st.ph = .failed then RDrop st sto
  else if st.ph ≠ .idle then RDrop st sto
  else if m.prm ≠ ok then RFatal st sto
  else if ¬usable then ROk st [{ ty := .rrej, echo := rhThh m }] [] stoRej
  else { st := rhSt st n k sto i0 m, out := [rhMsg n k sto i0 m], ev := [.early, .est], sto := rhSto n k sto i0 m,
         iss := [⟨tid n k, psk (res (rhCk2 n k sto i0 m) (rhThr n k m)) (tid n k), (rhSlot sto i0).peer⟩] }

/-- Responder::handle. -/
def RHandle (st : RState) (n k : Nat) (sto : Store) (m : Msg) : RRes :=
  if st.ph = .failed then RDrop st sto
  else match m.ty with
    | .init => RInitial st n k sto m
    | .fin => RFinish st n k sto m
    | .hello => RHello st n k sto m
    | _ => RDrop st sto

end Vinc.Hs
