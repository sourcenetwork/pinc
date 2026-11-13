import Vinc.Axioms

-- model v1 ready

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
verdict (`ok`, `drop`: input dropped, `fatal`: the machine stopped) and the signatures made.

Every field of a message is its own field (version, ALPN, connection ids, credit record, AEAD offer and choice,
length) and its own argument of the transcript terms, as in HsOps.tla. Differences from the TLA+ text, none of which
changes a behaviour: indices are 0-based and "no index" is `none` (TLA+: 0); a list of ticket ids is a `List Term`
(bound into the transcript as the right-nested term `tlist`); the retransmission count `sends` and the bytes `spent`
are exact naturals (TLA+ keeps them modulo 3 and saturated, for a finite state space); store stamps are unbounded
naturals taken above every stamp in the store (TLA+ renumbers them densely after each operation, only their order is
ever read); the lengths of the messages and the budgets are the constants below (no theorem depends on their values).
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

/-- Symbolic terms; a free algebra (perfect primitives). The constructors are the term makers of HsOps.tla. -/
inductive Term where
  | nil | ok
  | alp (i : Nat) | badAlp
  | cid (role n k : Nat)
  | off (n : Nat) | badOff
  | crd (n : Nat)
  | aead (of : Term) (r : Nat)
  | tidT (c : Nat)
  | tnil | tcons (t rest : Term)
  | pub (a : Atom)
  | ek (n : Nat)
  | hash (t : Term)
  | ct (coin : Atom) (ek : Term)
  | dh (a b : Atom)
  | kem (coin : Atom) (ek : Term)
  | junk (n : Nat) (c : Term)
  | ck1 (a b : Term)
  | ck1r (a b : Term)
  | hs (k : Term) (dir : Bool) (th : Term)
  | ck2 (k th : Term)
  | app (k : Term) (dir : Bool) (th : Term)
  | res (k th : Term)
  | cfk (k th : Term)
  | cids (k th : Term)
  | psk (r tid cr : Term)
  | ckpsk (p : Term)
  | early (c th : Term)
  | binder (p th : Term)
  | conf (c t : Term)
  | sig (id : Nat) (resp : Bool) (th : Term)
  | th0 (v al dc sc cr of e hpk : Term)
  | th1 (t rsc ad e ct : Term)
  | th2 (t : Term) (id : Nat) (rcr : Term)
  | th3 (t sg : Term)
  | th4 (t : Term) (id : Nat)
  | th5 (t sg : Term)
  | thH (v al dc sc ad tid e cr : Term)
  | thR (h b rsc e rcr : Term)
  | thT (t tids : Term)
  deriving DecidableEq, Repr

open Term

/-- The node behind a prekey term (an unknown shape is the attacker's). -/
def ekNode : Term → Nat
  | ek o => o
  | _ => 0

/-- The attacker can compute `t` from its own secrets. -/
def Known : Term → Prop
  | dh a b => owner a = att ∨ owner b = att
  | kem c e => owner c = att ∨ ekNode e = att
  | junk _ _ => False
  | ck1 a b => Known a ∧ Known b
  | ck1r a b => Known a ∧ Known b
  | hs k _ _ => Known k
  | ck2 k _ => Known k
  | app k _ _ => Known k
  | res k _ => Known k
  | cfk k _ => Known k
  | cids k _ => Known k
  | psk k _ _ => Known k
  | ckpsk k => Known k
  | early k _ => Known k
  | binder k _ => Known k
  | conf k _ => Known k
  | _ => False

/-- The same deduction with a half of the hybrid broken (`Known` of `HsOps.tla` with `BX` and `BK`): with `bx` the
attacker learns the Diffie-Hellman secret of every exchange (it sees every public value), with `bk` the KEM secret of
every ciphertext and the implicit-rejection value of every malformed one (`junk`). Signatures, hashes and the AEAD
stay ideal. With neither it is `Known` (`KnownB_ff`). -/
def KnownB (bx bk : Bool) : Term → Prop
  | dh a b => bx = true ∨ owner a = att ∨ owner b = att
  | kem c e => bk = true ∨ owner c = att ∨ ekNode e = att
  | junk _ _ => bk = true
  | ck1 a b => KnownB bx bk a ∧ KnownB bx bk b
  | ck1r a b => KnownB bx bk a ∧ KnownB bx bk b
  | hs k _ _ => KnownB bx bk k
  | ck2 k _ => KnownB bx bk k
  | app k _ _ => KnownB bx bk k
  | res k _ => KnownB bx bk k
  | cfk k _ => KnownB bx bk k
  | cids k _ => KnownB bx bk k
  | psk k _ _ => KnownB bx bk k
  | ckpsk k => KnownB bx bk k
  | early k _ => KnownB bx bk k
  | binder k _ => KnownB bx bk k
  | conf k _ => KnownB bx bk k
  | _ => False

theorem KnownB_ff (t : Term) : KnownB false false t ↔ Known t := by
  induction t <;> simp_all [KnownB, Known]

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

/-- A list of ticket ids as the right-nested term the transcript binds (`ThT`). -/
def tlist : List Term → Term
  | [] => tnil
  | t :: r => tcons t (tlist r)

theorem tlist_inj {a b : List Term} (h : tlist a = tlist b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [tlist]
  | cons x xs ih =>
    cases b with
    | nil => simp [tlist] at h
    | cons y ys => simp only [tlist, tcons.injEq] at h; rw [h.1, ih h.2]

/-! ## Field values -/

/-- The responder's own connection id for the session `(n, k)` (HsOps `RCid`). -/
def RCid (n k : Nat) : Term := cid 2 n k
/-- The responder's credit record (HsOps `RCr`). -/
def RCr (n : Nat) : Term := crd n
/-- The ALPNs the responders serve. -/
def Served (al : Term) : Prop := al = alp 1 ∨ al = alp 2
instance (al : Term) : Decidable (Served al) := by unfold Served; infer_instance
/-- The AEAD node `r` chooses from the offer `of` (none in common: `nil`). -/
def Choose (of : Term) (r : Nat) : Term := if of = badOff then nil else aead of r
/-- The reply AEAD is one of the initiator's offer (`ad[1] = "aead" /\ ad[2] = of`). -/
def inOfferB (of ad : Term) : Bool :=
  match ad with
  | aead o _ => o == of
  | _ => false
def InOffer (of ad : Term) : Prop := inOfferB of ad = true
instance (of ad : Term) : Decidable (InOffer of ad) := by unfold InOffer; infer_instance

/-! ## Constants -/

/-- Byte length of a full Initial, a short Initial, a resumption Hello and a resumption Reply, as the trace worlds
measure them (`TraceHandshake.cfg`); no theorem depends on the values. -/
def LF : Nat := 1258
def LS : Nat := 106
def LH : Nat := 122
def LR : Nat := 101
/-- `RESEND_BUDGET` and `LATE_INITIAL_BUDGET` of responder.rs. -/
def RB : Nat := 4096
def LB : Nat := 16384

/-! ## Messages -/

/-- A sealed blob: the key, the associated data and the plaintext (identity, signature, credit record). -/
structure Blob where
  k : Term
  ad : Term
  id : Nat
  sig : Term
  cr : Term
  deriving DecidableEq, Repr

def BadBlob : Blob := ⟨nil, nil, 0, nil, nil⟩

inductive MTy | nil | init | prej | reply | fin | hello | rreply | rrej
  deriving DecidableEq, Repr
inductive Form | nil | full | short
  deriving DecidableEq, Repr

/-- A handshake message; one record shape, unused fields are `nil` (HsOps `MNil`). -/
structure Msg where
  ty : MTy := .nil
  form : Form := .nil
  ver : Term := ok
  al : Term := alp 1
  dc : Term := nil
  sc : Term := nil
  of : Term := nil
  ad : Term := nil
  cr : Term := nil
  len : Nat := 0
  e : Term := nil
  pk : Term := nil
  ct : Term := nil
  sealed : Blob := BadBlob
  tid : Term := nil
  binder : Term := nil
  tids : List Term := []
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
inductive RPh | idle | sign | finish | resumed | done | failed
  deriving DecidableEq, Repr
inductive Mode | nil | short | full | resume | fallback
  deriving DecidableEq, Repr

/-- A signature made: the signer, whether it is the responder's, the transcript. -/
structure SigE where
  id : Nat
  resp : Bool
  th : Term
  deriving DecidableEq, Repr

/-! ## The stores (tickets.rs) -/

/-- A ticket: id, pre-shared key, the peer it was issued to (or, in a client store, issued by), ALPN, AEAD, the
credit record of the issuer. -/
structure Tk where
  tid : Term
  psk : Term
  peer : Nat
  al : Term
  ad : Term
  cr : Term
  deriving DecidableEq, Repr

/-- A ticket slot of a server or a client store. -/
structure Slot where
  occ : Bool := false
  tid : Term := nil
  psk : Term := nil
  peer : Nat := 0
  al : Term := nil
  ad : Term := nil
  cr : Term := nil
  exp : Bool := false
  stamp : Nat := 0
  deriving DecidableEq, Repr

def NoSlot : Slot := {}

/-- The shared state of one responder node: the prekey cache (hashes) and the ticket slots. -/
structure Store where
  pkc : List Term := []
  tks : List Slot := []
  deriving DecidableEq, Repr

def EmptyIdx (sl : List Slot) : Option Nat := sl.findIdx? (fun s => !s.occ)
def ExpiredIdx (sl : List Slot) : Option Nat := sl.findIdx? (fun s => s.occ && s.exp)

/-- The first occupied slot of the lowest stamp: the running best (index, stamp) over the slots from index `i`. -/
def oldestFrom : List Slot → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | [], _, best => best
  | s :: l, i, best =>
    oldestFrom l (i + 1)
      (if s.occ then (match best with
        | none => some (i, s.stamp)
        | some (j, b) => if s.stamp < b then some (i, s.stamp) else some (j, b))
       else best)

def OldestIdx (sl : List Slot) : Option Nat := (oldestFrom sl 0 none).map (·.1)

/-- tickets.rs victim: the first empty slot, else the first expired one, else the oldest; none for a store without
slots. -/
def Victim (sl : List Slot) : Option Nat := EmptyIdx sl <|> ExpiredIdx sl <|> OldestIdx sl

/-- A stamp above every stamp of the store. -/
def Stamp (sl : List Slot) : Nat := sl.foldl (fun a s => max a s.stamp) 0 + 1

/-- Store `x` at the index (nothing for none). -/
def Put (sl : List Slot) (v : Option Nat) (x : Slot) : List Slot :=
  match v with
  | none => sl
  | some i => sl.set i x

/-- ServerTickets: no occupied slot has the id. -/
def StoredIn (sl : List Slot) (t : Term) : Bool := sl.any (fun s => s.occ && s.tid == t)

/-- fresh_id: the first of the draws that no stored ticket has, or none (Failure::TicketId). -/
def FreshFrom (sl : List Slot) : List Nat → Option Term
  | [] => none
  | c :: r => if StoredIn sl (tidT c) then FreshFrom sl r else some (tidT c)

/-- One ticket of issue_batch. -/
structure One where
  ok : Bool
  sl : List Slot
  tid : Option Term

def IssueOne (sl : List Slot) (c : List Nat) (rs cr : Term) (peer : Nat) (al ad : Term) : One :=
  match FreshFrom sl c with
  | none => ⟨false, sl, none⟩
  | some tid =>
    let slot : Slot := { occ := true, tid := tid, psk := psk rs tid cr, peer := peer, al := al, ad := ad, cr := cr,
                         exp := false, stamp := Stamp sl }
    let v := Victim sl
    ⟨true, Put sl v slot, if v = none then none else some tid⟩

/-- The result of issue_batch: success, the slots, the ids of the tickets that did get stored. -/
structure Iss where
  ok : Bool
  sl : List Slot
  tids : List Term

/-- issue_batch: `cs` holds the draws of each ticket asked for. -/
def IssueAll (sl : List Slot) (rs cr : Term) (peer : Nat) (al ad : Term) (tids : List Term) : List (List Nat) → Iss
  | [] => ⟨true, sl, tids⟩
  | c :: cs =>
    let r := IssueOne sl c rs cr peer al ad
    if !r.ok then ⟨false, r.sl, tids⟩
    else IssueAll r.sl rs cr peer al ad (match r.tid with | none => tids | some t => tids ++ [t]) cs

def Issue (sl : List Slot) (cs : List (List Nat)) (rs cr : Term) (peer : Nat) (al ad : Term) : Iss :=
  IssueAll sl rs cr peer al ad [] cs

/-- The tickets an issue produced, for the ledger. -/
def IssuedOf (tids : List Term) (rs cr : Term) (peer : Nat) (al ad : Term) : List Tk :=
  tids.map (fun t => ⟨t, psk rs t cr, peer, al, ad, cr⟩)

def TicketOf (s : Slot) : Tk := ⟨s.tid, s.psk, s.peer, s.al, s.ad, s.cr⟩

/-- ClientTickets insert: the peer's slot is replaced; else the victim. -/
def CFindPeer (sl : List Slot) (peer : Nat) : Option Nat := sl.findIdx? (fun s => s.occ && s.peer == peer)

def CInsert (sl : List Slot) (tk : Tk) : List Slot :=
  let slot : Slot := { occ := true, tid := tk.tid, psk := tk.psk, peer := tk.peer, al := tk.al, ad := tk.ad, cr := tk.cr,
                       exp := false, stamp := Stamp sl }
  Put sl (CFindPeer sl tk.peer <|> Victim sl) slot

/-- accept_batch: each ticket of the batch in order, so the last of a peer is the one kept. -/
def CInsertAll (sl : List Slot) : List Tk → List Slot
  | [] => sl
  | t :: r => CInsertAll (CInsert sl t) r

/-- The entries of an export whose index is not in `drop`. -/
def KeepSeq : List Tk → List Nat → Nat → List Tk
  | [], _, _ => []
  | t :: r, drop, j => (if j ∈ drop then [] else [t]) ++ KeepSeq r drop (j + 1)

structure CTakeRes where
  sl : List Slot
  tk : Option Tk

/-- take: expired tickets are dropped, then the peer's ticket for the ALPN is removed and returned (or none). -/
def CDropExpired (sl : List Slot) : List Slot := sl.map (fun s => if s.occ && s.exp then NoSlot else s)
def CFind (sl : List Slot) (peer : Nat) (al : Term) : Option Nat :=
  sl.findIdx? (fun s => s.occ && s.peer == peer && s.al == al)

def CTake (sl : List Slot) (peer : Nat) (al : Term) : CTakeRes :=
  let d := CDropExpired sl
  match CFind d peer al with
  | none => ⟨d, none⟩
  | some i => ⟨Put d (some i) NoSlot, some (TicketOf (d.getD i NoSlot))⟩

/-- export: the newest at most `mx` unexpired tickets, oldest first. -/
def Live (sl : List Slot) : List Slot := sl.filter (fun s => s.occ && !s.exp)
def CExport (sl : List Slot) (mx : Nat) : List Tk :=
  let all := ((Live sl).mergeSort (fun a b => decide (a.stamp ≤ b.stamp))).map TicketOf
  all.drop (all.length - mx)

/-! ## The initiator -/

/-- The context kept when a Hello gave way to a full Initial: a late resumption reply still counts. -/
structure Late where
  on : Bool := false
  x : Atom := ⟨0, 0, 0⟩
  thh : Term := nil
  binder : Term := nil
  ckpsk : Term := nil
  rcr : Term := nil
  ad : Term := nil
  deriving DecidableEq, Repr

def NoLate : Late := {}

/-- The initiator's local state (INil of HsOps.tla). -/
structure IState where
  ph : IPh := .none
  peer : Nat := 0
  x : Atom := ⟨0, 0, 0⟩
  short : Bool := false
  th0 : Term := nil
  mode : Mode := .nil
  al : Term := nil
  dc : Term := nil
  sc : Term := nil
  of : Term := nil
  cr : Term := nil
  sends : Nat := 0
  ckpsk : Term := nil
  thh : Term := nil
  binder : Term := nil
  early : Term := nil
  tid : Term := nil
  late : Late := {}
  reply : Msg := {}
  th1 : Term := nil
  ssx : Term := nil
  hsi : Term := nil
  ck1 : Term := nil
  th2 : Term := nil
  th3 : Term := nil
  th4 : Term := nil
  fin : Msg := {}
  send : Term := nil
  recv : Term := nil
  res : Term := nil
  cid : Term := nil
  ath : Term := nil
  thf : Term := nil
  tids : List Term := []
  ad : Term := nil
  pcr : Term := nil
  rcr : Term := nil
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

/-- The Initial of an initiator in the short or the full form (write_initial). -/
def IInitMsg (n : Nat) (st : IState) (short : Bool) : Msg :=
  { ty := .init, form := if short then .short else .full, ver := ok, al := st.al, dc := st.dc, sc := st.sc,
    of := st.of, cr := st.cr, len := if short then LS else LF, e := pub st.x,
    pk := if short then hash (ek n) else ek n }

/-- Initiator::begin_full: a fresh ephemeral `x` (and destination id `dcid`), the short or the full Initial; `st0`
holds the parameters of the dial. -/
def IBeginFull (n : Nat) (st0 : IState) (x : Atom) (dcid : Term) (short : Bool) (thh : Term) : IRes :=
  let st : IState := { st0 with ph := .reply, x := x, dc := dcid, short := short,
                                th0 := th0 ok st0.al dcid st0.sc st0.cr st0.of (pub x) (hash (ek n)),
                                mode := if short then .short else .full, thh := thh, early := nil, sends := 1 }
  Ok st [IInitMsg n st short] []

/-- The Hello of a resuming initiator. -/
def IHello (st : IState) : Msg :=
  { ty := .hello, ver := ok, al := st.al, dc := st.dc, sc := st.sc, ad := st.ad, tid := st.tid, e := pub st.x,
    binder := st.binder, cr := st.cr, len := LH }

/-- Initiator::begin_resume with a ticket. -/
def IBeginResume (_n : Nat) (st0 : IState) (x : Atom) (dcid : Term) (tk : Tk) : IRes :=
  let e := pub x
  let thh := thH ok st0.al dcid st0.sc tk.ad tk.tid e st0.cr
  let b := binder tk.psk thh
  let ckp := ckpsk tk.psk
  Ok { st0 with ph := .resume, x := x, dc := dcid, mode := .resume, ckpsk := ckp, thh := thh, binder := b,
                early := early ckp thh, tid := tk.tid, ad := tk.ad, rcr := tk.cr, sends := 1 }
    [{ ty := .hello, ver := ok, al := st0.al, dc := dcid, sc := st0.sc, ad := tk.ad, tid := tk.tid, e := e, binder := b,
       cr := st0.cr, len := LH }] [.early]

/-- Initiator::new: the dial parameters, and a ticket (none for no ticket). -/
def INew (n k : Nat) (peer : Nat) (al : Term) (short : Bool) (tk : Option Tk) : IRes :=
  let st0 : IState := { peer := peer, al := al, sc := cid 0 n k, of := off n, cr := crd n }
  let x := atom 0 n k
  let dcid := cid 1 n k
  match tk with
  | some t => IBeginResume n st0 x dcid t
  | none => IBeginFull n st0 x dcid short nil

/-- The resumption reply as the initiator computes it, from the secrets of a Hello (x, thh, binder, ckpsk). -/
def RrThr (thh binder : Term) (m : Msg) : Term := thR thh binder m.sc m.e m.cr
def RrCk2 (x : Atom) (ckp : Term) (thr : Term) (m : Msg) : Term := ck2 (ck1r ckp (Dh x (atomOf m.e))) thr
def RrConfOK (x : Atom) (ckp thh binder : Term) (m : Msg) : Prop :=
  m.conf = conf (cfk (RrCk2 x ckp (RrThr thh binder m) m) (RrThr thh binder m)) (thT (RrThr thh binder m) (tlist m.tids))
instance (x : Atom) (ckp thh binder : Term) (m : Msg) : Decidable (RrConfOK x ckp thh binder m) := by
  unfold RrConfOK; infer_instance

/-- finish_resume: the established session of a resumption whose reply authenticated. -/
def IResumed (st : IState) (x : Atom) (ckp thh binder rcr ad : Term) (m : Msg) : IState :=
  let thr := RrThr thh binder m
  let ck := RrCk2 x ckp thr m
  { st with ph := .done, send := app ck true thr, recv := app ck false thr, res := res ck thr, cid := cids ck thr,
            ath := thr, thf := thr, tids := m.tids, pcr := m.cr, rcr := rcr, ad := ad, fin := {}, late := NoLate,
            auth := true, est := true, resumed := true }

/-- Initiator::handle for a message `m` received by node `n`. -/
def IHandle (st : IState) (n : Nat) (m : Msg) : IRes :=
  if st.ph = .failed then Drop st
  else match m.ty with
    | .reply =>
      if st.ph ≠ .reply then Drop st
      else if ¬ InOffer st.of m.ad then Fatal st
      else Ok { st with ph := .decap, reply := m, ad := m.ad, th1 := th1 st.th0 m.sc m.ad m.e m.ct,
                        ssx := Dh st.x (atomOf m.e) } [] []
    | .prej =>
      if ¬(st.ph = .reply ∧ st.short = true) ∨ m.echo ≠ st.th0 then Drop st
      else Ok { st with short := false, mode := .full } [IInitMsg n st false] []
    | .rreply =>
      if st.ph = .resume then
        if ¬ RrConfOK st.x st.ckpsk st.thh st.binder m then Drop st
        else Ok (IResumed st st.x st.ckpsk st.thh st.binder st.rcr st.ad m) [] [.est]
      else if (st.ph = .reply ∨ st.ph = .decap ∨ st.ph = .sign) ∧ st.late.on = true then
        if ¬ RrConfOK st.late.x st.late.ckpsk st.late.thh st.late.binder m then Drop st
        else Ok (IResumed st st.late.x st.late.ckpsk st.late.thh st.late.binder st.late.rcr st.late.ad m) [] [.est]
      else Drop st
    | .rrej =>
      if st.ph ≠ .resume ∨ m.echo ≠ st.thh then Drop st
      else
        let b := IBeginFull n { st with late := NoLate } (atom 1 st.x.n st.x.k) (cid 2 n st.x.k) false st.thh
        Ok { b.st with mode := .fallback, fell := true } b.out [.rejected]
    | _ => Drop st

/-- Initiator::retransmit: the host's loss timer fired. -/
def IRetransmit (n : Nat) (st : IState) : IRes :=
  if st.ph = .reply ∧ st.short = true then
    Ok { st with sends := st.sends + 1 } [IInitMsg n st (decide ((st.sends + 1) % 3 ≠ 0))] []
  else if st.ph = .resume then
    if st.sends + 1 ≥ 3 then
      let late : Late := { on := true, x := st.x, thh := st.thh, binder := st.binder, ckpsk := st.ckpsk, rcr := st.rcr,
                           ad := st.ad }
      let b := IBeginFull n { st with late := late } (atom 1 st.x.n st.x.k) st.dc false st.thh
      Ok { b.st with mode := .fallback, fell := true } b.out [.rejected]
    else Ok { st with sends := st.sends + 1 } [IHello st] []
  else if st.ph = .reply then Ok st [IInitMsg n st false] []
  else if st.ph = .done ∧ st.fin ≠ {} then Ok st [st.fin] []
  else Ok st [] []

/-- Initiator::shed: the transport knows the peer has the session. -/
def IShed (st : IState) : IState := { st with late := NoLate, fin := {} }

/-- The KEM secret node `n` obtains by decapsulating `c`: the real one if the ciphertext is to its prekey, else an
unrelated value only `n` knows. -/
def Decap (n : Nat) (c : Term) : Term :=
  match c with
  | ct coin e => if e = ek n then kem coin e else junk n c
  | _ => junk n c

/-- The KEM secret the initiator decapsulates, and the chain key it derives. -/
def ikSsk (st : IState) (n : Nat) : Term := Decap n st.reply.ct
def ikCk1 (st : IState) (n : Nat) : Term := ck1 (ikSsk st n) st.ssx
def ikTh2 (st : IState) : Term := th2 st.th1 st.reply.sealed.id st.reply.sealed.cr

def ikSignSt (st : IState) (n : Nat) : IState :=
  { st with ph := .sign, hsi := hs (ikCk1 st n) true st.th1, ck1 := ikCk1 st n, th2 := ikTh2 st,
            th3 := th3 (ikTh2 st) st.reply.sealed.sig, th4 := th4 (th3 (ikTh2 st) st.reply.sealed.sig) n,
            ath := ikTh2 st, pcr := st.reply.sealed.cr, auth := true }

/-- The initiator after a Reply that does not open: the Reply is dropped and it waits for the next one. -/
def ikBackSt (st : IState) : IState := { st with ph := .reply, reply := {}, th1 := nil, ssx := nil }

def ikSig (st : IState) (n : Nat) : Term := sig n false st.th4
def ikT5 (st : IState) (n : Nat) : Term := th5 st.th4 (ikSig st n)
def ikCk2 (st : IState) (n : Nat) : Term := ck2 st.ck1 (ikT5 st n)
def ikFin (st : IState) (n : Nat) : Msg := { ty := .fin, sealed := ⟨st.hsi, st.th3, n, ikSig st n, nil⟩ }
def ikDoneSt (st : IState) (n : Nat) : IState :=
  { st with ph := .done, send := app (ikCk2 st n) true (ikT5 st n), recv := app (ikCk2 st n) false (ikT5 st n),
            res := res (ikCk2 st n) (ikT5 st n), cid := cids (ikCk2 st n) (ikT5 st n), thf := ikT5 st n,
            fin := ikFin st n, rcr := nil, est := true }

/-- Initiator::on_key_response. -/
def IKey (st : IState) (n : Nat) (kind : KRes) : IRes :=
  if st.ph = .decap ∧ kind = .ok then
    let b := st.reply.sealed
    if b.k ≠ hs (ikCk1 st n) false st.th1 ∨ b.ad ≠ st.th1 then
      -- the Reply does not open: it is dropped and the initiator waits for the next one
      { st := ikBackSt st, err := .drop }
    else if b.cr = nil then Fatal st
    else if b.id ≠ st.peer then Fatal st
    else if b.sig ≠ sig b.id true (ikTh2 st) then Fatal st
    else Ok (ikSignSt st n) [] []
  else if st.ph = .sign ∧ kind = .ok then
    { st := ikDoneSt st n, out := [ikFin st n], ev := [.est], sg := [⟨n, false, st.th4⟩] }
  else if (st.ph = .decap ∨ st.ph = .sign) ∧ kind = .fail then Fatal st
  else Drop st

/-! ## The responder and its stores -/

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
  cid : Term := nil
  ath : Term := nil
  thf : Term := nil
  th4 : Term := nil
  peer : Nat := 0
  tid : Term := nil
  tpsk : Term := nil
  thh : Term := nil
  early : Term := nil
  mytids : List Term := []
  al : Term := nil
  ad : Term := nil
  dc : Term := nil
  sc : Term := nil
  pcr : Term := nil
  rcr : Term := nil
  spent : Nat := 0
  nre : Nat := 0
  sgn : Bool := false
  auth : Bool := false
  est : Bool := false
  resumed : Bool := false
  deriving DecidableEq, Repr

def RemoveSlot (sto : Store) (i : Option Nat) : Store := { sto with tks := Put sto.tks i NoSlot }

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

/-- The responder session `s = (n, k)`: its ephemeral atom and its KEM coin. -/
def ry (n k : Nat) : Atom := atom 2 n k
def rcoin (n k : Nat) : Atom := atom 3 n k

def rHpk (m : Msg) : Term := if m.form = .full then hash m.pk else m.pk
def rEk (m : Msg) : Term := if m.form = .full then m.pk else (match rHpk m with | Term.hash t => t | _ => nil)
def rT0 (m : Msg) : Term := th0 m.ver m.al m.dc m.sc m.cr m.of m.e (rHpk m)
def rAd (n : Nat) (m : Msg) : Term := Choose m.of n
def rC (n k : Nat) (m : Msg) : Term := ct (rcoin n k) (rEk m)
def rT1 (n k : Nat) (m : Msg) : Term := th1 (rT0 m) (RCid n k) (rAd n m) (pub (ry n k)) (rC n k m)
def rT2 (n k : Nat) (m : Msg) : Term := th2 (rT1 n k m) n (RCr n)
def rCk1 (n k : Nat) (m : Msg) : Term := ck1 (kem (rcoin n k) (rEk m)) (Dh (ry n k) (atomOf m.e))
def rInitSt (st : RState) (n k : Nat) (m : Msg) : RState :=
  { st with ph := .sign, th0 := rT0 m, hpk := rHpk m, ek := rEk m, fresh := decide (m.form = .full), ct := rC n k m,
            th1 := rT1 n k m, th2 := rT2 n k m, ath := rT2 n k m,
            hsr := hs (rCk1 n k m) false (rT1 n k m), hsi := hs (rCk1 n k m) true (rT1 n k m), ck1 := rCk1 n k m,
            al := m.al, ad := rAd n m, dc := m.dc, sc := m.sc, pcr := m.cr }

/-- Responder::on_initial for the session `(n, k)`. The bytes of a resumed responder count whether or not the Reply
goes out again. -/
def RInitial (st : RState) (n k : Nat) (sto : Store) (m : Msg) : RRes :=
  let sp := st.spent + m.len
  let st1 : RState := { st with spent := sp }
  if st.ph = .failed then RDrop st sto
  else if st.ph = .finish then
    (if st.th0 = rT0 m then ROk st [st.reply] [] sto else RDrop st sto)
  else if st.ph = .resumed then
    (if st.dc = m.dc ∧ st.sc = m.sc then
      (if st.reply.len ≤ 3 * m.len ∧ sp ≤ LB then ROk { st1 with nre := st1.nre + 1 } [st.reply] [] sto
       else { st := st1, err := .drop, sto := sto })
     else RDrop st sto)
  else if st.ph ≠ .idle then RDrop st sto
  else if m.ver ≠ ok then RFatal st sto
  else if ¬ Served m.al then RFatal st sto
  else if rAd n m = nil then RFatal st sto
  else if m.form = .short ∧ rHpk m ∉ sto.pkc then ROk st [{ ty := .prej, echo := rT0 m }] [] sto
  else ROk (rInitSt st n k m) [] [] sto

def rkSig (st : RState) (n : Nat) : Term := sig n true st.th2
def rkReply (st : RState) (n k : Nat) : Msg :=
  { ty := .reply, sc := RCid n k, ad := st.ad, e := pub (ry n k), ct := st.ct,
    sealed := ⟨st.hsr, st.th1, n, rkSig st n, RCr n⟩ }
def rkSt (st : RState) (n k : Nat) : RState :=
  { st with ph := .finish, th3 := th3 st.th2 (rkSig st n), reply := rkReply st n k, sgn := true }

/-- Responder::on_key_response: the host's signature of the Reply. -/
def RKey (st : RState) (n k : Nat) (sto : Store) (kind : KRes) : RRes :=
  if st.ph = .sign ∧ kind = .ok then
    { st := rkSt st n k, out := [rkReply st n k], sto := sto, sg := [⟨n, true, st.th2⟩] }
  else if st.ph = .sign ∧ kind = .fail then RFatal st sto
  else RDrop st sto

def rfT4 (st : RState) (m : Msg) : Term := th4 st.th3 m.sealed.id
def rfT5 (st : RState) (m : Msg) : Term := th5 (rfT4 st m) m.sealed.sig
def rfCk2 (st : RState) (m : Msg) : Term := ck2 st.ck1 (rfT5 st m)
def rfRes (st : RState) (m : Msg) : Term := res (rfCk2 st m) (rfT5 st m)
def rfIs (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : Iss :=
  Issue sto.tks cs (rfRes st m) (RCr n) m.sealed.id st.al st.ad
def rfSto1 (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : Store :=
  { sto with tks := (rfIs st n sto m cs).sl }
def rfSto2 (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : Store :=
  if st.fresh then { rfSto1 st n sto m cs with pkc := st.hpk :: (rfSto1 st n sto m cs).pkc } else rfSto1 st n sto m cs
def rfIss (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : List Tk :=
  IssuedOf (rfIs st n sto m cs).tids (rfRes st m) (RCr n) m.sealed.id st.al st.ad
def rfSt (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : RState :=
  { st with ph := .done, peer := m.sealed.id, th4 := rfT4 st m, send := app (rfCk2 st m) false (rfT5 st m),
            recv := app (rfCk2 st m) true (rfT5 st m), res := rfRes st m, cid := cids (rfCk2 st m) (rfT5 st m),
            thf := rfT5 st m, mytids := (rfIs st n sto m cs).tids, auth := true, est := true }

/-- Responder::on_finish; `cs` are the id draws of issue_batch. -/
def RFinish (st : RState) (n : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : RRes :=
  if st.ph = .failed then RDrop st sto
  else if st.ph ≠ .finish then RDrop st sto
  else if m.sealed.k ≠ st.hsi ∨ m.sealed.ad ≠ st.th3 then RDrop st sto
  else if m.sealed.sig ≠ sig m.sealed.id false (rfT4 st m) then RFatal st sto
  else if (rfIs st n sto m cs).ok = false then
    { st := { st with ph := .failed }, ev := [.failed], err := .fatal, sto := rfSto1 st n sto m cs,
      iss := rfIss st n sto m cs }
  else { st := rfSt st n sto m cs, ev := [.est], sto := rfSto2 st n sto m cs, iss := rfIss st n sto m cs }

/-- Responder::on_repeated_hello: a repeat of the Hello answered; the Reply goes out again within the byte budget.
The bytes count whether or not the Reply goes out. -/
def RRepeat (st : RState) (sto : Store) (m : Msg) : RRes :=
  let thh := thH m.ver m.al m.dc m.sc m.ad m.tid m.e m.cr
  let sp := st.spent + m.len
  let st1 : RState := { st with spent := sp }
  if st.thh ≠ thh ∨ sp > RB then { st := st1, err := .drop, sto := sto }
  else { st := { st1 with nre := st1.nre + 1 }, out := [st.reply], sto := sto }

/-- The pieces of Responder::on_hello for the session `(n, k)`. -/
def rhThh (m : Msg) : Term := thH m.ver m.al m.dc m.sc m.ad m.tid m.e m.cr
def rhI0 (sto : Store) (m : Msg) : Option Nat := sto.tks.findIdx? (fun s => s.occ && s.tid == m.tid)
def rhSlot (sto : Store) (m : Msg) : Slot :=
  match rhI0 sto m with
  | none => NoSlot
  | some i => sto.tks.getD i NoSlot
def rhUsable (sto : Store) (m : Msg) : Prop :=
  (rhI0 sto m).isSome = true ∧ (rhSlot sto m).exp = false ∧ (rhSlot sto m).al = m.al ∧ (rhSlot sto m).ad = m.ad ∧
    binder (rhSlot sto m).psk (rhThh m) = m.binder
instance (sto : Store) (m : Msg) : Decidable (rhUsable sto m) := by unfold rhUsable; infer_instance
def rhThr (n k : Nat) (m : Msg) : Term := thR (rhThh m) m.binder (RCid n k) (pub (ry n k)) (RCr n)
def rhCk2 (n k : Nat) (sto : Store) (m : Msg) : Term :=
  ck2 (ck1r (ckpsk (rhSlot sto m).psk) (Dh (ry n k) (atomOf m.e))) (rhThr n k m)
def rhStoR (sto : Store) (m : Msg) : Store := RemoveSlot sto (rhI0 sto m)
def rhIs (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : Iss :=
  Issue (rhStoR sto m).tks cs (res (rhCk2 n k sto m) (rhThr n k m)) (RCr n) (rhSlot sto m).peer m.al (rhSlot sto m).ad
def rhSto1 (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : Store :=
  { rhStoR sto m with tks := (rhIs n k sto m cs).sl }
def rhStoRej (sto : Store) (m : Msg) : Store :=
  if (rhI0 sto m).isSome = true ∧ (rhSlot sto m).exp = true then rhStoR sto m else sto
def rhReply (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : Msg :=
  { ty := .rreply, sc := RCid n k, e := pub (ry n k), tids := (rhIs n k sto m cs).tids, cr := RCr n, len := LR,
    conf := conf (cfk (rhCk2 n k sto m) (rhThr n k m)) (thT (rhThr n k m) (tlist (rhIs n k sto m cs).tids)) }
def rhIss (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : List Tk :=
  IssuedOf (rhIs n k sto m cs).tids (res (rhCk2 n k sto m) (rhThr n k m)) (RCr n) (rhSlot sto m).peer m.al
    (rhSlot sto m).ad
def rhSt (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : RState :=
  { st with ph := .resumed, peer := (rhSlot sto m).peer, tid := m.tid, tpsk := (rhSlot sto m).psk, thh := rhThh m,
            early := early (ckpsk (rhSlot sto m).psk) (rhThh m),
            send := app (rhCk2 n k sto m) false (rhThr n k m), recv := app (rhCk2 n k sto m) true (rhThr n k m),
            res := res (rhCk2 n k sto m) (rhThr n k m), cid := cids (rhCk2 n k sto m) (rhThr n k m),
            ath := rhThr n k m, thf := rhThr n k m, mytids := (rhIs n k sto m cs).tids, al := m.al,
            ad := (rhSlot sto m).ad, dc := m.dc, sc := m.sc, pcr := m.cr, rcr := (rhSlot sto m).cr,
            reply := rhReply n k sto m cs, spent := 0, sgn := true, auth := true, est := true, resumed := true }

/-- Responder::on_hello; `cs` are the id draws of issue_batch. -/
def RHello (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : RRes :=
  if st.ph = .failed then RDrop st sto
  else if st.ph = .resumed then RRepeat st sto m
  else if st.ph ≠ .idle then RDrop st sto
  else if m.ver ≠ ok then RFatal st sto
  else if ¬ Served m.al then RFatal st sto
  else if ¬ rhUsable sto m then ROk st [{ ty := .rrej, echo := rhThh m }] [] (rhStoRej sto m)
  else if (rhIs n k sto m cs).ok = false then
    { st := { st with ph := .failed }, ev := [.failed], err := .fatal, sto := rhSto1 n k sto m cs,
      iss := rhIss n k sto m cs }
  else { st := rhSt st n k sto m cs, out := [rhReply n k sto m cs], ev := [.early, .est], sto := rhSto1 n k sto m cs,
         iss := rhIss n k sto m cs }

/-- Responder::retransmit: the loss timer fired while waiting for the Finish. -/
def RRetransmit (st : RState) (sto : Store) : RRes :=
  if st.ph = .finish then ROk st [st.reply] [] sto else RDrop st sto

/-- Responder::shed: the transport knows the peer has the session. -/
def RShed (st : RState) : RState := if st.ph = .resumed then { st with ph := .done } else st

/-- Responder::handle. -/
def RHandle (st : RState) (n k : Nat) (sto : Store) (m : Msg) (cs : List (List Nat)) : RRes :=
  if st.ph = .failed then RDrop st sto
  else match m.ty with
    | .init => RInitial st n k sto m
    | .fin => RFinish st n sto m cs
    | .hello => RHello st n k sto m cs
    | _ => RDrop st sto

end Vinc.Hs
