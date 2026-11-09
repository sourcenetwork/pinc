import Vinc.HandshakeModel

/-!
# The global handshake system

Unboundedly many honest nodes, initiator and responder sessions `(node, k)`, tickets and store slots, running against
an attacker that owns the node `att`, learns every message sent (the network is the set of all of them, so any
message can be dropped, reordered, duplicated or replayed) and injects any message it can build (`Derivable`): a
sealed blob only under a key it knows (or one that is already on the network), a signature only of its own node or
one an honest node made, a binder or confirmation tag only under a key it knows (or one already on the network),
and every other field arbitrary. This is the Dolev-Yao closure over the network and the attacker's own secrets, and
a superset of what `ForgedToR` and `ForgedToI` of `Handshake.tla` build.

The actions are those of `Handshake.tla`, one function per action (`stepIStart`, ...) and one constructor of `Step`
per action with the enabling condition of the TLA+ action. The ticket ids a responder stores come from the
environment (`cs`, the draws of every ticket of a batch: any ids, collisions with stored ids included; the code
takes the first draw not stored, or fails). The store capacity `K` (server) and `C` (client) are arbitrary (at
least 1 for `Victim` to name a slot; all results hold for every `K` and `C`). The loss timers (`Retr`), the
acceptance of tickets (`Accept`) and the client store's export, restore and restart (`Persist`) are always enabled
(the TLA+ flags are configuration switches; the system here is the union).
-/

namespace Vinc.Hs
open Term

/-- Function update. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β := fun x => if x = a then b else f x

theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : upd f a b a = b := by simp [upd]
theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) (a x : α) (b : β) (h : x ≠ a) : upd f a b x = f x := by
  simp [upd, h]

/-- A global state. -/
structure G where
  ist : Nat × Nat → IState
  rst : Nat × Nat → RState
  sto : Nat → Store
  cli : Nat → List Slot
  snap : Nat → List Tk
  net : Msg → Prop
  signed : Nat → Bool → Term → Prop
  issued : Tk → Prop

/-- The initial state, for server store capacity `K` and client store capacity `C`. -/
def G0 (K C : Nat) : G :=
  ⟨fun _ => {}, fun _ => {}, fun _ => { tks := List.replicate K NoSlot }, fun _ => List.replicate C NoSlot,
   fun _ => [], fun _ => False, fun _ _ _ => False, fun _ => False⟩

/-- Every signature on the network of this shape is one the attacker may use: its own, or one an honest node made. -/
def SigGood (g : G) (b : Blob) : Prop :=
  ∀ id r th, b.sig = Term.sig id r th → id = att ∨ g.signed id r th

/-- Binders and confirmation tags the attacker can use: under a key it knows, or one already on the network. -/
def BinderOK (g : G) (b : Term) : Prop :=
  ∀ p th, b = Term.binder p th → Known p ∨ ∃ m, g.net m ∧ m.binder = b
def ConfOK (g : G) (c : Term) : Prop :=
  ∀ p th, c = Term.conf p th → Known p ∨ ∃ m, g.net m ∧ m.conf = c

/-- The messages that can be delivered: everything ever sent, and everything the attacker can build. -/
def Derivable (g : G) (m : Msg) : Prop :=
  g.net m ∨
  (SigGood g m.sealed ∧ (m.sealed.k = nil ∨ Known m.sealed.k ∨ ∃ m', g.net m' ∧ m'.sealed = m.sealed)
    ∧ BinderOK g m.binder ∧ ConfOK g m.conf)

def addNet (g : G) (out : List Msg) : Msg → Prop := fun m => g.net m ∨ m ∈ out

/-- The signatures a step made join the ledger. -/
def addSig (g : G) (sg : List SigE) : Nat → Bool → Term → Prop := fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ sg

/-- The tickets of an initiator's finished session as the client store receives them (`accept_batch`). -/
def acceptTks (st : IState) (tids : List Term) : List Tk :=
  tids.map (fun t => ⟨t, psk st.res t st.pcr, st.peer, st.al, st.ad, st.pcr⟩)

/-- The ticket ids a finished initiator session hands to its node's store: its own (resumed), or those of a finished
responder session of its peer with the same final transcript (full). -/
def AcceptTids (g : G) (s : Nat × Nat) (tids : List Term) : Prop :=
  if (g.ist s).resumed = true then tids = (g.ist s).tids
  else ∃ r : Nat × Nat, r.1 = (g.ist s).peer ∧ (g.rst r).ph = .done ∧ (g.rst r).thf = (g.ist s).thf ∧
    tids = (g.rst r).mytids

/-- IStart: Initiator::new, the host may take a ticket of the peer for the ALPN from its store first. -/
def stepIStart (g : G) (s : Nat × Nat) (peer : Nat) (al : Term) (short take : Bool) : G :=
  let c : CTakeRes := if take then CTake (g.cli s.1) peer al else ⟨g.cli s.1, none⟩
  let r := INew s.1 s.2 peer al short c.tk
  { g with ist := upd g.ist s r.st, cli := upd g.cli s.1 c.sl, net := addNet g r.out }

def stepIRecv (g : G) (s : Nat × Nat) (m : Msg) : G :=
  { g with ist := upd g.ist s (IHandle (g.ist s) s.1 m).st, net := addNet g (IHandle (g.ist s) s.1 m).out }

def stepIAnswer (g : G) (s : Nat × Nat) (kind : KRes) : G :=
  { g with ist := upd g.ist s (IKey (g.ist s) s.1 kind).st, net := addNet g (IKey (g.ist s) s.1 kind).out,
           signed := addSig g (IKey (g.ist s) s.1 kind).sg }

def stepIRetrans (g : G) (s : Nat × Nat) : G :=
  { g with ist := upd g.ist s (IRetransmit s.1 (g.ist s)).st, net := addNet g (IRetransmit s.1 (g.ist s)).out }

def stepIShed (g : G) (s : Nat × Nat) : G := { g with ist := upd g.ist s (IShed (g.ist s)) }

def stepIAccept (g : G) (s : Nat × Nat) (tids : List Term) : G :=
  { g with cli := upd g.cli s.1 (CInsertAll (g.cli s.1) (acceptTks (g.ist s) tids)),
           ist := upd g.ist s { g.ist s with acc := true } }

def stepRRecv (g : G) (s : Nat × Nat) (m : Msg) (cs : List (List Nat)) : G :=
  { g with rst := upd g.rst s (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).st,
           sto := upd g.sto s.1 (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).sto,
           net := addNet g (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).out,
           issued := fun t => g.issued t ∨ t ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m cs).iss }

def stepRAnswer (g : G) (s : Nat × Nat) (kind : KRes) : G :=
  { g with rst := upd g.rst s (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).st,
           net := addNet g (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).out,
           signed := addSig g (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).sg }

def stepRRetrans (g : G) (s : Nat × Nat) : G :=
  { g with net := addNet g (RRetransmit (g.rst s) (g.sto s.1)).out }

def stepRShed (g : G) (s : Nat × Nat) : G := { g with rst := upd g.rst s (RShed (g.rst s)) }

def stepExpire (g : G) (n i : Nat) : G :=
  { g with sto := upd g.sto n { g.sto n with tks := (g.sto n).tks.modify i (fun sl => { sl with exp := true }) } }

def stepExpireC (g : G) (n i : Nat) : G :=
  { g with cli := upd g.cli n ((g.cli n).modify i (fun sl => { sl with exp := true })) }

def stepExport (g : G) (n mx : Nat) : G := { g with snap := upd g.snap n (CExport (g.cli n) mx) }

def stepRestore (g : G) (n : Nat) (drop : List Nat) : G :=
  { g with cli := upd g.cli n (CInsertAll (g.cli n) (KeepSeq (g.snap n) drop 0)) }

def stepRestart (g : G) (n : Nat) : G := { g with cli := upd g.cli n ((g.cli n).map (fun _ => NoSlot)) }

/-- One step of the system: the actions of `Next` of `Handshake.tla`. Sessions and nodes of the sessions are honest
(`≠ att`). -/
inductive Step : G → G → Prop
  | iStart (g : G) (s : Nat × Nat) (peer : Nat) (al : Term) (short take : Bool) :
      s.1 ≠ att → (g.ist s).ph = .none → peer ≠ s.1 →
      Step g (stepIStart g s peer al short take)
  | iRecv (g : G) (s : Nat × Nat) (m : Msg) :
      s.1 ≠ att → Derivable g m → Step g (stepIRecv g s m)
  | iAnswer (g : G) (s : Nat × Nat) (kind : KRes) :
      s.1 ≠ att → ((g.ist s).ph = .decap ∨ (g.ist s).ph = .sign) → Step g (stepIAnswer g s kind)
  | iRetrans (g : G) (s : Nat × Nat) :
      s.1 ≠ att → (g.ist s).ph ≠ .none → Step g (stepIRetrans g s)
  | iShed (g : G) (s : Nat × Nat) :
      s.1 ≠ att → (g.ist s).ph ≠ .none → Step g (stepIShed g s)
  | iAccept (g : G) (s : Nat × Nat) (tids : List Term) :
      s.1 ≠ att → (g.ist s).ph = .done → (g.ist s).acc = false → (g.ist s).peer ≠ att → AcceptTids g s tids →
      Step g (stepIAccept g s tids)
  | rRecv (g : G) (s : Nat × Nat) (m : Msg) (cs : List (List Nat)) :
      s.1 ≠ att → Derivable g m → Step g (stepRRecv g s m cs)
  | rAnswer (g : G) (s : Nat × Nat) (kind : KRes) :
      s.1 ≠ att → (g.rst s).ph = .sign → Step g (stepRAnswer g s kind)
  | rRetrans (g : G) (s : Nat × Nat) :
      s.1 ≠ att → (g.rst s).ph = .finish → Step g (stepRRetrans g s)
  | rShed (g : G) (s : Nat × Nat) :
      s.1 ≠ att → Step g (stepRShed g s)
  | expire (g : G) (n i : Nat) (sl : Slot) :
      n ≠ att → (g.sto n).tks[i]? = some sl → sl.occ = true → sl.exp = false → Step g (stepExpire g n i)
  | expireC (g : G) (n i : Nat) (sl : Slot) :
      n ≠ att → (g.cli n)[i]? = some sl → sl.occ = true → sl.exp = false → Step g (stepExpireC g n i)
  | export (g : G) (n mx : Nat) : n ≠ att → Step g (stepExport g n mx)
  | restore (g : G) (n : Nat) (drop : List Nat) : n ≠ att → Step g (stepRestore g n drop)
  | restart (g : G) (n : Nat) : n ≠ att → Step g (stepRestart g n)

/-- Reachable states for server store capacity `K` and client store capacity `C`. -/
inductive Reach (K C : Nat) : G → Prop
  | init : Reach K C (G0 K C)
  | step {g g' : G} : Reach K C g → Step g g' → Reach K C g'

end Vinc.Hs
