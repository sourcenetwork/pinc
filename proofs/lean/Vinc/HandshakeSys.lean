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

The actions are those of `Handshake.tla`. The store capacity `K` is arbitrary (at least 1 for `Victim` to name a slot;
all results hold for every `K`).
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
  cli : Nat → List Tk
  net : Msg → Prop
  signed : Nat → Bool → Term → Prop
  issued : Tk → Prop

/-- The initial state, for store capacity `K`. -/
def G0 (K : Nat) : G :=
  ⟨fun _ => {}, fun _ => {}, fun _ => { tks := List.replicate K NoSlot }, fun _ => [], fun _ => False,
   fun _ _ _ => False, fun _ => False⟩

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

/-- One step of the system. -/
inductive Step : G → G → Prop
  | startFull (g : G) (s : Nat × Nat) (peer : Nat) (short : Bool) :
      s.1 ≠ att → (g.ist s).ph = .none → peer ≠ s.1 →
      Step g { g with ist := upd g.ist s (IBeginFull s.1 (atom 0 s.1 s.2) peer short nil nil).st,
                      net := addNet g (IBeginFull s.1 (atom 0 s.1 s.2) peer short nil nil).out }
  | startResume (g : G) (s : Nat × Nat) (tk : Tk) :
      s.1 ≠ att → (g.ist s).ph = .none → tk ∈ g.cli s.1 →
      Step g { g with ist := upd g.ist s (IBeginResume s.1 (atom 0 s.1 s.2) tk).st,
                      cli := upd g.cli s.1 ((g.cli s.1).filter (· ≠ tk)),
                      net := addNet g (IBeginResume s.1 (atom 0 s.1 s.2) tk).out }
  | iRecv (g : G) (s : Nat × Nat) (m : Msg) :
      s.1 ≠ att → Derivable g m →
      Step g { g with ist := upd g.ist s (IHandle (g.ist s) s.1 m).st, net := addNet g (IHandle (g.ist s) s.1 m).out }
  | iAnswer (g : G) (s : Nat × Nat) (kind : KRes) :
      s.1 ≠ att →
      Step g { g with ist := upd g.ist s (IKey (g.ist s) s.1 kind).st, net := addNet g (IKey (g.ist s) s.1 kind).out,
                      signed := fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ (IKey (g.ist s) s.1 kind).sg }
  | iRetransmit (g : G) (s : Nat × Nat) :
      (g.ist s).ph = .reply → (g.ist s).short = true →
      Step g { g with net := addNet g [{ ty := .init, form := .full, e := pub (g.ist s).x, pk := ek s.1 }] }
  | iAcceptFull (g : G) (s r : Nat × Nat) :
      (g.ist s).ph = .done → (g.ist s).acc = false → (g.ist s).peer ≠ att → (g.ist s).resumed = false →
      r.1 = (g.ist s).peer → (g.rst r).ph = .done → (g.rst r).thf = (g.ist s).thf →
      Step g { g with ist := upd g.ist s { g.ist s with acc := true },
                      cli := upd g.cli s.1 (⟨(g.rst r).mytid, psk (g.ist s).res (g.rst r).mytid, (g.ist s).peer⟩ :: g.cli s.1) }
  | iAcceptResumed (g : G) (s : Nat × Nat) (t : Term) :
      (g.ist s).ph = .done → (g.ist s).acc = false → (g.ist s).peer ≠ att → (g.ist s).resumed = true →
      t ∈ tidsList (g.ist s).tids →
      Step g { g with ist := upd g.ist s { g.ist s with acc := true },
                      cli := upd g.cli s.1 (⟨t, psk (g.ist s).res t, (g.ist s).peer⟩ :: g.cli s.1) }
  | rRecv (g : G) (s : Nat × Nat) (m : Msg) :
      s.1 ≠ att → Derivable g m →
      Step g { g with rst := upd g.rst s (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).st,
                      sto := upd g.sto s.1 (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).sto,
                      net := addNet g (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).out,
                      issued := fun t => g.issued t ∨ t ∈ (RHandle (g.rst s) s.1 s.2 (g.sto s.1) m).iss }
  | rAnswer (g : G) (s : Nat × Nat) (kind : KRes) :
      s.1 ≠ att →
      Step g { g with rst := upd g.rst s (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).st,
                      net := addNet g (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).out,
                      signed := fun id r th => g.signed id r th ∨ ⟨id, r, th⟩ ∈ (RKey (g.rst s) s.1 s.2 (g.sto s.1) kind).sg }
  | expire (g : G) (n i : Nat) :
      Step g { g with sto := upd g.sto n { g.sto n with tks := (g.sto n).tks.modify i (fun sl => { sl with exp := true }) } }

/-- Reachable states for store capacity `K`. -/
inductive Reach (K : Nat) : G → Prop
  | init : Reach K (G0 K)
  | step {g g' : G} : Reach K g → Step g g' → Reach K g'

end Vinc.Hs
