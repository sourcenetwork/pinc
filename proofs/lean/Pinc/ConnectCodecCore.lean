import Pinc.Varint
import Pinc.MembershipCodecNum

/-!
# The connectivity codecs: readers, writers and the field engine

The shared half of the model of the wire formats of `pinc-connect` (`carrier/frame.rs`, `relay/datagram.rs`,
`record.rs`, `local.rs`, `ticket.rs`, `relay/sleep.rs`, `client/punch.rs`): the reader and the writer of `pinc-wire`
as total functions over byte lists, the error types of the codecs as one inductive (`CErr`), and a table-driven field
engine for the formats that are a type byte followed by a fixed sequence of fields and an optional tail that runs to
the end of the input.

Bytes are `Nat`s below 256 (`Byte`). A node id is its 33 bytes (the algorithm tag, then 32 bytes), a field is a
`F`: a node, one byte, or raw bytes. Reading a field is `rdField`, the same step the code takes (`node::read`,
`take_alias`, `take_packet`, `take_body`, `read_u8`, `read_array`); a layout (`L`) reads its fields in order and then
its tail. Writing is a list of `Op`s run against a buffer of `cap` bytes (`run`): a `put` fails with the shortfall
exactly as `Writer::ensure` does, a `chk` is a validity check of the encoder, so the error an encoder returns is the
error of the first failing step, as in the code.

Theorems: a layout parses what it encodes (`rdLayout_enc`), accepts nothing else (`rdLayout_inv`), an encoder with
a buffer that holds the encoding returns it (`run_ok`), and with one that does not returns the shortfall
(`run_short`).
-/

namespace Pinc.ConnCodec
open Pinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-! ## Errors -/

/-- `WireError`. -/
inductive W where
  | trunc (needed : Nat)
  | small (needed : Nat)
  | vLong
  | vOver
  | vNonMin
  | unexpected (why : String)
  deriving DecidableEq, Repr

/-- Every error of the connectivity codecs, the nested enums of the code flattened: `FrameError`,
`DatagramError`, `RecordError`, `TicketError`, `BeaconError`. `dframe` is `DatagramError::Frame`, `daddr` is
`DatagramError::Addr`, `taddr` is `TicketError::Addr`, `baddr` is `BeaconError::Addr`. -/
inductive CErr where
  | wire (w : W)
  | unknownType (t : Nat)
  | trailing
  | alias (a : Nat)
  | packetSize
  | bodySize
  | status (s : Nat)
  | batch (why : String)
  | noRoom
  | magic
  | reach (t : Nat)
  | addrTag (t : Nat)
  | tooManyAddrs
  | hintsTooLong
  | version (v : Nat)
  | flags (f : Nat)
  | text
  | tooLong
  | padding
  | dframe (e : CErr)
  | daddr (e : CErr)
  | taddr (e : CErr)
  | baddr (e : CErr)
  deriving DecidableEq, Repr

/-- Lift the error of a `pinc-wire` step into the error type of a codec. -/
def liftW {α : Type} (lw : W → CErr) : Except W α → Except CErr α
  | .ok a => .ok a
  | .error e => .error (lw e)

@[simp] theorem liftW_ok {α : Type} (lw : W → CErr) (a : α) : liftW lw (.ok a) = .ok a := rfl
@[simp] theorem liftW_err {α : Type} (lw : W → CErr) (e : W) : liftW lw (.error e : Except W α) = .error (lw e) := rfl

theorem liftW_eq_ok {α : Type} {lw : W → CErr} {x : Except W α} {a : α} (h : liftW lw x = .ok a) : x = .ok a := by
  cases x <;> simp_all [liftW]

/-! ## The reader of `pinc-wire` -/

/-- `read_u8`. -/
def rdU8 : List Nat → Except W (Nat × List Nat)
  | [] => .error (.trunc 1)
  | x :: r => .ok (x, r)

/-- `read_bytes` (and `read_array`). -/
def rdBytes (n : Nat) (r : List Nat) : Except W (List Nat × List Nat) :=
  if n ≤ r.length then .ok (r.take n, r.drop n) else .error (.trunc (n - r.length))

/-- `read_u16`, `read_u32`, `read_u64`. -/
def rdBE (k : Nat) (r : List Nat) : Except W (Nat × List Nat) := do
  let (bs, r) ← rdBytes k r
  pure (beN bs, r)

/-- A node id is valid when it is an algorithm tag of the identity module and 32 bytes. -/
def NodeOk (b : List Nat) : Prop :=
  match b with
  | t :: bs => 1 ≤ t ∧ t ≤ 4 ∧ bs.length = 32
  | [] => False

/-- `node::read`: the tag, the 32 bytes, and only then the check of the tag. -/
def rdNode (r : List Nat) : Except W (List Nat × List Nat) := do
  let (t, r1) ← rdU8 r
  let (b, r2) ← rdBytes 32 r1
  if 1 ≤ t ∧ t ≤ 4 then pure (t :: b, r2) else throw (.unexpected "identity algorithm tag")

theorem bind_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

theorem rdBytes_app (a r : List Nat) : rdBytes a.length (a ++ r) = .ok (a, r) := by
  simp [rdBytes]

theorem rdBytes_ok {n r a r'} (h : rdBytes n r = .ok (a, r')) : r = a ++ r' ∧ a.length = n := by
  unfold rdBytes at h
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h
    simp_all
  · simp at h

theorem rdU8_ok {r x r'} (h : rdU8 r = .ok (x, r')) : r = x :: r' := by
  cases r with
  | nil => simp [rdU8] at h
  | cons y t => simp [rdU8] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem rdBE_app (k : Nat) (a r : List Nat) (h : a.length = k) : rdBE k (a ++ r) = .ok (beN a, r) := by
  subst h; simp [rdBE, rdBytes_app, bind, Except.bind, pure, Except.pure]

theorem rdBE_beBytes_lt (k v : Nat) (r : List Nat) (h : v < 256 ^ k) :
    rdBE k (beBytes k v ++ r) = .ok (v, r) := by
  rw [rdBE_app k _ r (beBytes_length k v), beN_beBytes, Nat.mod_eq_of_lt h]

theorem rdBE_ok {k r v r'} (h : rdBE k r = .ok (v, r')) : ∃ a, r = a ++ r' ∧ a.length = k ∧ v = beN a := by
  unfold rdBE at h
  cases hr : rdBytes k r with
  | error e => simp [hr, bind, Except.bind] at h
  | ok p =>
    obtain ⟨a, r2⟩ := p
    simp [hr, bind, Except.bind, pure, Except.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := rdBytes_ok hr
    exact ⟨a, h1, h2, rfl⟩

theorem rdNode_app (b r : List Nat) (h : NodeOk b) : rdNode (b ++ r) = .ok (b, r) := by
  rcases b with _ | ⟨t, bs⟩
  · exact absurd h (by simp [NodeOk])
  · obtain ⟨h1, h2, h3⟩ := h
    have e := rdBytes_app bs r
    rw [h3] at e
    simp [rdNode, rdU8, e, h1, h2, bind, Except.bind, pure, Except.pure]

theorem rdNode_ok {r b r'} (h : rdNode r = .ok (b, r')) : NodeOk b ∧ r = b ++ r' := by
  unfold rdNode at h
  simp only [bind_ok] at h
  obtain ⟨⟨t, r1⟩, h1, ⟨bs, r2⟩, h2, h⟩ := h
  have e1 := rdU8_ok h1
  obtain ⟨e2, l2⟩ := rdBytes_ok h2
  split at h
  · rename_i ht
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst e1 e2
    exact ⟨⟨ht.1, ht.2, l2⟩, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A rule of a parser: the input is refused with `e` unless `c` holds. -/
def chkE (c : Prop) [Decidable c] (e : CErr) : Except CErr Unit := if c then .ok () else .error e

theorem chkE_ok {c : Prop} [Decidable c] {e : CErr} (h : chkE c e = .ok ()) : c := by
  unfold chkE at h
  split at h
  · assumption
  · simp at h

theorem chkE_true {c : Prop} [Decidable c] (e : CErr) (h : c) : chkE c e = .ok () := by simp [chkE, h]

theorem chkE_false {c : Prop} [Decidable c] (e : CErr) (h : ¬ c) : chkE c e = .error e := by simp [chkE, h]

/-! ## Addresses -/

/-- `read_addr`: a family tag (4 or 6), the octets and the port; the tag is checked first, then the bytes are read in
two reads, as the code reads them. -/
def rdAddr (r : List Nat) : Except CErr (List Nat × List Nat) := do
  let (t, r1) ← liftW CErr.wire (rdU8 r)
  if t = 4 then do
    let (ip, r2) ← liftW CErr.wire (rdBytes 4 r1)
    let (pt, r3) ← liftW CErr.wire (rdBytes 2 r2)
    pure (t :: (ip ++ pt), r3)
  else if t = 6 then do
    let (ip, r2) ← liftW CErr.wire (rdBytes 16 r1)
    let (pt, r3) ← liftW CErr.wire (rdBytes 2 r2)
    pure (t :: (ip ++ pt), r3)
  else throw (CErr.addrTag t)

/-- The shape of an encoded address. -/
def AddrOk (b : List Nat) : Prop :=
  (∃ ip pt, b = 4 :: (ip ++ pt) ∧ ip.length = 4 ∧ pt.length = 2) ∨
    (∃ ip pt, b = 6 :: (ip ++ pt) ∧ ip.length = 16 ∧ pt.length = 2)

theorem rdAddr_app (b r : List Nat) (h : AddrOk b) : rdAddr (b ++ r) = .ok (b, r) := by
  rcases h with ⟨ip, pt, rfl, h1, h2⟩ | ⟨ip, pt, rfl, h1, h2⟩
  · have e1 := rdBytes_app ip (pt ++ r)
    have e2 := rdBytes_app pt r
    rw [h1] at e1
    rw [h2] at e2
    simp [rdAddr, rdU8, liftW, e1, e2, bind, Except.bind, pure, Except.pure]
  · have e1 := rdBytes_app ip (pt ++ r)
    have e2 := rdBytes_app pt r
    rw [h1] at e1
    rw [h2] at e2
    simp [rdAddr, rdU8, liftW, e1, e2, bind, Except.bind, pure, Except.pure]

theorem rdAddr_inv {r b r'} (h : rdAddr r = .ok (b, r')) : AddrOk b ∧ r = b ++ r' := by
  unfold rdAddr at h
  simp only [bind_ok] at h
  obtain ⟨⟨t, r1⟩, h1, h⟩ := h
  have e1 := rdU8_ok (liftW_eq_ok h1)
  subst e1
  by_cases h4 : t = 4
  · simp only [h4, ite_true, bind_ok, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨ip, r2⟩, h2, ⟨pt, r3⟩, h3, rfl, rfl⟩ := h
    obtain ⟨e2, l2⟩ := rdBytes_ok (liftW_eq_ok h2)
    obtain ⟨e3, l3⟩ := rdBytes_ok (liftW_eq_ok h3)
    subst e2 e3 h4
    exact ⟨Or.inl ⟨ip, pt, rfl, l2, l3⟩, by simp⟩
  · by_cases h6 : t = 6
    · simp only [if_neg h4, if_pos h6, bind_ok, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨ip, r2⟩, h2, ⟨pt, r3⟩, h3, rfl, rfl⟩ := h
      obtain ⟨e2, l2⟩ := rdBytes_ok (liftW_eq_ok h2)
      obtain ⟨e3, l3⟩ := rdBytes_ok (liftW_eq_ok h3)
      subst e2 e3 h6
      exact ⟨Or.inr ⟨ip, pt, rfl, l2, l3⟩, by simp⟩
    · simp [h4, h6, throw, throwThe, MonadExceptOf.throw] at h

/-- The wrapper the code puts around the error of an address: none, `DatagramError::Addr`, `TicketError::Addr`,
`BeaconError::Addr`. -/
def wrapA : Nat → CErr → CErr
  | 1 => CErr.daddr
  | 2 => CErr.taddr
  | 3 => CErr.baddr
  | _ => id

/-- Wrap the error of a step. -/
def mapE {α : Type} (f : CErr → CErr) : Except CErr α → Except CErr α
  | .ok a => .ok a
  | .error e => .error (f e)

theorem mapE_eq_ok {α : Type} {f : CErr → CErr} {x : Except CErr α} {a : α} (h : mapE f x = .ok a) : x = .ok a := by
  cases x <;> simp_all [mapE]

/-! ## The field engine -/

/-- One field of a layout. -/
inductive K where
  | node
  | alias
  | u8
  | fixed (n : Nat)
  | addr (w : Nat)
  deriving DecidableEq, Repr

/-- The value of a field. -/
inductive F where
  | node (b : List Nat)
  | u8 (b : Nat)
  | raw (b : List Nat)
  deriving DecidableEq, Repr

/-- The bytes a field writes. -/
def F.enc : F → List Nat
  | .node b => b
  | .u8 b => [b]
  | .raw b => b

/-- The bytes a list of fields writes. -/
def encFs (fs : List F) : List Nat := fs.flatMap F.enc

/-- The most aliases one carrier direction holds (`ALIAS_MAX`). -/
def aliasMax : Nat := 32

/-- One field read (`node::read`, `take_alias`, `read_u8`, `read_array`). -/
def rdField (lw : W → CErr) : K → List Nat → Except CErr (F × List Nat)
  | .node, r => liftW lw (do let (b, r) ← rdNode r; pure (F.node b, r))
  | .alias, r => do
    let (a, r) ← liftW lw (rdU8 r)
    if a < aliasMax then pure (F.u8 a, r) else throw (CErr.alias a)
  | .u8, r => liftW lw (do let (b, r) ← rdU8 r; pure (F.u8 b, r))
  | .fixed n, r => liftW lw (do let (b, r) ← rdBytes n r; pure (F.raw b, r))
  | .addr w, r => mapE (wrapA w) (do let (b, r) ← rdAddr r; pure (F.raw b, r))

/-- A field value is well formed for its kind. -/
def okK : K → F → Prop
  | .node, .node b => NodeOk b ∧ Byte b
  | .alias, .u8 a => a < aliasMax
  | .u8, .u8 b => b < 256
  | .fixed n, .raw b => b.length = n ∧ Byte b
  | .addr _, .raw b => AddrOk b ∧ Byte b
  | _, _ => False

/-- A layout: fixed-size fields, then an optional tail that runs to the end of the input. The tail is
`take_packet` or `take_body`: `max` is its bound and `e` the error for an empty or longer tail. -/
structure L where
  pre : List K
  tail : Option (Nat × CErr)

/-- The fields before the tail. -/
def rdPre (lw : W → CErr) : List K → List Nat → Except CErr (List F × List Nat)
  | [], r => .ok ([], r)
  | k :: ks, r => do
    let (f, r) ← rdField lw k r
    let (fs, r) ← rdPre lw ks r
    pure (f :: fs, r)

/-- The tail: all that is left, which must be 1 to `max` bytes. -/
def rdTail : Option (Nat × CErr) → List Nat → Except CErr (List F × List Nat)
  | none, r => .ok ([], r)
  | some (m, e), r => if r.length = 0 ∨ m < r.length then .error e else .ok ([F.raw r], [])

/-- All fields of a layout. -/
def rdLayout (lw : W → CErr) (l : L) (r : List Nat) : Except CErr (List F × List Nat) := do
  let (fs, r) ← rdPre lw l.pre r
  let (ts, r) ← rdTail l.tail r
  pure (fs ++ ts, r)

/-- The values match the kinds, position by position. -/
def PreOk : List K → List F → Prop
  | [], [] => True
  | k :: ks, f :: fs => okK k f ∧ PreOk ks fs
  | _, _ => False

/-- The tail value is within its bound. -/
def TailOk : Option (Nat × CErr) → List F → Prop
  | none, [] => True
  | some (m, _), [F.raw b] => 1 ≤ b.length ∧ b.length ≤ m ∧ Byte b
  | _, _ => False

/-- The fields are a well formed instance of the layout. -/
def LayoutOk (l : L) (fs : List F) : Prop :=
  ∃ pf tf, fs = pf ++ tf ∧ PreOk l.pre pf ∧ TailOk l.tail tf

theorem encFs_append (a b : List F) : encFs (a ++ b) = encFs a ++ encFs b := by
  simp [encFs, List.flatMap_append]

theorem rdField_app (lw : W → CErr) (k : K) (f : F) (h : okK k f) (r : List Nat) :
    rdField lw k (f.enc ++ r) = .ok (f, r) := by
  cases k <;> cases f <;> simp [okK] at h
  · obtain ⟨hn, _⟩ := h
    simp [rdField, F.enc, rdNode_app _ r hn, bind, Except.bind, pure, Except.pure]
  · rename_i a
    have h' : a < 32 := h
    simp [rdField, F.enc, rdU8, h', aliasMax, bind, Except.bind, pure, Except.pure]
  · simp [rdField, F.enc, rdU8, bind, Except.bind, pure, Except.pure]
  · obtain ⟨hl, _⟩ := h
    rename_i nn bb hh
    have e := rdBytes_app bb r
    rw [hl] at e
    simp [rdField, F.enc, e, bind, Except.bind, pure, Except.pure]
  · obtain ⟨ha, _⟩ := h
    simp [rdField, F.enc, rdAddr_app _ r ha, mapE, bind, Except.bind, pure, Except.pure]

theorem rdPre_app (lw : W → CErr) (ks : List K) (fs : List F) (h : PreOk ks fs) (r : List Nat) :
    rdPre lw ks (encFs fs ++ r) = .ok (fs, r) := by
  induction ks generalizing fs with
  | nil => cases fs <;> simp_all [PreOk, rdPre, encFs]
  | cons k ks ih =>
    cases fs with
    | nil => simp [PreOk] at h
    | cons f fs =>
      obtain ⟨h1, h2⟩ := h
      have e1 := rdField_app lw k f h1 (encFs fs ++ r)
      have e2 := ih fs h2
      simp only [encFs, List.flatMap_cons, List.append_assoc] at e1 e2 ⊢
      simp [rdPre, e1, e2, bind, Except.bind, pure, Except.pure]

theorem rdTail_enc (t : Option (Nat × CErr)) (tf : List F) (h : TailOk t tf) :
    rdTail t (encFs tf) = .ok (tf, []) := by
  rcases t with _ | ⟨m, e⟩
  · cases tf <;> simp_all [TailOk, rdTail, encFs]
  · rcases tf with _ | ⟨f, _ | ⟨g, tf⟩⟩
    · simp [TailOk] at h
    · cases f <;> simp [TailOk] at h
      rename_i b
      obtain ⟨h1, h2, _⟩ := h
      have : ¬ (b.length = 0 ∨ m < b.length) := by omega
      have hne : b ≠ [] := by intro h0; subst h0; simp at h1
      simp [rdTail, encFs, F.enc, hne]; omega
    · cases f <;> simp [TailOk] at h

/-- A layout reads what it writes. -/
theorem rdLayout_enc (lw : W → CErr) (l : L) (fs : List F) (h : LayoutOk l fs) :
    rdLayout lw l (encFs fs) = .ok (fs, []) := by
  obtain ⟨pf, tf, rfl, h1, h2⟩ := h
  have e1 := rdPre_app lw l.pre pf h1 (encFs tf)
  have e2 := rdTail_enc l.tail tf h2
  simp [rdLayout, encFs_append, e1, e2, bind, Except.bind, pure, Except.pure]

/-- A layout with no tail leaves what follows it. -/
theorem rdLayout_enc_app (lw : W → CErr) (l : L) (hl : l.tail = none) (fs : List F) (h : LayoutOk l fs)
    (r : List Nat) : rdLayout lw l (encFs fs ++ r) = .ok (fs, r) := by
  obtain ⟨pf, tf, rfl, h1, h2⟩ := h
  rw [hl] at h2
  cases tf with
  | cons => simp [TailOk] at h2
  | nil =>
    have e1 := rdPre_app lw l.pre pf h1 r
    simp [rdLayout, hl, rdTail, encFs_append, encFs, bind, Except.bind, pure, Except.pure] at e1 ⊢
    simp [e1]

theorem byte_append {a b : List Nat} (h : Byte (a ++ b)) : Byte a ∧ Byte b :=
  ⟨fun x hx => h x (by simp [hx]), fun x hx => h x (by simp [hx])⟩

theorem byte_cons {x : Nat} {b : List Nat} (h : Byte (x :: b)) : x < 256 ∧ Byte b :=
  ⟨h x (by simp), fun y hy => h y (by simp [hy])⟩

theorem rdField_inv (lw : W → CErr) (k : K) {r f r'} (h : rdField lw k r = .ok (f, r')) (hb : Byte r) :
    okK k f ∧ r = f.enc ++ r' := by
  cases k
  · have h1 := liftW_eq_ok h
    simp only [bind_ok] at h1
    obtain ⟨⟨b, r2⟩, h2, h3⟩ := h1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨hn, hr⟩ := rdNode_ok h2
    subst hr
    exact ⟨⟨hn, (byte_append hb).1⟩, rfl⟩
  · unfold rdField at h
    simp only [bind_ok] at h
    obtain ⟨⟨a, r2⟩, h2, h3⟩ := h
    have e := rdU8_ok (liftW_eq_ok h2)
    split at h3
    · rename_i ha
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      subst e
      exact ⟨ha, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h3
  · have h1 := liftW_eq_ok h
    simp only [bind_ok] at h1
    obtain ⟨⟨b, r2⟩, h2, h3⟩ := h1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    have e := rdU8_ok h2
    subst e
    exact ⟨(byte_cons hb).1, rfl⟩
  · have h1 := liftW_eq_ok h
    simp only [bind_ok] at h1
    obtain ⟨⟨b, r2⟩, h2, h3⟩ := h1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨e, l⟩ := rdBytes_ok h2
    subst e
    exact ⟨⟨l, (byte_append hb).1⟩, rfl⟩
  · have h1 := mapE_eq_ok h
    simp only [bind_ok] at h1
    obtain ⟨⟨b, r2⟩, h2, h3⟩ := h1
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨ha, e⟩ := rdAddr_inv h2
    subst e
    exact ⟨⟨ha, (byte_append hb).1⟩, rfl⟩

theorem rdPre_inv (lw : W → CErr) (ks : List K) :
    ∀ {r fs r'}, rdPre lw ks r = .ok (fs, r') → Byte r → PreOk ks fs ∧ r = encFs fs ++ r' := by
  induction ks with
  | nil =>
    intro r fs r' h _
    simp [rdPre] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [PreOk, encFs]
  | cons k ks ih =>
    intro r fs r' h hb
    unfold rdPre at h
    simp only [bind_ok] at h
    obtain ⟨⟨f, r1⟩, h1, ⟨fs1, r2⟩, h2, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hf, e1⟩ := rdField_inv lw k h1 hb
    subst e1
    obtain ⟨_, hb2⟩ := byte_append hb
    obtain ⟨hp, e2⟩ := ih h2 hb2
    subst e2
    refine ⟨⟨hf, hp⟩, ?_⟩
    simp [encFs]

theorem rdTail_inv {t : Option (Nat × CErr)} {r tf r'} (h : rdTail t r = .ok (tf, r')) (hb : Byte r) :
    TailOk t tf ∧ r = encFs tf ++ r' ∧ (t.isSome → r' = []) := by
  rcases t with _ | ⟨m, e⟩
  · simp [rdTail] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [TailOk, encFs]
  · by_cases hn : (r.length = 0 ∨ m < r.length)
    · simp only [rdTail] at h
      rw [if_pos hn] at h
      cases h
    · simp only [rdTail] at h
      rw [if_neg hn] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [not_or, Nat.not_lt] at hn
      refine ⟨⟨by omega, hn.2, hb⟩, by simp [encFs, F.enc], by simp⟩

/-- A layout accepts only what it writes. -/
theorem rdLayout_inv (lw : W → CErr) (l : L) {r fs r'} (h : rdLayout lw l r = .ok (fs, r')) (hb : Byte r) :
    LayoutOk l fs ∧ r = encFs fs ++ r' ∧ (l.tail.isSome → r' = []) := by
  unfold rdLayout at h
  simp only [bind_ok] at h
  obtain ⟨⟨pf, r1⟩, h1, ⟨tf, r2⟩, h2, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hp, e1⟩ := rdPre_inv lw l.pre h1 hb
  subst e1
  obtain ⟨_, hb2⟩ := byte_append hb
  obtain ⟨ht, e2, e3⟩ := rdTail_inv h2 hb2
  subst e2
  refine ⟨⟨pf, tf, rfl, hp, ht⟩, ?_, e3⟩
  simp [encFs_append]

/-! ## The writer -/

/-- A step of an encoder: write bytes, or check a rule of the encoder. -/
inductive Op where
  | put (bs : List Nat)
  | chk (ok : Bool) (e : CErr)

/-- The bytes a step writes. -/
def Op.bytes : Op → List Nat
  | .put bs => bs
  | .chk _ _ => []

/-- A step that cannot fail but for the buffer. -/
def Op.good : Op → Prop
  | .put _ => True
  | .chk b _ => b = true

/-- The bytes a list of steps writes. -/
def opsBytes (ops : List Op) : List Nat := ops.flatMap Op.bytes

/-- Run an encoder against a buffer of `cap` bytes holding `acc`: a `put` that does not fit fails with the
shortfall (`Writer::ensure`), a failed check fails with its error. -/
def run (lw : W → CErr) (cap : Nat) : List Op → List Nat → Except CErr (List Nat)
  | [], acc => .ok acc
  | .put bs :: ops, acc =>
    if bs.length ≤ cap - acc.length then run lw cap ops (acc ++ bs)
    else .error (lw (.small (bs.length - (cap - acc.length))))
  | .chk b e :: ops, acc => if b then run lw cap ops acc else .error e

theorem run_ok (lw : W → CErr) (cap : Nat) (ops : List Op) (hg : ∀ o ∈ ops, o.good) :
    ∀ acc : List Nat, acc.length + (opsBytes ops).length ≤ cap → run lw cap ops acc = .ok (acc ++ opsBytes ops) := by
  induction ops with
  | nil => intro acc _; simp [run, opsBytes]
  | cons o ops ih =>
    intro acc hc
    have hg' : ∀ o ∈ ops, o.good := fun x hx => hg x (by simp [hx])
    cases o with
    | put bs =>
      have hfit : bs.length ≤ cap - acc.length := by
        simp [opsBytes, Op.bytes] at hc; omega
      have := ih hg' (acc ++ bs) (by simp [opsBytes, Op.bytes] at hc ⊢; omega)
      simp only [run, hfit, ite_true, this, opsBytes, List.flatMap_cons, Op.bytes, List.append_assoc]
    | chk b e =>
      have hb : b = true := by have := hg (Op.chk b e) (by simp); simpa [Op.good] using this
      subst hb
      have := ih hg' acc (by simpa [opsBytes, Op.bytes] using hc)
      simpa [run, opsBytes, Op.bytes] using this

/-- A buffer that does not hold the encoding fails with the shortfall of the first write that overflows. -/
theorem run_short (lw : W → CErr) (cap : Nat) (ops : List Op) (hg : ∀ o ∈ ops, o.good) :
    ∀ acc : List Nat, acc.length ≤ cap → cap < acc.length + (opsBytes ops).length →
      ∃ k, 0 < k ∧ run lw cap ops acc = .error (lw (.small k)) := by
  induction ops with
  | nil => intro acc _ h; simp [opsBytes] at h; omega
  | cons o ops ih =>
    intro acc hle hc
    have hg' : ∀ o ∈ ops, o.good := fun x hx => hg x (by simp [hx])
    cases o with
    | put bs =>
      by_cases hfit : bs.length ≤ cap - acc.length
      · obtain ⟨k, hk, e⟩ := ih hg' (acc ++ bs) (by simp; omega) (by simp [opsBytes, Op.bytes] at hc ⊢; omega)
        exact ⟨k, hk, by simp only [run, hfit, ite_true, e]⟩
      · exact ⟨bs.length - (cap - acc.length), by omega, by simp only [run, hfit, ite_false]⟩
    | chk b e =>
      have hb : b = true := by have := hg (Op.chk b e) (by simp); simpa [Op.good] using this
      subst hb
      obtain ⟨k, hk, e'⟩ := ih hg' acc hle (by simpa [opsBytes, Op.bytes] using hc)
      exact ⟨k, hk, by simpa [run] using e'⟩

/-- The first failing check is the error, when everything before it fits the buffer. -/
theorem run_chk (lw : W → CErr) (cap : Nat) (pre rest : List Op) (e : CErr) (hg : ∀ o ∈ pre, o.good) :
    ∀ acc : List Nat, acc.length + (opsBytes pre).length ≤ cap →
      run lw cap (pre ++ Op.chk false e :: rest) acc = .error e := by
  induction pre with
  | nil => intro acc _; simp [run]
  | cons o pre ih =>
    intro acc hc
    have hg' : ∀ o ∈ pre, o.good := fun x hx => hg x (by simp [hx])
    cases o with
    | put bs =>
      have hfit : bs.length ≤ cap - acc.length := by simp [opsBytes, Op.bytes] at hc; omega
      have := ih hg' (acc ++ bs) (by simp [opsBytes, Op.bytes] at hc ⊢; omega)
      simpa [run, hfit] using this
    | chk b e' =>
      have hb : b = true := by have := hg (Op.chk b e') (by simp); simpa [Op.good] using this
      subst hb
      have := ih hg' acc (by simpa [opsBytes, Op.bytes] using hc)
      simpa [run] using this

end Pinc.ConnCodec
