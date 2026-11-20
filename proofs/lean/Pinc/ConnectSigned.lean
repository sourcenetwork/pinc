import Pinc.ConnectRecord

/-!
# Beacons and sleep notices

`Beacon::parse` and `prepare` of `local.rs`, `Notice::parse`, `prepare` and `message` of `relay/sleep.rs`, in the style
of `ConnectRecord.lean`. A beacon is `magic(8) node(33) seq(8) n(1) addrs hint_len(1) hint public_key signature`
with at most 4 addresses and 8 hint bytes; a notice is `node(33) ts(8) public_key signature`, and the message its
signature covers is `"pinc-sleep" relay(33) node(33) ts(8)`.
-/

namespace Pinc.ConnCodec
open Pinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-! ## The beacon -/

/-- The fields of a beacon. -/
structure Bcn where
  node : List Nat
  seq : Nat
  addrs : List (List Nat)
  hint : List Nat
  pk : List Nat
  sg : List Nat
  deriving DecidableEq, Repr

/-- `Beacon::parse` after the magic, the node and the sequence number. -/
def Bcn.tail (node : List Nat) (seq : Nat) (r : List Nat) : Except CErr Bcn := do
  let (n, r) ← liftW CErr.wire (rdU8 r)
  chkE (n ≤ 4) CErr.tooLong
  let (addrs, r) ← rdAddrs 3 n r
  let (hl, r) ← liftW CErr.wire (rdU8 r)
  chkE (hl ≤ 8) CErr.tooLong
  let (hint, r) ← liftW CErr.wire (rdBytes hl r)
  let (pk, r) ← liftW CErr.wire (rdBytes (pkLen (algOf node)) r)
  let (sg, r) ← liftW CErr.wire (rdBytes (sigLen (algOf node)) r)
  chkE (r = []) CErr.trailing
  pure ⟨node, seq, addrs, hint, pk, sg⟩

/-- `Beacon::parse`. -/
def Bcn.parse (b : List Nat) : Except CErr Bcn := do
  let (m, r) ← liftW CErr.wire (rdBytes 8 b)
  chkE (m = beaconMagic) CErr.magic
  let (node, r) ← liftW CErr.wire (rdNode r)
  let (seq, r) ← liftW CErr.wire (rdBE 8 r)
  Bcn.tail node seq r

/-- What the signature of a beacon covers. -/
def Bcn.head (r : Bcn) : List Nat :=
  beaconMagic ++ r.node ++ beBytes 8 r.seq ++ [r.addrs.length] ++ r.addrs.flatten ++ [r.hint.length] ++ r.hint ++
    r.pk

def Bcn.bytes (r : Bcn) : List Nat := r.head ++ r.sg

def Bcn.valid (r : Bcn) : Prop :=
  NodeOk r.node ∧ Byte r.node ∧ r.seq < 2 ^ 64 ∧ r.addrs.length ≤ 4 ∧ (∀ a ∈ r.addrs, AddrOk a ∧ Byte a) ∧
    r.hint.length ≤ 8 ∧ Byte r.hint ∧ r.pk.length = pkLen (algOf r.node) ∧ Byte r.pk ∧
    r.sg.length = sigLen (algOf r.node) ∧ Byte r.sg

def Bcn.prepareOps (r : Bcn) : List Op :=
  [.chk (decide (r.addrs.length ≤ 4 ∧ r.hint.length ≤ 8)) .tooLong,
    .put beaconMagic, .put r.node, .put (beBytes 8 r.seq), .put [r.addrs.length]] ++
    r.addrs.map Op.put ++ [.put [r.hint.length], .put r.hint, .put r.pk]

def Bcn.prepare (cap : Nat) (r : Bcn) : Except CErr (List Nat) := run CErr.wire cap r.prepareOps []

theorem Bcn.parse_bytes (r : Bcn) (hv : r.valid) : Bcn.parse r.bytes = .ok r := by
  obtain ⟨hn, hbn, hs, hna, hal, hhl, hbhi, hpk, hbpk, hsg, hbsg⟩ := hv
  obtain ⟨node, seq, addrs, hint, pk, sg⟩ := r
  simp only at *
  have e1 := rdBytes_app beaconMagic (node ++ beBytes 8 seq ++ [addrs.length] ++ addrs.flatten ++
    [hint.length] ++ hint ++ pk ++ sg)
  have e2 := rdNode_app node (beBytes 8 seq ++ [addrs.length] ++ addrs.flatten ++ [hint.length] ++ hint ++ pk ++ sg) hn
  have e4 := rdBE_beBytes_lt 8 seq ([addrs.length] ++ addrs.flatten ++ [hint.length] ++ hint ++ pk ++ sg)
    (by rw [Pinc.MemCodec.p256_8]; exact hs)
  have e5 := rdAddrs_app 3 addrs (fun a ha => (hal a ha).1) ([hint.length] ++ hint ++ pk ++ sg)
  have e6 := rdBytes_app hint (pk ++ sg)
  have e7 := rdBytes_app pk sg
  have e8 := rdBytes_app sg []
  rw [hpk] at e7
  rw [hsg] at e8
  have hm : beaconMagic.length = 8 := rfl
  rw [hm] at e1
  have hn4 : addrs.length ≤ 4 := hna
  have hh8 : hint.length ≤ 8 := hhl
  simp only [Bcn.bytes, Bcn.head, List.append_assoc, List.singleton_append, List.cons_append, List.append_nil,
    List.nil_append] at e1 e2 e4 e5 e6 e7 e8 ⊢
  simp [Bcn.parse, Bcn.tail, e1, e2, e4, e5, e6, e7, e8, rdU8, liftW, hn4, hh8, chkE, bind, Except.bind, pure,
    Except.pure]

theorem Bcn.parse_inv {b r} (h : Bcn.parse b = .ok r) (hb : Byte b) : r.valid ∧ r.bytes = b := by
  unfold Bcn.parse Bcn.tail at h
  simp only [bind_ok] at h
  obtain ⟨⟨m, b1⟩, h1, u1, hu1, ⟨node, b2⟩, h2, ⟨seq, b3⟩, h3, ⟨n, b4⟩, h4, u3, hu3, ⟨addrs, b5⟩, h5, ⟨hl, b6⟩, h6,
    u4, hu4, ⟨hint, b7⟩, h7, ⟨pk, b8⟩, h8, ⟨sg, b9⟩, h9, u5, hu5, h⟩ := h
  have hm := chkE_ok hu1
  have hn := chkE_ok hu3
  have hhl := chkE_ok hu4
  have hnil := chkE_ok hu5
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨e1, l1⟩ := rdBytes_ok (liftW_eq_ok h1)
  obtain ⟨hnode, e2⟩ := rdNode_ok (liftW_eq_ok h2)
  obtain ⟨a3, e3, l3, v3⟩ := rdBE_ok (liftW_eq_ok h3)
  have e4 := rdU8_ok (liftW_eq_ok h4)
  obtain ⟨hlen, hal, e5⟩ := rdAddrs_inv 3 n h5
  have e6 := rdU8_ok (liftW_eq_ok h6)
  obtain ⟨e7, l7⟩ := rdBytes_ok (liftW_eq_ok h7)
  obtain ⟨e8, l8⟩ := rdBytes_ok (liftW_eq_ok h8)
  obtain ⟨e9, l9⟩ := rdBytes_ok (liftW_eq_ok h9)
  simp only at hnil
  subst hnil hm
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 v3
  simp only [List.append_nil] at *
  obtain ⟨_, hb1⟩ := byte_append hb
  obtain ⟨hbn, hb2⟩ := byte_append hb1
  obtain ⟨hba3, hb3⟩ := byte_append hb2
  obtain ⟨_, hb4⟩ := byte_cons hb3
  obtain ⟨hbad, hb5⟩ := byte_append hb4
  obtain ⟨_, hb6⟩ := byte_cons hb5
  obtain ⟨hbhi, hb7⟩ := byte_append hb6
  obtain ⟨hbpk, hbsg⟩ := byte_append hb7
  have hbe : Pinc.MemCodec.beBytes 8 (beN a3) = a3 := Pinc.MemCodec.beBytes_beN 8 a3 l3 hba3
  have hlt : beN a3 < 2 ^ 64 := by
    have := beN_lt a3 hba3
    rw [l3, Pinc.MemCodec.p256_8] at this
    exact this
  have hn' : addrs.length ≤ 4 := by rw [hlen]; exact hn
  refine ⟨⟨hnode, hbn, hlt, hn', fun a ha => ⟨hal a ha, addrs_byte hbad a ha⟩, (by rw [l7]; exact hhl), hbhi, l8,
    hbpk, l9, hbsg⟩, ?_⟩
  simp [Bcn.bytes, Bcn.head, hbe, hlen, l7]

theorem Bcn.parse_injective {a b r} (ha : Bcn.parse a = .ok r) (hb : Bcn.parse b = .ok r) (hba : Byte a)
    (hbb : Byte b) : a = b := by
  rw [← (Bcn.parse_inv ha hba).2, ← (Bcn.parse_inv hb hbb).2]

theorem Bcn.prepare_good (r : Bcn) (hv : r.valid) :
    (∀ o ∈ r.prepareOps, o.good) ∧ opsBytes r.prepareOps = r.head := by
  obtain ⟨hn, hbn, hs, hna, hal, hhl, hbhi, hpk, hbpk, hsg, hbsg⟩ := hv
  refine ⟨?_, ?_⟩
  · intro o ho
    simp only [Bcn.prepareOps, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ho
    rcases ho with ((rfl | rfl | rfl | rfl | rfl) | ⟨a, _, rfl⟩) | (rfl | rfl | rfl) <;> simp [Op.good, hna, hhl]
  · simp [opsBytes, Bcn.prepareOps, Bcn.head, List.flatMap_append, flatMap_put, Op.bytes]

theorem Bcn.prepare_ok (cap : Nat) (r : Bcn) (hv : r.valid) (hc : r.head.length ≤ cap) :
    r.prepare cap = .ok r.head := by
  obtain ⟨g, b⟩ := Bcn.prepare_good r hv
  have := run_ok CErr.wire cap r.prepareOps g [] (by rw [b]; simpa using hc)
  simpa [Bcn.prepare, b] using this

theorem Bcn.prepare_short (cap : Nat) (r : Bcn) (hv : r.valid) (hc : cap < r.head.length) :
    ∃ k, 0 < k ∧ r.prepare cap = .error (CErr.wire (.small k)) := by
  obtain ⟨g, b⟩ := Bcn.prepare_good r hv
  exact run_short CErr.wire cap r.prepareOps g [] (by simp) (by rw [b]; simpa using hc)

/-- Too many addresses or hint bytes are refused before anything is written. -/
theorem Bcn.prepare_toolong (cap : Nat) (r : Bcn) (h : ¬ (r.addrs.length ≤ 4 ∧ r.hint.length ≤ 8)) :
    r.prepare cap = .error .tooLong := by
  have := run_chk CErr.wire cap [] (r.prepareOps.drop 1) .tooLong (by simp) [] (by simp [opsBytes])
  have hd : decide (r.addrs.length ≤ 4 ∧ r.hint.length ≤ 8) = false := by simp; omega
  simpa [Bcn.prepare, Bcn.prepareOps, hd] using this

theorem Bcn.parse_empty : Bcn.parse [] = .error (.wire (.trunc 8)) := by
  simp [Bcn.parse, rdBytes, liftW, bind, Except.bind]

/-! ## The sleep notice -/

/-- The fields of a notice. -/
structure Ntc where
  node : List Nat
  ts : Nat
  pk : List Nat
  sg : List Nat
  deriving DecidableEq, Repr

/-- `Notice::parse`; bytes after the signature are `Wire(Unexpected("trailing bytes"))`. -/
def Ntc.parse (b : List Nat) : Except CErr Ntc := do
  let (node, r) ← liftW CErr.wire (rdNode b)
  let (ts, r) ← liftW CErr.wire (rdBE 8 r)
  let (pk, r) ← liftW CErr.wire (rdBytes (pkLen (algOf node)) r)
  let (sg, r) ← liftW CErr.wire (rdBytes (sigLen (algOf node)) r)
  chkE (r = []) (CErr.wire (.unexpected "trailing bytes"))
  pure ⟨node, ts, pk, sg⟩

def Ntc.head (r : Ntc) : List Nat := r.node ++ beBytes 8 r.ts ++ r.pk
def Ntc.bytes (r : Ntc) : List Nat := r.head ++ r.sg

def Ntc.valid (r : Ntc) : Prop :=
  NodeOk r.node ∧ Byte r.node ∧ r.ts < 2 ^ 64 ∧ r.pk.length = pkLen (algOf r.node) ∧ Byte r.pk ∧
    r.sg.length = sigLen (algOf r.node) ∧ Byte r.sg

def Ntc.prepareOps (r : Ntc) : List Op := [.put r.node, .put (beBytes 8 r.ts), .put r.pk]
def Ntc.prepare (cap : Nat) (r : Ntc) : Except CErr (List Nat) := run CErr.wire cap r.prepareOps []

theorem Ntc.parse_bytes (r : Ntc) (hv : r.valid) : Ntc.parse r.bytes = .ok r := by
  obtain ⟨hn, hbn, hs, hpk, hbpk, hsg, hbsg⟩ := hv
  obtain ⟨node, ts, pk, sg⟩ := r
  simp only at *
  have e2 := rdNode_app node (beBytes 8 ts ++ pk ++ sg) hn
  have e4 := rdBE_beBytes_lt 8 ts (pk ++ sg) (by rw [Pinc.MemCodec.p256_8]; exact hs)
  have e7 := rdBytes_app pk sg
  have e8 := rdBytes_app sg []
  rw [hpk] at e7
  rw [hsg] at e8
  simp only [Ntc.bytes, Ntc.head, List.append_assoc, List.append_nil] at e2 e4 e7 e8 ⊢
  simp [Ntc.parse, e2, e4, e7, e8, liftW, chkE, bind, Except.bind, pure, Except.pure]

theorem Ntc.parse_inv {b r} (h : Ntc.parse b = .ok r) (hb : Byte b) : r.valid ∧ r.bytes = b := by
  unfold Ntc.parse at h
  simp only [bind_ok] at h
  obtain ⟨⟨node, b1⟩, h1, ⟨ts, b2⟩, h2, ⟨pk, b3⟩, h3, ⟨sg, b4⟩, h4, u, hu, h⟩ := h
  have hnil := chkE_ok hu
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hnode, e1⟩ := rdNode_ok (liftW_eq_ok h1)
  obtain ⟨a2, e2, l2, v2⟩ := rdBE_ok (liftW_eq_ok h2)
  obtain ⟨e3, l3⟩ := rdBytes_ok (liftW_eq_ok h3)
  obtain ⟨e4, l4⟩ := rdBytes_ok (liftW_eq_ok h4)
  simp only at hnil
  subst hnil
  subst e1 e2 e3 e4 v2
  simp only [List.append_nil] at *
  obtain ⟨hbn, hb1⟩ := byte_append hb
  obtain ⟨hba2, hb2⟩ := byte_append hb1
  obtain ⟨hbpk, hbsg⟩ := byte_append hb2
  have hbe : Pinc.MemCodec.beBytes 8 (beN a2) = a2 := Pinc.MemCodec.beBytes_beN 8 a2 l2 hba2
  have hlt : beN a2 < 2 ^ 64 := by
    have := beN_lt a2 hba2
    rw [l2, Pinc.MemCodec.p256_8] at this
    exact this
  refine ⟨⟨hnode, hbn, hlt, l3, hbpk, l4, hbsg⟩, ?_⟩
  simp [Ntc.bytes, Ntc.head, hbe]

theorem Ntc.parse_injective {a b r} (ha : Ntc.parse a = .ok r) (hb : Ntc.parse b = .ok r) (hba : Byte a)
    (hbb : Byte b) : a = b := by
  rw [← (Ntc.parse_inv ha hba).2, ← (Ntc.parse_inv hb hbb).2]

theorem Ntc.prepare_ok (cap : Nat) (r : Ntc) (hv : r.valid) (hc : r.head.length ≤ cap) :
    r.prepare cap = .ok r.head := by
  have g : ∀ o ∈ r.prepareOps, o.good := by
    intro o ho; simp [Ntc.prepareOps] at ho; rcases ho with rfl | rfl | rfl <;> simp [Op.good]
  have b : opsBytes r.prepareOps = r.head := by simp [opsBytes, Ntc.prepareOps, Ntc.head, Op.bytes]
  have := run_ok CErr.wire cap r.prepareOps g [] (by rw [b]; simpa using hc)
  simpa [Ntc.prepare, b] using this

theorem Ntc.prepare_short (cap : Nat) (r : Ntc) (hc : cap < r.head.length) :
    ∃ k, 0 < k ∧ r.prepare cap = .error (CErr.wire (.small k)) := by
  have g : ∀ o ∈ r.prepareOps, o.good := by
    intro o ho; simp [Ntc.prepareOps] at ho; rcases ho with rfl | rfl | rfl <;> simp [Op.good]
  have b : opsBytes r.prepareOps = r.head := by simp [opsBytes, Ntc.prepareOps, Ntc.head, Op.bytes]
  exact run_short CErr.wire cap r.prepareOps g [] (by simp) (by rw [b]; simpa using hc)

/-- The label of the signed message of a sleep notice. -/
def sleepLabel : List Nat := [112, 105, 110, 99, 45, 115, 108, 101, 101, 112]

/-- `message`: what a notice's signature covers, the relay it is for, the node and the clock. -/
def sleepMessage (relay node : List Nat) (ts : Nat) : List Nat := sleepLabel ++ relay ++ node ++ beBytes 8 ts

/-- A notice for one relay is useless at another: the signed message determines the relay, the node and the clock. -/
theorem sleepMessage_injective (r1 n1 r2 n2 : List Nat) (t1 t2 : Nat) (hr1 : r1.length = 33) (hn1 : n1.length = 33)
    (hr2 : r2.length = 33) (hn2 : n2.length = 33) (ht1 : t1 < 2 ^ 64) (ht2 : t2 < 2 ^ 64)
    (h : sleepMessage r1 n1 t1 = sleepMessage r2 n2 t2) : r1 = r2 ∧ n1 = n2 ∧ t1 = t2 := by
  unfold sleepMessage at h
  simp only [List.append_assoc] at h
  have h1 := List.append_cancel_left h
  have e1 : r1 = r2 := by
    have := congrArg (List.take 33) h1
    rw [List.take_left' hr1, List.take_left' hr2] at this
    exact this
  subst e1
  have h2 := List.append_cancel_left h1
  have e2 : n1 = n2 := by
    have := congrArg (List.take 33) h2
    rw [List.take_left' hn1, List.take_left' hn2] at this
    exact this
  subst e2
  have h3 := List.append_cancel_left h2
  have := congrArg beN h3
  rw [beN_beBytes, beN_beBytes, Nat.mod_eq_of_lt (by rw [Pinc.MemCodec.p256_8]; exact ht1),
    Nat.mod_eq_of_lt (by rw [Pinc.MemCodec.p256_8]; exact ht2)] at this
  exact ⟨rfl, rfl, this⟩

theorem sleepMessage_length (relay node : List Nat) (ts : Nat) (hr : relay.length = 33) (hn : node.length = 33) :
    (sleepMessage relay node ts).length = 84 := by
  simp [sleepMessage, sleepLabel, hr, hn, beBytes_length]

theorem Ntc.parse_empty : Ntc.parse [] = .error (.wire (.trunc 1)) := by
  simp [Ntc.parse, rdNode, rdU8, liftW, bind, Except.bind]

end Pinc.ConnCodec
