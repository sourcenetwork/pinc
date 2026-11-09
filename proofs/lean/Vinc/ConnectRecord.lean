import Vinc.ConnectDatagram

/-!
# Signed records, beacons and sleep notices

`Record::parse` and `prepare` of `record.rs`, `Beacon::parse` and `prepare` of `local.rs`, `Notice::parse` and
`prepare` of `relay/sleep.rs`: the layouts of the three signed structures, with the key and signature lengths of the
node's algorithm. The signature check itself is the identity module's (`verify_node`); here a structure is its fields,
and what a parse accepts is exactly what `prepare` followed by `finish` writes.

* A record: `magic(8) node(33) home(33) seq(8) reach(1) n(1) addrs hint_len(1) hints public_key signature`.
* A beacon: `magic(8) node(33) seq(8) n(1) addrs hint_len(1) hint public_key signature`.
* A notice: `node(33) ts(8) public_key signature`.

Theorems per structure: `*_roundtrip`, `*_inv` (an accepted input is a valid structure that re-encodes to it),
`*_injective`, and the encoder: `*_prepare_ok` writes the bytes before the signature, and refuses too many
addresses or hints before writing anything.
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-- The public key length of the algorithm a node id names (`IdentityAlg::public_key_len`). -/
def pkLen : Nat → Nat
  | 1 => 32
  | 2 => 33
  | 3 => 1952
  | 4 => 1984
  | _ => 0

/-- The signature length of the algorithm (`IdentityAlg::signature_len`). -/
def sigLen : Nat → Nat
  | 1 => 64
  | 2 => 64
  | 3 => 3309
  | 4 => 3373
  | _ => 0

/-- The algorithm tag of an encoded node id. -/
def algOf (node : List Nat) : Nat := node.headD 0

/-- `MAGIC` of a record: `"VNCREC"` and the version `0, 1`. -/
def recMagic : List Nat := [86, 78, 67, 82, 69, 67, 0, 1]
/-- `MAGIC` of a beacon: `"VNCBCN"` and the version `0, 1`. -/
def beaconMagic : List Nat := [86, 78, 67, 66, 67, 78, 0, 1]

/-- The addresses of a list, read one after the other (`read_addr` `n` times); the error is wrapped as the caller
wraps it (`wrapA`). -/
def rdAddrs (w : Nat) : Nat → List Nat → Except CErr (List (List Nat) × List Nat)
  | 0, r => .ok ([], r)
  | k + 1, r => do
    let (a, r1) ← mapE (wrapA w) (rdAddr r)
    let (as, r2) ← rdAddrs w k r1
    pure (a :: as, r2)

theorem rdAddrs_app (w : Nat) (as : List (List Nat)) (h : ∀ a ∈ as, AddrOk a) (r : List Nat) :
    rdAddrs w as.length (as.flatten ++ r) = .ok (as, r) := by
  induction as with
  | nil => simp [rdAddrs]
  | cons a as ih =>
    have ha := h a (by simp)
    have e1 := rdAddr_app a (as.flatten ++ r) ha
    have e2 := ih (fun x hx => h x (by simp [hx]))
    simp [rdAddrs, e1, e2, mapE, bind, Except.bind, pure, Except.pure]

theorem rdAddrs_inv (w : Nat) : ∀ (n : Nat) {r as r'}, rdAddrs w n r = .ok (as, r') →
    as.length = n ∧ (∀ a ∈ as, AddrOk a) ∧ r = as.flatten ++ r' := by
  intro n
  induction n with
  | zero => intro r as r' h; simp [rdAddrs] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | succ n ih =>
    intro r as r' h
    unfold rdAddrs at h
    simp only [bind_ok] at h
    obtain ⟨⟨a, r1⟩, h1, ⟨as1, r2⟩, h2, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ha, e1⟩ := rdAddr_inv (mapE_eq_ok h1)
    obtain ⟨hl, hs, e2⟩ := ih h2
    subst e1 e2
    refine ⟨by simp [hl], ?_, by simp⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact hs x hx

theorem addrs_byte {as : List (List Nat)} (h : Byte as.flatten) : ∀ a ∈ as, Byte a := by
  intro a ha x hx
  exact h x (List.mem_flatten.2 ⟨a, ha, hx⟩)

/-! ## The record -/

/-- The fields of a record. -/
structure Rec where
  node : List Nat
  home : List Nat
  seq : Nat
  reach : Nat
  addrs : List (List Nat)
  hints : List Nat
  pk : List Nat
  sg : List Nat
  deriving DecidableEq, Repr

/-- `Record::parse` after the magic, the node ids and the sequence number. -/
def Rec.tail (node home : List Nat) (seq : Nat) (r : List Nat) : Except CErr Rec := do
  let (tag, r) ← liftW CErr.wire (rdU8 r)
  chkE (1 ≤ tag ∧ tag ≤ 5) (CErr.reach tag)
  let (n, r) ← liftW CErr.wire (rdU8 r)
  chkE (n ≤ 8) CErr.tooManyAddrs
  let (addrs, r) ← rdAddrs 0 n r
  let (hl, r) ← liftW CErr.wire (rdU8 r)
  chkE (hl ≤ 64) CErr.hintsTooLong
  let (hints, r) ← liftW CErr.wire (rdBytes hl r)
  let (pk, r) ← liftW CErr.wire (rdBytes (pkLen (algOf node)) r)
  let (sg, r) ← liftW CErr.wire (rdBytes (sigLen (algOf node)) r)
  chkE (r = []) CErr.trailing
  pure ⟨node, home, seq, tag, addrs, hints, pk, sg⟩

/-- `Record::parse`. -/
def Rec.parse (b : List Nat) : Except CErr Rec := do
  let (m, r) ← liftW CErr.wire (rdBytes 8 b)
  chkE (m = recMagic) CErr.magic
  let (node, r) ← liftW CErr.wire (rdNode r)
  let (home, r) ← liftW CErr.wire (rdNode r)
  let (seq, r) ← liftW CErr.wire (rdBE 8 r)
  Rec.tail node home seq r

/-- Everything of a record but its signature: what `prepare` writes and the signature covers. -/
def Rec.head (r : Rec) : List Nat :=
  recMagic ++ r.node ++ r.home ++ beBytes 8 r.seq ++ [r.reach] ++ [r.addrs.length] ++ r.addrs.flatten ++
    [r.hints.length] ++ r.hints ++ r.pk

/-- The bytes of a record. -/
def Rec.bytes (r : Rec) : List Nat := r.head ++ r.sg

/-- A record the code can hold. -/
def Rec.valid (r : Rec) : Prop :=
  NodeOk r.node ∧ Byte r.node ∧ NodeOk r.home ∧ Byte r.home ∧ r.seq < 2 ^ 64 ∧ 1 ≤ r.reach ∧ r.reach ≤ 5 ∧
    r.addrs.length ≤ 8 ∧ (∀ a ∈ r.addrs, AddrOk a ∧ Byte a) ∧ r.hints.length ≤ 64 ∧ Byte r.hints ∧
    r.pk.length = pkLen (algOf r.node) ∧ Byte r.pk ∧ r.sg.length = sigLen (algOf r.node) ∧ Byte r.sg

/-- The steps of `prepare`: the bounds are checked before anything is written. -/
def Rec.prepareOps (r : Rec) : List Op :=
  [.chk (decide (r.addrs.length ≤ 8)) .tooManyAddrs, .chk (decide (r.hints.length ≤ 64)) .hintsTooLong,
    .put recMagic, .put r.node, .put r.home, .put (beBytes 8 r.seq), .put [r.reach], .put [r.addrs.length]] ++
    r.addrs.map Op.put ++ [.put [r.hints.length], .put r.hints, .put r.pk]

/-- `prepare` into a buffer of `cap` bytes: the bytes the signature covers. -/
def Rec.prepare (cap : Nat) (r : Rec) : Except CErr (List Nat) := run CErr.wire cap r.prepareOps []

/-- A record reads back. -/
theorem Rec.parse_bytes (r : Rec) (hv : r.valid) : Rec.parse r.bytes = .ok r := by
  obtain ⟨hn, hbn, hh, hbh, hs, hr1, hr2, hna, hal, hhl, hbhi, hpk, hbpk, hsg, hbsg⟩ := hv
  obtain ⟨node, home, seq, reach, addrs, hints, pk, sg⟩ := r
  simp only at *
  have e1 := rdBytes_app recMagic (node ++ home ++ beBytes 8 seq ++ [reach] ++ [addrs.length] ++ addrs.flatten ++
    [hints.length] ++ hints ++ pk ++ sg)
  have e2 := rdNode_app node (home ++ beBytes 8 seq ++ [reach] ++ [addrs.length] ++ addrs.flatten ++
    [hints.length] ++ hints ++ pk ++ sg) hn
  have e3 := rdNode_app home (beBytes 8 seq ++ [reach] ++ [addrs.length] ++ addrs.flatten ++
    [hints.length] ++ hints ++ pk ++ sg) hh
  have e4 := rdBE_beBytes_lt 8 seq ([reach] ++ [addrs.length] ++ addrs.flatten ++ [hints.length] ++ hints ++ pk ++ sg)
    (by rw [Vinc.MemCodec.p256_8]; exact hs)
  have e5 := rdAddrs_app 0 addrs (fun a ha => (hal a ha).1) ([hints.length] ++ hints ++ pk ++ sg)
  have e6 := rdBytes_app hints (pk ++ sg)
  have e7 := rdBytes_app pk sg
  have e8 := rdBytes_app sg []
  rw [hpk] at e7
  rw [hsg] at e8
  have hm : recMagic.length = 8 := rfl
  rw [hm] at e1
  have hrt : (1 ≤ reach ∧ reach ≤ 5) := ⟨hr1, hr2⟩
  have hn8 : addrs.length ≤ 8 := hna
  have hh64 : hints.length ≤ 64 := hhl
  simp only [Rec.bytes, Rec.head, List.append_assoc, List.singleton_append, List.cons_append, List.append_nil,
    List.nil_append]
    at e1 e2 e3 e4 e5 e6 e7 e8 ⊢
  simp [Rec.parse, Rec.tail, e1, e2, e3, e4, e5, e6, e7, e8, rdU8, liftW, hrt, hn8, hh64, chkE, bind, Except.bind, pure, Except.pure]

theorem Rec.parse_inv {b r} (h : Rec.parse b = .ok r) (hb : Byte b) : r.valid ∧ r.bytes = b := by
  unfold Rec.parse Rec.tail at h
  simp only [bind_ok] at h
  obtain ⟨⟨m, b1⟩, h1, u1, hu1, ⟨node, b2⟩, h2, ⟨home, b3⟩, h3, ⟨seq, b4⟩, h4, ⟨tag, b5⟩, h5, u2, hu2, ⟨n, b6⟩, h6,
    u3, hu3, ⟨addrs, b7⟩, h7, ⟨hl, b8⟩, h8, u4, hu4, ⟨hints, b9⟩, h9, ⟨pk, b10⟩, h10, ⟨sg, b11⟩, h11, u5, hu5, h⟩ := h
  have hm := chkE_ok hu1
  have htag := chkE_ok hu2
  have hn := chkE_ok hu3
  have hhl := chkE_ok hu4
  have hnil := chkE_ok hu5
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨e1, l1⟩ := rdBytes_ok (liftW_eq_ok h1)
  obtain ⟨hnode, e2⟩ := rdNode_ok (liftW_eq_ok h2)
  obtain ⟨hhome, e3⟩ := rdNode_ok (liftW_eq_ok h3)
  obtain ⟨a4, e4, l4, v4⟩ := rdBE_ok (liftW_eq_ok h4)
  have e5 := rdU8_ok (liftW_eq_ok h5)
  have e6 := rdU8_ok (liftW_eq_ok h6)
  obtain ⟨hlen, hal, e7⟩ := rdAddrs_inv 0 n h7
  have e8 := rdU8_ok (liftW_eq_ok h8)
  obtain ⟨e9, l9⟩ := rdBytes_ok (liftW_eq_ok h9)
  obtain ⟨e10, l10⟩ := rdBytes_ok (liftW_eq_ok h10)
  obtain ⟨e11, l11⟩ := rdBytes_ok (liftW_eq_ok h11)
  simp only at hnil
  subst hnil hm
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 v4
  simp only [List.append_nil] at *
  obtain ⟨_, hb1⟩ := byte_append hb
  obtain ⟨hbn, hb2⟩ := byte_append hb1
  obtain ⟨hbh, hb3⟩ := byte_append hb2
  obtain ⟨hba4, hb4⟩ := byte_append hb3
  obtain ⟨_, hb5⟩ := byte_cons hb4
  obtain ⟨_, hb6⟩ := byte_cons hb5
  obtain ⟨hbad, hb7⟩ := byte_append hb6
  obtain ⟨_, hb8⟩ := byte_cons hb7
  obtain ⟨hbhi, hb9⟩ := byte_append hb8
  obtain ⟨hbpk, hbsg⟩ := byte_append hb9
  have hbe : Vinc.MemCodec.beBytes 8 (beN a4) = a4 := Vinc.MemCodec.beBytes_beN 8 a4 l4 hba4
  have hlt : beN a4 < 2 ^ 64 := by
    have := beN_lt a4 hba4
    rw [l4, Vinc.MemCodec.p256_8] at this
    exact this
  have hn' : addrs.length ≤ 8 := by rw [hlen]; exact hn
  refine ⟨⟨hnode, hbn, hhome, hbh, hlt, htag.1, htag.2, hn', fun a ha => ⟨hal a ha, addrs_byte hbad a ha⟩,
    (by rw [l9]; exact hhl), hbhi, l10, hbpk, l11, hbsg⟩, ?_⟩
  simp [Rec.bytes, Rec.head, hbe, hlen, l9]

theorem flatMap_put (as : List (List Nat)) : (as.map Op.put).flatMap Op.bytes = as.flatten := by
  induction as with
  | nil => simp
  | cons a as ih => simp [Op.bytes, ih]

theorem Rec.prepare_good (r : Rec) (hv : r.valid) :
    (∀ o ∈ r.prepareOps, o.good) ∧ opsBytes r.prepareOps = r.head := by
  obtain ⟨hn, hbn, hh, hbh, hs, hr1, hr2, hna, hal, hhl, hbhi, hpk, hbpk, hsg, hbsg⟩ := hv
  refine ⟨?_, ?_⟩
  · intro o ho
    simp only [Rec.prepareOps, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ho
    rcases ho with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨a, _, rfl⟩) | (rfl | rfl | rfl) <;>
      simp [Op.good, hna, hhl]
  · simp [opsBytes, Rec.prepareOps, Rec.head, List.flatMap_append, flatMap_put, Op.bytes]

/-- `prepare` writes the bytes the signature covers when the buffer holds them. -/
theorem Rec.prepare_ok (cap : Nat) (r : Rec) (hv : r.valid) (hc : r.head.length ≤ cap) :
    r.prepare cap = .ok r.head := by
  obtain ⟨g, b⟩ := Rec.prepare_good r hv
  have := run_ok CErr.wire cap r.prepareOps g [] (by rw [b]; simpa using hc)
  simpa [Rec.prepare, b] using this

theorem Rec.prepare_short (cap : Nat) (r : Rec) (hv : r.valid) (hc : cap < r.head.length) :
    ∃ k, 0 < k ∧ r.prepare cap = .error (CErr.wire (.small k)) := by
  obtain ⟨g, b⟩ := Rec.prepare_good r hv
  exact run_short CErr.wire cap r.prepareOps g [] (by simp) (by rw [b]; simpa using hc)

/-- More than 8 addresses are refused before anything is written, whatever the buffer. -/
theorem Rec.prepare_toomany (cap : Nat) (r : Rec) (h : 8 < r.addrs.length) :
    r.prepare cap = .error .tooManyAddrs := by
  have := run_chk CErr.wire cap [] (r.prepareOps.drop 1) .tooManyAddrs (by simp) [] (by simp [opsBytes])
  have hd : decide (r.addrs.length ≤ 8) = false := by simp; omega
  simpa [Rec.prepare, Rec.prepareOps, hd] using this

/-- More than 64 hint bytes are refused before anything is written. -/
theorem Rec.prepare_hints (cap : Nat) (r : Rec) (h8 : r.addrs.length ≤ 8) (h : 64 < r.hints.length) :
    r.prepare cap = .error .hintsTooLong := by
  have := run_chk CErr.wire cap [Op.chk (decide (r.addrs.length ≤ 8)) .tooManyAddrs] (r.prepareOps.drop 2)
    .hintsTooLong (by simp [Op.good, h8]) [] (by simp [opsBytes, Op.bytes])
  have hd : decide (r.hints.length ≤ 64) = false := by simp; omega
  simpa [Rec.prepare, Rec.prepareOps, hd] using this

theorem Rec.parse_injective {a b r} (ha : Rec.parse a = .ok r) (hb : Rec.parse b = .ok r) (hba : Byte a)
    (hbb : Byte b) : a = b := by
  rw [← (Rec.parse_inv ha hba).2, ← (Rec.parse_inv hb hbb).2]

/-! ## The refusals of a record -/

theorem Rec.parse_empty : Rec.parse [] = .error (.wire (.trunc 8)) := by
  simp [Rec.parse, rdBytes, liftW, bind, Except.bind]

theorem Rec.parse_magic (b : List Nat) (h8 : 8 ≤ b.length) (h : b.take 8 ≠ recMagic) :
    Rec.parse b = .error .magic := by
  simp [Rec.parse, rdBytes, h8, liftW, chkE_false _ h, bind, Except.bind, chkE, h]

/-- The three nodes and the number: the prefix a record shares with every refusal below. -/
theorem Rec.parse_prefix (node home : List Nat) (seq : Nat) (rest : List Nat) (hn : NodeOk node) (hbn : Byte node)
    (hh : NodeOk home) (hbh : Byte home) (hs : seq < 2 ^ 64) :
    Rec.parse (recMagic ++ node ++ home ++ beBytes 8 seq ++ rest) = Rec.tail node home seq rest := by
  have e1 := rdBytes_app recMagic (node ++ home ++ beBytes 8 seq ++ rest)
  have e2 := rdNode_app node (home ++ beBytes 8 seq ++ rest) hn
  have e3 := rdNode_app home (beBytes 8 seq ++ rest) hh
  have e4 := rdBE_beBytes_lt 8 seq rest (by rw [Vinc.MemCodec.p256_8]; exact hs)
  have hm : recMagic.length = 8 := rfl
  rw [hm] at e1
  simp only [List.append_assoc] at e1 e2 e3 e4 ⊢
  simp [Rec.parse, e1, e2, e3, e4, liftW, chkE, bind, Except.bind]

theorem Rec.tail_reach (node home : List Nat) (seq tag : Nat) (rest : List Nat) (h : ¬ (1 ≤ tag ∧ tag ≤ 5)) :
    Rec.tail node home seq (tag :: rest) = .error (.reach tag) := by
  simp [Rec.tail, rdU8, liftW, chkE_false _ h, bind, Except.bind]

theorem Rec.tail_toomany (node home : List Nat) (seq tag n : Nat) (rest : List Nat) (ht : 1 ≤ tag ∧ tag ≤ 5)
    (h : 8 < n) : Rec.tail node home seq (tag :: n :: rest) = .error .tooManyAddrs := by
  have h' : ¬ (n ≤ 8) := by omega
  simp [Rec.tail, rdU8, liftW, chkE_true _ ht, chkE_false _ h', bind, Except.bind]

theorem Rec.tail_hints (node home : List Nat) (seq tag : Nat) (as : List (List Nat)) (hl : Nat) (rest : List Nat)
    (ht : 1 ≤ tag ∧ tag ≤ 5) (ha : ∀ a ∈ as, AddrOk a) (hn : as.length ≤ 8) (h : 64 < hl) :
    Rec.tail node home seq (tag :: as.length :: (as.flatten ++ hl :: rest)) = .error .hintsTooLong := by
  have e5 := rdAddrs_app 0 as ha (hl :: rest)
  have h' : ¬ (hl ≤ 64) := by omega
  simp [Rec.tail, rdU8, liftW, chkE_true _ ht, chkE_true _ hn, e5, chkE_false _ h', bind, Except.bind]

/-- Bytes after the signature are refused. -/
theorem Rec.parse_trailing (r : Rec) (hv : r.valid) (x : Nat) (t : List Nat) :
    Rec.parse (r.bytes ++ x :: t) = .error .trailing := by
  obtain ⟨hn, hbn, hh, hbh, hs, hr1, hr2, hna, hal, hhl, hbhi, hpk, hbpk, hsg, hbsg⟩ := hv
  obtain ⟨node, home, seq, reach, addrs, hints, pk, sg⟩ := r
  simp only at *
  have e5 := rdAddrs_app 0 addrs (fun a ha => (hal a ha).1) ([hints.length] ++ hints ++ pk ++ sg ++ x :: t)
  have e6 := rdBytes_app hints (pk ++ sg ++ x :: t)
  have e7 := rdBytes_app pk (sg ++ x :: t)
  have e8 := rdBytes_app sg (x :: t)
  rw [hpk] at e7
  rw [hsg] at e8
  have hrt : (1 ≤ reach ∧ reach ≤ 5) := ⟨hr1, hr2⟩
  have hn8 : addrs.length ≤ 8 := hna
  have hh64 : hints.length ≤ 64 := hhl
  have hp := Rec.parse_prefix node home seq ([reach] ++ [addrs.length] ++ addrs.flatten ++ [hints.length] ++ hints ++
    pk ++ sg ++ x :: t) hn hbn hh hbh hs
  have hne : ¬ (x :: t = []) := by simp
  simp only [Rec.bytes, Rec.head, List.append_assoc, List.singleton_append, List.cons_append, List.append_nil,
    List.nil_append] at e5 e6 e7 e8 hp ⊢
  rw [hp]
  simp [Rec.tail, e5, e6, e7, e8, rdU8, liftW, hrt, hn8, hh64, chkE_false _ hne, chkE, bind, Except.bind]

end Vinc.ConnCodec
