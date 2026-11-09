import Vinc.DtnCodec
import Vinc.DtnLayout

/-!
# The head and acknowledgement codecs (`head.rs`, `custody.rs`, `endorse.rs`)

`SignedHead::{encode, decode}` and `CustodyAck::{encode, decode}` as `Codec`s built from the combinators of
`Vinc.DtnCodec`, field for field in the order of the code: the head is the bundle id (32 bytes), the source and
destination (an identity tag byte in 1..4 and 32 bytes), the creation time (`u64` wall, `u32` counter), the lifetime
(`u64`), the copy budget (`u16`), `k`, `m` and the slice log (`u8` each), the payload length (`u64`), the root (32
bytes), the key epoch (`u32`), the ephemeral key (32 bytes) and the KEM ciphertext (1088 bytes): `HEAD_LEN = 1287`
bytes, after which the layout must be valid (`Head::read` calls `layout()`). The endorsement is the two length
fields and the two byte strings, each length exactly the algorithm's public key and signature length
(`Endorsement::decode`); the zero padding of the in-memory form is a representation detail with no wire image. The
acknowledgement is the bundle id, the custodian, the previous custodian, the time, and the endorsement of the
custodian's algorithm (`ACK_BODY_LEN = 110` bytes before it).

What is not here: that a signature verifies is a property of the signature scheme, assumed (the codec only fixes the
bytes the signature covers: the unsigned head, which is the first `HEAD_LEN` bytes of the encoding).
-/

namespace Vinc.DtnCodecWire
open Vinc.DtnCodec

/-- `IdentityAlg::public_key_len` for the tags 1 (Ed25519), 2 (ECDSA P-256), 3 (ML-DSA-65), 4 (hybrid). -/
def pkLen : Nat → Nat
  | 1 => 32 | 2 => 33 | 3 => 1952 | 4 => 1984 | _ => 0

/-- `IdentityAlg::signature_len`. -/
def sigLen : Nat → Nat
  | 1 => 64 | 2 => 64 | 3 => 3309 | 4 => 3373 | _ => 0

abbrev Node := Nat × Bytes

/-- An identity: a known algorithm tag and 32 bytes (`get_node`). -/
def nodeC : Codec Node :=
  guardC (pair (uC 1) (bytesC 32)) (fun p => 1 ≤ p.1 ∧ p.1 ≤ 4)

/-- The endorsement for algorithm `alg`: public key length, public key, signature length, signature. -/
def endC (alg : Nat) : Codec (Nat × Bytes × Nat × Bytes) :=
  pairD (guardC (uC 2) (fun l => l = pkLen alg)) fun pl =>
    pair (bytesC pl) (pairD (guardC (uC 2) (fun l => l = sigLen alg)) fun sl => bytesC sl)

/-- The fields of a head, in wire order. -/
abbrev HeadT :=
  Bytes × Node × Node × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bytes × Nat × Bytes × Bytes

def headT : Codec HeadT :=
  pair (bytesC 32) (pair nodeC (pair nodeC (pair (uC 8) (pair (uC 4) (pair (uC 8) (pair (uC 2) (pair (uC 1)
    (pair (uC 1) (pair (uC 1) (pair (uC 8) (pair (bytesC 32) (pair (uC 4) (pair (bytesC 32) (bytesC 1088))))))))))))))

structure HeadM where
  id : Bytes
  src : Node
  dst : Node
  wall : Nat
  counter : Nat
  life : Nat
  copies : Nat
  k : Nat
  m : Nat
  log : Nat
  payload : Nat
  root : Bytes
  epoch : Nat
  eph : Bytes
  ct : Bytes

def HeadM.toT (h : HeadM) : HeadT :=
  (h.id, h.src, h.dst, h.wall, h.counter, h.life, h.copies, h.k, h.m, h.log, h.payload, h.root, h.epoch, h.eph, h.ct)

def HeadM.ofT (t : HeadT) : HeadM :=
  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- `Head::layout()` succeeds (the validation of `Head::read`). -/
def HeadM.layoutOk (h : HeadM) : Prop := (DtnLayout.L.valid ⟨h.k, h.m, h.log, h.payload⟩) = true

instance (h : HeadM) : Decidable h.layoutOk := inferInstanceAs (Decidable (_ = true))

/-- `Head::{write, read}`. -/
def headC : Codec HeadM :=
  guardC (mapC headT HeadM.ofT HeadM.toT (fun _ => rfl) (fun _ => rfl)) HeadM.layoutOk

/-- `SignedHead::{encode, decode}`. -/
def signedC : Codec (HeadM × (Nat × Bytes × Nat × Bytes)) :=
  pairD headC fun h => endC h.src.1

/-- The fields of an acknowledgement body: bundle, custodian, previous custodian, wall, counter. -/
abbrev AckT := Bytes × Node × Node × Nat × Nat

def ackBodyC : Codec AckT := pair (bytesC 32) (pair nodeC (pair nodeC (pair (uC 8) (uC 4))))

/-- `CustodyAck::{encode, decode}`. -/
def ackC : Codec (AckT × (Nat × Bytes × Nat × Bytes)) :=
  pairD ackBodyC fun b => endC b.2.1.1

/-! ## Fixed width -/

theorem headC_len (h : HeadM) (w : headC.wf h) : (headC.emit h).length = 1287 := by
  have e : headC.emit h = headT.emit h.toT := rfl
  rw [e]
  have w' : headT.wf h.toT := w.1
  obtain ⟨id, src, dst, wall, counter, life, copies, k, m, log, payload, root, epoch, eph, ct⟩ := h
  simp [HeadM.toT, headT, pair, pairD, bytesC, uC, toBE_length, nodeC, guardC] at w' ⊢
  omega

theorem signed_len (v : HeadM × (Nat × Bytes × Nat × Bytes)) (w : signedC.wf v) :
    (signedC.emit v).length = 1287 + 4 + pkLen v.1.src.1 + sigLen v.1.src.1 := by
  obtain ⟨h, pl, pk, sl, sg⟩ := v
  have hh := headC_len h w.1
  simp [signedC, pairD, endC, pair, guardC, bytesC, uC, toBE_length, List.length_append] at w ⊢
  obtain ⟨_, ⟨_, hpl⟩, hpk, ⟨_, hsl⟩, hsg⟩ := w
  omega

/-! ## The properties of the signed head -/

theorem signed_roundtrip (v) (w : signedC.wf v) : decodeAll signedC (signedC.emit v) = some v :=
  decodeAll_emit signedC v w

/-- Garbage is rejected: a byte string that decodes is the canonical encoding of a well-formed signed head. -/
theorem signed_canonical (bs v) (h : decodeAll signedC bs = some v) : bs = signedC.emit v ∧ signedC.wf v :=
  decodeAll_some signedC bs v h

theorem signed_injective (a b) (ha : signedC.wf a) (hb : signedC.wf b) (h : signedC.emit a = signedC.emit b) : a = b :=
  emit_inj signedC a b ha hb h

theorem signed_trailing (v) (w : signedC.wf v) (extra : Bytes) (hx : extra ≠ []) :
    decodeAll signedC (signedC.emit v ++ extra) = none :=
  decodeAll_trailing signedC v w extra hx

theorem signed_truncated (v) (w : signedC.wf v) (p q : Bytes) (hq : q ≠ []) (h : p ++ q = signedC.emit v) :
    decodeAll signedC p = none :=
  decodeAll_prefix signedC v w p q hq h

theorem nodeC_wf (n : Node) (w : nodeC.wf n) : 1 ≤ n.1 ∧ n.1 ≤ 4 := w.2

theorem headC_wf (h : HeadM) (w : headC.wf h) : nodeC.wf h.src ∧ nodeC.wf h.dst ∧ h.layoutOk :=
  ⟨w.1.2.1, w.1.2.2.1, w.2⟩

theorem endC_wf (a : Nat) (v : Nat × Bytes × Nat × Bytes) (w : (endC a).wf v) :
    v.1 = pkLen a ∧ v.2.2.1 = sigLen a ∧ v.2.1.length = v.1 ∧ v.2.2.2.length = v.2.2.1 :=
  ⟨w.1.2, w.2.2.1.2, w.2.1, w.2.2.2⟩

/-- What a decoded head satisfies: known identity tags, a valid layout, and endorsement lengths exactly those of the
source's algorithm. -/
theorem signed_checks (bs v) (h : decodeAll signedC bs = some v) :
    (1 ≤ v.1.src.1 ∧ v.1.src.1 ≤ 4) ∧ (1 ≤ v.1.dst.1 ∧ v.1.dst.1 ≤ 4) ∧ v.1.layoutOk ∧
      v.2.1 = pkLen v.1.src.1 ∧ v.2.2.2.1 = sigLen v.1.src.1 ∧ v.2.2.1.length = pkLen v.1.src.1 ∧
      v.2.2.2.2.length = sigLen v.1.src.1 := by
  have w := (decodeAll_some signedC bs v h).2
  have hw := headC_wf v.1 w.1
  have ew := endC_wf v.1.src.1 v.2 w.2
  refine ⟨nodeC_wf _ hw.1, nodeC_wf _ hw.2.1, hw.2.2, ew.1, ew.2.1, ?_, ?_⟩ <;> omega

/-! ## The properties of the acknowledgement -/

theorem ack_len (v : AckT × (Nat × Bytes × Nat × Bytes)) (w : ackC.wf v) :
    (ackC.emit v).length = 110 + 4 + pkLen v.1.2.1.1 + sigLen v.1.2.1.1 := by
  obtain ⟨⟨b, c, p, t, n⟩, pl, pk, sl, sg⟩ := v
  simp [ackC, ackBodyC, pairD, endC, pair, guardC, bytesC, uC, nodeC, toBE_length, List.length_append] at w ⊢
  obtain ⟨⟨hb, ⟨_, hc⟩, ⟨_, hp⟩, _, _⟩, ⟨_, hpl⟩, hpk, ⟨_, hsl⟩, hsg⟩ := w
  omega

theorem ack_roundtrip (v) (w : ackC.wf v) : decodeAll ackC (ackC.emit v) = some v :=
  decodeAll_emit ackC v w

theorem ack_canonical (bs v) (h : decodeAll ackC bs = some v) : bs = ackC.emit v ∧ ackC.wf v :=
  decodeAll_some ackC bs v h

theorem ack_injective (a b) (ha : ackC.wf a) (hb : ackC.wf b) (h : ackC.emit a = ackC.emit b) : a = b :=
  emit_inj ackC a b ha hb h

theorem ack_trailing (v) (w : ackC.wf v) (extra : Bytes) (hx : extra ≠ []) :
    decodeAll ackC (ackC.emit v ++ extra) = none :=
  decodeAll_trailing ackC v w extra hx

theorem ack_truncated (v) (w : ackC.wf v) (p q : Bytes) (hq : q ≠ []) (h : p ++ q = ackC.emit v) :
    decodeAll ackC p = none :=
  decodeAll_prefix ackC v w p q hq h

/-- The bytes the head signature covers are exactly the canonical head encoding, the first `HEAD_LEN` bytes of the
signed head. -/
theorem signed_body (h : HeadM) (e : Nat × Bytes × Nat × Bytes) :
    signedC.emit (h, e) = headC.emit h ++ (endC h.src.1).emit e := rfl

#print axioms signed_roundtrip
#print axioms signed_canonical
#print axioms signed_truncated
#print axioms signed_checks
#print axioms ack_canonical
#print axioms ack_len

end Vinc.DtnCodecWire
