import Vinc.ConnectFrameThm

/-!
# The carrier frame codec: the refusals

The exact error for each class of malformed input: an empty input, an unknown type, bytes after a fixed-size frame,
a missing or oversized packet (or record, or notice), an alias of 32 or more, an unknown answer status, a truncated
or mistagged node id, a batch count outside 2 to 64, and a batch of an empty frame. The theorems are about
`decode`; the encoder's refusals are `encode_field` (a field the decoder would refuse is refused by the encoder
once everything before it fits the buffer) and `encode_short`.
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

theorem decode_empty : decode [] = .error (.wire (.trunc 1)) := by
  simp [decode, decodeWith, rdU8, liftW, bind, Except.bind]

theorem decode_unknown (t : Nat) (r : List Nat) (hl : layoutOf t = none) (h13 : t ≠ 13) (h15 : t ≠ 15) :
    decode (t :: r) = .error (.unknownType t) := by
  simp [decode, decodeWith, rdU8, liftW, h13, h15, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Types 0, 1 and 19 or more are not frames. -/
theorem decode_unknown_low (t : Nat) (r : List Nat) (h : t < 2) : decode (t :: r) = .error (.unknownType t) := by
  apply decode_unknown <;> (try omega)
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> rfl

theorem decode_unknown_high (t : Nat) (r : List Nat) (h : 19 ≤ t) : decode (t :: r) = .error (.unknownType t) := by
  apply decode_unknown <;> (try omega)
  unfold layoutOf
  split <;> first | rfl | (exfalso; omega)

/-- Bytes after a frame of a fixed size are refused, whatever they are. -/
theorem decode_trailing (f : Fr) (l : L) (h13 : f.ty ≠ 13) (h15 : f.ty ≠ 15) (hl : layoutOf f.ty = some l)
    (ht : l.tail = none) (hv : LayoutOk l f.fs) (x : Nat) (r : List Nat) :
    decode (f.ty :: (encFs f.fs ++ x :: r)) = .error .trailing := by
  rw [decode, decodeWith_layout _ f.ty l _ h13 h15 hl, rdLayout_enc_app CErr.wire l ht f.fs hv]
  simp [finish_cons, bind, Except.bind]

/-- A packet, record or notice that is empty or longer than its bound is refused with the error of its tail. -/
theorem decode_tail_refused (ty : Nat) (l : L) (m : Nat) (e : CErr) (pf b : List F) (bs : List Nat)
    (h13 : ty ≠ 13) (h15 : ty ≠ 15) (hl : layoutOf ty = some l) (ht : l.tail = some (m, e))
    (hp : PreOk l.pre pf) (hb : bs.length = 0 ∨ m < bs.length) :
    decode (ty :: (encFs pf ++ bs)) = .error e := by
  rw [decode, decodeWith_layout _ ty l _ h13 h15 hl]
  have e1 := rdPre_app CErr.wire l.pre pf hp bs
  have e2 : rdTail l.tail bs = .error e := by
    rw [ht]; simp only [rdTail]; rw [if_pos hb]
  simp [rdLayout, e1, e2, bind, Except.bind]

/-- A SEND (type 2) with a node and a flag and no packet. -/
theorem decode_send_no_packet (n : List Nat) (fl : Nat) (hn : NodeOk n) (hbn : Byte n) (hfl : fl < 256) :
    decode (2 :: (n ++ [fl])) = .error .packetSize := by
  have := decode_tail_refused 2 ⟨[K.node, K.u8], packetTail⟩ maxPacket .packetSize [F.node n, F.u8 fl] [] []
    (by decide) (by decide) rfl rfl ⟨⟨hn, hbn⟩, by simpa [okK] using hfl, trivial⟩ (Or.inl rfl)
  simpa [encFs, F.enc] using this

/-- An alias of 32 or more, at the front of a SEND by alias (10) or a RECV by alias (12). -/
theorem decode_alias (ty a : Nat) (r : List Nat) (hty : ty = 10 ∨ ty = 12) (ha : aliasMax ≤ a) :
    decode (ty :: a :: r) = .error (.alias a) := by
  rcases hty with rfl | rfl <;>
  simp [decode, decodeWith, rdU8, liftW, layoutOf, rdLayout, rdPre, rdField, packetTail, throw, throwThe,
    MonadExceptOf.throw, bind, Except.bind, Nat.not_lt.2 ha]

/-- An answer status above 2 in a DNSR. -/
theorem decode_status (p : List Nat) (hn : NodeOk p) (hbn : Byte p) (s : Nat) (r : List Nat) (hs : 3 ≤ s) :
    decode (15 :: (p ++ s :: r)) = .error (.status s) := by
  have e1 := rdField_app CErr.wire K.node (F.node p) ⟨hn, hbn⟩ (s :: r)
  simp only [F.enc] at e1
  rcases s with _ | _ | _ | s <;> try omega
  have e2 : rdField CErr.wire K.u8 ((s + 1 + 1 + 1) :: r) = .ok (F.u8 (s + 1 + 1 + 1), r) := by
    simp [rdField, rdU8, liftW, bind, Except.bind, pure, Except.pure]
  simp [decode, decodeWith, rdU8, liftW, decodeDnsr, decodeDnsrG, rdPre, e1, e2, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]

/-- The empty node id, and a truncated one: the shortfall is reported. -/
theorem decode_dnsq_truncated (bs : List Nat) (h1 : 1 ≤ bs.length) (h2 : bs.length < 33) :
    decode (14 :: bs) = .error (.wire (.trunc (33 - bs.length))) := by
  obtain ⟨t, r1, rfl⟩ : ∃ t r1, bs = t :: r1 := by
    cases bs with
    | nil => simp at h1
    | cons t r1 => exact ⟨t, r1, rfl⟩
  have hr : ¬ 32 ≤ r1.length := by simp at h2; omega
  have hlay : layoutOf 14 = some ⟨[K.node], none⟩ := rfl
  simp [decode, decodeWith, rdU8, liftW, hlay, rdLayout, rdPre, rdField, rdNode, rdBytes, hr, bind,
    Except.bind]

theorem decode_batch_count (c : Nat) (r : List Nat) (h : c < 2 ∨ batchFrames < c) :
    decode (13 :: c :: r) = .error (.batch "frame count") := by
  simp [decode, decodeWith, rdU8, liftW, decodeBatch, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem decode_batch_truncated : decode [13] = .error (.wire (.trunc 1)) := by
  simp [decode, decodeWith, rdU8, liftW, decodeBatch, bind, Except.bind]

/-- A packet, record or notice the decoder would refuse is refused by the encoder with the same error, once the
type byte and the fields before it fit the buffer. -/
theorem encode_field (ty : Nat) (l : L) (m : Nat) (e : CErr) (pf : List F) (bs : List Nat) (cap : Nat)
    (h13 : ty ≠ 13) (h15 : ty ≠ 15) (hl : layoutOf ty = some l) (ht : l.tail = some (m, e))
    (hp : PreOk l.pre pf) (hb : ¬ (1 ≤ bs.length ∧ bs.length ≤ m)) (hc : 1 + (encFs pf).length ≤ cap) :
    (Fr.mk ty (pf ++ [F.raw bs])).encode cap = .error e := by
  have hlen := PreOk_length hp
  have ht1 : (pf ++ [F.raw bs]).take l.pre.length = pf := by rw [← hlen]; simp
  have ht2 : (pf ++ [F.raw bs]).drop l.pre.length = [F.raw bs] := by rw [← hlen]; simp
  obtain ⟨g, b⟩ := opsPre_good hp
  have hd : decide (1 ≤ bs.length ∧ bs.length ≤ m) = false := by simp [hb]
  have := run_chk CErr.wire cap (Op.put [ty] :: opsPre l.pre pf) [Op.put bs] e
    (by intro o ho; simp only [List.mem_cons] at ho; rcases ho with rfl | ho <;> simp_all [Op.good])
    [] (by
      have b' : (opsBytes (opsPre l.pre pf)).length = (encFs pf).length := by rw [b]
      simp only [opsBytes, List.flatMap_cons, Op.bytes, List.length_append, List.length_singleton,
        List.length_nil] at b' ⊢
      omega)
  simpa [Fr.encode, Fr.ops, h13, h15, hl, opsLayout, ht1, ht2, ht, opsTail, hd] using this

end Vinc.ConnCodec
