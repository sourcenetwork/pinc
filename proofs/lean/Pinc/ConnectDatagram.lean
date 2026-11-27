import Pinc.ConnectFrameErr

/-!
# The relay datagram codec

`Datagram::decode` and `Datagram::encode` of `pinc-connect/src/relay/datagram.rs`: QAD (1), QADR (2), DNSQ (3),
DNSR (4), SLEEP (6), SPL (8) and SPU (9), on the field engine of `ConnectCodecCore.lean` and the DNSR step of the
carrier frames (`decodeDnsrG`). A datagram is a `Fr`: its type byte and its fields.

The packet of SPL and SPU is 1 to `maxTunnel - 35` bytes: the code reads it up to `maxTunnel` and then refuses a
datagram whose header and packet exceed `maxTunnel`, both with `PacketSize` and with nothing in between that can
fail (the packet runs to the end of the datagram), so the two checks are one bound here.

A QAD and a DNSQ carry zero bytes after their fields (`padD`): the query is `QAD_LEN` (19) and `DNSQ_LEN` (484)
bytes, the least lengths whose three times pay for the longest answer and its 28 header bytes (`query_pays`), so the
ledger of the node that answers lets the answer go to a source that proved nothing. A short padding is `Truncated`,
a padding byte that is not zero is `Padding`.

Theorems: `decodeD_bytes` (round trip), `decodeD_inv` (canonical form), `decodeD_injective`, `encodeD_ok`,
`encodeD_short`, `query_pays`, and the exact refusals.
-/

namespace Pinc.ConnCodec
open Pinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-- `MAX_TUNNEL_DATAGRAM`: the path MTU bound less the IPv6 and UDP headers. -/
def maxTunnel : Nat := maxPacket - 28

/-- Every wire error of a datagram is `DatagramError::Frame(FrameError::Wire(_))`. -/
def lwD : W → CErr := fun w => CErr.dframe (CErr.wire w)

/-- The layout of a datagram other than DNSR. -/
def layoutD : Nat → Option L
  | 1 => some ⟨[.fixed 8], none⟩
  | 2 => some ⟨[.fixed 8, .addr 1], none⟩
  | 3 => some ⟨[.node], none⟩
  | 6 => some ⟨[], some (maxNotice, CErr.dframe .bodySize)⟩
  | 8 | 9 => some ⟨[.node, .u8], some (maxTunnel - 35, .packetSize)⟩
  | _ => none

/-- The zero bytes after the fields of a datagram: 10 after a QAD's nonce, 450 after a DNSQ's node, none else. -/
def padD (ty : Nat) : Nat := if ty = 1 then 10 else if ty = 3 then 450 else 0

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Nat := List.replicate n 0

/-- Read the padding: `n` bytes, each zero. -/
def rdPad (n : Nat) (r : List Nat) : Except CErr (List Nat) :=
  if r.length < n then .error (lwD (.trunc (n - r.length)))
  else if r.take n = zeros n then .ok (r.drop n) else .error .padding

/-- The longest QADR (type, nonce, an IPv6 address) and the longest DNSR (`MAX_DNS_DATAGRAM`, which is
`maxTunnel`) with their 28 header bytes are at most three times the padded query, and one byte less would not do. -/
theorem query_pays :
    (1 + 8 + 19) + 28 ≤ 3 * (1 + 8 + padD 1) ∧ 3 * (1 + 8 + padD 1 - 1) < (1 + 8 + 19) + 28 ∧
    maxTunnel + 28 ≤ 3 * (1 + 33 + padD 3) ∧ 3 * (1 + 33 + padD 3 - 1) < maxTunnel + 28 := by
  simp [padD, maxTunnel, maxPacket]

/-- `Datagram::decode`. -/
def decodeD (b : List Nat) : Except CErr Fr := do
  let (ty, r) ← liftW lwD (rdU8 b)
  if ty = 4 then decodeDnsrG lwD (fun s => CErr.dframe (CErr.status s)) (CErr.dframe .bodySize) 4 r
  else
    match layoutD ty with
    | none => throw (CErr.unknownType ty)
    | some l => do
      let (fs, r) ← rdLayout lwD l r
      let r ← rdPad (padD ty) r
      finish r
      pure ⟨ty, fs⟩

/-- `Datagram::encode` (with the field checks of the decoder, and the padding written in one put). -/
def Fr.opsD (f : Fr) : List Op :=
  .put [f.ty] ::
    if f.ty = 4 then opsLayout ⟨[.node, .u8], some (maxRecordLen, CErr.dframe .bodySize)⟩ f.fs
    else match layoutD f.ty with
      | some l => opsLayout l f.fs ++ [.put (zeros (padD f.ty))]
      | none => []

def Fr.encodeD (cap : Nat) (f : Fr) : Except CErr (List Nat) := run lwD cap f.opsD []

/-- A datagram the code can hold. -/
def Fr.validD (f : Fr) : Prop :=
  if f.ty = 4 then DnsrOk f.fs
  else match layoutD f.ty with
    | some l => LayoutOk l f.fs
    | none => False

/-- The bytes of a datagram. -/
def Fr.bytesD (f : Fr) : List Nat := f.ty :: (encFs f.fs ++ zeros (padD f.ty))

theorem decodeD_layout (ty : Nat) (l : L) (r : List Nat) (h4 : ty ≠ 4) (hl : layoutD ty = some l) :
    decodeD (ty :: r) =
      (do let (fs, r) ← rdLayout lwD l r; let r ← rdPad (padD ty) r; finish r; pure ⟨ty, fs⟩) := by
  simp [decodeD, rdU8, liftW, h4, hl, bind, Except.bind, pure, Except.pure]

theorem zeros_length (n : Nat) : (zeros n).length = n := by simp [zeros]

theorem rdPad_zeros (n : Nat) (r : List Nat) : rdPad n (zeros n ++ r) = .ok r := by
  have ht : (zeros n ++ r).take n = zeros n := List.take_left' (zeros_length n)
  have hd : (zeros n ++ r).drop n = r := List.drop_left' (zeros_length n)
  have hl : ¬ (zeros n ++ r).length < n := by rw [List.length_append, zeros_length]; omega
  unfold rdPad
  rw [if_neg hl, if_pos ht, hd]

theorem rdPad_inv {n r r'} (h : rdPad n r = .ok r') : r = zeros n ++ r' := by
  unfold rdPad at h
  by_cases hl : r.length < n
  · simp [hl] at h
  · by_cases ht : r.take n = zeros n
    · simp only [hl, ht, ite_false, ite_true, Except.ok.injEq] at h
      subst h
      rw [← ht, List.take_append_drop]
    · simp [hl, ht] at h

/-- The layouts with a tail carry no padding. -/
theorem padD_tail {ty : Nat} {l : L} (hl : layoutD ty = some l) (ht : l.tail ≠ none) : padD ty = 0 := by
  unfold layoutD at hl
  split at hl <;> simp only [Option.some.injEq, reduceCtorEq] at hl <;> subst hl <;> simp_all [padD]

theorem decodeD_bytes (f : Fr) (hv : f.validD) : decodeD f.bytesD = .ok f := by
  obtain ⟨ty, fs⟩ := f
  by_cases h4 : ty = 4
  · subst h4
    have hv' : DnsrOk fs := by unfold Fr.validD at hv; simpa using hv
    have := dnsrG_enc lwD (fun s => CErr.dframe (CErr.status s)) (CErr.dframe .bodySize) 4 fs hv'
    simpa [Fr.bytesD, padD, zeros, decodeD, rdU8, liftW, bind, Except.bind, pure, Except.pure] using this
  · cases hl : layoutD ty with
    | none => unfold Fr.validD at hv; simp [h4, hl] at hv
    | some l =>
      have hv' : LayoutOk l fs := by unfold Fr.validD at hv; simpa [h4, hl] using hv
      simp only [Fr.bytesD]
      rw [decodeD_layout ty l _ h4 hl]
      by_cases ht : l.tail = none
      · have := rdLayout_enc_app lwD l ht fs hv' (zeros (padD ty))
        have hp := rdPad_zeros (padD ty) []
        rw [List.append_nil] at hp
        simp [this, hp, finish_nil, bind, Except.bind, pure, Except.pure]
      · have := rdLayout_enc lwD l fs hv'
        have hp : padD ty = 0 := padD_tail hl ht
        simp [this, hp, zeros, rdPad, finish_nil, bind, Except.bind, pure, Except.pure]

theorem decodeD_inv {b f} (h : decodeD b = .ok f) (hb : Byte b) : f.validD ∧ f.bytesD = b := by
  rcases b with _ | ⟨ty, r⟩
  · simp [decodeD, rdU8, liftW, bind, Except.bind] at h
  · have hbr : Byte r := (byte_cons hb).2
    by_cases h4 : ty = 4
    · subst h4
      simp [decodeD, rdU8, liftW, bind, Except.bind] at h
      obtain ⟨t, hd, e⟩ := decodeDnsrG_inv h hbr
      refine ⟨?_, ?_⟩
      · unfold Fr.validD; simp [t, hd]
      · simp [Fr.bytesD, padD, zeros, t, e]
    · cases hl : layoutD ty with
      | none => simp [decodeD, rdU8, liftW, h4, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | some l =>
        rw [decodeD_layout ty l r h4 hl] at h
        simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨⟨fs, r1⟩, h1, r2, h2, u, hu, rfl⟩ := h
        have hf := finish_ok hu
        subst hf
        have hz := rdPad_inv h2
        rw [List.append_nil] at hz
        subst hz
        obtain ⟨hlo, e, _⟩ := rdLayout_inv lwD l h1 hbr
        refine ⟨?_, ?_⟩
        · unfold Fr.validD; simp [h4, hl, hlo]
        · simp [Fr.bytesD]
          exact e.symm

theorem decodeD_injective {a b f} (ha : decodeD a = .ok f) (hb : decodeD b = .ok f) (hba : Byte a) (hbb : Byte b) :
    a = b := by
  rw [← (decodeD_inv ha hba).2, ← (decodeD_inv hb hbb).2]

theorem opsD_good (f : Fr) (hv : f.validD) : (∀ o ∈ f.opsD, o.good) ∧ opsBytes f.opsD = f.bytesD := by
  by_cases h4 : f.ty = 4
  · have hv' : DnsrOk f.fs := by unfold Fr.validD at hv; simpa [h4] using hv
    obtain ⟨g, b⟩ := dnsr_ops (CErr.dframe .bodySize) f.fs hv'
    refine ⟨?_, ?_⟩
    · intro o ho
      simp only [Fr.opsD, h4, ite_true, List.mem_cons] at ho
      rcases ho with rfl | ho
      · simp [Op.good]
      · exact g o ho
    · unfold opsBytes at b
      simp [Fr.opsD, Fr.bytesD, h4, padD, zeros, opsBytes, Op.bytes, b]
  · cases hl : layoutD f.ty with
    | none => unfold Fr.validD at hv; simp [h4, hl] at hv
    | some l =>
      have hv' : LayoutOk l f.fs := by unfold Fr.validD at hv; simpa [h4, hl] using hv
      obtain ⟨g, b⟩ := opsLayout_good hv'
      refine ⟨?_, ?_⟩
      · intro o ho
        simp only [Fr.opsD, h4, hl, ite_false, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | ho | rfl
        · simp [Op.good]
        · exact g o ho
        · simp [Op.good]
      · unfold opsBytes at b
        simp [Fr.opsD, Fr.bytesD, h4, hl, opsBytes, Op.bytes, b]

theorem encodeD_ok (cap : Nat) (f : Fr) (hv : f.validD) (hc : f.bytesD.length ≤ cap) :
    f.encodeD cap = .ok f.bytesD := by
  obtain ⟨g, b⟩ := opsD_good f hv
  have := run_ok lwD cap f.opsD g [] (by rw [b]; simpa using hc)
  simpa [Fr.encodeD, b] using this

theorem encodeD_short (cap : Nat) (f : Fr) (hv : f.validD) (hc : cap < f.bytesD.length) :
    ∃ k, 0 < k ∧ f.encodeD cap = .error (CErr.dframe (CErr.wire (.small k))) := by
  obtain ⟨g, b⟩ := opsD_good f hv
  exact run_short lwD cap f.opsD g [] (by simp) (by rw [b]; simpa using hc)

theorem decodeD_encode {b f} (h : decodeD b = .ok f) (hb : Byte b) : f.encodeD b.length = .ok b := by
  obtain ⟨hv, e⟩ := decodeD_inv h hb
  have := encodeD_ok b.length f hv (Nat.le_of_eq (congrArg List.length e))
  rw [e] at this
  exact this

/-! ## The refusals -/

theorem decodeD_empty : decodeD [] = .error (.dframe (.wire (.trunc 1))) := by
  simp [decodeD, rdU8, liftW, lwD, bind, Except.bind]

theorem decodeD_unknown (t : Nat) (r : List Nat) (h4 : t ≠ 4) (hl : layoutD t = none) :
    decodeD (t :: r) = .error (.unknownType t) := by
  simp [decodeD, rdU8, liftW, h4, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Bytes after a datagram of a fixed size and its padding are refused. -/
theorem decodeD_trailing (f : Fr) (l : L) (h4 : f.ty ≠ 4) (hl : layoutD f.ty = some l) (ht : l.tail = none)
    (hv : LayoutOk l f.fs) (x : Nat) (r : List Nat) :
    decodeD (f.ty :: (encFs f.fs ++ (zeros (padD f.ty) ++ x :: r))) = .error .trailing := by
  rw [decodeD_layout f.ty l _ h4 hl, rdLayout_enc_app lwD l ht f.fs hv]
  have hp := rdPad_zeros (padD f.ty) (x :: r)
  simp [hp, finish_cons, bind, Except.bind]

/-- A padding shorter than its datagram's is refused with the shortfall: the unpadded QAD and DNSQ among them. -/
theorem decodeD_pad_short (f : Fr) (l : L) (h4 : f.ty ≠ 4) (hl : layoutD f.ty = some l) (ht : l.tail = none)
    (hv : LayoutOk l f.fs) (k : Nat) (hk : k < padD f.ty) :
    decodeD (f.ty :: (encFs f.fs ++ zeros k)) = .error (lwD (.trunc (padD f.ty - k))) := by
  rw [decodeD_layout f.ty l _ h4 hl, rdLayout_enc_app lwD l ht f.fs hv]
  have hp : rdPad (padD f.ty) (zeros k) = .error (lwD (.trunc (padD f.ty - k))) := by
    simp [rdPad, zeros_length, hk]
  simp [hp, bind, Except.bind]

/-- A padding of the right length that is not all zero is refused. -/
theorem decodeD_pad_nonzero (f : Fr) (l : L) (h4 : f.ty ≠ 4) (hl : layoutD f.ty = some l) (ht : l.tail = none)
    (hv : LayoutOk l f.fs) (z r : List Nat) (hz : z.length = padD f.ty) (hnz : z ≠ zeros (padD f.ty)) :
    decodeD (f.ty :: (encFs f.fs ++ (z ++ r))) = .error .padding := by
  rw [decodeD_layout f.ty l _ h4 hl, rdLayout_enc_app lwD l ht f.fs hv]
  have hp : rdPad (padD f.ty) (z ++ r) = .error .padding := by
    have hl' : ¬ z.length + r.length < padD f.ty := by omega
    have ht' : (z ++ r).take (padD f.ty) = z := List.take_left' hz
    simp [rdPad, List.length_append, hl', ht', hnz]
  simp [hp, bind, Except.bind]

/-- A tunnelled packet that is empty or too long for the datagram. -/
theorem decodeD_tunnel_packet (ty : Nat) (hty : ty = 8 ∨ ty = 9) (n : List Nat) (hn : NodeOk n) (hbn : Byte n)
    (fl : Nat) (hfl : fl < 256) (bs : List Nat) (hb : bs.length = 0 ∨ maxTunnel - 35 < bs.length) :
    decodeD (ty :: (n ++ fl :: bs)) = .error .packetSize := by
  have hl : layoutD ty = some ⟨[K.node, K.u8], some (maxTunnel - 35, .packetSize)⟩ := by
    rcases hty with rfl | rfl <;> rfl
  have h4 : ty ≠ 4 := by omega
  rw [decodeD_layout ty _ _ h4 hl]
  have e1 := rdPre_app lwD [K.node, K.u8] [F.node n, F.u8 fl] ⟨⟨hn, hbn⟩, by simpa [okK] using hfl, trivial⟩ bs
  simp only [encFs, List.flatMap_cons, List.flatMap_nil, F.enc, List.append_nil, List.append_assoc,
    List.nil_append, List.cons_append] at e1
  have e2 : rdTail (some (maxTunnel - 35, CErr.packetSize)) bs = .error .packetSize := by
    simp only [rdTail]; rw [if_pos hb]
  simp [rdLayout, e1, e2, bind, Except.bind]

end Pinc.ConnCodec
