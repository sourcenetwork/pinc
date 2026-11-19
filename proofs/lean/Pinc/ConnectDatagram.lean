import Pinc.ConnectFrameErr

/-!
# The relay datagram codec

`Datagram::decode` and `Datagram::encode` of `pinc-connect/src/relay/datagram.rs`: QAD (1), QADR (2), DNSQ (3),
DNSR (4), SLEEP (6), SPL (8) and SPU (9), on the field engine of `ConnectCodecCore.lean` and the DNSR step of the
carrier frames (`decodeDnsrG`). A datagram is a `Fr`: its type byte and its fields.

The packet of SPL and SPU is 1 to `maxTunnel - 35` bytes: the code reads it up to `maxTunnel` and then refuses a
datagram whose header and packet exceed `maxTunnel`, both with `PacketSize` and with nothing in between that can
fail (the packet runs to the end of the datagram), so the two checks are one bound here.

Theorems: `decodeD_bytes` (round trip), `decodeD_inv` (canonical form), `decodeD_injective`, `encodeD_ok`,
`encodeD_short`, and the exact refusals.
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

/-- `Datagram::decode`. -/
def decodeD (b : List Nat) : Except CErr Fr := do
  let (ty, r) ← liftW lwD (rdU8 b)
  if ty = 4 then decodeDnsrG lwD (fun s => CErr.dframe (CErr.status s)) (CErr.dframe .bodySize) 4 r
  else
    match layoutD ty with
    | none => throw (CErr.unknownType ty)
    | some l => do
      let (fs, r) ← rdLayout lwD l r
      finish r
      pure ⟨ty, fs⟩

/-- `Datagram::encode` (with the field checks of the decoder). -/
def Fr.opsD (f : Fr) : List Op :=
  .put [f.ty] ::
    if f.ty = 4 then opsLayout ⟨[.node, .u8], some (maxRecordLen, CErr.dframe .bodySize)⟩ f.fs
    else match layoutD f.ty with
      | some l => opsLayout l f.fs
      | none => []

def Fr.encodeD (cap : Nat) (f : Fr) : Except CErr (List Nat) := run lwD cap f.opsD []

/-- A datagram the code can hold. -/
def Fr.validD (f : Fr) : Prop :=
  if f.ty = 4 then DnsrOk f.fs
  else match layoutD f.ty with
    | some l => LayoutOk l f.fs
    | none => False

/-- The bytes of a datagram. -/
def Fr.bytesD (f : Fr) : List Nat := f.ty :: encFs f.fs

theorem decodeD_layout (ty : Nat) (l : L) (r : List Nat) (h4 : ty ≠ 4) (hl : layoutD ty = some l) :
    decodeD (ty :: r) = (do let (fs, r) ← rdLayout lwD l r; finish r; pure ⟨ty, fs⟩) := by
  simp [decodeD, rdU8, liftW, h4, hl, bind, Except.bind, pure, Except.pure]

theorem decodeD_bytes (f : Fr) (hv : f.validD) : decodeD f.bytesD = .ok f := by
  obtain ⟨ty, fs⟩ := f
  by_cases h4 : ty = 4
  · subst h4
    have hv' : DnsrOk fs := by unfold Fr.validD at hv; simpa using hv
    have := dnsrG_enc lwD (fun s => CErr.dframe (CErr.status s)) (CErr.dframe .bodySize) 4 fs hv'
    simpa [Fr.bytesD, decodeD, rdU8, liftW, bind, Except.bind, pure, Except.pure] using this
  · cases hl : layoutD ty with
    | none => unfold Fr.validD at hv; simp [h4, hl] at hv
    | some l =>
      have hv' : LayoutOk l fs := by unfold Fr.validD at hv; simpa [h4, hl] using hv
      simp only [Fr.bytesD]
      rw [decodeD_layout ty l _ h4 hl]
      by_cases ht : l.tail = none
      · have := rdLayout_enc_app lwD l ht fs hv' []
        rw [List.append_nil] at this
        simp [this, finish_nil, bind, Except.bind, pure, Except.pure]
      · have := rdLayout_enc lwD l fs hv'
        simp [this, finish_nil, bind, Except.bind, pure, Except.pure]

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
      · simp [Fr.bytesD, t, e]
    · cases hl : layoutD ty with
      | none => simp [decodeD, rdU8, liftW, h4, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | some l =>
        rw [decodeD_layout ty l r h4 hl] at h
        simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨⟨fs, r1⟩, h1, u, hu, rfl⟩ := h
        have hf := finish_ok hu
        simp only at hf
        subst hf
        obtain ⟨hlo, e, _⟩ := rdLayout_inv lwD l h1 hbr
        refine ⟨?_, ?_⟩
        · unfold Fr.validD; simp [h4, hl, hlo]
        · rw [List.append_nil] at e
          simp [Fr.bytesD]
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
      simp [Fr.opsD, Fr.bytesD, h4, opsBytes, Op.bytes, b]
  · cases hl : layoutD f.ty with
    | none => unfold Fr.validD at hv; simp [h4, hl] at hv
    | some l =>
      have hv' : LayoutOk l f.fs := by unfold Fr.validD at hv; simpa [h4, hl] using hv
      obtain ⟨g, b⟩ := opsLayout_good hv'
      refine ⟨?_, ?_⟩
      · intro o ho
        simp only [Fr.opsD, h4, hl, ite_false, List.mem_cons] at ho
        rcases ho with rfl | ho
        · simp [Op.good]
        · exact g o ho
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

/-- Bytes after a datagram of a fixed size are refused. -/
theorem decodeD_trailing (f : Fr) (l : L) (h4 : f.ty ≠ 4) (hl : layoutD f.ty = some l) (ht : l.tail = none)
    (hv : LayoutOk l f.fs) (x : Nat) (r : List Nat) :
    decodeD (f.ty :: (encFs f.fs ++ x :: r)) = .error .trailing := by
  rw [decodeD_layout f.ty l _ h4 hl, rdLayout_enc_app lwD l ht f.fs hv]
  simp [finish_cons, bind, Except.bind]

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
