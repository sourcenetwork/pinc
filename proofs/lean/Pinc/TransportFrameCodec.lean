import Pinc.TransportFrameThm

/-!
# The PINCER frame codecs: round trip and the accepted encodings

For every frame type of `Frame::decode` and `Frame::write` (the model of `TransportFrame.lean`):

* **Round trip** (`decode_bytes`): decoding the encoding of a frame followed by `rest` yields that frame and leaves
  exactly `rest`, so it consumes exactly `encoded_len` bytes (`bytes_length`). Three frames take what follows
  them, and the statement says so (`Frame.Sep`): a PADDING frame is the whole run of zero bytes, so what follows it
  must not start with a zero; a STREAM or DATAGRAM frame without a length runs to the end of the packet, so
  nothing may follow it.
* **Canonical, and where the parser is lenient** (`decode_inv`): an accepted input is the encoding of the frame it
  yields followed by what is left, with one exception: a STREAM frame whose type has the OFF bit and whose offset
  is written as 0 is accepted, and `write` never sets the OFF bit for offset 0 (`offBytes`, accepted by
  `decode_offBytes`). So a frame has one accepted encoding, and a STREAM frame at offset 0 has two. A varint that
  is not minimal, a type below `0x40` that is not assigned (`decode_unknown`), an ACK beyond the range cap or with
  a range below packet number 0, a stream end beyond 2^62 - 1, a REKEY kind above 1 and a ticket count above 4 are
  refused. The frame returned is a value `write` accepts (`Frame.Good`).
* **Progress** (`decode_progress`): a decoded frame takes at least one byte, so `FrameIter` ends
  (`iterFuel_enough`), and a payload made of encodings yields its frames in order with no error (`frames_bytes`).
-/

namespace Pinc.TransportFrame
open Pinc
open Pinc.Varint (ValidBytes)

/-- What may follow a frame in a payload for it to be read back as itself. -/
def Frame.Sep : Frame → List Nat → Prop
  | .padding _, rest => zeroRun rest = 0
  | .stream _ _ _ _ imp, rest => imp = true → rest = []
  | .datagram _ imp, rest => imp = true → rest = []
  | _, _ => True

/-- The second accepted encoding of a STREAM frame at offset 0: the OFF bit set and the offset written as 0. -/
def offBytes (id : Nat) (fin : Bool) (data : List Nat) (imp : Bool) : List Nat :=
  flat ([.v (streamType 1 fin imp), .v id, .v 0] ++ (if imp then [.s data] else [.v data.length, .s data]))

/-! ## Helpers -/

theorem rdV_enc {v : Nat} (hv : v < Varint.limit) (rest : List Nat) :
    rdVarint (Varint.encodeBytes v ++ rest) = .ok (v, rest) := rdVarint_enc v rest hv

theorem rdBytes_app {x : List Nat} {n : Nat} (h : x.length = n) (r : List Nat) :
    rdBytes n (x ++ r) = .ok (x, r) := rdBytes_append x r n h

theorem rdBytes_all (b : List Nat) : rdBytes b.length b = .ok (b, []) := by simp [rdBytes]

theorem rdBytes_cons1 (a : Nat) (r : List Nat) : rdBytes 1 (a :: r) = .ok ([a], r) := by simp [rdBytes]

theorem rdLP_enc {x : List Nat} (hx : x.length < Varint.limit) (rest : List Nat) :
    rdLenPrefixed (Varint.encodeBytes x.length ++ (x ++ rest)) = .ok (x, rest) := rdLenPrefixed_enc x rest hx

theorem zeroRun_rep (n : Nat) (rest : List Nat) : zeroRun (List.replicate n 0 ++ rest) = n + zeroRun rest := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, zeroRun, ih]; omega

theorem zeroRun_split (l : List Nat) : l = List.replicate (zeroRun l) 0 ++ l.drop (zeroRun l) := by
  induction l with
  | nil => simp [zeroRun]
  | cons a l ih =>
    by_cases h : a = 0
    · subst h
      simp only [zeroRun, ite_true, List.replicate_succ, List.cons_append, List.drop_succ_cons]
      rw [← ih]
    · simp [zeroRun, h]

theorem zeroRun_drop (l : List Nat) : zeroRun (l.drop (zeroRun l)) = 0 := by
  induction l with
  | nil => simp [zeroRun]
  | cons a l ih =>
    by_cases h : a = 0
    · subst h; simpa [zeroRun] using ih
    · simp [zeroRun, h]

theorem be_be32 (v : Nat) (h : v < 2 ^ 32) : be (be32 v) = v := by
  simp only [be, be32, List.foldl]
  omega

theorem be32_be (lt : List Nat) (hl : lt.length = 4) (hv : ValidBytes lt) : be32 (be lt) = lt ∧ be lt < 2 ^ 32 := by
  match lt, hl, hv with
  | [a, b, c, d], _, hv =>
    have ha := hv a (by simp)
    have hb := hv b (by simp)
    have hc := hv c (by simp)
    have hd := hv d (by simp)
    simp only [be, be32, List.foldl]
    refine ⟨?_, by omega⟩
    congr 1
    · omega
    · congr 1
      · omega
      · congr 1
        · omega
        · congr 1
          omega

theorem len1 (k : List Nat) (h : k.length = 1) : ∃ a, k = [a] := by
  match k, h with
  | [a], _ => exact ⟨a, rfl⟩

theorem ackLoop_append (rest : List Nat) : ∀ (x ps : Nat) (tail : List Nat) (q : Nat), ValidBytes tail →
    ackLoop x ps tail = .ok (q, []) → ackLoop x ps (tail ++ rest) = .ok (q, rest) := by
  intro x
  induction x with
  | zero =>
    intro ps tail q _ h
    simp only [ackLoop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [ackLoop]
  | succ k ih =>
    intro ps tail q hv h
    simp only [ackLoop, andThen_eq_ok] at h
    obtain ⟨gap, r1, h1, len, r2, h2, h3⟩ := h
    obtain ⟨rfl, hg, v1⟩ := rdVarint_inv hv h1
    obtain ⟨rfl, hl, v2⟩ := rdVarint_inv v1 h2
    simp only [ackLoop, List.append_assoc, rdV_enc hg, rdV_enc hl, andThen_ok]
    split at h3
    · cases h3
    · rename_i c1
      split at h3
      · cases h3
      · rename_i c2
        rw [if_neg c1, if_neg c2]
        exact ih _ _ _ v2 h3

theorem ackLoop_inv : ∀ (x ps : Nat) (b : List Nat) (q : Nat) (r4 : List Nat), ValidBytes b →
    ackLoop x ps b = .ok (q, r4) →
    ∃ tail, b = tail ++ r4 ∧ ackLoop x ps tail = .ok (q, []) ∧ ValidBytes tail ∧ ValidBytes r4 := by
  intro x
  induction x with
  | zero =>
    intro ps b q r4 hv h
    simp only [ackLoop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, by simp [ackLoop], valid_nil, hv⟩
  | succ k ih =>
    intro ps b q r4 hv h
    simp only [ackLoop, andThen_eq_ok] at h
    obtain ⟨gap, r1, h1, len, r2, h2, h3⟩ := h
    obtain ⟨rfl, hg, v1⟩ := rdVarint_inv hv h1
    obtain ⟨rfl, hl, v2⟩ := rdVarint_inv v1 h2
    split at h3
    · cases h3
    · rename_i c1
      split at h3
      · cases h3
      · rename_i c2
        obtain ⟨tail, rfl, ht, vt, vr⟩ := ih _ _ _ _ v2 h3
        refine ⟨Varint.encodeBytes gap ++ (Varint.encodeBytes len ++ tail), by simp, ?_,
          (valid_append _ _).mpr ⟨valid_enc _, (valid_append _ _).mpr ⟨valid_enc _, vt⟩⟩, vr⟩
        simp only [ackLoop, rdV_enc hg, rdV_enc hl, andThen_ok]
        rw [if_neg c1, if_neg c2]
        exact ht

/-- The bytes of the tickets of a batch. -/
def ticketBytes (es : List (List Nat × Nat)) : List Nat :=
  flat (es.flatMap (fun e => [Put.s e.1, Put.s (be32 e.2)]))

theorem ticketBytes_cons (e : List Nat × Nat) (es : List (List Nat × Nat)) :
    ticketBytes (e :: es) = e.1 ++ (be32 e.2 ++ ticketBytes es) := by
  simp [ticketBytes, flat]

theorem rdTickets_enc (rest : List Nat) : ∀ (es : List (List Nat × Nat)),
    (∀ e ∈ es, e.1.length = 16 ∧ ValidBytes e.1 ∧ e.2 < 2 ^ 32) →
    rdTickets es.length (ticketBytes es ++ rest) = .ok (es, rest) := by
  intro es
  induction es with
  | nil => intro _; simp [rdTickets, ticketBytes, flat]
  | cons e es ih =>
    intro h
    obtain ⟨h1, _, h3⟩ := h e (List.mem_cons_self ..)
    have ih' := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [List.length_cons, rdTickets, ticketBytes_cons, List.append_assoc, rdBytes_app h1,
      rdBytes_app (be32_len e.2), andThen_ok, ih', be_be32 _ h3]

theorem rdTickets_inv : ∀ (k : Nat) (b : List Nat) (es : List (List Nat × Nat)) (r : List Nat), ValidBytes b →
    rdTickets k b = .ok (es, r) →
    b = ticketBytes es ++ r ∧ es.length = k ∧ (∀ e ∈ es, e.1.length = 16 ∧ ValidBytes e.1 ∧ e.2 < 2 ^ 32) ∧
      ValidBytes r := by
  intro k
  induction k with
  | zero =>
    intro b es r hv h
    simp only [rdTickets, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [ticketBytes, flat], rfl, by simp, hv⟩
  | succ k ih =>
    intro b es r hv h
    simp only [rdTickets, andThen_eq_ok] at h
    obtain ⟨tid, r1, h1, lt, r2, h2, es', r3, h3, h4⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    obtain ⟨rfl, l1, vt, v1⟩ := rdBytes_inv hv h1
    obtain ⟨rfl, l2, vl, v2⟩ := rdBytes_inv v1 h2
    obtain ⟨rfl, l3, he, v3⟩ := ih _ _ _ v2 h3
    obtain ⟨e1, e2⟩ := be32_be lt l2 vl
    refine ⟨by simp [ticketBytes_cons, e1], by simp [l3], ?_, v3⟩
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨l1, vt, e2⟩
    · exact he e hm

/-- For a type of `0x40` or more the frame is an extension frame. -/
theorem decodeBody_ext (t : Nat) (h : extBase ≤ t) (r : List Nat) :
    decodeBody t r = andThen (rdLenPrefixed r) fun body r1 => .ok (.ext t body, r1) := by
  unfold decodeBody
  simp only [extBase] at h
  iterate 19 rw [if_neg (by omega)]
  rw [if_pos (by simp only [extBase]; omega)]

/-- The types below `0x40` that are not assigned. -/
def Unassigned (t : Nat) : Prop :=
  t = 0x03 ∨ t = 0x06 ∨ t = 0x07 ∨ t = 0x10 ∨ (0x13 ≤ t ∧ t ≤ 0x19) ∨ (0x1d ≤ t ∧ t ≤ 0x2f) ∨
    (0x32 ≤ t ∧ t ≤ 0x39)

/-- Strict: a type below `0x40` that is not assigned is refused with its number, whatever follows. -/
theorem decode_unknown (t : Nat) (h : Unassigned t) (r : List Nat) :
    decode (t :: r) = .error (.unknownType t) := by
  unfold Unassigned at h
  unfold decode
  rw [rdVarint_byte t r (by omega), andThen_ok]
  unfold decodeBody
  iterate 19 rw [if_neg (by omega)]
  rw [if_neg (by simp only [extBase]; omega)]

theorem good_of (f : Frame) (hwf : f.WF) (hv : ∀ v ∈ f.varintFields, v < Varint.limit)
    (hs : ∀ id off fin data imp, f = .stream id off fin data imp → off + data.length ≤ maxEnd)
    (he : ∀ ty body, f = .ext ty body → extBase ≤ ty) : f.Good :=
  ⟨hwf, (validate_ok_iff f).mpr ⟨hv, hs, he⟩⟩

theorem stype_eq (t : Nat) (h : 8 ≤ t ∧ t ≤ 15) (off : Nat) (hx : t / 4 % 2 = 1 ↔ off ≠ 0) :
    streamType off (decide (t % 2 = 1)) (decide (t / 2 % 2 = 0)) = t := by
  unfold streamType
  by_cases h1 : off = 0 <;> by_cases h2 : t % 2 = 1 <;> by_cases h3 : t / 2 % 2 = 0 <;>
    simp [h1, h2, h3] at hx ⊢ <;> omega

theorem stype_off (t : Nat) (h : 8 ≤ t ∧ t ≤ 15) (hx : t / 4 % 2 = 1) :
    streamType 1 (decide (t % 2 = 1)) (decide (t / 2 % 2 = 0)) = t := by
  unfold streamType
  by_cases h2 : t % 2 = 1 <;> by_cases h3 : t / 2 % 2 = 0 <;> simp [h2, h3] <;> omega

/-! ## Round trip -/

/-- Round trip: decoding the encoding of a frame, followed by anything that may follow it (`Frame.Sep`), yields
the frame and leaves what follows, so exactly the bytes of the frame are consumed. -/
theorem decode_bytes (f : Frame) (hg : f.Good) (rest : List Nat) (hsep : f.Sep rest) :
    decode (f.bytes ++ rest) = .ok (f, rest) := by
  obtain ⟨hwf, hval⟩ := hg
  rw [validate_ok_iff] at hval
  obtain ⟨hv, hs, he⟩ := hval
  cases f with
  | padding len =>
    have hwf' : 1 ≤ len := hwf
    have hz : zeroRun rest = 0 := hsep
    obtain ⟨n, rfl⟩ : ∃ n, len = n + 1 := ⟨len - 1, by omega⟩
    simp only [Frame.bytes, Frame.puts, zeroChunks_flat, List.replicate_succ, List.cons_append, decode,
      rdVarint_byte 0 _ (by omega), andThen_ok, decodeBody, ite_true, zeroRun_rep, hz, Nat.add_zero]
    have := zeroRun_split (List.replicate n 0 ++ rest)
    rw [zeroRun_rep, hz, Nat.add_zero] at this
    have h2 : (List.replicate n 0 ++ rest).drop n = rest := by simp
    rw [h2]
  | ping => simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte]
  | sleep => simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte]
  | wake => simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte]
  | ready => simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte]
  | ack l f x tail =>
    obtain ⟨h1, h2, h3, vt, q, hq⟩ := hwf
    have l1 : l < Varint.limit := by simp only [maxPn] at h1; rw [limit_eq]; omega
    have l2 : x < Varint.limit := by simp only [maxAckRanges] at h2; rw [limit_eq]; omega
    have l3 : f < Varint.limit := by omega
    have hloop := ackLoop_append rest x (l - f) tail q vt hq
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, parseAck, rdV_enc l1,
      rdV_enc l2, rdV_enc l3, hloop, Nat.not_lt.mpr h1, Nat.not_le.mpr h2, Nat.not_lt.mpr h3]
  | resetStream id e fs =>
    have l1 := hv id (by simp [Frame.varintFields])
    have l2 := hv e (by simp [Frame.varintFields])
    have l3 := hv fs (by simp [Frame.varintFields])
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdV_enc l1, rdV_enc l2,
      rdV_enc l3]
  | stopSending id e =>
    have l1 := hv id (by simp [Frame.varintFields])
    have l2 := hv e (by simp [Frame.varintFields])
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdV_enc l1, rdV_enc l2]
  | maxStreamData id m =>
    have l1 := hv id (by simp [Frame.varintFields])
    have l2 := hv m (by simp [Frame.varintFields])
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdV_enc l1, rdV_enc l2]
  | maxStreams l =>
    have l1 := hv l (by simp [Frame.varintFields])
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdV_enc l1]
  | close e =>
    have l1 := hv e (by simp [Frame.varintFields])
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdV_enc l1]
  | pathChallenge d =>
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdBytes_app hwf.1]
  | pathResponse d =>
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdBytes_app hwf.1]
  | mtuProbeEcho m =>
    have hm : m < 65536 := hwf
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, be16, rdBytes, be]
    omega
  | datagram d imp =>
    cases imp with
    | true =>
      have hr : rest = [] := hsep rfl
      subst hr
      simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdBytes_all]
    | false =>
      have hlen := hwf.2 rfl
      simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdLP_enc hlen]
  | rekey a sh echo spn =>
    obtain ⟨h1, _, h2, _, h3⟩ := hwf
    have l1 := hv spn (by simp [Frame.varintFields])
    cases a with
    | true =>
      simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdRekey, rdBytes_cons1,
        rdBytes_app h1, rdBytes_app h2, rdV_enc l1]
    | false =>
      obtain ⟨rfl, rfl⟩ := h3 rfl
      simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdRekey, rdBytes_cons1,
        rdBytes_app h1]
  | newTickets es =>
    obtain ⟨h1, h2⟩ := hwf
    have ht := rdTickets_enc rest es h2
    simp only [ticketBytes] at ht
    simp only [maxBatch] at h1
    simp [decode, decodeBody, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte, rdTicketBatch,
      rdBytes_cons1, ht, maxBatch, Nat.not_lt.mpr h1]
  | ext ty body =>
    have l1 := hv ty (by simp [Frame.varintFields])
    have h1 := he ty body rfl
    have hlen := hwf.2
    simp [decode, Frame.bytes, Frame.puts, flat, rdV_enc l1, decodeBody_ext ty h1, rdLP_enc hlen]
  | stream id off fin data imp =>
    have l1 := hv id (by simp [Frame.varintFields])
    have l2 := hv off (by simp [Frame.varintFields])
    have hend : ¬ maxEnd < off + data.length := Nat.not_lt.mpr (hs _ _ _ _ _ rfl)
    have hend0 : ¬ maxEnd < data.length := by omega
    have hlen : data.length < Varint.limit := by
      have := hs _ _ _ _ _ rfl
      simp only [maxEnd] at this
      rw [limit_eq]; omega
    by_cases ho : off = 0
    · subst ho
      cases imp with
      | true =>
        have hr : rest = [] := hsep rfl
        subst hr
        cases fin <;>
          simp [decode, decodeBody, decodeStream, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte,
            streamType, rdV_enc l1, rdBytes_all, hend0]
      | false =>
        cases fin <;>
          simp [decode, decodeBody, decodeStream, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte,
            streamType, rdV_enc l1, rdLP_enc hlen, hend0]
    · cases imp with
      | true =>
        have hr : rest = [] := hsep rfl
        subst hr
        cases fin <;>
          simp [decode, decodeBody, decodeStream, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte,
            streamType, ho, rdV_enc l1, rdV_enc l2, rdBytes_all, hend]
      | false =>
        cases fin <;>
          simp [decode, decodeBody, decodeStream, Frame.bytes, Frame.puts, flat, enc_small, rdVarint_byte,
            streamType, ho, rdV_enc l1, rdV_enc l2, rdLP_enc hlen, hend]

/-- Where the parser is lenient: a STREAM frame at offset 0 is also accepted with the OFF bit set and the offset
written as 0. -/
theorem decode_offBytes (id : Nat) (fin : Bool) (data : List Nat) (imp : Bool)
    (hg : (Frame.stream id 0 fin data imp).Good) (rest : List Nat)
    (hsep : (Frame.stream id 0 fin data imp).Sep rest) :
    decode (offBytes id fin data imp ++ rest) = .ok (.stream id 0 fin data imp, rest) := by
  obtain ⟨hwf, hval⟩ := hg
  rw [validate_ok_iff] at hval
  obtain ⟨hv, hs, _⟩ := hval
  have l1 := hv id (by simp [Frame.varintFields])
  have l0 : (0 : Nat) < Varint.limit := by rw [limit_eq]; omega
  have hend0 : ¬ maxEnd < data.length := by have := hs _ _ _ _ _ rfl; omega
  have hlen : data.length < Varint.limit := by
    have := hs _ _ _ _ _ rfl
    simp only [maxEnd] at this
    rw [limit_eq]; omega
  cases imp with
  | true =>
    have hr : rest = [] := hsep rfl
    subst hr
    cases fin <;>
      simp [decode, decodeBody, decodeStream, offBytes, flat, enc_small, rdVarint_byte, streamType, rdV_enc l1,
        rdBytes_all, hend0]
  | false =>
    cases fin <;>
      simp [decode, decodeBody, decodeStream, offBytes, flat, enc_small, rdVarint_byte, streamType, rdV_enc l1,
        rdLP_enc hlen, hend0]

/-! ## The accepted encodings -/

/-- What an accepted input `b` is: the frame `f` is one `write` accepts, what is left may follow it, and `b` is the
encoding of `f` followed by what is left, or, for a STREAM frame at offset 0, its encoding with the OFF bit. -/
def Accepted (b : List Nat) (f : Frame) (r : List Nat) : Prop :=
  f.Good ∧ f.Sep r ∧ ValidBytes r ∧
    (b = f.bytes ++ r ∨
      ∃ id fin data imp, f = .stream id 0 fin data imp ∧ b = offBytes id fin data imp ++ r)

theorem nil_of_len0 (l : List Nat) (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t => simp at h

theorem be16_be (d : List Nat) (hl : d.length = 2) (hv : ValidBytes d) : be16 (be d) = d ∧ be d < 65536 := by
  match d, hl, hv with
  | [a, b], _, hv =>
    have ha := hv a (by simp)
    have hb := hv b (by simp)
    simp only [be, be16, List.foldl]
    refine ⟨?_, by omega⟩
    congr 1
    · omega
    · congr 1
      omega

theorem body_inv (t : Nat) (r0 : List Nat) (f : Frame) (r : List Nat) (ht : t < Varint.limit)
    (hb : ValidBytes r0) (h : decodeBody t r0 = .ok (f, r)) : Accepted (Varint.encodeBytes t ++ r0) f r := by
  have h0 : (0 : Nat) < Varint.limit := by rw [limit_eq]; omega
  unfold decodeBody at h
  by_cases h_t : t = 0x00
  · -- PADDING
    rw [if_pos h_t] at h; subst h_t
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨good_of _ (by simp [Frame.WF]) (by simp [Frame.varintFields, h0]) (by simp) (by simp),
      zeroRun_drop r0, fun x hx => hb x (List.mem_of_mem_drop hx), Or.inl ?_⟩
    simp only [Frame.bytes, Frame.puts, zeroChunks_flat, enc_small 0 (by omega), List.replicate_succ,
      List.cons_append, List.nil_append]
    exact congrArg (List.cons 0) (zeroRun_split r0)
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x01
  · -- PING
    rw [if_pos h_t] at h; subst h_t
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, hb,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x02
  · -- ACK
    rw [if_pos h_t] at h; subst h_t
    unfold parseAck at h
    rw [andThen_eq_ok] at h; obtain ⟨l, r1, h1, h⟩ := h
    obtain ⟨rfl, ll, v1⟩ := rdVarint_inv hb h1
    split at h
    · cases h
    rename_i c1
    rw [andThen_eq_ok] at h; obtain ⟨x, r2, h2, h⟩ := h
    obtain ⟨rfl, lx, v2⟩ := rdVarint_inv v1 h2
    split at h
    · cases h
    rename_i c2
    rw [andThen_eq_ok] at h; obtain ⟨fr, r3, h3, h⟩ := h
    obtain ⟨rfl, lf, v3⟩ := rdVarint_inv v2 h3
    split at h
    · cases h
    rename_i c3
    rw [andThen_eq_ok] at h; obtain ⟨q, r4, h4, h⟩ := h
    obtain ⟨tail, rfl, ht4, vt, vr⟩ := ackLoop_inv _ _ _ _ _ v3 h4
    have e1 : (tail ++ r4).take ((tail ++ r4).length - r4.length) = tail := by simp
    have e2 : (tail ++ r4).drop ((tail ++ r4).length - r4.length) = r4 := by simp
    rw [e1, e2] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨good_of _ ⟨Nat.le_of_not_lt c1, Nat.lt_of_not_ge c2, Nat.le_of_not_lt c3, vt, q, ht4⟩
      (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, vr,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x04
  · -- RESET_STREAM
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨id, r1, h1, e, r2, h2, fs, r3, h3, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, v1⟩ := rdVarint_inv hb h1
    obtain ⟨rfl, l2, v2⟩ := rdVarint_inv v1 h2
    obtain ⟨rfl, l3, v3⟩ := rdVarint_inv v2 h3
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, l1, l2, l3]) (by simp) (by simp), trivial, v3,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x05
  · -- STOP_SENDING
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨id, r1, h1, e, r2, h2, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, v1⟩ := rdVarint_inv hb h1
    obtain ⟨rfl, l2, v2⟩ := rdVarint_inv v1 h2
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, l1, l2, h0]) (by simp) (by simp), trivial, v2,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h8 : 0x08 ≤ t ∧ t ≤ 0x0f
  · -- STREAM
    rw [if_pos h8] at h
    unfold decodeStream at h
    simp only [andThen_eq_ok] at h
    obtain ⟨id, r1, h1, off, r2, h2, data, r3, h3, h⟩ := h
    obtain ⟨rfl, lid, v1⟩ := rdVarint_inv hb h1
    split at h
    · cases h
    rename_i hend
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hend' : off + data.length ≤ maxEnd := Nat.le_of_not_lt hend
    have hA : ValidBytes r2 ∧ off < Varint.limit ∧
        ((t / 4 % 2 = 1 ∧ r1 = Varint.encodeBytes off ++ r2) ∨ (¬ t / 4 % 2 = 1 ∧ off = 0 ∧ r1 = r2)) := by
      by_cases c : t / 4 % 2 = 1
      · rw [if_pos c] at h2
        obtain ⟨e, lo, v2⟩ := rdVarint_inv v1 h2
        exact ⟨v2, lo, Or.inl ⟨c, e⟩⟩
      · rw [if_neg c] at h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨v1, h0, Or.inr ⟨c, rfl, rfl⟩⟩
    obtain ⟨v2, lo, hA⟩ := hA
    have hB : ValidBytes data ∧ ValidBytes r3 ∧
        ((t / 2 % 2 = 0 ∧ r2 = data ∧ r3 = []) ∨
          (¬ t / 2 % 2 = 0 ∧ r2 = Varint.encodeBytes data.length ++ (data ++ r3))) := by
      by_cases c : t / 2 % 2 = 0
      · rw [if_pos c] at h3
        obtain ⟨e, l, vd, vr⟩ := rdBytes_inv v2 h3
        have hnil : r3 = [] := nil_of_len0 r3 (by rw [e, List.length_append] at l; omega)
        exact ⟨vd, vr, Or.inl ⟨c, by rw [e, hnil]; simp, hnil⟩⟩
      · rw [if_neg c] at h3
        obtain ⟨e, _, vd, vr⟩ := rdLenPrefixed_inv v2 h3
        exact ⟨vd, vr, Or.inr ⟨c, e⟩⟩
    obtain ⟨vd, vr, hB⟩ := hB
    refine ⟨good_of _ vd (by simp [Frame.varintFields, lid, lo, h0])
      (by intro _ _ _ _ _ he; cases he; exact hend') (by simp), ?_, vr, ?_⟩
    · intro hi
      rcases hB with ⟨_, _, e⟩ | ⟨c, _⟩
      · exact e
      · exact absurd (of_decide_eq_true hi) c
    · rcases hA with ⟨c4, e1⟩ | ⟨c4, o0, e1⟩
      · by_cases ho : off = 0
        · subst ho
          refine Or.inr ⟨id, _, data, _, rfl, ?_⟩
          rcases hB with ⟨c2, e2, e3⟩ | ⟨c2, e2⟩
          · subst e1 e2 e3
            simp only [offBytes, stype_off t h8 c4]
            simp [flat, c2]
          · subst e1 e2
            simp only [offBytes, stype_off t h8 c4]
            simp [flat, c2]
        · refine Or.inl ?_
          have hst := stype_eq t h8 off ⟨fun _ => ho, fun _ => c4⟩
          rcases hB with ⟨c2, e2, e3⟩ | ⟨c2, e2⟩
          · subst e1 e2 e3
            simp only [Frame.bytes, Frame.puts, hst]
            simp [flat, c2, ho]
          · subst e1 e2
            simp only [Frame.bytes, Frame.puts, hst]
            simp [flat, c2, ho]
      · subst o0
        refine Or.inl ?_
        have hst := stype_eq t h8 0 ⟨fun h => absurd h c4, fun h => absurd rfl h⟩
        rcases hB with ⟨c2, e2, e3⟩ | ⟨c2, e2⟩
        · subst e1 e2 e3
          simp only [Frame.bytes, Frame.puts, hst]
          simp [flat, c2]
        · subst e1 e2
          simp only [Frame.bytes, Frame.puts, hst]
          simp [flat, c2]
  rw [if_neg h8] at h
  by_cases h_t : t = 0x11
  · -- MAX_STREAM_DATA
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨id, r1, h1, e, r2, h2, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, v1⟩ := rdVarint_inv hb h1
    obtain ⟨rfl, l2, v2⟩ := rdVarint_inv v1 h2
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, l1, l2, h0]) (by simp) (by simp), trivial, v2,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x12
  · -- MAX_STREAMS
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨id, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, v1⟩ := rdVarint_inv hb h1
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, l1, h0]) (by simp) (by simp), trivial, v1,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x1a
  · -- PATH_CHALLENGE
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨d, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, vd, v1⟩ := rdBytes_inv hb h1
    exact ⟨good_of _ ⟨l1, vd⟩ (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, v1,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x1b
  · -- PATH_RESPONSE
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨d, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, vd, v1⟩ := rdBytes_inv hb h1
    exact ⟨good_of _ ⟨l1, vd⟩ (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, v1,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x1c
  · -- CLOSE
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨id, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, v1⟩ := rdVarint_inv hb h1
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, l1, h0]) (by simp) (by simp), trivial, v1,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x30
  · -- DATAGRAM to the end of the packet
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨d, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e, l1, vd, v1⟩ := rdBytes_inv hb h1
    have hnil : r1 = [] := nil_of_len0 r1 (by rw [e, List.length_append] at l1; omega)
    subst hnil
    simp only [List.append_nil] at e
    subst e
    exact ⟨good_of _ ⟨vd, by simp⟩ (by simp [Frame.varintFields, h0]) (by simp) (by simp), fun _ => rfl, v1,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x31
  · -- DATAGRAM with a length
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨d, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, vd, v1⟩ := rdLenPrefixed_inv hb h1
    exact ⟨good_of _ ⟨vd, fun _ => l1⟩ (by simp [Frame.varintFields, h0]) (by simp) (by simp),
      (by intro hi; cases hi), v1, Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x3a
  · -- MTU_PROBE_ECHO
    rw [if_pos h_t] at h; subst h_t
    simp only [andThen_eq_ok] at h
    obtain ⟨d, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l1, vd, v1⟩ := rdBytes_inv hb h1
    obtain ⟨e1, e2⟩ := be16_be d l1 vd
    exact ⟨good_of _ e2 (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, v1,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small, e1])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x3b
  · -- SLEEP
    rw [if_pos h_t] at h; subst h_t
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, hb,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x3c
  · -- WAKE
    rw [if_pos h_t] at h; subst h_t
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, hb,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x3d
  · -- REKEY
    rw [if_pos h_t] at h; subst h_t
    unfold rdRekey at h
    rw [andThen_eq_ok] at h; obtain ⟨k, r1, h1, h⟩ := h
    obtain ⟨rfl, lk, vk, v1⟩ := rdBytes_inv hb h1
    obtain ⟨kb, rfl⟩ := len1 k lk
    by_cases hk : [kb].headD 0 > 1
    · rw [if_pos hk] at h; cases h
    rw [if_neg hk] at h
    have hk' : ¬ kb > 1 := hk
    rw [andThen_eq_ok] at h; obtain ⟨sh, r2, h2, h⟩ := h
    obtain ⟨rfl, ls, vs, v2⟩ := rdBytes_inv v1 h2
    by_cases hk1 : [kb].headD 0 = 1
    · rw [if_pos hk1] at h
      have hk1' : kb = 1 := hk1
      subst hk1'
      simp only [andThen_eq_ok] at h
      obtain ⟨echo, r3, h3, spn, r4, h4, h⟩ := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, le, ve, v3⟩ := rdBytes_inv v2 h3
      obtain ⟨rfl, lspn, v4⟩ := rdVarint_inv v3 h4
      exact ⟨good_of _ ⟨ls, vs, le, ve, by simp⟩ (by simp [Frame.varintFields, lspn, h0]) (by simp) (by simp),
        trivial, v4, Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
    · rw [if_neg hk1] at h
      have hk1' : ¬ kb = 1 := hk1
      have hz : kb = 0 := by omega
      subst hz
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨good_of _ ⟨ls, vs, by simp, valid_replicate 8, fun _ => ⟨rfl, rfl⟩⟩
        (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, v2,
        Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x3e
  · -- READY
    rw [if_pos h_t] at h; subst h_t
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨good_of _ trivial (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial, hb,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small])⟩
  rw [if_neg h_t] at h
  by_cases h_t : t = 0x3f
  · -- NEW_TICKETS
    rw [if_pos h_t] at h; subst h_t
    unfold rdTicketBatch at h
    rw [andThen_eq_ok] at h; obtain ⟨c, r1, h1, h⟩ := h
    obtain ⟨rfl, lc, vc, v1⟩ := rdBytes_inv hb h1
    obtain ⟨cb, rfl⟩ := len1 c lc
    by_cases hc : [cb].headD 0 > maxBatch
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h
    rw [andThen_eq_ok] at h; obtain ⟨es, r2, h2, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, l3, hes, v3⟩ := rdTickets_inv _ _ _ _ v1 h2
    have l3' : es.length = cb := l3
    subst l3'
    exact ⟨good_of _ ⟨(show es.length ≤ maxBatch from Nat.le_of_not_lt hc), hes⟩ (by simp [Frame.varintFields, h0]) (by simp) (by simp), trivial,
      v3, Or.inl (by simp [Frame.bytes, Frame.puts, flat, enc_small, ticketBytes])⟩
  rw [if_neg h_t] at h
  by_cases hext : t ≥ extBase
  · -- an extension frame
    rw [if_pos hext] at h
    rw [andThen_eq_ok] at h; obtain ⟨body, r1, h1, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, ll, vb, vr⟩ := rdLenPrefixed_inv hb h1
    exact ⟨good_of _ ⟨vb, ll⟩ (by simp [Frame.varintFields, ht, h0]) (by simp)
      (by intro ty body' he; injection he with e1 _; subst e1; exact hext), trivial, vr,
      Or.inl (by simp [Frame.bytes, Frame.puts, flat])⟩
  rw [if_neg hext] at h
  cases h

/-- Canonical, with the one leniency: an accepted input is the encoding of the frame it yields followed by what is
left, or, for a STREAM frame at offset 0, that encoding with the OFF bit set and a zero offset; the frame is one
`write` accepts and what is left is what may follow it. -/
theorem decode_inv (b : List Nat) (hb : ValidBytes b) (f : Frame) (r : List Nat) (h : decode b = .ok (f, r)) :
    Accepted b f r := by
  unfold decode at h
  rw [andThen_eq_ok] at h
  obtain ⟨t, r0, h1, h2⟩ := h
  obtain ⟨rfl, lt, v0⟩ := rdVarint_inv hb h1
  exact body_inv t r0 f r lt v0 h2

theorem encodedLen_pos (f : Frame) (hwf : f.WF) : 1 ≤ f.encodedLen := by
  cases f with
  | padding len => exact hwf
  | ext ty body =>
    have := Varint.encodedLen_pos ty
    simp only [Frame.encodedLen]
    omega
  | _ => simp only [Frame.encodedLen, streamOverhead, datagramOverhead] <;> omega

theorem offBytes_pos (id : Nat) (fin : Bool) (data : List Nat) (imp : Bool) :
    1 ≤ (offBytes id fin data imp).length := by
  have := Varint.encodedLen_pos (streamType 1 fin imp)
  simp only [offBytes, List.cons_append, flat, List.length_append, Varint.length_encodeBytes]
  omega

/-- Progress: a decoded frame takes at least one byte. -/
theorem decode_progress (b : List Nat) (hb : ValidBytes b) (f : Frame) (r : List Nat)
    (h : decode b = .ok (f, r)) : r.length < b.length ∧ ValidBytes r := by
  obtain ⟨hg, _, vr, hbytes⟩ := decode_inv b hb f r h
  refine ⟨?_, vr⟩
  rcases hbytes with rfl | ⟨id, fin, data, imp, _, rfl⟩
  · have h1 := bytes_length f hg.1
    have h2 := encodedLen_pos f hg.1
    rw [List.length_append]
    omega
  · have := offBytes_pos id fin data imp
    rw [List.length_append]
    omega

/-- An accepted frame is written back in its canonical encoding: the bytes that were read, except for the OFF bit
of a STREAM frame at offset 0. -/
theorem decode_write (b : List Nat) (hb : ValidBytes b) (f : Frame) (r : List Nat) (h : decode b = .ok (f, r))
    (cap : Nat) (w : List Nat) (hroom : f.encodedLen ≤ cap - w.length) : f.write cap w = .ok (w ++ f.bytes) := by
  obtain ⟨hg, _, _, _⟩ := decode_inv b hb f r h
  rw [write_eq cap w f hg.1, hg.2]
  simp [hroom]

/-! ## The iterator -/

/-- `FrameIter` never runs out of fuel: any fuel of at least the length of the payload gives the same frames. -/
theorem iterFuel_enough : ∀ (n m : Nat) (b : List Nat), ValidBytes b → b.length ≤ n → b.length ≤ m →
    iterFuel n b = iterFuel m b := by
  intro n
  induction n with
  | zero =>
    intro m b _ h1 _
    have hb : b = [] := nil_of_len0 b (by omega)
    subst hb
    cases m <;> simp [iterFuel]
  | succ n ih =>
    intro m b hv h1 h2
    cases m with
    | zero =>
      have hb : b = [] := nil_of_len0 b (by omega)
      subst hb
      simp [iterFuel]
    | succ m =>
      simp only [iterFuel]
      by_cases hb : b = []
      · simp [hb]
      · rw [if_neg hb, if_neg hb]
        cases hd : decode b with
        | error e => rfl
        | ok p =>
          obtain ⟨f, r⟩ := p
          obtain ⟨hl, vr⟩ := decode_progress b hv f r hd
          simp only
          rw [ih m r vr (by omega) (by omega)]

/-- The bytes of a payload made of frames. -/
def payload : List Frame → List Nat
  | [] => []
  | f :: fs => f.bytes ++ payload fs

/-- A payload the code builds: every frame is one `write` accepts and is followed by what may follow it (no zero
byte right after a PADDING run that is to be read as one frame; a frame without a length is the last). -/
def Packet : List Frame → Prop
  | [] => True
  | f :: fs => f.Good ∧ f.Sep (payload fs) ∧ Packet fs

theorem iter_payload : ∀ (fs : List Frame) (n : Nat), Packet fs → (payload fs).length ≤ n →
    iterFuel n (payload fs) = (fs, none) := by
  intro fs
  induction fs with
  | nil => intro n _ _; cases n <;> simp [iterFuel, payload]
  | cons f fs ih =>
    intro n hp hlen
    obtain ⟨hg, hsep, hp'⟩ := hp
    have h1 := bytes_length f hg.1
    have h2 := encodedLen_pos f hg.1
    simp only [payload, List.length_append] at hlen
    cases n with
    | zero => omega
    | succ n =>
      have hne : f.bytes ++ payload fs ≠ [] := by
        intro e
        have := congrArg List.length e
        rw [List.length_append, List.length_nil] at this
        omega
      show iterFuel (n + 1) (f.bytes ++ payload fs) = _
      simp only [iterFuel]
      rw [if_neg hne, decode_bytes f hg _ hsep]
      simp only
      rw [ih n hp' (by omega)]

/-- Round trip of a payload: `FrameIter` over the encodings of frames yields the frames in order and no error. -/
theorem frames_bytes (fs : List Frame) (h : Packet fs) : frames (payload fs) = (fs, none) :=
  iter_payload fs _ h (Nat.le_refl _)

end Pinc.TransportFrame

#audit_axioms Pinc.TransportFrame.decode_bytes
#audit_axioms Pinc.TransportFrame.decode_offBytes
#audit_axioms Pinc.TransportFrame.decode_unknown
#audit_axioms Pinc.TransportFrame.decode_inv
#audit_axioms Pinc.TransportFrame.decode_progress
#audit_axioms Pinc.TransportFrame.decode_write
#audit_axioms Pinc.TransportFrame.iterFuel_enough
#audit_axioms Pinc.TransportFrame.frames_bytes
