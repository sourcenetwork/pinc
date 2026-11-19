import Pinc.TransportFrameCodec

/-!
# The PINCER frame codecs: the ranges of an ACK

`write_ack` and `ack_len` take packet-number ranges, highest first; `Ack::parse` validates the wire form and
`Ack::ranges` gives the ranges back (the model of `TransportFrame.lean`).

* **Round trip and length** (`writeAck_ok`, `writeAck_decode`): what `write_ack` writes is the encoding of an ACK
  frame that `decode` reads back, whose ranges are the first 32 of the ranges given (the range cap), and `ack_len`
  is the number of bytes written.
* **Errors are total, a refusal writes nothing** (`ackLen_error`, `writeAck_room`): ranges that `ack_len` refuses
  are refused by `write_ack` with the same error, always `Ack` (no range, an empty range, one above 2^62 - 1, out
  of order, touching or overlapping, among the first 32); otherwise `write_ack` fails exactly when the room is
  short, with `BufferTooSmall` and the shortfall. An error returns no writer.
* **Canonical** (`ranges_write`): the ranges of a validated ACK are `extra + 1` ranges that `write_ack` accepts
  and writes back as the same bytes, so the wire form and the list of ranges determine each other.
-/

namespace Pinc.TransportFrame
open Pinc
open Pinc.Varint (ValidBytes)

theorem pairBytes_len (its : List (Nat × Nat)) : (pairBytes its).length = pairLen its := by
  induction its with
  | nil => rfl
  | cons p its ih =>
    obtain ⟨a, b⟩ := p
    simp only [pairBytes, pairLen, List.length_append, Varint.length_encodeBytes, ih]

theorem pairBytes_valid (its : List (Nat × Nat)) : ValidBytes (pairBytes its) := by
  induction its with
  | nil => exact valid_nil
  | cons p its ih =>
    obtain ⟨a, b⟩ := p
    simp only [pairBytes]
    exact (valid_append _ _).mpr ⟨(valid_append _ _).mpr ⟨valid_enc a, valid_enc b⟩, ih⟩

theorem flat_pairs (its : List (Nat × Nat)) :
    flat (its.flatMap (fun p => [Put.v p.1, Put.v p.2])) = pairBytes its := by
  induction its with
  | nil => simp [flat, pairBytes]
  | cons p its ih =>
    obtain ⟨a, b⟩ := p
    simp [flat, pairBytes, ih]

theorem maxPn_lt : maxPn < Varint.limit := by
  simp only [maxPn]; rw [limit_eq]; omega

/-- The further ranges `write_ack` accepts are read back by `Ack::parse` and by `Ack::ranges`. -/
theorem wire_loop : ∀ (rs : List (Nat × Nat)) (p : Nat) (its : List (Nat × Nat)), p ≤ maxPn →
    wireFields (some p) rs = .ok its →
    its.length = rs.length ∧ (∀ q ∈ its, q.1 < Varint.limit ∧ q.2 < Varint.limit) ∧
      (∃ q, ackLoop its.length p (pairBytes its) = .ok (q, [])) ∧
      rangesLoop its.length p (pairBytes its) = rs := by
  intro rs
  induction rs with
  | nil =>
    intro p its _ h
    simp only [wireFields, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, by simp, ⟨p, by simp [ackLoop, pairBytes]⟩, by simp [rangesLoop]⟩
  | cons r rs ih =>
    intro p its hp h
    simp only [wireFields] at h
    cases hi : wireItem (some p) r.1 r.2 with
    | error e => rw [hi] at h; cases h
    | ok it =>
      rw [hi] at h
      dsimp only at h
      cases hw : wireFields (some r.1) rs with
      | error e => rw [hw] at h; cases h
      | ok its' =>
        rw [hw] at h
        simp only [Except.ok.injEq] at h
        subst h
        unfold wireItem at hi
        split at hi
        · cases hi
        rename_i c0
        dsimp only at hi
        split at hi
        · cases hi
        rename_i c1
        simp only [Except.ok.injEq] at hi
        subst hi
        have hm := maxPn_lt
        have hs : r.1 ≤ maxPn := by omega
        obtain ⟨hl, hlt, ⟨q, hq⟩, hr⟩ := ih r.1 its' hs hw
        have hg : p - r.2 - 2 < Varint.limit := by omega
        have hn : r.2 - r.1 < Varint.limit := by omega
        have e1 : p - (p - r.2 - 2) - 2 = r.2 := by omega
        have e2 : r.2 - (r.2 - r.1) = r.1 := by omega
        have c2 : ¬ p < p - r.2 - 2 + 2 := by omega
        have c3 : ¬ r.2 < r.2 - r.1 := by omega
        refine ⟨by simp [hl], ?_, ⟨q, ?_⟩, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hg, hn⟩
          · exact hlt x hx
        · simp only [List.length_cons, ackLoop, pairBytes, List.append_assoc, rdV_enc hg, rdV_enc hn, andThen_ok,
            e1, e2]
          rw [if_neg c2, if_neg c3]
          exact hq
        · simp only [List.length_cons, rangesLoop, pairBytes, List.append_assoc, rdV_enc hg, rdV_enc hn, e1, e2]
          rw [if_neg c2, if_neg c3, hr]

/-- What `write_ack` writes for ranges it accepts is the encoding of a frame `write` accepts, whose ranges are the
first 32 of the ranges given. -/
theorem fields_spec (rs : List (Nat × Nat)) (l f : Nat) (its : List (Nat × Nat))
    (h : wireFields none (rs.take maxAckRanges) = .ok ((l, f) :: its)) :
    (Frame.ack l f its.length (pairBytes its)).Good ∧ PutsOk (ackPuts l f its) ∧
      flat (ackPuts l f its) = (Frame.ack l f its.length (pairBytes its)).bytes ∧
      ackRanges l f its.length (pairBytes its) = rs.take maxAckRanges := by
  have hTl : (rs.take maxAckRanges).length ≤ 32 := by
    simp only [maxAckRanges, List.length_take]; omega
  generalize rs.take maxAckRanges = T at h hTl
  have h0 : (0 : Nat) < Varint.limit := by rw [limit_eq]; omega
  have hm := maxPn_lt
  cases T with
  | nil => simp [wireFields] at h
  | cons r rs' =>
    simp only [wireFields] at h
    cases hi : wireItem none r.1 r.2 with
    | error e => rw [hi] at h; cases h
    | ok it =>
      rw [hi] at h
      dsimp only at h
      cases hw : wireFields (some r.1) rs' with
      | error e => rw [hw] at h; cases h
      | ok its' =>
        rw [hw] at h
        simp only [Except.ok.injEq, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        unfold wireItem at hi
        split at hi
        · cases hi
        rename_i c0
        dsimp only at hi
        simp only [Except.ok.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        have hs : r.1 ≤ maxPn := by omega
        obtain ⟨hl, hlt, ⟨q, hq⟩, hr⟩ := wire_loop rs' r.1 its' hs hw
        have e : r.2 - (r.2 - r.1) = r.1 := by omega
        have hx : its'.length < 32 := by simp only [List.length_cons] at hTl; omega
        refine ⟨good_of _ ⟨by omega, hx, by omega, pairBytes_valid its', q, by rw [e]; exact hq⟩
          (by simp [Frame.varintFields, h0]) (by simp) (by simp), ?_, ?_, ?_⟩
        · intro x hx'
          simp only [ackPuts, List.mem_append, List.mem_cons, Put.v.injEq, List.not_mem_nil, or_false,
            List.mem_flatMap] at hx'
          rcases hx' with (rfl | rfl | rfl | rfl) | ⟨p, hp, hx'⟩
          · rw [limit_eq]; omega
          · omega
          · rw [limit_eq]; omega
          · omega
          · rcases hx' with rfl | rfl
            · exact (hlt p hp).1
            · exact (hlt p hp).2
        · simp [ackPuts, Frame.bytes, Frame.puts, flat, flat_pairs]
        · unfold ackRanges
          rw [if_neg (by omega), e, hr]

theorem ackShape_ok (rs : List (Nat × Nat)) (c body : Nat) (h : ackShape rs = .ok (c, body)) :
    ∃ l f its, wireFields none (rs.take maxAckRanges) = .ok ((l, f) :: its) ∧ c = its.length + 1 ∧
      body = pairLen its + (Varint.encodedLen l + Varint.encodedLen its.length + Varint.encodedLen f) := by
  unfold ackShape at h
  split at h
  · cases h
  · cases h
  · rename_i l f its hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨l, f, its, hw, h.1.symm, h.2.symm⟩

theorem ackPuts_len (rs : List (Nat × Nat)) (l f : Nat) (its : List (Nat × Nat))
    (h : wireFields none (rs.take maxAckRanges) = .ok ((l, f) :: its)) :
    (flat (ackPuts l f its)).length =
      1 + (pairLen its + (Varint.encodedLen l + Varint.encodedLen its.length + Varint.encodedLen f)) := by
  obtain ⟨hg, _, hf, _⟩ := fields_spec rs l f its h
  rw [hf, bytes_length _ hg.1]
  simp only [Frame.encodedLen, pairBytes_len]
  omega

/-- Round trip and length: what `write_ack` appends is the encoding of an ACK frame `write` accepts, the ranges of
that frame are the first 32 of the ranges given, and `ack_len` is the number of bytes appended. -/
theorem writeAck_ok (cap : Nat) (w : List Nat) (rs : List (Nat × Nat)) (out : List Nat)
    (h : writeAck cap w rs = .ok out) :
    ∃ l f x tail, (Frame.ack l f x tail).Good ∧ out = w ++ (Frame.ack l f x tail).bytes ∧
      ackRanges l f x tail = rs.take maxAckRanges ∧ ackLen rs = .ok (Frame.ack l f x tail).bytes.length := by
  unfold writeAck at h
  cases hs : ackShape rs with
  | error e => rw [hs] at h; cases h
  | ok p =>
    obtain ⟨c, body⟩ := p
    rw [hs] at h
    dsimp only at h
    obtain ⟨l, f, its, hw, rfl, rfl⟩ := ackShape_ok rs c body hs
    split at h
    · rename_i hroom
      rw [hw] at h
      dsimp only at h
      obtain ⟨hg, hp, hf, hr⟩ := fields_spec rs l f its hw
      have hlen := ackPuts_len rs l f its hw
      rw [runPuts_ok cap _ w hp (by omega)] at h
      simp only [Except.ok.injEq] at h
      refine ⟨l, f, its.length, pairBytes its, hg, by rw [← hf]; exact h.symm, hr, ?_⟩
      unfold ackLen
      rw [hs, ← hf, hlen]
    · cases h

/-- Round trip through the decoder: an ACK written by `write_ack` into an empty buffer, followed by anything, is
read back as a frame whose ranges are the first 32 of the ranges given, and what follows is left. -/
theorem writeAck_decode (cap : Nat) (rs : List (Nat × Nat)) (out rest : List Nat)
    (h : writeAck cap [] rs = .ok out) :
    ∃ l f x tail, decode (out ++ rest) = .ok (.ack l f x tail, rest) ∧
      ackRanges l f x tail = rs.take maxAckRanges ∧ ackLen rs = .ok out.length := by
  obtain ⟨l, f, x, tail, hg, ho, hr, hl⟩ := writeAck_ok cap [] rs out h
  simp only [List.nil_append] at ho
  subst ho
  exact ⟨l, f, x, tail, decode_bytes _ hg rest trivial, hr, hl⟩

/-- Errors are total: when `ack_len` accepts the ranges, `write_ack` fails exactly when the room is short, with
the shortfall, and otherwise writes. -/
theorem writeAck_room (cap : Nat) (w : List Nat) (rs : List (Nat × Nat)) (n : Nat) (h : ackLen rs = .ok n) :
    (n ≤ cap - w.length → ∃ out, writeAck cap w rs = .ok out) ∧
      (¬ n ≤ cap - w.length → writeAck cap w rs = .error (.bufferTooSmall (n - (cap - w.length)))) := by
  unfold ackLen at h
  cases hs : ackShape rs with
  | error e => rw [hs] at h; cases h
  | ok p =>
    obtain ⟨c, body⟩ := p
    rw [hs] at h
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨l, f, its, hw, rfl, rfl⟩ := ackShape_ok rs c body hs
    constructor
    · intro hroom
      obtain ⟨_, hp, _, _⟩ := fields_spec rs l f its hw
      have hlen := ackPuts_len rs l f its hw
      refine ⟨w ++ flat (ackPuts l f its), ?_⟩
      unfold writeAck
      rw [hs]
      dsimp only
      rw [if_pos hroom, hw]
      dsimp only
      exact runPuts_ok cap _ w hp (by omega)
    · intro hroom
      unfold writeAck
      rw [hs]
      dsimp only
      rw [if_neg hroom]

theorem wireFields_error : ∀ (rs : List (Nat × Nat)) (prev : Option Nat) (e : Err),
    wireFields prev rs = .error e → e = .ack := by
  intro rs
  induction rs with
  | nil => intro prev e h; simp [wireFields] at h
  | cons r rs ih =>
    intro prev e h
    simp only [wireFields] at h
    cases hi : wireItem prev r.1 r.2 with
    | error e' =>
      rw [hi] at h
      simp only [Except.error.injEq] at h
      subst h
      unfold wireItem at hi
      split at hi
      · simp only [Except.error.injEq] at hi; exact hi.symm
      · split at hi
        · cases hi
        · split at hi
          · simp only [Except.error.injEq] at hi; exact hi.symm
          · cases hi
    | ok it =>
      rw [hi] at h
      dsimp only at h
      cases hw : wireFields (some r.1) rs with
      | error e' =>
        rw [hw] at h
        simp only [Except.error.injEq] at h
        subst h
        exact ih _ _ hw
      | ok its => rw [hw] at h; cases h

/-- Errors are total: ranges that `ack_len` refuses are refused with `Ack`, and `write_ack` refuses them with the
same error whatever the room. -/
theorem ackLen_error (rs : List (Nat × Nat)) (e : Err) (h : ackLen rs = .error e) :
    e = .ack ∧ ∀ cap w, writeAck cap w rs = .error .ack := by
  unfold ackLen at h
  cases hs : ackShape rs with
  | ok p => rw [hs] at h; cases h
  | error e' =>
    rw [hs] at h
    simp only [Except.error.injEq] at h
    subst h
    have he : e' = .ack := by
      unfold ackShape at hs
      split at hs
      · rename_i e'' hw
        simp only [Except.error.injEq] at hs
        subst hs
        exact wireFields_error _ _ _ hw
      · simp only [Except.error.injEq] at hs; exact hs.symm
      · cases hs
    subst he
    refine ⟨rfl, fun cap w => ?_⟩
    unfold writeAck
    rw [hs]

/-- The further ranges of a validated ACK are ranges `write_ack` accepts, with the same wire fields. -/
theorem loop_wire : ∀ (x ps : Nat) (tail : List Nat) (q : Nat), ps ≤ maxPn → ValidBytes tail →
    ackLoop x ps tail = .ok (q, []) →
    ∃ its, wireFields (some ps) (rangesLoop x ps tail) = .ok its ∧ pairBytes its = tail ∧ its.length = x ∧
      (rangesLoop x ps tail).length = x := by
  intro x
  induction x with
  | zero =>
    intro ps tail q _ _ h
    simp only [ackLoop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], by simp [rangesLoop, wireFields], rfl, rfl, by simp [rangesLoop]⟩
  | succ k ih =>
    intro ps tail q hp hv h
    simp only [ackLoop, andThen_eq_ok] at h
    obtain ⟨gap, r1, h1, len, r2, h2, h3⟩ := h
    obtain ⟨rfl, hg, v1⟩ := rdVarint_inv hv h1
    obtain ⟨rfl, hl, v2⟩ := rdVarint_inv v1 h2
    split at h3
    · cases h3
    rename_i c1
    split at h3
    · cases h3
    rename_i c2
    obtain ⟨its, hw, hb, hn, hrl⟩ := ih _ _ _ (by omega) v2 h3
    have hrng : rangesLoop (k + 1) ps (Varint.encodeBytes gap ++ (Varint.encodeBytes len ++ r2)) =
        (ps - gap - 2 - len, ps - gap - 2) :: rangesLoop k (ps - gap - 2 - len) r2 := by
      simp only [rangesLoop, rdV_enc hg, rdV_enc hl]
      rw [if_neg c1, if_neg c2]
    have hitem : wireItem (some ps) (ps - gap - 2 - len) (ps - gap - 2) = .ok (gap, len) := by
      unfold wireItem
      rw [if_neg (by omega)]
      show (if ps < ps - gap - 2 + 2 then _ else _) = _
      rw [if_neg (by omega), show ps - (ps - gap - 2) - 2 = gap by omega,
        show ps - gap - 2 - (ps - gap - 2 - len) = len by omega]
    rw [hrng]
    refine ⟨(gap, len) :: its, ?_, by simp [pairBytes, hb], by simp [hn], by simp [hrl]⟩
    simp only [wireFields, hitem, hw]

/-- Canonical: the ranges of a validated ACK are `extra + 1` ranges, and `write_ack` writes them back as the
bytes of the frame. -/
theorem ranges_write (l f x : Nat) (tail : List Nat) (h : AckOk l f x tail) (cap : Nat) (w : List Nat)
    (hroom : (Frame.ack l f x tail).encodedLen ≤ cap - w.length) :
    writeAck cap w (ackRanges l f x tail) = .ok (w ++ (Frame.ack l f x tail).bytes) ∧
      (ackRanges l f x tail).length = x + 1 := by
  obtain ⟨h1, h2, h3, vt, q, hq⟩ := h
  obtain ⟨its, hw, hb, hn, hrl⟩ := loop_wire x (l - f) tail q (by omega) vt hq
  have hR : ackRanges l f x tail = (l - f, l) :: rangesLoop x (l - f) tail := by
    unfold ackRanges
    rw [if_neg (by omega)]
  have hlen : (ackRanges l f x tail).length = x + 1 := by rw [hR]; simp [hrl]
  have htake : (ackRanges l f x tail).take maxAckRanges = ackRanges l f x tail :=
    List.take_of_length_le (by rw [hlen]; simp only [maxAckRanges] at h2 ⊢; omega)
  have hitem : wireItem none (l - f) l = .ok (l, f) := by
    unfold wireItem
    rw [if_neg (by omega)]
    show Except.ok (l, l - (l - f)) = _
    rw [show l - (l - f) = f by omega]
  have hfields : wireFields none ((ackRanges l f x tail).take maxAckRanges) = .ok ((l, f) :: its) := by
    rw [htake, hR]
    simp only [wireFields, hitem, hw]
  refine ⟨?_, hlen⟩
  obtain ⟨hg, hp, hf, _⟩ := fields_spec _ l f its hfields
  have hpl := ackPuts_len _ l f its hfields
  subst hn
  subst hb
  simp only [Frame.encodedLen, pairBytes_len] at hroom
  unfold writeAck ackShape
  rw [hfields]
  dsimp only
  rw [if_pos (by omega)]
  rw [runPuts_ok cap _ w hp (by omega), hf]

/-- The ranges of a decoded ACK are written back as the bytes that were read. -/
theorem decode_ranges (b : List Nat) (hb : ValidBytes b) (l f x : Nat) (tail r : List Nat)
    (h : decode b = .ok (.ack l f x tail, r)) :
    writeAck b.length [] (ackRanges l f x tail) = .ok (b.take (b.length - r.length)) ∧
      (ackRanges l f x tail).length = x + 1 := by
  obtain ⟨hg, _, _, hbytes⟩ := decode_inv b hb _ r h
  have hbytes' : b = (Frame.ack l f x tail).bytes ++ r := by
    rcases hbytes with e | ⟨_, _, _, _, e, _⟩
    · exact e
    · cases e
  have hl := bytes_length _ hg.1
  have hroom : (Frame.ack l f x tail).encodedLen ≤ b.length - ([] : List Nat).length := by
    rw [hbytes', List.length_append, hl]
    simp
  obtain ⟨hw, hn⟩ := ranges_write l f x tail hg.1 b.length [] hroom
  refine ⟨?_, hn⟩
  rw [hw]
  have : b.take (b.length - r.length) = (Frame.ack l f x tail).bytes := by
    rw [hbytes']
    simp
  rw [this]
  simp

end Pinc.TransportFrame

#audit_axioms Pinc.TransportFrame.writeAck_ok
#audit_axioms Pinc.TransportFrame.writeAck_decode
#audit_axioms Pinc.TransportFrame.writeAck_room
#audit_axioms Pinc.TransportFrame.ackLen_error
#audit_axioms Pinc.TransportFrame.ranges_write
#audit_axioms Pinc.TransportFrame.decode_ranges
