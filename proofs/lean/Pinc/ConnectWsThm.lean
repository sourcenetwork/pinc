import Pinc.ConnectWs

/-!
# The WebSocket framing of the carrier: what the decoder accepts and what it refuses

`Valid` is the rule written from the documentation of `ws.rs` and RFC 6455, from the header alone: no reserved bit,
an opcode of continuation, binary, close, ping or pong, the mask bit the sender's role asks for, the length in its
shortest form, a length of at most `MAX_PAYLOAD`, a control frame final and of at most 125 bytes, and a continuation
exactly inside a fragmented message. For every header the decoder either asks for more bytes, refuses, or accepts:

- it refuses exactly the invalid headers, from the header alone, whatever payload is or is not held
  (`decode_err_iff`): so a wrong mask, a longer length form, an unknown opcode, a reserved bit, a fragmented or long
  control frame, a frame out of sequence (a continuation with no message in progress, a data frame between fragments)
  and a length over the bound are each refused (`wrong_mask`, ...), and the length over the bound is refused before a
  byte of its payload is waited for or kept (`oversize_refused`);
- it accepts exactly the valid frames whose bytes are all held (`decode_frame_iff`), unmasking the payload, and takes
  exactly the frame's bytes; a valid frame with bytes missing, and a header that is not whole yet, wait
  (`decode_idle_iff`);
- after an accepted data frame a message is open exactly when FIN was clear; a control frame leaves that as it was
  (`accepted_inm`).
-/

namespace Pinc.ConnectWs

/-- The rule, from the header: first byte `b0`, second byte `b1`, the declared length `len`. -/
def Valid (mp : Nat) (peer : Peer) (inm : Bool) (b0 b1 len : Nat) : Prop :=
  b0 / 16 % 8 = 0 ∧
  (b0 % 16 = 0 ∨ b0 % 16 = 2 ∨ b0 % 16 = 8 ∨ b0 % 16 = 9 ∨ b0 % 16 = 10) ∧
  (128 ≤ b1 ↔ peer = .client) ∧
  ((b1 % 128 ≤ 125 ∧ len = b1 % 128) ∨ (b1 % 128 = 126 ∧ 126 ≤ len) ∨ (b1 % 128 = 127 ∧ 65536 ≤ len)) ∧
  len ≤ mp ∧
  (8 ≤ b0 % 16 → 128 ≤ b0 ∧ len ≤ 125) ∧
  (b0 % 16 < 8 → ((b0 % 16 = 0) ↔ inm = true))

/-- The checks made before the length is known. -/
def Pre (peer : Peer) (b0 b1 : Nat) : Prop :=
  b0 / 16 % 8 = 0 ∧
  (b0 % 16 = 0 ∨ b0 % 16 = 2 ∨ b0 % 16 = 8 ∨ b0 % 16 = 9 ∨ b0 % 16 = 10) ∧
  (128 ≤ b1 ↔ peer = .client)

/-- The bytes of the frame: header, mask key and payload. -/
def Whole (b1 len head : Nat) : Nat := head + (if 128 ≤ b1 then 4 else 0) + len

theorem isOp_iff (o : Nat) : isOp o = true ↔ (o = 0 ∨ o = 2 ∨ o = 8 ∨ o = 9 ∨ o = 10) := by
  simp [isOp, or_assoc]

theorem isCtl_iff (o : Nat) : isCtl o = true ↔ 8 ≤ o := by simp [isCtl]

theorem decode_short (mp peer inm B n) (h : n < 2) : decode mp peer inm B n = .idle := by
  simp [decode, h]

/-- What the length bytes give: the 7-bit form is the field itself, the others read their extension. -/
theorem declared_form (B : Nat → Nat) (n l7 len head : Nat) (h : declared B n l7 = some (len, head)) :
    (l7 ≠ 126 → l7 ≠ 127 → len = l7 ∧ head = 2) ∧ (l7 = 126 → head = 4) ∧ (l7 = 127 → head = 10) := by
  unfold declared at h
  by_cases h1 : l7 = 126
  · simp only [h1, ite_true] at h; split at h <;> simp_all
  · by_cases h2 : l7 = 127
    · simp only [h2, ite_true, ite_false] at h; split at h <;> simp_all
    · simp only [h1, h2, ite_false] at h; simp_all

/-- The shortest-form test of the code is the form clause of `Valid`, for what the length bytes declare. -/
theorem canon_iff (B : Nat → Nat) (n len head : Nat) (hb : B 1 % 128 < 128)
    (h : declared B n (B 1 % 128) = some (len, head)) :
    canon (B 1 % 128) len = true ↔
      ((B 1 % 128 ≤ 125 ∧ len = B 1 % 128) ∨ (B 1 % 128 = 126 ∧ 126 ≤ len) ∨ (B 1 % 128 = 127 ∧ 65536 ≤ len)) := by
  have hf := declared_form B n _ len head h
  unfold canon
  by_cases h1 : B 1 % 128 = 126
  · simp [h1]
  · by_cases h2 : B 1 % 128 = 127
    · simp [h2]
    · have := hf.1 h1 h2
      simp [h1, h2]
      omega

theorem decode_pre (mp peer inm B n) (h2 : 2 ≤ n) (h : ¬ Pre peer (B 0) (B 1)) :
    ∃ e, decode mp peer inm B n = .err e := by
  unfold decode
  have : ¬ n < 2 := by omega
  simp only [this, ite_false]
  unfold Pre at h
  by_cases r : B 0 / 16 % 8 = 0
  · by_cases o : isOp (B 0 % 16) = true
    · have o' := (isOp_iff _).1 o
      have hm : ¬ (128 ≤ B 1 ↔ peer = .client) := fun hm => h ⟨r, o', hm⟩
      exact ⟨.mask, by simp [r, o, hm]⟩
    · exact ⟨.opcode, by simp [r, o]⟩
  · exact ⟨.reserved, by simp [r]⟩

theorem decode_none (mp peer inm B n) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = none) : decode mp peer inm B n = .idle := by
  obtain ⟨r, o, m⟩ := hp
  have o' : isOp (B 0 % 16) = true := (isOp_iff _).2 o
  have : ¬ n < 2 := by omega
  simp [decode, this, r, o', hd, m]


/-- Split the validity of a header whose first checks pass. -/
theorem valid_iff (mp peer inm B n len head) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) :
    Valid mp peer inm (B 0) (B 1) len ↔
      (canon (B 1 % 128) len = true ∧ len ≤ mp ∧ (8 ≤ B 0 % 16 → 128 ≤ B 0 ∧ len ≤ 125) ∧
        (B 0 % 16 < 8 → ((B 0 % 16 = 0) ↔ inm = true))) := by
  have hc := canon_iff B n len head (by omega) hd
  obtain ⟨r, o, m⟩ := hp
  unfold Valid
  rw [hc]
  constructor
  · rintro ⟨_, _, _, f, b, c, s⟩; exact ⟨f, b, c, s⟩
  · rintro ⟨f, b, c, s⟩; exact ⟨r, o, m, f, b, c, s⟩

theorem decode_some (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) :
    decode mp peer inm B n =
      if canon (B 1 % 128) len = false then .err .lenForm
      else if mp < len then .err .tooLong
      else if (8 ≤ B 0 % 16) ∧ (B 0 < 128 ∨ 125 < len) then .err .control
      else if (B 0 % 16 < 8) ∧ (decide (B 0 % 16 = 0) != inm) = true then .err .sequence
      else if 128 ≤ B 1 ∧ n < head + 4 then .idle
      else if n < Whole (B 1) len head then .idle
      else accept B (B 0) (B 1) len head inm := by
  obtain ⟨r, o, m⟩ := hp
  have o' : isOp (B 0 % 16) = true := (isOp_iff _).2 o
  have : ¬ n < 2 := by omega
  simp [decode, this, r, o', hd, m, Whole, isCtl]

theorem decode_invalid (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hv : ¬ Valid mp peer inm (B 0) (B 1) len) :
    ∃ e, decode mp peer inm B n = .err e := by
  rw [valid_iff mp peer inm B n len head hp hd] at hv
  rw [decode_some mp peer inm B n len head h2 hp hd]
  by_cases c1 : canon (B 1 % 128) len = true
  · by_cases c2 : mp < len
    · exact ⟨.tooLong, by simp [c1, c2]⟩
    · by_cases c3 : (8 ≤ B 0 % 16) ∧ (B 0 < 128 ∨ 125 < len)
      · exact ⟨.control, by simp [c1, c2, c3]⟩
      · have c4 : (B 0 % 16 < 8) ∧ (decide (B 0 % 16 = 0) != inm) = true := by
          refine Classical.byContradiction fun hc => ?_
          apply hv
          refine ⟨c1, by omega, ?_, ?_⟩
          · intro h8; refine Classical.byContradiction fun hh => ?_; exact c3 ⟨h8, by omega⟩
          · intro h8
            refine Classical.byContradiction fun hh => ?_
            exact hc ⟨h8, by cases inm <;> simp_all <;> omega⟩
        exact ⟨.sequence, by simp [c1, c2, c3, c4]⟩
  · exact ⟨.lenForm, by simp_all⟩


/-- For a valid header the code's refusals do not fire: the rest is waiting or accepting. -/
theorem decode_valid (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hv : Valid mp peer inm (B 0) (B 1) len) :
    decode mp peer inm B n =
      if 128 ≤ B 1 ∧ n < head + 4 then .idle
      else if n < Whole (B 1) len head then .idle
      else accept B (B 0) (B 1) len head inm := by
  have hv' := (valid_iff mp peer inm B n len head hp hd).1 hv
  obtain ⟨c1, c2, c3, c4⟩ := hv'
  rw [decode_some mp peer inm B n len head h2 hp hd]
  have e1 : ¬ (canon (B 1 % 128) len = false) := by simp [c1]
  have e2 : ¬ (mp < len) := by omega
  have e3 : ¬ ((8 ≤ B 0 % 16) ∧ (B 0 < 128 ∨ 125 < len)) := by
    rintro ⟨h8, h⟩; have := c3 h8; omega
  have e4 : ¬ ((B 0 % 16 < 8) ∧ (decide (B 0 % 16 = 0) != inm) = true) := by
    rintro ⟨h8, h⟩
    have := c4 h8
    cases inm <;> simp_all
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4]

theorem decode_valid_idle (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hv : Valid mp peer inm (B 0) (B 1) len)
    (hn : n < Whole (B 1) len head) : decode mp peer inm B n = .idle := by
  rw [decode_valid mp peer inm B n len head h2 hp hd hv]
  by_cases hm : 128 ≤ B 1 ∧ n < head + 4
  · rw [if_pos hm]
  · rw [if_neg hm, if_pos hn]

theorem decode_valid_frame (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hv : Valid mp peer inm (B 0) (B 1) len)
    (hn : Whole (B 1) len head ≤ n) : decode mp peer inm B n = accept B (B 0) (B 1) len head inm := by
  rw [decode_valid mp peer inm B n len head h2 hp hd hv]
  have : ¬ (128 ≤ B 1 ∧ n < head + 4) := by
    unfold Whole at hn
    by_cases hm : 128 ≤ B 1
    · simp only [hm, ite_true] at hn; omega
    · exact fun h => hm h.1
  rw [if_neg this, if_neg (Nat.not_lt.2 hn)]

theorem accept_ne_idle (B b0 b1 len head inm) : accept B b0 b1 len head inm ≠ .idle := by simp [accept]
theorem accept_ne_err (B b0 b1 len head inm e) : accept B b0 b1 len head inm ≠ .err e := by simp [accept]

/-- The header decides refusal: invalid headers are refused, whatever is held behind them; the checks that need the
length wait only for the length bytes. -/
theorem decode_err_iff (mp peer inm B n) (h2 : 2 ≤ n) :
    (∃ e, decode mp peer inm B n = .err e) ↔
      (¬ Pre peer (B 0) (B 1) ∨
        ∃ len head, declared B n (B 1 % 128) = some (len, head) ∧ ¬ Valid mp peer inm (B 0) (B 1) len) := by
  constructor
  · rintro ⟨e, he⟩
    by_cases hp : Pre peer (B 0) (B 1)
    · right
      cases hd : declared B n (B 1 % 128) with
      | none => rw [decode_none mp peer inm B n h2 hp hd] at he; cases he
      | some p =>
        obtain ⟨len, head⟩ := p
        refine ⟨len, head, rfl, fun hv => ?_⟩
        by_cases hw : n < Whole (B 1) len head
        · rw [decode_valid_idle mp peer inm B n len head h2 hp hd hv hw] at he; cases he
        · rw [decode_valid_frame mp peer inm B n len head h2 hp hd hv (by omega)] at he
          exact accept_ne_err _ _ _ _ _ _ _ he
    · exact Or.inl hp
  · rintro (h | ⟨len, head, hd, hv⟩)
    · exact decode_pre mp peer inm B n h2 h
    · by_cases hp : Pre peer (B 0) (B 1)
      · exact decode_invalid mp peer inm B n len head h2 hp hd hv
      · exact decode_pre mp peer inm B n h2 hp

/-- Exactly the valid frames whose bytes are all held are accepted, and then the decoder takes exactly their bytes. -/
theorem decode_frame_iff (mp peer inm B n) (h2 : 2 ≤ n) (len head : Nat)
    (hd : declared B n (B 1 % 128) = some (len, head)) :
    (∃ k pl st used inm', decode mp peer inm B n = .frame k pl st used inm') ↔
      (Valid mp peer inm (B 0) (B 1) len ∧ Whole (B 1) len head ≤ n) := by
  constructor
  · rintro ⟨k, pl, st, used, inm', h⟩
    by_cases hp : Pre peer (B 0) (B 1)
    · by_cases hv : Valid mp peer inm (B 0) (B 1) len
      · refine ⟨hv, ?_⟩
        by_cases hw : n < Whole (B 1) len head
        · rw [decode_valid_idle mp peer inm B n len head h2 hp hd hv hw] at h; cases h
        · omega
      · obtain ⟨e, he⟩ := decode_invalid mp peer inm B n len head h2 hp hd hv
        rw [he] at h; cases h
    · obtain ⟨e, he⟩ := decode_pre mp peer inm B n h2 hp
      rw [he] at h; cases h
  · rintro ⟨hv, hw⟩
    have hp : Pre peer (B 0) (B 1) := ⟨hv.1, hv.2.1, hv.2.2.1⟩
    rw [decode_valid_frame mp peer inm B n len head h2 hp hd hv hw]
    exact ⟨_, _, _, _, _, rfl⟩

/-- Waiting: a header not whole yet, or a valid frame with bytes missing; nothing else waits. -/
theorem decode_idle_iff (mp peer inm B n) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1)) :
    decode mp peer inm B n = .idle ↔
      (declared B n (B 1 % 128) = none ∨
        ∃ len head, declared B n (B 1 % 128) = some (len, head) ∧ Valid mp peer inm (B 0) (B 1) len ∧
          n < Whole (B 1) len head) := by
  constructor
  · intro h
    cases hd : declared B n (B 1 % 128) with
    | none => exact Or.inl rfl
    | some p =>
      obtain ⟨len, head⟩ := p
      right
      refine ⟨len, head, rfl, ?_, ?_⟩
      · refine Classical.byContradiction fun hv => ?_
        obtain ⟨e, he⟩ := decode_invalid mp peer inm B n len head h2 hp hd hv
        rw [he] at h; cases h
      · refine Classical.byContradiction fun hw => ?_
        have hv : Valid mp peer inm (B 0) (B 1) len := by
          refine Classical.byContradiction fun hv => ?_
          obtain ⟨e, he⟩ := decode_invalid mp peer inm B n len head h2 hp hd hv
          rw [he] at h; cases h
        rw [decode_valid_frame mp peer inm B n len head h2 hp hd hv (by omega)] at h
        exact accept_ne_idle _ _ _ _ _ _ h
  · rintro (hd | ⟨len, head, hd, hv, hw⟩)
    · exact decode_none mp peer inm B n h2 hp hd
    · exact decode_valid_idle mp peer inm B n len head h2 hp hd hv hw


/-! ## The rules one by one -/

theorem frame_shape (mp peer inm B n k pl st used inm')
    (h : decode mp peer inm B n = .frame k pl st used inm') :
    2 ≤ n ∧ Pre peer (B 0) (B 1) ∧ ∃ len head, declared B n (B 1 % 128) = some (len, head) ∧
      Valid mp peer inm (B 0) (B 1) len ∧ Whole (B 1) len head ≤ n ∧
      decode mp peer inm B n = accept B (B 0) (B 1) len head inm := by
  have h2 : 2 ≤ n := by
    refine Classical.byContradiction fun hn => ?_
    rw [decode_short mp peer inm B n (by omega)] at h; cases h
  have hp : Pre peer (B 0) (B 1) := by
    refine Classical.byContradiction fun hp => ?_
    obtain ⟨e, he⟩ := decode_pre mp peer inm B n h2 hp
    rw [he] at h; cases h
  cases hd : declared B n (B 1 % 128) with
  | none => rw [decode_none mp peer inm B n h2 hp hd] at h; cases h
  | some p =>
    obtain ⟨len, head⟩ := p
    have := (decode_frame_iff mp peer inm B n h2 len head hd).1 ⟨_, _, _, _, _, h⟩
    exact ⟨h2, hp, len, head, rfl, this.1, this.2, decode_valid_frame mp peer inm B n len head h2 hp hd this.1 this.2⟩

/-- A reserved bit is refused. -/
theorem reserved_refused (mp peer inm B n) (h2 : 2 ≤ n) (h : B 0 / 16 % 8 ≠ 0) :
    decode mp peer inm B n = .err .reserved := by
  have : ¬ n < 2 := by omega
  simp [decode, this, h]

/-- An opcode other than continuation, binary, close, ping and pong (text included) is refused. -/
theorem opcode_refused (mp peer inm B n) (h2 : 2 ≤ n) (hr : B 0 / 16 % 8 = 0)
    (h : B 0 % 16 ≠ 0 ∧ B 0 % 16 ≠ 2 ∧ B 0 % 16 ≠ 8 ∧ B 0 % 16 ≠ 9 ∧ B 0 % 16 ≠ 10) :
    decode mp peer inm B n = .err .opcode := by
  have : ¬ n < 2 := by omega
  have ho : isOp (B 0 % 16) = false := by simp [isOp, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
  simp [decode, this, hr, ho]

/-- The wrong mask bit for the sender's role is refused: a client's frame unmasked, a server's frame masked. -/
theorem wrong_mask (mp peer inm B n) (h2 : 2 ≤ n) (hr : B 0 / 16 % 8 = 0)
    (ho : B 0 % 16 = 0 ∨ B 0 % 16 = 2 ∨ B 0 % 16 = 8 ∨ B 0 % 16 = 9 ∨ B 0 % 16 = 10)
    (hm : ¬ (128 ≤ B 1 ↔ peer = .client)) : decode mp peer inm B n = .err .mask := by
  have : ¬ n < 2 := by omega
  have ho' : isOp (B 0 % 16) = true := (isOp_iff _).2 ho
  simp [decode, this, hr, ho', hm]

/-- A longer length form than the shortest is refused: the 16-bit form below 126, the 64-bit form below 65536. -/
theorem longer_form_refused (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head))
    (h : (B 1 % 128 = 126 ∧ len < 126) ∨ (B 1 % 128 = 127 ∧ len < 65536)) :
    decode mp peer inm B n = .err .lenForm := by
  rw [decode_some mp peer inm B n len head h2 hp hd]
  have : canon (B 1 % 128) len = false := by
    unfold canon
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1]; omega
    · simp [h1]; omega
  simp [this]

/-- A payload length over `MAX_PAYLOAD` is refused as soon as the length bytes are held, whatever else is. -/
theorem oversize_refused (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hc : canon (B 1 % 128) len = true) (h : mp < len) :
    decode mp peer inm B n = .err .tooLong := by
  rw [decode_some mp peer inm B n len head h2 hp hd]
  simp [hc, h]

/-- A control frame that is fragmented or longer than 125 bytes is refused. -/
theorem control_refused (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hc : canon (B 1 % 128) len = true) (hb : len ≤ mp)
    (h8 : 8 ≤ B 0 % 16) (h : B 0 < 128 ∨ 125 < len) : decode mp peer inm B n = .err .control := by
  rw [decode_some mp peer inm B n len head h2 hp hd]
  have : ¬ mp < len := by omega
  simp [hc, this, h8, h]

/-- A continuation with no message in progress, and a data frame inside one, are refused. -/
theorem sequence_refused (mp peer inm B n len head) (h2 : 2 ≤ n) (hp : Pre peer (B 0) (B 1))
    (hd : declared B n (B 1 % 128) = some (len, head)) (hc : canon (B 1 % 128) len = true) (hb : len ≤ mp)
    (hctl : B 0 % 16 < 8) (h : (B 0 % 16 = 0 ∧ inm = false) ∨ (B 0 % 16 ≠ 0 ∧ inm = true)) :
    decode mp peer inm B n = .err .sequence := by
  rw [decode_some mp peer inm B n len head h2 hp hd]
  have h1 : ¬ mp < len := by omega
  have h2' : ¬ (8 ≤ B 0 % 16) := by omega
  have h3 : (decide (B 0 % 16 = 0) != inm) = true := by
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b]
  simp [hc, h1, h2', hctl, h3]

/-- After an accepted frame: a data frame leaves a message open exactly when FIN was clear, a control frame leaves the
state as it was; the bytes taken are the whole frame; the payload is that of the frame, unmasked for a client. -/
theorem accepted_state (mp peer inm B n k pl st used inm')
    (h : decode mp peer inm B n = .frame k pl st used inm') :
    inm' = (if 8 ≤ B 0 % 16 then inm else !decide (128 ≤ B 0)) ∧ used ≤ n ∧
      (128 ≤ B 1 ↔ peer = .client) ∧ (B 0 % 16 < 8 → (B 0 % 16 = 0 ↔ inm = true)) := by
  obtain ⟨h2, hp, len, head, hd, hv, hw, he⟩ := frame_shape mp peer inm B n k pl st used inm' h
  rw [he] at h
  simp only [accept, DRes.frame.injEq] at h
  obtain ⟨-, -, -, hu, hi⟩ := h
  refine ⟨?_, ?_, hv.2.2.1, hv.2.2.2.2.2.2⟩
  · rw [← hi]; simp [isCtl]
  · rw [← hu]; unfold Whole at hw; simpa [accept] using hw

#audit_axioms Pinc.ConnectWs.decode_err_iff
#audit_axioms Pinc.ConnectWs.decode_frame_iff
#audit_axioms Pinc.ConnectWs.decode_idle_iff
#audit_axioms Pinc.ConnectWs.reserved_refused
#audit_axioms Pinc.ConnectWs.opcode_refused
#audit_axioms Pinc.ConnectWs.wrong_mask
#audit_axioms Pinc.ConnectWs.longer_form_refused
#audit_axioms Pinc.ConnectWs.oversize_refused
#audit_axioms Pinc.ConnectWs.control_refused
#audit_axioms Pinc.ConnectWs.sequence_refused
#audit_axioms Pinc.ConnectWs.accepted_state

end Pinc.ConnectWs
