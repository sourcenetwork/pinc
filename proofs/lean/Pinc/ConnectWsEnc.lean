import Pinc.ConnectWsThm

/-!
# The WebSocket framing of the carrier: the encoder, and what the decoder reads back

- `encode` writes the length in the shortest form (the 7-bit field up to 125, else 126 and two bytes) and masks the
  payload only when given a key (`encHdr`, `encBody`); it refuses, in this order, a payload over `MAX_PAYLOAD`
  (`encode_toolong`), a control payload over 125 bytes (`encode_control`) and an output buffer that is too small
  (`encode_noroom`); `encode_ok` says what a success is;
- a decoder of the role that matches the mask (`peer` is the sender's role: the key is present exactly for a client)
  reads from the bytes `encode` wrote exactly the payload back (unmasked), takes exactly the frame, and no message
  is open afterwards, however many bytes lie behind the frame and however many of them are held (`encode_decode`);
  at every proper prefix of the frame it waits (`encode_prefix`); together with `wrong_mask` a decoder of the other
  role refuses the frame;
- so the frames the encoder writes are the `Good` ones that `ConnectWsSplit.lean` (`good_of_encode`) reads whole.
The opcode is one of binary, close, ping and pong: the encoder will also write a continuation with FIN set, which its
own decoder refuses unless a message is open (it is the host's to write fragments with the FIN bit cleared).
-/

namespace Pinc.ConnectWs

theorem bf_left (a b : List Nat) (j : Nat) (h : j < a.length) : bf (a ++ b) j = bf a j := by
  simp [bf, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem bf_right (a b : List Nat) (j : Nat) : bf (a ++ b) (a.length + j) = bf b j := by
  simp [bf, List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.add_sub_cancel_left]

theorem slice_bf_right (a b : List Nat) (m : Nat) : slice (bf (a ++ b)) a.length m = slice (bf b) 0 m := by
  unfold slice
  apply List.map_congr_left
  intro j _
  rw [Nat.zero_add]; exact bf_right a b j

theorem slice_bf_zero (l : List Nat) (m : Nat) (h : m ≤ l.length) : slice (bf l) 0 m = l.take m := by
  apply List.ext_getElem
  · simp [slice]
    omega
  · intro i h1 h2
    have hi : i < m := by simpa [slice] using h1
    simp [slice, bf, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

theorem mask_mask (k d : List Nat) : mask k (mask k d) = d := by
  have : ∀ (j : Nat) (d : List Nat), maskAt k j (maskAt k j d) = d := by
    intro j d
    induction d generalizing j with
    | nil => rfl
    | cons b t ih => simp [maskAt, ih, Nat.xor_assoc]
  exact this 0 d

theorem mask_length (k d : List Nat) : (mask k d).length = d.length := by
  have : ∀ (j : Nat) (d : List Nat), (maskAt k j d).length = d.length := by
    intro j d
    induction d generalizing j with
    | nil => rfl
    | cons b t ih => simp [maskAt, ih]
  exact this 0 d


theorem encode_ok (mp op pl mk cap e) (h : encode mp op pl mk cap = .ok e) :
    pl.length ≤ mp ∧ ¬ (8 ≤ op ∧ 125 < pl.length) ∧ (encHdr op pl.length mk).length + pl.length ≤ cap ∧
      e = encHdr op pl.length mk ++ encBody mk pl := by
  unfold encode at h
  by_cases c1 : pl.length > mp
  · simp [c1] at h
  · by_cases c2 : isCtl op = true ∧ pl.length > 125
    · simp [c1, c2] at h
    · by_cases c3 : (encHdr op pl.length mk).length + pl.length > cap
      · simp [c1, c2, c3] at h
      · simp only [c1, c2, c3, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
        have := Except.ok.inj h
        refine ⟨by omega, ?_, by omega, this.symm⟩
        rintro ⟨h8, h125⟩
        exact c2 ⟨(isCtl_iff op).2 h8, h125⟩

theorem encode_toolong (mp op pl mk cap) (h : mp < pl.length) : encode mp op pl mk cap = .error .tooLong := by
  simp [encode, h]

theorem encode_control (mp op pl mk cap) (h : pl.length ≤ mp) (h8 : 8 ≤ op) (h125 : 125 < pl.length) :
    encode mp op pl mk cap = .error .control := by
  have : ¬ mp < pl.length := by omega
  simp [encode, this, isCtl, h8, h125]

theorem encode_noroom (mp op pl mk cap) (h : pl.length ≤ mp) (hc : ¬ (8 ≤ op ∧ 125 < pl.length))
    (h' : cap < (encHdr op pl.length mk).length + pl.length) : encode mp op pl mk cap = .error .noRoom := by
  have : ¬ mp < pl.length := by omega
  have hc' : ¬ (isCtl op = true ∧ 125 < pl.length) := fun ⟨a, b⟩ => hc ⟨(isCtl_iff op).1 a, b⟩
  simp [encode, this, hc', h']

theorem encHdr_length (op n mk) (hk : ∀ k, mk = some k → k.length = 4) :
    (encHdr op n mk).length = (if n ≤ 125 then 2 else 4) + (if mk.isSome then 4 else 0) := by
  unfold encHdr
  cases mk with
  | none => by_cases h : n ≤ 125 <;> simp [h, be16]
  | some k => have := hk k rfl; by_cases h : n ≤ 125 <;> simp [h, be16, this]


/-- The first bytes of an encoded frame, seen through any bytes behind it. -/
theorem enc_bytes (op n : Nat) (mk : Option (List Nat)) (body rest : List Nat) (hn : n < 65536)
    (B : Nat → Nat) (hB : B = bf (encHdr op n mk ++ body ++ rest)) :
    B 0 = 128 + op ∧ B 1 = (if mk.isSome then 128 else 0) + (if n ≤ 125 then n else 126) ∧
      (125 < n → B 2 = n / 256 ∧ B 3 = n % 256) := by
  subst hB
  unfold encHdr
  by_cases h : n ≤ 125
  · cases mk <;> (simp [bf, h]; intro h'; omega)
  · have h' : 125 < n := by omega
    cases mk <;> simp [bf, h, be16]


/-- The header before the key. -/
def preHdr (op n : Nat) (mk : Option (List Nat)) : List Nat :=
  (128 + op) :: (if n ≤ 125 then [(if mk.isSome then 128 else 0) + n] else ((if mk.isSome then 128 else 0) + 126) :: be16 n)

theorem encHdr_eq (op n mk) : encHdr op n mk = preHdr op n mk ++ mk.getD [] := by
  unfold encHdr preHdr; simp

theorem preHdr_length (op n mk) : (preHdr op n mk).length = if n ≤ 125 then 2 else 4 := by
  unfold preHdr; by_cases h : n ≤ 125 <;> simp [h, be16]

/-- What a decoder of the right role reads from the encoder's bytes, however many bytes lie behind them: the payload
back, the frame's bytes taken, no message open. -/
theorem encode_decode (mp : Nat) (peer : Peer) (op : Nat) (pl : List Nat) (mk : Option (List Nat)) (cap : Nat)
    (e rest : List Nat) (N : Nat) (hNe : e.length ≤ N) (hmp : mp < 65536) (hop : op = 2 ∨ op = 8 ∨ op = 9 ∨ op = 10)
    (hk : ∀ k, mk = some k → k.length = 4) (hm : mk.isSome = true ↔ peer = .client)
    (h : encode mp op pl mk cap = .ok e) :
    decode mp peer false (bf (e ++ rest)) N =
      .frame (kindOf op) (if op == 8 then [] else pl)
        (if op == 8 && 2 ≤ pl.length then some (pl.getD 0 0 * 256 + pl.getD 1 0) else none) e.length false := by
  obtain ⟨hn, hc, hcap, he⟩ := encode_ok mp op pl mk cap e h
  subst he
  have hlen := encHdr_length op pl.length mk hk
  have hbl : (encBody mk pl).length = pl.length := by
    unfold encBody; cases mk <;> simp [mask_length]
  have hpre := preHdr_length op pl.length mk
  have hH := encHdr_eq op pl.length mk
  simp only [List.length_append, hbl] at hNe
  obtain ⟨b0, b1, b23⟩ := enc_bytes op pl.length mk (encBody mk pl) rest (by omega) _ rfl
  -- the payload and the key as the accept step reads them
  have hs1 : slice (bf (encHdr op pl.length mk ++ encBody mk pl ++ rest)) (encHdr op pl.length mk).length pl.length
      = encBody mk pl := by
    rw [List.append_assoc, slice_bf_right, slice_bf_zero _ _ (by simp [hbl])]
    exact List.take_left' hbl
  have hs2 : ∀ k, mk = some k → slice (bf (encHdr op pl.length mk ++ encBody mk pl ++ rest)) (preHdr op pl.length mk).length 4 = k := by
    intro k hmk
    have hk4 := hk k hmk
    rw [hH, hmk]
    simp only [Option.getD_some, List.append_assoc]
    rw [slice_bf_right, slice_bf_zero _ _ (by simp [hk4])]
    exact List.take_left' hk4
  generalize hB : bf (encHdr op pl.length mk ++ encBody mk pl ++ rest) = B at *
  have hl7 : B 1 % 128 = if pl.length ≤ 125 then pl.length else 126 := by
    rw [b1]; by_cases h1 : pl.length ≤ 125 <;> by_cases h2 : mk.isSome = true <;> simp [h1, h2] <;> omega
  have hmaskB : (128 ≤ B 1) ↔ mk.isSome = true := by
    rw [b1]; by_cases h1 : pl.length ≤ 125 <;> by_cases h2 : mk.isSome = true <;> simp [h1, h2] <;> omega
  have hhead : ∃ head, declared B N (B 1 % 128)
      = some (pl.length, head) ∧ head = (if pl.length ≤ 125 then 2 else 4) := by
    by_cases h125 : pl.length ≤ 125
    · refine ⟨2, ?_, by simp [h125]⟩
      rw [hl7, if_pos h125]
      unfold declared
      have : pl.length ≠ 126 := by omega
      have : pl.length ≠ 127 := by omega
      simp [*]
    · refine ⟨4, ?_, by simp [h125]⟩
      rw [hl7, if_neg h125]
      have h4 : 4 ≤ (encHdr op pl.length mk).length := by rw [hlen]; simp [h125]
      have := b23 (by omega)
      unfold declared
      simp only [ite_true]
      have : ¬ (N < 4) := by omega
      simp [this, b23 (by omega)]
      omega
  obtain ⟨head, hdecl, hhd⟩ := hhead
  have hopm : (128 + op) % 16 = op := by rcases hop with rfl | rfl | rfl | rfl <;> rfl
  have hPre : Pre peer (B 0) (B 1) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [b0]; rcases hop with rfl | rfl | rfl | rfl <;> omega
    · rw [b0, hopm]; omega
    · rw [hmaskB]; exact hm
  have hV : Valid mp peer false (B 0) (B 1) pl.length := by
    refine ⟨hPre.1, hPre.2.1, hPre.2.2, ?_, hn, ?_, ?_⟩
    · rw [hl7]; by_cases h125 : pl.length ≤ 125
      · left; simp [h125]
      · right; left; simp [h125]; omega
    · rw [b0, hopm]; intro h8; exact ⟨by omega, by omega⟩
    · rw [b0, hopm]; intro h8
      rcases hop with rfl | rfl | rfl | rfl <;> simp_all
  have hstart : head + (if decide (128 ≤ B 1) = true then 4 else 0) = (encHdr op pl.length mk).length := by
    rw [hhd, hlen]
    by_cases h2 : mk.isSome = true
    · simp [hmaskB.2 h2, h2]
    · have : ¬ 128 ≤ B 1 := fun h => h2 (hmaskB.1 h)
      simp [this, h2]
  have hW : Whole (B 1) pl.length head = (encHdr op pl.length mk ++ encBody mk pl).length := by
    unfold Whole
    have : head + (if 128 ≤ B 1 then 4 else 0) = head + (if decide (128 ≤ B 1) = true then 4 else 0) := by simp
    rw [List.length_append, hbl, this, hstart]
  have hN : 2 ≤ N := by
    have h2H : 2 ≤ (encHdr op pl.length mk).length := by
      rw [hlen]; by_cases h : pl.length ≤ 125 <;> simp [h] <;> omega
    omega
  have hmaskeq : (if decide (128 ≤ B 1) = true then mask (slice B head 4) (slice B (head + (if decide (128 ≤ B 1) = true then 4 else 0)) pl.length)
      else slice B (head + (if decide (128 ≤ B 1) = true then 4 else 0)) pl.length) = pl := by
    rw [hstart, hs1]
    cases hmk : mk with
    | none =>
      have : ¬ 128 ≤ B 1 := fun h => by have := hmaskB.1 h; simp [hmk] at this
      simp [this, encBody]
    | some k =>
      have hm1 : 128 ≤ B 1 := hmaskB.2 (by simp [hmk])
      have hd1 : decide (128 ≤ B 1) = true := by simpa using hm1
      simp only [hd1, ite_true]
      rw [show head = (preHdr op pl.length mk).length from by rw [hhd, hpre]]
      rw [hs2 k hmk]
      simp [encBody, hmk, mask_mask]
  rw [decode_valid_frame mp peer false B _ pl.length head hN hPre hdecl hV (by rw [hW]; simp only [List.length_append, hbl]; omega)]
  unfold accept
  dsimp only
  rw [hmaskeq, hstart, b0, hopm]
  have hfin : (if isCtl op = true then false else !decide (128 ≤ 128 + op)) = false := by
    by_cases h : isCtl op = true <;> simp [h]
  rw [hfin]
  simp [List.length_append, hbl]

/-- No proper prefix of the encoder's bytes is accepted or refused: the decoder waits, whatever follows them. -/
theorem encode_prefix (mp : Nat) (peer : Peer) (op : Nat) (pl : List Nat) (mk : Option (List Nat)) (cap : Nat)
    (e rest : List Nat) (hmp : mp < 65536) (hop : op = 2 ∨ op = 8 ∨ op = 9 ∨ op = 10)
    (hk : ∀ k, mk = some k → k.length = 4) (hm : mk.isSome = true ↔ peer = .client)
    (h : encode mp op pl mk cap = .ok e) (j : Nat) (hj : j < e.length) :
    decode mp peer false (bf (e ++ rest)) j = .idle := by
  obtain ⟨hn, hc, hcap, he⟩ := encode_ok mp op pl mk cap e h
  subst he
  have hlen := encHdr_length op pl.length mk hk
  have hbl : (encBody mk pl).length = pl.length := by
    unfold encBody; cases mk <;> simp [mask_length]
  obtain ⟨b0, b1, b23⟩ := enc_bytes op pl.length mk (encBody mk pl) rest (by omega) _ rfl
  generalize hB : bf (encHdr op pl.length mk ++ encBody mk pl ++ rest) = B at *
  have hl7 : B 1 % 128 = if pl.length ≤ 125 then pl.length else 126 := by
    rw [b1]; by_cases h1 : pl.length ≤ 125 <;> by_cases h2 : mk.isSome = true <;> simp [h1, h2] <;> omega
  have hmaskB : (128 ≤ B 1) ↔ mk.isSome = true := by
    rw [b1]; by_cases h1 : pl.length ≤ 125 <;> by_cases h2 : mk.isSome = true <;> simp [h1, h2] <;> omega
  have hopm : (128 + op) % 16 = op := by rcases hop with rfl | rfl | rfl | rfl <;> rfl
  have hPre : Pre peer (B 0) (B 1) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [b0]; rcases hop with rfl | rfl | rfl | rfl <;> omega
    · rw [b0, hopm]; omega
    · rw [hmaskB]; exact hm
  have hV : Valid mp peer false (B 0) (B 1) pl.length := by
    refine ⟨hPre.1, hPre.2.1, hPre.2.2, ?_, hn, ?_, ?_⟩
    · rw [hl7]; by_cases h125 : pl.length ≤ 125
      · left; simp [h125]
      · right; left; simp [h125]; omega
    · rw [b0, hopm]; intro h8; exact ⟨by omega, by omega⟩
    · rw [b0, hopm]; intro h8
      rcases hop with rfl | rfl | rfl | rfl <;> simp_all
  by_cases h2 : j < 2
  · exact decode_short _ _ _ _ _ h2
  · have h2' : 2 ≤ j := by omega
    have hjl : j < (encHdr op pl.length mk).length + pl.length := by simpa [hbl] using hj
    by_cases h125 : pl.length ≤ 125
    · have hd : declared B j (B 1 % 128) = some (pl.length, 2) := by
        rw [hl7, if_pos h125]
        unfold declared
        have : pl.length ≠ 126 := by omega
        have : pl.length ≠ 127 := by omega
        simp [*]
      apply decode_valid_idle mp peer false B j pl.length 2 h2' hPre hd hV
      unfold Whole
      rw [hlen] at hjl
      by_cases h3 : 128 ≤ B 1
      · have := hmaskB.1 h3; simp [h3, h125, this] at hjl ⊢; omega
      · have : ¬ mk.isSome = true := fun x => h3 (hmaskB.2 x)
        simp [h3, h125, this] at hjl ⊢; omega
    · by_cases h4 : j < 4
      · apply decode_none mp peer false B j h2' hPre
        rw [hl7, if_neg h125]
        unfold declared
        simp [h4]
      · have hd : declared B j (B 1 % 128) = some (pl.length, 4) := by
          rw [hl7, if_neg h125]
          unfold declared
          simp only [ite_true]
          have := b23 (by omega)
          simp [h4, this.1, this.2]
          omega
        apply decode_valid_idle mp peer false B j pl.length 4 h2' hPre hd hV
        unfold Whole
        rw [hlen] at hjl
        by_cases h3 : 128 ≤ B 1
        · have := hmaskB.1 h3; simp [h3, h125, this] at hjl ⊢; omega
        · have : ¬ mk.isSome = true := fun x => h3 (hmaskB.2 x)
          simp [h3, h125, this] at hjl ⊢; omega


#audit_axioms Pinc.ConnectWs.encode_decode
#audit_axioms Pinc.ConnectWs.encode_prefix

end Pinc.ConnectWs
