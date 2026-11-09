import Vinc.ConnectBatch

/-!
# The carrier frame codec: the theorems

* `decode_bytes`: for every valid frame `f`, `decode f.bytes = f` (round trip), batches included.
* `decode_inv`: an accepted input is a valid frame and `f.bytes` is that input (canonical form); so a frame has exactly
  one accepted encoding (`decode_injective`) and `encode` of an accepted frame returns the input (`decode_encode`).
* `encode_ok`, `encode_short`: with room the encoder writes `f.bytes`, without it reports the shortfall of the first
  write that does not fit (`WireError::BufferTooSmall`).
* The exact refusal for each class of malformed input (`decode_empty`, `decode_unknown`, `decode_trailing`,
  `decode_packet_empty`, `decode_alias`, `decode_status`, `decode_batch_count`).
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

theorem le_sum_of_mem : ∀ {ls : List Nat} {l : Nat}, l ∈ ls → l ≤ ls.sum := by
  intro ls
  induction ls with
  | nil => intro l h; simp at h
  | cons a ls ih =>
    intro l h
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem batch_roundtrip (f : Fr) (h13 : f.ty = 13) (hv : BatchOk f.fs) : decode f.bytes = .ok f := by
  obtain ⟨ty, fs⟩ := f
  simp only at h13
  subst h13
  obtain ⟨ps, rfl, h2, h64, hok, hsum⟩ := hv
  have hparts : (ps.map F.raw).map F.enc = ps := by simp [F.enc, List.map_map, Function.comp_def]
  have hpos : ∀ l ∈ ps.map List.length, 0 < l ∧ l < Varint.limit := by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨p, hp, rfl⟩ := hl
    have hne := (hok p hp).1
    have hle := le_sum_of_mem (List.mem_map_of_mem (f := List.length) hp)
    refine ⟨List.length_pos_iff.2 hne, ?_⟩
    have : (16384 : Nat) < Varint.limit := by decide
    unfold batchBytes at hsum
    omega
  have hflat : ps.flatten.length = (ps.map List.length).sum := by simp [List.length_flatten]
  have hl := rdLens_enc (ps.map List.length) hpos 0 ps.flatten (by
    have : (16384 : Nat) < 2 ^ 64 := by decide
    unfold batchBytes at hsum
    omega)
  rw [List.length_map] at hl
  have hm := rdMembers_enc ps (fun p hp => ⟨(hok p hp).1, (hok p hp).2.1, (hok p hp).2.2.2⟩)
  have hbytes : (Fr.mk 13 (ps.map F.raw)).bytes = 13 :: ps.length :: (lensEnc (ps.map List.length) ++ ps.flatten) := by
    simp [Fr.bytes, Fr.parts, hparts, lensBytes_eq]
  rw [hbytes]
  have hc1 : ¬ (ps.length < 2 ∨ batchFrames < ps.length) := by
    unfold batchFrames at *; omega
  have hc2 : ¬ ((ps.map List.length).sum ≠ ps.flatten.length ∨ batchBytes < (ps.map List.length).sum) := by
    rw [hflat]; unfold batchBytes at *; omega
  simp [decode, decodeWith, rdU8, decodeBatch, liftW, hl, hc1, hsum, hm, bind, Except.bind, pure, Except.pure]

theorem batch_inv {r f} (h : decodeBatch decodeNB r = .ok f) (hb : Byte r) :
    f.valid ∧ f.bytes = 13 :: r := by
  unfold decodeBatch at h
  simp only [bind_ok] at h
  obtain ⟨⟨c, rest⟩, h1, h⟩ := h
  have e1 := rdU8_ok (liftW_eq_ok h1)
  subst e1
  have hbr : Byte rest := (byte_cons hb).2
  by_cases hc : c < 2 ∨ batchFrames < c
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [hc, ite_false, bind_ok] at h
    obtain ⟨⟨ls, body⟩, h2, h⟩ := h
    obtain ⟨hlen, hpos, hrest, hsum0⟩ := rdLens_inv c 0 h2 hbr (by decide)
    have hbb : Byte body := (byte_append (hrest ▸ hbr)).2
    by_cases hs : ls.sum ≠ body.length ∨ batchBytes < ls.sum
    · simp [hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp only [hs, ite_false, bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨ps, h3, rfl⟩ := h
      have hs1 : ls.sum = body.length := Classical.byContradiction fun hne => hs (Or.inl hne)
      have hs2 : ls.sum ≤ batchBytes := Classical.byContradiction fun hne => hs (Or.inr (by omega))
      obtain ⟨m1, m2, m3⟩ := rdMembers_inv decodeNB ls body h3 (fun l hl => (hpos l hl).1) (by omega)
      have hbt : body.take ls.sum = body := by rw [hs1]; simp
      rw [hbt] at m2
      have hpl : ps.length = c := by rw [← hlen, ← m1]; simp
      have hparts : (ps.map F.raw).map F.enc = ps := by simp [F.enc, List.map_map, Function.comp_def]
      refine ⟨?_, ?_⟩
      · refine ⟨ps, rfl, by omega, by unfold batchFrames at *; omega, ?_, ?_⟩
        · intro p hp
          obtain ⟨a, b, d⟩ := m3 p hp
          refine ⟨a, b, ?_, d⟩
          intro x hx
          have : x ∈ ps.flatten := List.mem_flatten.2 ⟨p, hp, hx⟩
          rw [m2] at this
          exact hbb x this
        · rw [m1]; exact hs2
      · have hbs : (Fr.mk 13 (ps.map F.raw)).bytes = 13 :: ps.length :: (lensEnc (ps.map List.length) ++ ps.flatten) := by
          simp [Fr.bytes, Fr.parts, hparts, lensBytes_eq]
        rw [hbs, hpl, m1, m2, hrest]

/-- Every decoder of a frame that is not a batch is canonical: the generic step, given the batch case. -/
theorem decodeWith_inv (bat : List Nat → Except CErr Fr)
    (hbat : ∀ {r f}, bat r = .ok f → Byte r → f.valid ∧ f.bytes = 13 :: r)
    {b f} (h : decodeWith bat b = .ok f) (hb : Byte b) : f.valid ∧ f.bytes = b := by
  rcases b with _ | ⟨ty, r⟩
  · simp [decodeWith, rdU8, liftW, bind, Except.bind] at h
  · have hbr : Byte r := (byte_cons hb).2
    by_cases h13 : ty = 13
    · subst h13
      simp [decodeWith, rdU8, liftW, bind, Except.bind] at h
      exact hbat h hbr
    · by_cases h15 : ty = 15
      · subst h15
        simp [decodeWith, rdU8, liftW, bind, Except.bind] at h
        obtain ⟨t, hd, e⟩ := decodeDnsr_inv h hbr
        have hv : f.valid := by
          unfold Fr.valid; simp [t, hd]
        refine ⟨hv, ?_⟩
        simp [Fr.bytes, t, e]
      · cases hl : layoutOf ty with
        | none => simp [decodeWith, rdU8, liftW, h13, h15, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        | some l =>
          rw [decodeWith_layout bat ty l r h13 h15 hl] at h
          simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
          obtain ⟨⟨fs, r1⟩, h1, u, hu, rfl⟩ := h
          have hf := finish_ok hu
          simp only at hf
          subst hf
          obtain ⟨hlo, e, _⟩ := rdLayout_inv CErr.wire l h1 hbr
          refine ⟨?_, ?_⟩
          · unfold Fr.valid
            simp [h13, h15, hl, hlo]
          · rw [List.append_nil] at e
            simp [Fr.bytes, h13]
            exact e.symm

/-- A valid frame that is not a batch reads back (`decode_bytes` for every frame follows). -/
theorem decode_bytes (f : Fr) (hv : f.valid) : decode f.bytes = .ok f := by
  by_cases h13 : f.ty = 13
  · exact batch_roundtrip f h13 (by unfold Fr.valid at hv; simpa [h13] using hv)
  · by_cases h15 : f.ty = 15
    · exact dnsr_roundtrip _ f h15 (by unfold Fr.valid at hv; simpa [h13, h15] using hv)
    · cases hl : layoutOf f.ty with
      | none => unfold Fr.valid at hv; simp [h13, h15, hl] at hv
      | some l =>
        exact layout_roundtrip _ f l h13 h15 hl (by unfold Fr.valid at hv; simpa [h13, h15, hl] using hv)

/-- Canonical form: an accepted input is a valid frame, and `f.bytes` is that input. -/
theorem decode_inv {b f} (h : decode b = .ok f) (hb : Byte b) : f.valid ∧ f.bytes = b :=
  decodeWith_inv (decodeBatch decodeNB) (fun h hb => batch_inv h hb) h hb

/-- A frame has exactly one accepted encoding. -/
theorem decode_injective {a b f} (ha : decode a = .ok f) (hb : decode b = .ok f) (hba : Byte a) (hbb : Byte b) :
    a = b := by
  rw [← (decode_inv ha hba).2, ← (decode_inv hb hbb).2]

theorem dnsr_ops (e : CErr) (fs : List F) (h : DnsrOk fs) :
    (∀ o ∈ opsLayout ⟨[K.node, K.u8], some (maxRecordLen, e)⟩ fs, o.good) ∧
      opsBytes (opsLayout ⟨[K.node, K.u8], some (maxRecordLen, e)⟩ fs) = encFs fs := by
  rcases fs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, fs⟩⟩⟩⟩
  · simp [DnsrOk] at h
  · simp [DnsrOk] at h
  · rcases a with p | s | q <;> try (simp [DnsrOk] at h; done)
    rcases b with p2 | s2 | q2 <;> try (simp [DnsrOk] at h; done)
    rcases s2 with _ | _ | _ | s3 <;> try (simp [DnsrOk] at h; done)
    all_goals simp [opsLayout, opsPre, opsK, opsTail, opsBytes, Op.good, Op.bytes, encFs, F.enc]
  · rcases a with p | s | q <;> try (simp [DnsrOk] at h; done)
    rcases b with p2 | s2 | q2 <;> try (simp [DnsrOk] at h; done)
    rcases s2 with _ | _ | _ | s3 <;> try (simp [DnsrOk] at h; done)
    rcases c with p3 | s3 | q3 <;> try (simp [DnsrOk] at h; done)
    obtain ⟨hn, hb, h1, h2, h3⟩ := h
    simp [opsLayout, opsPre, opsK, opsTail, opsBytes, Op.good, Op.bytes, encFs, F.enc, h1, h2]
  · rcases a with p | s | q <;> simp [DnsrOk] at h

theorem ops_good (f : Fr) (hv : f.valid) : (∀ o ∈ f.ops, o.good) ∧ opsBytes f.ops = f.bytes := by
  by_cases h13 : f.ty = 13
  · have hv' : BatchOk f.fs := by unfold Fr.valid at hv; simpa [h13] using hv
    obtain ⟨ps, hfs, _⟩ := hv'
    have hparts : f.parts = ps := by simp [Fr.parts, hfs, F.enc, List.map_map, Function.comp_def]
    refine ⟨?_, ?_⟩
    · intro o ho
      simp [Fr.ops, h13] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp [Op.good]
    · simp [Fr.ops, Fr.bytes, h13, opsBytes, Op.bytes]
  · by_cases h15 : f.ty = 15
    · have hv' : DnsrOk f.fs := by unfold Fr.valid at hv; simpa [h13, h15] using hv
      obtain ⟨g, b⟩ := dnsr_ops .bodySize f.fs hv'
      refine ⟨?_, ?_⟩
      · intro o ho
        simp only [Fr.ops, h13, h15, ite_true, ite_false, List.mem_cons] at ho
        rcases ho with rfl | ho
        · simp [Op.good]
        · exact g o ho
      · unfold opsBytes at b
        simp [Fr.ops, Fr.bytes, h13, h15, opsBytes, Op.bytes, recordTail, b]
    · cases hl : layoutOf f.ty with
      | none => unfold Fr.valid at hv; simp [h13, h15, hl] at hv
      | some l =>
        have hv' : LayoutOk l f.fs := by unfold Fr.valid at hv; simpa [h13, h15, hl] using hv
        obtain ⟨g, b⟩ := opsLayout_good hv'
        refine ⟨?_, ?_⟩
        · intro o ho
          simp only [Fr.ops, h13, h15, hl, ite_false, List.mem_cons] at ho
          rcases ho with rfl | ho
          · simp [Op.good]
          · exact g o ho
        · unfold opsBytes at b
          simp [Fr.ops, Fr.bytes, h13, h15, hl, opsBytes, Op.bytes, b]

/-- With room the encoder writes the bytes of the frame. -/
theorem encode_ok (cap : Nat) (f : Fr) (hv : f.valid) (hc : f.bytes.length ≤ cap) : f.encode cap = .ok f.bytes := by
  obtain ⟨g, b⟩ := ops_good f hv
  have := run_ok CErr.wire cap f.ops g [] (by rw [b]; simpa using hc)
  simpa [Fr.encode, b] using this

/-- Without room it reports the shortfall of the first write that does not fit. -/
theorem encode_short (cap : Nat) (f : Fr) (hv : f.valid) (hc : cap < f.bytes.length) :
    ∃ k, 0 < k ∧ f.encode cap = .error (CErr.wire (.small k)) := by
  obtain ⟨g, b⟩ := ops_good f hv
  exact run_short CErr.wire cap f.ops g [] (by simp) (by rw [b]; simpa using hc)

/-- Re-encoding what was decoded gives the input. -/
theorem decode_encode {b f} (h : decode b = .ok f) (hb : Byte b) : f.encode b.length = .ok b := by
  obtain ⟨hv, e⟩ := decode_inv h hb
  have := encode_ok b.length f hv (Nat.le_of_eq (congrArg List.length e))
  rw [e] at this
  exact this

end Vinc.ConnCodec
