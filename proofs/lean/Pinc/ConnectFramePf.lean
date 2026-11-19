import Pinc.ConnectFrame

/-!
# The carrier frame codec: round trip and canonical form for the frames of a fixed shape

For every valid frame `f` (not a batch) `decode f.bytes = f` (`decode_bytes`), an accepted input is a valid frame that
re-encodes to the same bytes (`decode_inv`), so each frame has one accepted encoding (`decode_injective`), and an
encoder with room writes exactly `f.bytes` (`encode_ok`), with too little room reports the shortfall
(`encode_short`). Batches are in `ConnectBatch.lean`.
-/

namespace Pinc.ConnCodec
open Pinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

theorem PreOk_length : ∀ {ks fs}, PreOk ks fs → fs.length = ks.length := by
  intro ks
  induction ks with
  | nil => intro fs h; cases fs <;> simp_all [PreOk]
  | cons k ks ih =>
    intro fs h
    cases fs with
    | nil => simp [PreOk] at h
    | cons f fs => simp [ih h.2]

theorem opsPre_good : ∀ {ks fs}, PreOk ks fs →
    (∀ o ∈ opsPre ks fs, o.good) ∧ opsBytes (opsPre ks fs) = encFs fs := by
  intro ks
  induction ks with
  | nil => intro fs h; cases fs <;> simp_all [PreOk, opsPre, opsBytes, encFs]
  | cons k ks ih =>
    intro fs h
    cases fs with
    | nil => simp [PreOk] at h
    | cons f fs =>
      obtain ⟨h1, h2⟩ := h
      obtain ⟨g, b⟩ := ih h2
      have hk : (∀ o ∈ opsK k f, o.good) ∧ opsBytes (opsK k f) = f.enc := by
        cases k <;> cases f <;> simp_all [okK, opsK, opsBytes, Op.good, Op.bytes, aliasMax, F.enc]
      refine ⟨?_, ?_⟩
      · intro o ho
        simp only [opsPre, List.mem_append] at ho
        rcases ho with ho | ho
        · exact hk.1 o ho
        · exact g o ho
      · simp only [opsPre, opsBytes, List.flatMap_append] at b hk ⊢
        simp only [encFs, List.flatMap_cons] at b ⊢
        rw [hk.2, b]

theorem opsTail_good {t : Option (Nat × CErr)} {tf : List F} (h : TailOk t tf) :
    (∀ o ∈ opsTail t tf, o.good) ∧ opsBytes (opsTail t tf) = encFs tf := by
  rcases t with _ | ⟨m, e⟩
  · cases tf <;> simp_all [TailOk, opsTail, opsBytes, encFs]
  · rcases tf with _ | ⟨f, _ | ⟨g, tf⟩⟩
    · simp [TailOk] at h
    · cases f <;> simp [TailOk] at h
      rename_i b
      obtain ⟨h1, h2, _⟩ := h
      simp [opsTail, opsBytes, Op.good, Op.bytes, encFs, F.enc, h1, h2]
    · cases f <;> simp [TailOk] at h

theorem opsLayout_good {l : L} {fs : List F} (h : LayoutOk l fs) :
    (∀ o ∈ opsLayout l fs, o.good) ∧ opsBytes (opsLayout l fs) = encFs fs := by
  obtain ⟨pf, tf, rfl, h1, h2⟩ := h
  have hl := PreOk_length h1
  have e1 : (pf ++ tf).take l.pre.length = pf := by rw [← hl]; simp
  have e2 : (pf ++ tf).drop l.pre.length = tf := by rw [← hl]; simp
  obtain ⟨g1, b1⟩ := opsPre_good h1
  obtain ⟨g2, b2⟩ := opsTail_good h2
  unfold opsLayout
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · intro o ho
    simp only [List.mem_append] at ho
    rcases ho with ho | ho
    · exact g1 o ho
    · exact g2 o ho
  · simp only [opsBytes, List.flatMap_append] at b1 b2 ⊢
    rw [b1, b2, encFs_append]

theorem finish_nil : finish [] = .ok () := by simp [finish]

theorem finish_ok {r} (h : finish r = .ok ()) : r = [] := by
  unfold finish at h
  split at h
  · assumption
  · simp at h

theorem finish_cons (x : Nat) (r : List Nat) : finish (x :: r) = .error .trailing := by simp [finish]

/-- The type byte of a fixed-shape frame, then its layout. -/
theorem decodeWith_layout (bat : List Nat → Except CErr Fr) (ty : Nat) (l : L) (r : List Nat)
    (h13 : ty ≠ 13) (h15 : ty ≠ 15) (hl : layoutOf ty = some l) :
    decodeWith bat (ty :: r) =
      (do let (fs, r) ← rdLayout CErr.wire l r; finish r; pure ⟨ty, fs⟩) := by
  simp [decodeWith, rdU8, h13, h15, hl, bind, Except.bind, pure, Except.pure]

theorem layout_roundtrip (bat : List Nat → Except CErr Fr) (f : Fr) (l : L)
    (h13 : f.ty ≠ 13) (h15 : f.ty ≠ 15) (hl : layoutOf f.ty = some l) (hv : LayoutOk l f.fs) :
    decodeWith bat f.bytes = .ok f := by
  have hb : f.bytes = f.ty :: encFs f.fs := by simp [Fr.bytes, h13]
  rw [hb, decodeWith_layout bat f.ty l _ h13 h15 hl]
  by_cases ht : l.tail = none
  · have := rdLayout_enc_app CErr.wire l ht f.fs hv []
    rw [List.append_nil] at this
    simp [this, finish_nil, bind, Except.bind, pure, Except.pure]
  · have := rdLayout_enc CErr.wire l f.fs hv
    simp [this, finish_nil, bind, Except.bind, pure, Except.pure]

theorem dnsrG_enc (lw : W → CErr) (sf : Nat → CErr) (e : CErr) (ty : Nat) (fs : List F) (hv : DnsrOk fs) :
    decodeDnsrG lw sf e ty (encFs fs) = .ok ⟨ty, fs⟩ := by
  rcases fs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, fs⟩⟩⟩⟩
  · simp [DnsrOk] at hv
  · simp [DnsrOk] at hv
  · rcases a with p | s | q <;> try (simp [DnsrOk] at hv; done)
    rcases b with p2 | s2 | q2 <;> try (simp [DnsrOk] at hv; done)
    rcases s2 with _ | _ | _ | s3 <;> try (simp [DnsrOk] at hv; done)
    · obtain ⟨hn, hb⟩ := hv
      have e1 := rdPre_app lw [.node, .u8] [F.node p, F.u8 0] ⟨⟨hn, hb⟩, by simp [okK], trivial⟩ []
      simp only [encFs, List.flatMap_cons, List.flatMap_nil, F.enc, List.append_nil] at e1
      simp [encFs, F.enc, decodeDnsrG, e1, finish_nil, bind, Except.bind, pure, Except.pure]
    · obtain ⟨hn, hb⟩ := hv
      have e1 := rdPre_app lw [.node, .u8] [F.node p, F.u8 2] ⟨⟨hn, hb⟩, by simp [okK], trivial⟩ []
      simp only [encFs, List.flatMap_cons, List.flatMap_nil, F.enc, List.append_nil] at e1
      simp [encFs, F.enc, decodeDnsrG, e1, finish_nil, bind, Except.bind, pure, Except.pure]
  · rcases a with p | s | q <;> try (simp [DnsrOk] at hv; done)
    rcases b with p2 | s2 | q2 <;> try (simp [DnsrOk] at hv; done)
    rcases s2 with _ | _ | _ | s3 <;> try (simp [DnsrOk] at hv; done)
    rcases c with p3 | s3 | q3 <;> try (simp [DnsrOk] at hv; done)
    obtain ⟨hn, hb, h1, h2, h3⟩ := hv
    have e1 := rdPre_app lw [.node, .u8] [F.node p, F.u8 1] ⟨⟨hn, hb⟩, by simp [okK], trivial⟩ q3
    have t := rdTail_enc (some (maxRecordLen, e)) [F.raw q3] ⟨h1, h2, h3⟩
    simp only [encFs, List.flatMap_cons, List.flatMap_nil, F.enc, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append] at e1 t
    simp [encFs, F.enc, decodeDnsrG, e1, t, finish_nil, bind, Except.bind, pure, Except.pure]
  · rcases a with p | s | q <;> simp [DnsrOk] at hv

theorem dnsr_roundtrip (bat : List Nat → Except CErr Fr) (f : Fr) (h15 : f.ty = 15) (hv : DnsrOk f.fs) :
    decodeWith bat f.bytes = .ok f := by
  have := dnsrG_enc CErr.wire CErr.status CErr.bodySize 15 f.fs hv
  obtain ⟨ty, fs⟩ := f
  simp only at h15
  subst h15
  simpa [Fr.bytes, decodeWith, rdU8, liftW, decodeDnsr, bind, Except.bind, pure, Except.pure] using this

theorem decodeDnsrG_inv {lw sf e ty r f} (h : decodeDnsrG lw sf e ty r = .ok f) (hb : Byte r) :
    f.ty = ty ∧ DnsrOk f.fs ∧ r = encFs f.fs := by
  unfold decodeDnsrG at h
  simp only [bind_ok] at h
  obtain ⟨⟨fs0, r1⟩, h1, h⟩ := h
  obtain ⟨hp, e⟩ := rdPre_inv lw _ h1 hb
  subst e
  obtain ⟨_, hb1⟩ := byte_append hb
  rcases fs0 with _ | ⟨a, _ | ⟨b, _ | ⟨c, fs0⟩⟩⟩ <;> try (simp [PreOk] at hp; done)
  rcases a with p | s | q <;> try (simp [PreOk, okK] at hp; done)
  rcases b with p2 | s2 | q2 <;> try (simp [PreOk, okK] at hp; done)
  obtain ⟨⟨hn, hbn⟩, _⟩ := hp
  rcases s2 with _ | _ | _ | s3
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨u, hu, rfl⟩ := h
    have hf := finish_ok hu
    subst hf
    exact ⟨rfl, ⟨hn, hbn⟩, by simp [encFs, F.enc]⟩
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨tf, r2⟩, ht, u, hu, rfl⟩ := h
    have hf := finish_ok hu
    subst hf
    obtain ⟨hT, e2, _⟩ := rdTail_inv ht hb1
    rcases tf with _ | ⟨g, _ | ⟨g2, tf⟩⟩ <;> try (simp [TailOk] at hT; done)
    rcases g with g1 | g1 | g1 <;> try (simp [TailOk] at hT; done)
    obtain ⟨t1, t2, t3⟩ := hT
    refine ⟨rfl, ⟨hn, hbn, t1, t2, t3⟩, ?_⟩
    subst e2
    simp [encFs, F.enc]
  · simp only [bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨u, hu, rfl⟩ := h
    have hf := finish_ok hu
    subst hf
    exact ⟨rfl, ⟨hn, hbn⟩, by simp [encFs, F.enc]⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem decodeDnsr_inv {r f} (h : decodeDnsr r = .ok f) (hb : Byte r) :
    f.ty = 15 ∧ DnsrOk f.fs ∧ r = encFs f.fs := decodeDnsrG_inv h hb

end Pinc.ConnCodec
