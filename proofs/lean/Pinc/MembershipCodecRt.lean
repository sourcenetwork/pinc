import Pinc.MembershipCodecNum

/-!
# Hub stream codec: round trip

For every valid frame `f`, `parse (encBody f) = f`, `read (enc f ++ rest) = (f, 4 + len)`, and the encoded size is
`bodyLen f`. The proof goes through one lemma per frame type (`hello_rt`, `delta_rt`, `snap_rt`, `down_rt`,
`dispatch_other`) and the entry lemmas they share.
-/

namespace Pinc.MemCodec

/-! ## Entries -/

theorem encEntry_length (e : Entry) (h : e.valid) : (encEntry e).length = entryLen := by
  obtain ⟨hm, _, hi, hv, hl, _⟩ := h
  simp [encEntry, beBytes_length, hm, hl, entryLen]

theorem entry_rt (e : Entry) (h : e.valid) (r : List Nat) : rdEntry (encEntry e ++ r) = .ok (e, r) := by
  obtain ⟨hm, _, hi, hv, hl, _⟩ := h
  have e1 := rdBytes_app e.member (beBytes 8 e.rc.inc ++ beBytes 2 e.rc.ver ++ e.rc.th ++ [e.alive.toNat] ++ r)
  rw [hm] at e1
  have e2 := rdBE_beBytes_lt 8 e.rc.inc (beBytes 2 e.rc.ver ++ e.rc.th ++ [e.alive.toNat] ++ r)
    (by rw [p256_8]; exact hi)
  have e3 := rdBE_beBytes_lt 2 e.rc.ver (e.rc.th ++ [e.alive.toNat] ++ r) (by rw [p256_2]; exact hv)
  have e4 := rdBytes_app e.rc.th ([e.alive.toNat] ++ r)
  rw [hl] at e4
  simp only [encEntry, List.append_assoc, List.singleton_append] at e1 e2 e3 e4 ⊢
  rcases e with ⟨m, ⟨i, v, t⟩, a⟩
  cases a <;> simp_all [rdEntry, rdU8, Alive.toNat, aliveOf, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

theorem entryOf_rt (e : Entry) (h : e.valid) : entryOf (encEntry e) = .ok e := by
  have := entry_rt e h []
  rw [List.append_nil] at this
  simp [entryOf, this, bind, Except.bind, pure, Except.pure]

theorem rdBytes_self (r : List Nat) : rdBytes r.length r = .ok (r, []) := by
  simpa using rdBytes_app r []

/-! ## Chunks and snapshots -/

theorem chunks_cons (c rest : List Nat) (hc : c.length = entryLen) :
    chunks (c ++ rest) = c :: chunks rest := by
  rw [chunks]
  have h : entryLen ≤ (c ++ rest).length := by simp [hc]
  rw [dif_pos h]
  simp [hc]

theorem chunks_flat (es : List Entry) (h : ∀ e ∈ es, e.valid) :
    chunks (es.flatMap encEntry) = es.map encEntry := by
  induction es with
  | nil => rw [chunks]; simp [entryLen]
  | cons e es ih =>
    simp only [List.flatMap_cons, List.map_cons]
    rw [chunks_cons _ _ (encEntry_length e (h e (by simp)))]
    rw [ih (fun x hx => h x (by simp [hx]))]

theorem flat_length (es : List Entry) (h : ∀ e ∈ es, e.valid) :
    (es.flatMap encEntry).length = es.length * entryLen := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [encEntry_length e (h e (by simp)), ih (fun x hx => h x (by simp [hx]))]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem snapEntry_rt (e : Entry) (hv : e.valid) (ha : e.alive = Alive.alive) : snapEntry (encEntry e) = .ok e := by
  simp [snapEntry, entryOf_rt e hv, ha, bind, Except.bind, pure, Except.pure]

theorem mapM_entries (es : List Entry) (h : ∀ e ∈ es, e.valid ∧ e.alive = Alive.alive) :
    (es.map encEntry).mapM snapEntry = .ok es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hv, ha⟩ := h e (by simp)
    have ih := ih (fun x hx => h x (by simp [hx]))
    simp [List.mapM_cons, snapEntry_rt e hv ha, ih, bind, Except.bind, pure, Except.pure]

theorem snapNew_rt (es : List Entry) (h : ∀ e ∈ es, e.valid ∧ e.alive = Alive.alive) (hn : es.length ≤ snapMax) :
    snapNew (es.flatMap encEntry) = .ok es := by
  have hv : ∀ e ∈ es, e.valid := fun e he => (h e he).1
  unfold snapNew
  rw [flat_length es hv, chunks_flat es hv]
  have h1 : ¬ (es.length * entryLen % entryLen ≠ 0 ∨ snapMax < (es.map encEntry).length) := by
    simp [entryLen]; simpa [snapMax] using hn
  split
  · exact absurd ‹_› h1
  · exact mapM_entries es h

/-! ## The frames -/

theorem flags_rt (s h : Bool) : (b2n s + 2 * b2n h) / 4 = 0 ∧ ((b2n s + 2 * b2n h) % 2 == 1) = s ∧
    ((b2n s + 2 * b2n h) / 2 % 2 == 1) = h := by
  cases s <;> cases h <;> simp [b2n]

theorem hello_rt (r : Rec) (s h : Bool) (hv : r.valid) :
    pHello (beBytes 8 r.inc ++ beBytes 2 r.ver ++ r.th ++ [b2n s + 2 * b2n h]) = .ok (.hello r s h) := by
  obtain ⟨hi, hv2, hl, hb⟩ := hv
  have e1 := rdBE_beBytes_lt 8 r.inc (beBytes 2 r.ver ++ r.th ++ [b2n s + 2 * b2n h]) (by rw [p256_8]; exact hi)
  have e2 := rdBE_beBytes_lt 2 r.ver (r.th ++ [b2n s + 2 * b2n h]) (by rw [p256_2]; exact hv2)
  have e3 := rdBytes_app r.th [b2n s + 2 * b2n h]
  rw [hl] at e3
  simp only [List.append_assoc] at e1 e2 ⊢
  simp [pHello, e1, e2, e3, rdU8, only, bind, Except.bind, pure, Except.pure]
  cases s <;> cases h <;> simp [b2n]

theorem delta_rt (e : Entry) (hv : e.valid) : pDelta (encEntry e) = .ok (.delta e) := by
  have := rdBytes_app (encEntry e) []
  rw [encEntry_length e hv, List.append_nil] at this
  simp [pDelta, this, entryOf_rt e hv, only, bind, Except.bind, pure, Except.pure]

theorem snap_rt (p m : Bool) (es : List Entry) (hv : (Frame.snap p m es).valid) :
    pSnap ((b2n p + 2 * b2n m) :: es.flatMap encEntry) = .ok (.snap p m es) := by
  obtain ⟨hn, h⟩ := hv
  obtain ⟨f1, f2, f3⟩ := flags_rt p m
  have hs := snapNew_rt es h hn
  have hr := rdBytes_self (es.flatMap encEntry)
  generalize es.flatMap encEntry = X at hs hr
  simp [pSnap, rdU8, f1, hr, hs, bind, Except.bind, pure, Except.pure]
  cases p <;> cases m <;> simp [b2n]

theorem probes_rt (ps : List Probe) (r : List Nat) (h : ∀ p ∈ ps, p.age < 2 ^ 32) :
    rdProbes ps.length (ps.flatMap encProbe ++ r) = .ok (ps, r) := by
  induction ps with
  | nil => simp [rdProbes]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ih := ih (fun x hx => h x (by simp [hx])) 
    have e1 := rdBE_beBytes_lt 4 p.age ([p.path.toNat] ++ (ps.flatMap encProbe ++ r)) (by rw [p256_4]; exact hp)
    simp only [List.flatMap_cons, encProbe, List.length_cons, rdProbes, List.append_assoc, List.singleton_append] at *
    rcases p with ⟨a, pa⟩
    cases pa <;> simp_all [rdU8, Path.toNat, pathOf, bind, Except.bind, pure, Except.pure]

theorem down_rt (mb : List Nat) (inc : Nat) (pf : Proof) (hv : (Frame.down mb inc pf).valid) :
    pDown (mb ++ beBytes 8 inc ++ beBytes 4 pf.sil ++ [pf.probes.length] ++ pf.probes.flatMap encProbe) =
      .ok (.down mb inc pf) := by
  obtain ⟨hm, _, hi, hs, h1, h4, hp⟩ := hv
  have e1 := rdBytes_app mb (beBytes 8 inc ++ beBytes 4 pf.sil ++ [pf.probes.length] ++ pf.probes.flatMap encProbe)
  rw [hm] at e1
  have e2 := rdBE_beBytes_lt 8 inc (beBytes 4 pf.sil ++ [pf.probes.length] ++ pf.probes.flatMap encProbe)
    (by rw [p256_8]; exact hi)
  have e3 := rdBE_beBytes_lt 4 pf.sil ([pf.probes.length] ++ pf.probes.flatMap encProbe) (by rw [p256_4]; exact hs)
  have e5 := probes_rt pf.probes [] hp
  rw [List.append_nil] at e5
  have hc : ¬ (pf.probes.length = 0 ∨ maxProbes < pf.probes.length) := by omega
  have hc1 : pf.probes.length ≠ 0 := by omega
  have hc2 : ¬ maxProbes < pf.probes.length := by omega
  have hn : Proof.new pf.sil pf.probes = some pf := by simp [Proof.new, hc1, hc2]
  have hne : pf.probes ≠ [] := fun h => hc1 (by rw [h]; rfl)
  simp only [List.append_assoc, List.singleton_append] at e1 e2 e3 ⊢
  simp [pDown, hne, hc2, e1, e2, e3, e5, rdU8, hc, only, hn, bind, Except.bind, pure, Except.pure]

theorem dispatch_other (ty : Nat) (topic r : List Nat) (h : isMem ty = false) :
    dispatch ty topic r = .ok (.other ty topic r) := by
  have : ty ≠ 1 ∧ ty ≠ 2 ∧ ty ≠ 3 ∧ ty ≠ 4 ∧ ty ≠ 12 ∧ ty ≠ 13 := by
    simp [isMem] at h; omega
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := this
  unfold dispatch
  split <;> simp_all [rdBytes_self, bind, Except.bind, pure, Except.pure]

theorem parse_hdr (ty : Nat) (topic r : List Nat) :
    parse (ty :: topic.length :: (topic ++ r)) =
      if topic ≠ [] ∧ isMem ty = true then .error .topicOnMembership else dispatch ty topic r := by
  have := rdBytes_app topic r
  unfold parse
  simp only [rdU8, this, bind, Except.bind]
  split
  · simp [throw, throwThe, MonadExceptOf.throw]
  · simp [*]

theorem parse_hdr0 (ty : Nat) (r : List Nat) : parse (ty :: 0 :: r) = dispatch ty [] r := by
  have := parse_hdr ty [] r
  simpa using this

/-- **Round trip.** Every valid frame parses back from its body. -/
theorem parse_encBody (f : Frame) (hv : f.valid) : parse (encBody f) = .ok f := by
  cases f with
  | hello rc s h =>
    simp only [encBody, List.cons_append, List.nil_append, List.append_assoc]
    rw [parse_hdr0]
    exact hello_rt rc s h hv
  | ack => simp [encBody, parse_hdr0, dispatch, only, bind, Except.bind, pure, Except.pure]
  | probe => simp [encBody, parse_hdr0, dispatch, only, bind, Except.bind, pure, Except.pure]
  | delta e =>
    simp only [encBody, List.cons_append, List.nil_append]
    rw [parse_hdr0]
    exact delta_rt e hv
  | snap p m es =>
    simp only [encBody, List.cons_append, List.nil_append]
    rw [parse_hdr0]
    exact snap_rt p m es hv
  | down mb inc pf =>
    simp only [encBody, List.cons_append, List.nil_append, List.append_assoc]
    rw [parse_hdr0]
    have := down_rt mb inc pf hv
    simp only [List.append_assoc, List.singleton_append] at this
    exact this
  | other t tp rest =>
    obtain ⟨ht, hm, htl, htb, hrb⟩ := hv
    have := parse_hdr t tp rest
    simp only [encBody, List.cons_append, List.nil_append, List.append_assoc]
    rw [this, hm, dispatch_other t tp rest hm]
    simp

/-! ## Sizes and the stream read -/

theorem probes_length (ps : List Probe) : (ps.flatMap encProbe).length = 5 * ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, encProbe, beBytes_length]
    simp; omega

/-- `body_len` is the length of the bytes `encode` writes after the prefix. -/
theorem encBody_length (f : Frame) (hv : f.valid) : (encBody f).length = bodyLen f := by
  cases f with
  | hello rc s h =>
    obtain ⟨_, _, hl, _⟩ := hv
    simp [encBody, bodyLen, beBytes_length, hl, helloLen]
  | ack => rfl
  | probe => rfl
  | delta e => simp [encBody, bodyLen, encEntry_length e hv, entryLen]
  | snap p m es =>
    obtain ⟨_, h⟩ := hv
    simp [encBody, bodyLen, flat_length es (fun e he => (h e he).1)]
    omega
  | down mb inc pf =>
    obtain ⟨hm, _⟩ := hv
    simp only [encBody, bodyLen, List.length_append, List.length_cons, List.length_nil, beBytes_length,
      probes_length, hm]
    omega
  | other t tp rest => simp [encBody, bodyLen]; omega

/-- `Frame::read_with` for any limit at or above the default returns the frame and the bytes it used, whatever
follows it in the buffer. -/
theorem readWith_enc (mb : Nat) (hm : maxBody ≤ mb) (f : Frame) (hv : f.valid) (hs : bodyLen f ≤ maxBody)
    (rest : List Nat) :
    readWith mb (enc f ++ rest) = .ok (some (f, 4 + bodyLen f)) := by
  have hl := encBody_length f hv
  have h4 : beN (beBytes 4 (encBody f).length) = bodyLen f := by
    rw [beN_beBytes, Nat.mod_eq_of_lt, hl]
    rw [p256_4]; simp [maxBody] at hs; omega
  have hb : (beBytes 4 (encBody f).length).length = 4 := beBytes_length _ _
  have e3 : (encBody f ++ rest).take (bodyLen f) = encBody f := by
    rw [← hl]; exact List.take_left' rfl
  have e4 : ¬ ((beBytes 4 (encBody f).length ++ (encBody f ++ rest)).length < 4) := by
    simp [beBytes_length]
  have e5 : ¬ ((encBody f ++ rest).length < bodyLen f) := by
    simp [← hl]
  have e6 : ¬ (mb < bodyLen f) := Nat.not_lt.mpr (Nat.le_trans hs hm)
  unfold readWith enc
  simp only [List.append_assoc]
  rw [List.take_left' hb, List.drop_left' hb, h4]
  simp only [e4, e5, e6, e3, parse_encBody f hv, if_false, bind, Except.bind, pure, Except.pure]

/-- `Frame::read` returns the frame and the bytes it used, whatever follows it in the buffer. -/
theorem read_enc (f : Frame) (hv : f.valid) (hs : bodyLen f ≤ maxBody) (rest : List Nat) :
    read (enc f ++ rest) = .ok (some (f, 4 + bodyLen f)) := readWith_enc maxBody (Nat.le_refl _) f hv hs rest

end Pinc.MemCodec
