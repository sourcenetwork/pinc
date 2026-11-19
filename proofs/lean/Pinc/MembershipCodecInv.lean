import Pinc.MembershipCodecRt

/-!
# Hub stream codec: canonical form

An accepted body is a valid frame and re-encodes to the same bytes (`parse_canonical`), so each frame has exactly
one accepted body (`parse_injective`), and the stream read uses exactly the bytes of the frame it returns
(`read_canonical`).
-/

namespace Pinc.MemCodec

theorem throw_ne {α : Type} (e : Err) (k : Unit → Except Err α) (y : α) :
    ((do throw e; k ()) : Except Err α) ≠ .ok y := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem only_ok {e r} (h : only e r = .ok ()) : r = [] := by
  unfold only at h
  split at h
  · assumption
  · simp at h

theorem byte_append {a b : List Nat} (h : Byte (a ++ b)) : Byte a ∧ Byte b :=
  ⟨fun x hx => h x (by simp [hx]), fun x hx => h x (by simp [hx])⟩

theorem byte_cons {x : Nat} {b : List Nat} (h : Byte (x :: b)) : x < 256 ∧ Byte b :=
  ⟨h x (by simp), fun y hy => h y (by simp [hy])⟩

/-! ## Entries -/

theorem aliveOf_ok {a al} (h : aliveOf a = .ok al) : a = al.toNat := by
  unfold aliveOf at h
  split at h <;> simp at h <;> subst h <;> rfl

theorem pathOf_ok {a p} (h : pathOf a = .ok p) : a = p.toNat := by
  unfold pathOf at h
  split at h <;> simp at h <;> subst h <;> rfl

theorem rdEntry_inv {r e r'} (h : rdEntry r = .ok (e, r')) (hb : Byte r) :
    e.valid ∧ r = encEntry e ++ r' := by
  unfold rdEntry at h
  simp only [bind_ok] at h
  obtain ⟨⟨m, r1⟩, h1, ⟨inc, r2⟩, h2, ⟨ver, r3⟩, h3, ⟨th, r4⟩, h4, ⟨a, r5⟩, h5, al, h6, h⟩ := h
  obtain ⟨e1, l1⟩ := rdBytes_ok h1
  obtain ⟨a2, e2, l2, v2⟩ := rdBE_ok h2
  obtain ⟨a3, e3, l3, v3⟩ := rdBE_ok h3
  obtain ⟨e4, l4⟩ := rdBytes_ok h4
  have e5 := rdU8_ok h5
  have ha := aliveOf_ok h6
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst e5 ha
  subst e4 e3 e2 e1
  obtain ⟨hm, hb⟩ := byte_append hb
  obtain ⟨h2b, hb⟩ := byte_append hb
  obtain ⟨h3b, hb⟩ := byte_append hb
  obtain ⟨hthb, hb⟩ := byte_append hb
  subst v2 v3
  refine ⟨⟨l1, hm, ?_, ?_, l4, hthb⟩, ?_⟩
  · have := beN_lt a2 h2b; rw [l2, p256_8] at this; exact this
  · have := beN_lt a3 h3b; rw [l3, p256_2] at this; exact this
  · simp [encEntry, beBytes_beN _ _ l2 h2b, beBytes_beN _ _ l3 h3b, Alive.toNat]

theorem entryOf_inv {b e} (h : entryOf b = .ok e) (hl : b.length = entryLen) (hb : Byte b) :
    e.valid ∧ encEntry e = b := by
  unfold entryOf at h
  simp only [bind_ok] at h
  obtain ⟨⟨e', r'⟩, h1, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hv, hr⟩ := rdEntry_inv h1 hb
  refine ⟨hv, ?_⟩
  have := encEntry_length _ hv
  have hr' : r' = [] := by
    have h2 := congrArg List.length hr
    rw [List.length_append, encEntry_length _ hv, hl] at h2
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hr'
  simpa using hr.symm

theorem snapEntry_inv {c e} (h : snapEntry c = .ok e) (hl : c.length = entryLen) (hb : Byte c) :
    e.valid ∧ e.alive = Alive.alive ∧ encEntry e = c := by
  unfold snapEntry at h
  simp only [bind_ok] at h
  obtain ⟨e', h1, h⟩ := h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hv, hc⟩ := entryOf_inv h1 hl hb
    refine ⟨hv, ?_, hc⟩
    rename_i hne
    simpa using hne

/-! ## The frames -/

theorem flags_inv (fl : Nat) (h : fl / 4 = 0) : b2n (fl % 2 == 1) + 2 * b2n (fl / 2 % 2 == 1) = fl := by
  have : fl < 4 := by omega
  rcases (by omega : fl = 0 ∨ fl = 1 ∨ fl = 2 ∨ fl = 3) with rfl | rfl | rfl | rfl <;> simp [b2n]

theorem pHello_inv {r f} (h : pHello r = .ok f) (hb : Byte r) :
    f.valid ∧ encBody f = 1 :: 0 :: r := by
  unfold pHello at h
  simp only [bind_ok] at h
  obtain ⟨⟨inc, r1⟩, h1, ⟨ver, r2⟩, h2, ⟨th, r3⟩, h3, ⟨fl, r4⟩, h4, h⟩ := h
  obtain ⟨a1, e1, l1, v1⟩ := rdBE_ok h1
  obtain ⟨a2, e2, l2, v2⟩ := rdBE_ok h2
  obtain ⟨e3, l3⟩ := rdBytes_ok h3
  have e4 := rdU8_ok h4
  simp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i hf
    simp only [bind_ok] at h
    obtain ⟨u, hu, h⟩ := h
    have hr4 := only_ok hu
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    subst e4 e3 e2 e1 hr4 v1 v2
    obtain ⟨hb1, hb⟩ := byte_append hb
    obtain ⟨hb2, hb⟩ := byte_append hb
    obtain ⟨hb3, hb⟩ := byte_append hb
    have hf0 : fl / 4 = 0 := by omega
    refine ⟨⟨?_, ?_, l3, hb3⟩, ?_⟩
    · have := beN_lt a1 hb1; rw [l1, p256_8] at this; exact this
    · have := beN_lt a2 hb2; rw [l2, p256_2] at this; exact this
    · simp only [encBody]
      simp [beBytes_beN _ _ l1 hb1, beBytes_beN _ _ l2 hb2, flags_inv fl hf0]

theorem pDelta_inv {r f} (h : pDelta r = .ok f) (hb : Byte r) : f.valid ∧ encBody f = 3 :: 0 :: r := by
  unfold pDelta at h
  simp only [bind_ok] at h
  obtain ⟨⟨eb, r1⟩, h1, e, h2, u, hu, h⟩ := h
  obtain ⟨e1, l1⟩ := rdBytes_ok h1
  have hr := only_ok hu
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only at hr
  subst hr
  subst e1
  obtain ⟨hb1, _⟩ := byte_append hb
  obtain ⟨hv, hc⟩ := entryOf_inv h2 l1 hb1
  exact ⟨hv, by simp [encBody, hc]⟩

/-! ## Snapshots -/

theorem chunks_spec : ∀ (n : Nat) (bs : List Nat), bs.length = n → n % entryLen = 0 →
    (chunks bs).flatten = bs ∧ (∀ c ∈ chunks bs, c.length = entryLen) ∧ (chunks bs).length = n / entryLen := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro bs hn hm
    rw [chunks]
    by_cases h : entryLen ≤ bs.length
    · rw [dif_pos h]
      have hlt : (bs.drop entryLen).length < n := by simp [entryLen] at *; omega
      have hm2 : (bs.drop entryLen).length % entryLen = 0 := by simp [entryLen] at *; omega
      obtain ⟨i1, i2, i3⟩ := ih _ hlt _ rfl hm2
      refine ⟨?_, ?_, ?_⟩
      · simp [i1]
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · simp; omega
        · exact i2 c hc
      · simp [i3]; simp [entryLen] at *; omega
    · rw [dif_neg h]
      have : n = 0 := by simp [entryLen] at *; omega
      subst this
      have : bs = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      simp

theorem mapM_snapEntry_inv (cs : List (List Nat)) (es : List Entry) (h : cs.mapM snapEntry = .ok es)
    (hc : ∀ c ∈ cs, c.length = entryLen ∧ Byte c) :
    (∀ e ∈ es, e.valid ∧ e.alive = Alive.alive) ∧ es.flatMap encEntry = cs.flatten ∧ es.length = cs.length := by
  induction cs generalizing es with
  | nil =>
    simp [List.mapM_nil, pure, Except.pure] at h
    subst h; simp
  | cons c cs ih =>
    simp only [List.mapM_cons, bind_ok] at h
    obtain ⟨e, h1, es', h2, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hb⟩ := hc c (by simp)
    obtain ⟨hv, ha, he⟩ := snapEntry_inv h1 hl hb
    obtain ⟨i1, i2, i3⟩ := ih es' h2 (fun x hx => hc x (by simp [hx]))
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hv, ha⟩
      · exact i1 x hx
    · simp [he, i2]
    · simp [i3]

theorem snapNew_inv {bs es} (h : snapNew bs = .ok es) (hb : Byte bs) :
    es.length ≤ snapMax ∧ (∀ e ∈ es, e.valid ∧ e.alive = Alive.alive) ∧ es.flatMap encEntry = bs := by
  unfold snapNew at h
  split at h
  · simp at h
  · rename_i hn
    have hm : bs.length % entryLen = 0 := by
      exact Classical.byContradiction fun hne => hn (Or.inl hne)
    have hs : ¬ snapMax < (chunks bs).length := fun hh => hn (Or.inr hh)
    obtain ⟨i1, i2, i3⟩ := chunks_spec _ bs rfl hm
    have hcb : ∀ c ∈ chunks bs, c.length = entryLen ∧ Byte c := by
      intro c hc
      refine ⟨i2 c hc, fun x hx => hb x ?_⟩
      rw [← i1]
      exact List.mem_flatten.2 ⟨c, hc, hx⟩
    obtain ⟨j1, j2, j3⟩ := mapM_snapEntry_inv _ _ h hcb
    refine ⟨?_, j1, ?_⟩
    · rw [j3]; omega
    · rw [j2, i1]

theorem pSnap_inv {r f} (h : pSnap r = .ok f) (hb : Byte r) : f.valid ∧ encBody f = 4 :: 0 :: r := by
  unfold pSnap at h
  simp only [bind_ok] at h
  obtain ⟨⟨fl, r1⟩, h1, hh⟩ := h
  have e1 := rdU8_ok h1
  simp only at hh
  split at hh
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hh
  · rename_i hf
    simp only [bind_ok] at hh
    obtain ⟨⟨eb, r2⟩, h2, es, h3, hh⟩ := hh
    obtain ⟨e2, l2⟩ := rdBytes_ok h2
    simp only [pure, Except.pure, Except.ok.injEq] at hh
    subst hh
    simp only at h3
    subst e1
    obtain ⟨hf1, hb1⟩ := byte_cons hb
    have hr2 : r2 = [] := by
      have := congrArg List.length e2
      simp at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr2
    simp only [List.append_nil] at e2
    subst e2
    obtain ⟨i1, i2, i3⟩ := snapNew_inv h3 hb1
    have hf0 : fl / 4 = 0 := by omega
    refine ⟨⟨i1, i2⟩, ?_⟩
    simp [encBody, flags_inv fl hf0, i3]

/-! ## DOWN and the dispatch -/

theorem rdProbes_inv : ∀ (n : Nat) (r : List Nat) (ps : List Probe) (r' : List Nat),
    rdProbes n r = .ok (ps, r') → Byte r → ps.length = n ∧ r = ps.flatMap encProbe ++ r' ∧
      ∀ p ∈ ps, p.age < 2 ^ 32
  | 0, r, ps, r', h, _ => by
    simp [rdProbes, pure, Except.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | k + 1, r, ps, r', h, hb => by
    unfold rdProbes at h
    simp only [bind_ok] at h
    obtain ⟨⟨age, r1⟩, h1, ⟨pb, r2⟩, h2, pa, h3, ⟨ps', r3⟩, h4, h⟩ := h
    obtain ⟨a1, e1, l1, v1⟩ := rdBE_ok h1
    have e2 := rdU8_ok h2
    have e3 := pathOf_ok h3
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only at *
    subst e2 e1 v1
    obtain ⟨hb1, hb2⟩ := byte_append hb
    obtain ⟨_, hb3⟩ := byte_cons hb2
    obtain ⟨i1, i2, i3⟩ := rdProbes_inv k r2 ps' r3 h4 hb3
    refine ⟨by simp [i1], ?_, ?_⟩
    · simp only [List.flatMap_cons, encProbe, List.append_assoc, List.singleton_append]
      rw [i2, ← e3, beBytes_beN _ _ l1 hb1]
      simp
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · have := beN_lt a1 hb1; rw [l1, p256_4] at this; exact this
      · exact i3 p hp

theorem proofNew_inv {sil ps pf} (h : Proof.new sil ps = some pf) :
    pf = ⟨sil, ps⟩ ∧ 1 ≤ ps.length ∧ ps.length ≤ maxProbes := by
  unfold Proof.new at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_, ?_⟩ <;> omega

theorem pDown_inv {r f} (h : pDown r = .ok f) (hb : Byte r) : f.valid ∧ encBody f = 13 :: 0 :: r := by
  unfold pDown at h
  simp only [bind_ok] at h
  obtain ⟨⟨mb, r1⟩, h1, ⟨inc, r2⟩, h2, ⟨sil, r3⟩, h3, ⟨n, r4⟩, h4, hh⟩ := h
  obtain ⟨e1, l1⟩ := rdBytes_ok h1
  obtain ⟨a2, e2, l2, v2⟩ := rdBE_ok h2
  obtain ⟨a3, e3, l3, v3⟩ := rdBE_ok h3
  have e4 := rdU8_ok h4
  simp only at hh
  split at hh
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hh
  · rename_i hn
    simp only [bind_ok] at hh
    obtain ⟨⟨ps, r5⟩, h5, u, hu, hh⟩ := hh
    have hr5 := only_ok hu
    simp only at hr5
    subst hr5
    cases hp : Proof.new sil ps with
    | none => simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hh
    | some pf =>
      simp only [hp] at hh
      simp only [pure, Except.pure, Except.ok.injEq] at hh
      subst hh
      obtain ⟨hpf, hp1, hp2⟩ := proofNew_inv hp
      subst e4 e3 e2 e1 hpf v2 v3
      obtain ⟨hb1, hb⟩ := byte_append hb
      obtain ⟨hb2, hb⟩ := byte_append hb
      obtain ⟨hb3, hb⟩ := byte_append hb
      obtain ⟨_, hb⟩ := byte_cons hb
      obtain ⟨i1, i2, i3⟩ := rdProbes_inv n _ ps [] h5 hb
      simp only [List.append_nil] at i2
      have hn4 : n = ps.length := i1.symm
      subst hn4
      refine ⟨⟨l1, hb1, ?_, ?_, hp1, hp2, i3⟩, ?_⟩
      · have := beN_lt a2 hb2; rw [l2, p256_8] at this; exact this
      · have := beN_lt a3 hb3; rw [l3, p256_4] at this; exact this
      · simp only [encBody]
        rw [beBytes_beN _ _ l2 hb2, beBytes_beN _ _ l3 hb3, ← i2]
        simp

theorem dispatch_inv {ty topic r f} (h : dispatch ty topic r = .ok f) (hm : ¬(topic ≠ [] ∧ isMem ty = true))
    (hb : Byte r) (hty : ty < 256) (htb : Byte topic) (htl : topic.length < 256) :
    f.valid ∧ encBody f = ty :: topic.length :: (topic ++ r) := by
  have hnil : isMem ty = true → topic = [] := fun hi => Classical.byContradiction fun hne => hm ⟨hne, hi⟩
  by_cases h1 : ty = 1
  · subst h1
    have := hnil rfl
    subst this
    simp only [dispatch] at h
    simpa using pHello_inv h hb
  by_cases h2 : ty = 2
  · subst h2
    have := hnil rfl
    subst this
    simp only [dispatch, bind_ok] at h
    obtain ⟨u, hu, h⟩ := h
    have := only_ok hu
    subst this
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [encBody, Frame.valid]
  by_cases h3 : ty = 3
  · subst h3
    have := hnil rfl
    subst this
    simp only [dispatch] at h
    simpa using pDelta_inv h hb
  by_cases h4 : ty = 4
  · subst h4
    have := hnil rfl
    subst this
    simp only [dispatch] at h
    simpa using pSnap_inv h hb
  by_cases h12 : ty = 12
  · subst h12
    have := hnil rfl
    subst this
    simp only [dispatch, bind_ok] at h
    obtain ⟨u, hu, h⟩ := h
    have := only_ok hu
    subst this
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [encBody, Frame.valid]
  by_cases h13 : ty = 13
  · subst h13
    have := hnil rfl
    subst this
    simp only [dispatch] at h
    simpa using pDown_inv h hb
  have hmem : isMem ty = false := by simp [isMem, h1, h2, h3, h4, h12, h13]
  have hd := dispatch_other ty topic r hmem
  rw [hd] at h
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨⟨hty, hmem, by omega, htb, hb⟩, ?_⟩
  simp [encBody]

/-- **Canonical form.** An accepted body (of bytes) is a valid frame, and the frame re-encodes to the same bytes. -/
theorem parse_canonical {b f} (h : parse b = .ok f) (hb : Byte b) : f.valid ∧ encBody f = b := by
  unfold parse at h
  simp only [bind_ok] at h
  obtain ⟨⟨ty, r1⟩, h1, ⟨tl, r2⟩, h2, ⟨topic, r3⟩, h3, hh⟩ := h
  have e1 := rdU8_ok h1
  have e2 := rdU8_ok h2
  obtain ⟨e3, l3⟩ := rdBytes_ok h3
  simp only at hh
  subst e1 e2 e3
  split at hh
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hh
  · rename_i hm
    obtain ⟨hty, hb⟩ := byte_cons hb
    obtain ⟨htl, hb⟩ := byte_cons hb
    obtain ⟨htb, hb⟩ := byte_append hb
    have := dispatch_inv hh hm hb hty htb (by omega)
    simpa [l3] using this

/-- Each accepted body is the encoding of exactly one frame: two bodies that parse to the same frame are equal. -/
theorem parse_injective {b b' f} (h : parse b = .ok f) (h' : parse b' = .ok f) (hb : Byte b) (hb' : Byte b') :
    b = b' := by
  rw [← (parse_canonical h hb).2, ← (parse_canonical h' hb').2]

/-- The stream read uses exactly the bytes of the frame it returns. -/
theorem read_canonical {buf f n} (h : read buf = .ok (some (f, n))) (hb : Byte buf) :
    f.valid ∧ enc f = buf.take n := by
  unfold read readWith at h
  split at h
  · simp at h
  · rename_i h4
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hl
        simp only [bind_ok] at h
        obtain ⟨f', h1, h⟩ := h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hbb : Byte ((buf.drop 4).take (beN (buf.take 4))) := by
          intro x hx
          exact hb x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
        obtain ⟨hv, he⟩ := parse_canonical h1 hbb
        refine ⟨hv, ?_⟩
        have hlen : (encBody f').length = beN (buf.take 4) := by
          rw [he, List.length_take]; exact Nat.min_eq_left (Nat.not_lt.mp hl)
        have hb4 : Byte (buf.take 4) := fun x hx => hb x (List.mem_of_mem_take hx)
        unfold enc
        rw [hlen, beBytes_beN 4 _ (by simp; omega) hb4, he]
        exact List.take_add.symm

end Pinc.MemCodec
