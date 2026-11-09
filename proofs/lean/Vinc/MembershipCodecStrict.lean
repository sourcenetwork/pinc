import Vinc.MembershipCodecInv

/-!
# Hub stream codec: strictness and buffers

Every malformed class is refused, with the refusal the code names: a topic on a membership frame, a reserved flag,
a stray byte, an alive byte or a path byte out of range, a probe count of 0 or above 4, a snapshot that is not whole
entries, a snapshot entry that is not alive, a body too short. `read` returns `none` for every proper prefix of a
frame, whatever the frame, and `tooLarge` for a prefix that names a body above the limit. The buffers `node.rs`
encodes into (160 bytes, 4 + 3 + 64 * 51, `FLOOR_MAX + 8`) are large enough, so `encode` is total on the frames the
machines send.
-/

namespace Vinc.MemCodec

theorem rdBytes_app' (n : Nat) (a r : List Nat) (h : a.length = n) : rdBytes n (a ++ r) = .ok (a, r) := by
  subst h; exact rdBytes_app a r

theorem rdBytes_short {n r} (h : r.length < n) : rdBytes n r = .error .short := by
  simp [rdBytes]; omega

theorem rdBE_short {k r} (h : r.length < k) : rdBE k r = .error .short := by
  simp [rdBE, rdBytes_short h, bind, Except.bind]

/-! ## The stream read -/

theorem read_short (buf : List Nat) (h : buf.length < 4) : read buf = .ok none := by
  simp [read, h]

theorem read_tooLarge (buf : List Nat) (h : 4 ≤ buf.length) (hl : maxBody < beN (buf.take 4)) :
    read buf = .error .tooLarge := by
  have : ¬ buf.length < 4 := by omega
  simp [read, this, hl]

/-- Every proper prefix of a frame is a partial frame: `read` asks for more bytes. -/
theorem read_prefix (f : Frame) (hv : f.valid) (hs : bodyLen f ≤ maxBody) (k : Nat) (hk : k < (enc f).length) :
    read ((enc f).take k) = .ok none := by
  by_cases h4 : k < 4
  · apply read_short
    simp [List.length_take]; omega
  · have hl := encBody_length f hv
    have hb : (beBytes 4 (encBody f).length).length = 4 := beBytes_length _ _
    have hn : beN (beBytes 4 (encBody f).length) = bodyLen f := by
      rw [beN_beBytes, Nat.mod_eq_of_lt, hl]
      rw [p256_4]; simp [maxBody] at hs; omega
    have hel : (enc f).length = 4 + bodyLen f := by simp [enc, hl, beBytes_length]
    have e1 : (enc f).take k = beBytes 4 (encBody f).length ++ (encBody f).take (k - 4) := by
      unfold enc
      rw [List.take_append, List.take_of_length_le (by omega), hb]
    have e1' : (beBytes 4 (encBody f).length ++ (encBody f).take (k - 4)).take 4 = beBytes 4 (encBody f).length :=
      List.take_left' hb
    have e2' : (beBytes 4 (encBody f).length ++ (encBody f).take (k - 4)).drop 4 = (encBody f).take (k - 4) :=
      List.drop_left' hb
    rw [e1]
    have hlen4 : ¬ ((beBytes 4 (encBody f).length ++ (encBody f).take (k - 4)).length < 4) := by
      simp [hb]
    have h5 : ((encBody f).take (k - 4)).length < bodyLen f := by
      rw [List.length_take]; omega
    have h6 : ¬ (maxBody < bodyLen f) := Nat.not_lt.mpr hs
    unfold read
    simp only [hlen4, e1', e2', hn, ite_false, h5, h6, ite_true]

/-! ## The malformed classes -/

theorem parse_empty : parse [] = .error .short := by simp [parse, rdU8, bind, Except.bind]

theorem parse_topic_membership (ty : Nat) (topic r : List Nat) (hm : isMem ty = true) (ht : topic ≠ []) :
    parse (ty :: topic.length :: (topic ++ r)) = .error .topicOnMembership := by
  rw [parse_hdr]; simp [hm, ht]

theorem hello_flag (a1 a2 th r : List Nat) (fl : Nat) (h1 : a1.length = 8) (h2 : a2.length = 2)
    (h3 : th.length = 8) (hf : fl / 4 ≠ 0) : pHello (a1 ++ a2 ++ th ++ fl :: r) = .error .helloFlag := by
  have e1 := rdBE_app 8 a1 (a2 ++ th ++ fl :: r) h1
  have e2 := rdBE_app 2 a2 (th ++ fl :: r) h2
  have e3 := rdBytes_app' 8 th (fl :: r) h3
  simp only [List.append_assoc] at e1 e2 ⊢
  simp [pHello, e1, e2, e3, rdU8, hf, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem hello_trailing (a1 a2 th r : List Nat) (fl x : Nat) (h1 : a1.length = 8) (h2 : a2.length = 2)
    (h3 : th.length = 8) (hf : fl / 4 = 0) : pHello (a1 ++ a2 ++ th ++ fl :: x :: r) = .error .helloLen := by
  have e1 := rdBE_app 8 a1 (a2 ++ th ++ fl :: x :: r) h1
  have e2 := rdBE_app 2 a2 (th ++ fl :: x :: r) h2
  have e3 := rdBytes_app' 8 th (fl :: x :: r) h3
  simp only [List.append_assoc] at e1 e2 ⊢
  simp [pHello, e1, e2, e3, rdU8, hf, only, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem hello_short (r : List Nat) (h : r.length < helloLen) : pHello r = .error .short := by
  unfold pHello
  by_cases h8 : r.length < 8
  · simp [rdBE_short h8, bind, Except.bind]
  · obtain ⟨a, r1, rfl, ha⟩ : ∃ a r1, r = a ++ r1 ∧ a.length = 8 :=
      ⟨r.take 8, r.drop 8, by simp, by simp; omega⟩
    rw [rdBE_app 8 a r1 ha]
    simp only [bind, Except.bind]
    by_cases h2 : r1.length < 2
    · simp [rdBE_short h2]
    · obtain ⟨b, r2, rfl, hb⟩ : ∃ b r2, r1 = b ++ r2 ∧ b.length = 2 :=
        ⟨r1.take 2, r1.drop 2, by simp, by simp; omega⟩
      rw [rdBE_app 2 b r2 hb]
      simp only [bind, Except.bind]
      by_cases h3 : r2.length < 8
      · simp [rdBytes_short h3]
      · obtain ⟨c, r3, rfl, hc⟩ : ∃ c r3, r2 = c ++ r3 ∧ c.length = 8 :=
          ⟨r2.take 8, r2.drop 8, by simp, by simp; omega⟩
        rw [rdBytes_app' 8 c r3 hc]
        have : r3 = [] := by
          simp [helloLen] at h; apply List.eq_nil_of_length_eq_zero; omega
        subst this
        simp [rdU8]

theorem ack_trailing (x : Nat) (r : List Nat) : parse (2 :: 0 :: x :: r) = .error .ackLen := by
  rw [parse_hdr0]; simp [dispatch, only, bind, Except.bind]

theorem probe_trailing (x : Nat) (r : List Nat) : parse (12 :: 0 :: x :: r) = .error .probeLen := by
  rw [parse_hdr0]; simp [dispatch, only, bind, Except.bind]

theorem delta_short (r : List Nat) (h : r.length < entryLen) : pDelta r = .error .short := by
  simp [pDelta, rdBytes_short h, bind, Except.bind]

theorem delta_trailing (eb : List Nat) (x : Nat) (e : Entry) (r : List Nat) (hl : eb.length = entryLen)
    (he : entryOf eb = .ok e) : pDelta (eb ++ x :: r) = .error .deltaLen := by
  simp [pDelta, rdBytes_app' _ _ _ hl, he, only, bind, Except.bind]

theorem delta_alive_byte (eb r : List Nat) (hl : eb.length = entryLen) (h : entryOf eb = .error .aliveByte) :
    pDelta (eb ++ r) = .error .aliveByte := by
  simp [pDelta, rdBytes_app' _ _ _ hl, h, bind, Except.bind]

theorem snap_flag (fl : Nat) (r : List Nat) (hf : fl / 4 ≠ 0) : pSnap (fl :: r) = .error .snapFlag := by
  simp [pSnap, rdU8, hf, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem snap_size (fl : Nat) (eb : List Nat) (hf : fl / 4 = 0) (hn : eb.length % entryLen ≠ 0) :
    pSnap (fl :: eb) = .error .snapSize := by
  simp [pSnap, rdU8, hf, rdBytes_self, snapNew, hn, bind, Except.bind]

theorem snap_too_many (fl : Nat) (eb : List Nat) (hf : fl / 4 = 0) (hn : snapMax < (chunks eb).length) :
    pSnap (fl :: eb) = .error .snapSize := by
  simp [pSnap, rdU8, hf, rdBytes_self, snapNew, hn, bind, Except.bind]

theorem snap_not_alive (e : Entry) (hne : e.alive ≠ Alive.alive) (c : List Nat) (hc : entryOf c = .ok e) :
    snapEntry c = .error .snapNotAlive := by
  have : (e.alive != Alive.alive) = true := by simpa using hne
  simp [snapEntry, hc, this, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem down_count (mb : List Nat) (a b : List Nat) (n : Nat) (r : List Nat) (hm : mb.length = 32)
    (ha : a.length = 8) (hb : b.length = 4) (hn : n = 0 ∨ maxProbes < n) :
    pDown (mb ++ a ++ b ++ n :: r) = .error .probeCount := by
  have e1 := rdBytes_app' 32 mb (a ++ b ++ n :: r) hm
  have e2 := rdBE_app 8 a (b ++ n :: r) ha
  have e3 := rdBE_app 4 b (n :: r) hb
  simp only [List.append_assoc] at *
  simp [pDown, e1, e2, e3, rdU8, hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem probe_path (age : List Nat) (pb : Nat) (hl : age.length = 4) (hp : pathOf pb = .error .probePath)
    (k : Nat) (rest : List Nat) :
    rdProbes (k + 1) (age ++ pb :: rest) = .error .probePath := by
  simp [rdProbes, rdBE_app 4 age (pb :: rest) hl, rdU8, hp, bind, Except.bind]

theorem down_trailing (mb : List Nat) (inc : Nat) (pf : Proof) (hv : (Frame.down mb inc pf).valid) (x : Nat)
    (r : List Nat) :
    pDown (mb ++ beBytes 8 inc ++ beBytes 4 pf.sil ++ [pf.probes.length] ++ pf.probes.flatMap encProbe ++ x :: r) =
      .error .downLen := by
  obtain ⟨hm, _, hi, hs, h1, h4, hp⟩ := hv
  have e1 := rdBytes_app mb (beBytes 8 inc ++ beBytes 4 pf.sil ++ [pf.probes.length] ++
    pf.probes.flatMap encProbe ++ x :: r)
  rw [hm] at e1
  have e2 := rdBE_beBytes_lt 8 inc (beBytes 4 pf.sil ++ [pf.probes.length] ++ pf.probes.flatMap encProbe ++ x :: r)
    (by rw [p256_8]; exact hi)
  have e3 := rdBE_beBytes_lt 4 pf.sil ([pf.probes.length] ++ pf.probes.flatMap encProbe ++ x :: r)
    (by rw [p256_4]; exact hs)
  have e5 := probes_rt pf.probes (x :: r) hp
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] at e1 e2 e3 e5 ⊢
  have hc1 : pf.probes.length ≠ 0 := by omega
  have hc2 : ¬ maxProbes < pf.probes.length := by omega
  simp [pDown, e1, e2, e3, e5, rdU8, hc1, hc2, only, bind, Except.bind, pure, Except.pure]

end Vinc.MemCodec
