import Vinc.MembershipCodecStrict

/-!
# Hub stream codec: encoding into the buffers of `node.rs`

`encode` succeeds exactly when the frame is within `maxBody`, its topic fits a byte and the buffer holds the
prefix and the body. The buffers the machines encode into suffice for the frames they send: 160 bytes for HELLO,
ACK, DELTA, PROBE and DOWN, `4 + 3 + 64 * 51` for a snapshot chunk, `floorMax + 8` for FLOOR. So the machine
models may treat `Frame::encode` as total on what they send. `snapFrames` is the chunking loop of `send_snapshot`.
-/

namespace Vinc.MemCodec

theorem encode_ok (cap : Nat) (f : Frame) (hv : f.valid) (hs : bodyLen f ≤ maxBody) (hc : 4 + bodyLen f ≤ cap) :
    encode cap f = .ok (enc f) := by
  have h5 : ¬ cap < 5 := by
    cases f <;> simp [bodyLen, helloLen, entryLen] at hc <;> omega
  have ht : ¬ 255 < f.topic.length := by
    cases f <;> simp [Frame.topic] ; case other t tp rest => exact hv.2.2.1
  unfold encode
  simp [Nat.not_lt.mpr hs, h5, ht, Nat.not_lt.mpr hc]

theorem encode_tooLarge (cap : Nat) (f : Frame) (h : maxBody < bodyLen f) : encode cap f = .error .tooLarge := by
  simp [encode, h]

theorem encode_small (cap : Nat) (f : Frame) (hv : f.valid) (hs : bodyLen f ≤ maxBody) (hc : cap < 4 + bodyLen f) :
    encode cap f = .error .bufferSmall := by
  have ht : ¬ 255 < f.topic.length := by
    cases f <;> simp [Frame.topic] ; case other t tp rest => exact hv.2.2.1
  unfold encode
  by_cases h5 : cap < 5
  · simp [Nat.not_lt.mpr hs, h5]
  · simp [Nat.not_lt.mpr hs, h5, ht, hc]

theorem encode_topicLong (cap : Nat) (t : Nat) (tp rest : List Nat) (h5 : 5 ≤ cap) (hs : bodyLen (.other 0 tp rest) ≤ maxBody)
    (hl : 255 < tp.length) : encode cap (.other t tp rest) = .error .topicLong := by
  have : bodyLen (.other t tp rest) = bodyLen (.other 0 tp rest) := rfl
  unfold encode
  simp [this, Nat.not_lt.mpr hs, Nat.not_lt.mpr h5, Frame.topic, hl]

/-- The frames that go through `Membership::tx` (not a snapshot chunk, not a passthrough frame). -/
def Frame.small : Frame → Prop
  | .snap .. | .other .. => False
  | _ => True

/-- The small frames fit the 160-byte buffer of `Membership::tx`. -/
theorem small_fits (f : Frame) (hv : f.valid) (hk : f.small) :
    4 + bodyLen f ≤ 160 := by
  cases f with
  | hello _ _ _ => simp [bodyLen, helloLen]
  | ack => simp [bodyLen]
  | probe => simp [bodyLen]
  | delta _ => simp [bodyLen, entryLen]
  | down mb inc pf =>
    obtain ⟨_, _, _, _, _, h4, _⟩ := hv
    simp [bodyLen]; simp [maxProbes] at h4; omega
  | snap _ _ _ => exact hk.elim
  | other _ _ _ => exact hk.elim

/-- A snapshot chunk of at most `snapChunk` entries fits `4 + 3 + 64 * 51`. -/
theorem snap_chunk_fits (p m : Bool) (es : List Entry) (h : es.length ≤ snapChunk) :
    4 + bodyLen (.snap p m es) ≤ 4 + 3 + snapChunk * entryLen := by
  simp [bodyLen, snapChunk, entryLen] at *
  omega

/-- A chunk of whole alive entries is a valid frame (so `Snap::new` accepts it). -/
theorem snap_chunk_valid (p m : Bool) (es : List Entry) (h : es.length ≤ snapChunk)
    (hv : ∀ e ∈ es, e.valid ∧ e.alive = Alive.alive) : (Frame.snap p m es).valid :=
  ⟨by simp [snapChunk, snapMax] at *; omega, hv⟩

/-- The FLOOR frame (`send_floor`: no topic, at most `floorMax` bytes) fits `floorMax + 8`. -/
theorem floor_fits (rest : List Nat) (h : rest.length ≤ floorMax) : 4 + bodyLen (.other 14 [] rest) ≤ floorMax + 8 := by
  simp [bodyLen]; omega

theorem floor_valid (rest : List Nat) (hb : Byte rest) : (Frame.other 14 [] rest).valid :=
  ⟨by decide, by decide, by simp, by intro b hb; simp at hb, hb⟩

/-- Every size the machines encode is within `maxBody`. -/
theorem sizes_ok_snap (es : List Entry) (h : es.length ≤ snapChunk) (p m : Bool) :
    bodyLen (.snap p m es) ≤ maxBody := by
  simp [bodyLen, snapChunk, entryLen, maxBody] at *; omega

/-! ## The chunking loop of `send_snapshot` -/

/-- The loop: `acc` holds the entries of the frame being filled; a full frame is sent (more follows) when the next
entry arrives; the last frame (possibly empty) is sent with `more` clear. -/
def snapGo : List Entry → List Entry → List (Bool × List Entry)
  | acc, [] => [(false, acc)]
  | acc, e :: es => if acc.length = snapChunk then (true, acc) :: snapGo [e] es else snapGo (acc ++ [e]) es

/-- The frames `send_snapshot` sends for the entries `es`. -/
def snapFrames (es : List Entry) : List (Bool × List Entry) := snapGo [] es

theorem snapGo_flat : ∀ (es acc : List Entry), ((snapGo acc es).flatMap (·.2)) = acc ++ es
  | [], acc => by simp [snapGo]
  | e :: es, acc => by
    unfold snapGo
    split
    · simp [snapGo_flat es [e]]
    · simp [snapGo_flat es (acc ++ [e])]

theorem snapGo_len : ∀ (es acc : List Entry), acc.length ≤ snapChunk →
    ∀ c ∈ snapGo acc es, c.2.length ≤ snapChunk
  | [], acc, h, c, hc => by simp [snapGo] at hc; subst hc; exact h
  | e :: es, acc, h, c, hc => by
    unfold snapGo at hc
    split at hc
    · rename_i hf
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [hf, snapChunk]
      · exact snapGo_len es [e] (by simp [snapChunk]) c hc
    · rename_i hf
      exact snapGo_len es (acc ++ [e]) (by simp; simp [snapChunk] at *; omega) c hc

/-- All frames but the last have `more` set and are full; the last has `more` clear. -/
theorem snapGo_shape : ∀ (es acc : List Entry), acc.length ≤ snapChunk →
    ∃ init last, snapGo acc es = init ++ [last] ∧ last.1 = false ∧
      ∀ c ∈ init, c.1 = true ∧ c.2.length = snapChunk
  | [], acc, h => ⟨[], (false, acc), by simp [snapGo], rfl, by simp⟩
  | e :: es, acc, h => by
    unfold snapGo
    split
    · rename_i hf
      obtain ⟨i, l, h1, h2, h3⟩ := snapGo_shape es [e] (by simp [snapChunk])
      refine ⟨(true, acc) :: i, l, by simp [h1], h2, ?_⟩
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨rfl, hf⟩
      · exact h3 c hc
    · rename_i hf
      exact snapGo_shape es (acc ++ [e]) (by simp; simp [snapChunk] at *; omega)

theorem snapFrames_flat (es : List Entry) : (snapFrames es).flatMap (·.2) = es := by
  simp [snapFrames, snapGo_flat]

theorem snapFrames_len (es : List Entry) : ∀ c ∈ snapFrames es, c.2.length ≤ snapChunk :=
  snapGo_len es [] (by simp [snapChunk])

theorem snapFrames_shape (es : List Entry) :
    ∃ init last, snapFrames es = init ++ [last] ∧ last.1 = false ∧ ∀ c ∈ init, c.1 = true ∧ c.2.length = snapChunk :=
  snapGo_shape es [] (by simp [snapChunk])

end Vinc.MemCodec
