import Pinc.ConnectPack

/-!
# The batch builder: the theorems

For every configuration and every sequence of offers (`Reach`; the offered frames are well formed: a BATCH frame, a
frame whose encoder fails, or an encoding the decoder accepts and that is not a BATCH):

* `offer_added_iff`, `offer_refused_iff` (in a state where the frames lie in the buffer), `offer_noroom_iff`, `offer_small_iff`, `offer_bad_iff`: exactly when a frame
  is added, refused, or an error, in the terms of the module documentation. `offer_stay`: a refused or failed offer
  changes nothing. `offer_order`: an added frame becomes the last member. `offer_long`: a BATCH frame or a long-header
  packet is always refused and changes nothing, so it neither joins a batch nor starts one.
* `pack_bounds`: at most `F` frames and `B` bytes of frames, the frames lie in the buffer after the header room.
  `never_long`: no member is a long-header packet, a BATCH, or a frame whose encoder failed.
* `finish_readback`: an empty batch finishes as nothing, one frame as itself (without a header), more as a BATCH
  frame that `Frame::decode` reads back as exactly the members in order (for `F ≤ 64` and `B ≤ 16384`, the limits of
  the decoder). `header_fits`: the header fits the `head` bytes kept for it, and the record is the header and the frames.
-/

namespace Pinc.ConnPack
open Pinc.ConnCodec
open Pinc.MemCodec (Byte)

/-! ## The offer -/

theorem offer_added_iff (c : Cfg) (st : St) (f : Cand) :
    (offer c st f).1 = .added ↔
      (f.isBatch = false ∧ f.long = false ∧ st.count < c.F ∧ f.bad = false ∧
        c.head + st.used + f.n ≤ c.cap ∧ st.used + f.n ≤ c.B) := by
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> omega

theorem offer_refused_iff (c : Cfg) (st : St) (f : Cand) (hI : 0 < st.count → c.head + st.used ≤ c.cap) :
    (offer c st f).1 = .refused ↔
      (f.isBatch = true ∨ f.long = true ∨ c.F ≤ st.count ∨
        (0 < st.count ∧ c.cap < c.head + st.used + f.n) ∨
        (f.bad = false ∧ c.head + st.used + f.n ≤ c.cap ∧ c.B < st.used + f.n)) := by
  revert hI
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> omega

theorem offer_noroom_iff (c : Cfg) (st : St) (f : Cand) :
    (offer c st f).1 = .noroom ↔
      (f.isBatch = false ∧ f.long = false ∧ st.count < c.F ∧ c.cap < c.head + st.used) := by
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> omega

theorem offer_small_iff (c : Cfg) (st : St) (f : Cand) :
    (offer c st f).1 = .small ↔
      (f.isBatch = false ∧ f.long = false ∧ st.count = 0 ∧ c.F ≠ 0 ∧ c.head + st.used ≤ c.cap ∧
        c.cap < c.head + st.used + f.n) := by
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> omega

theorem offer_bad_iff (c : Cfg) (st : St) (f : Cand) (e : Nat) :
    (offer c st f).1 = .bad e ↔
      (e = f.err ∧ f.isBatch = false ∧ f.long = false ∧ st.count < c.F ∧ f.bad = true ∧
        c.head + st.used + f.n ≤ c.cap) := by
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> omega

theorem offer_stay (c : Cfg) (st : St) (f : Cand) (h : (offer c st f).1 ≠ .added) : (offer c st f).2 = st := by
  revert h
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> simp_all [Cand.n]

theorem offer_order (c : Cfg) (st : St) (f : Cand) (h : (offer c st f).1 = .added) :
    (offer c st f).2 = ⟨st.ps ++ [f.raw]⟩ := by
  revert h
  cases hb : f.isBatch <;> cases hl : f.long <;> cases hd : f.bad <;> by_cases a : c.F ≤ st.count <;> by_cases b : c.cap < c.head + st.used <;> by_cases d : c.cap - (c.head + st.used) < f.n <;> by_cases e : 0 < st.count <;> by_cases g : c.B < st.used + f.n <;> simp [offer, hb, hl, hd, a, b, d, e, g] <;> simp_all [Cand.n]

theorem offer_long (c : Cfg) (st : St) (f : Cand) (h : f.long = true ∨ f.isBatch = true) :
    offer c st f = (.refused, st) := by
  unfold offer
  rcases h with h | h <;> simp [h]

/-! ## The state of a builder -/

/-- A frame the code can offer: a BATCH frame, one whose encoder fails, or an encoding the decoder accepts that is
not a BATCH frame. -/
def Good (p : List Nat) : Prop := p ≠ [] ∧ p.head? ≠ some 13 ∧ Byte p ∧ ∃ fr, decodeNB p = .ok fr

def Wf (f : Cand) : Prop := f.isBatch = true ∨ f.bad = true ∨ Good f.raw

/-- The builders reachable by offers; `fs` are the frames accepted so far. -/
inductive Reach (c : Cfg) : St → List Cand → Prop where
  | empty : Reach c ⟨[]⟩ []
  | add {st fs f} : Reach c st fs → Wf f → (offer c st f).1 = .added → Reach c (offer c st f).2 (fs ++ [f])
  | skip {st fs f} : Reach c st fs → Wf f → (offer c st f).1 ≠ .added → Reach c st fs

theorem sum_append_single (l : List Nat) (x : Nat) : (l ++ [x]).sum = l.sum + x := by simp

/-- The invariant. -/
def Inv (c : Cfg) (st : St) (fs : List Cand) : Prop :=
  st.ps = fs.map Cand.raw ∧ st.count ≤ c.F ∧ st.used ≤ c.B ∧ (0 < st.count → c.head + st.used ≤ c.cap) ∧
    ∀ f ∈ fs, f.long = false ∧ f.isBatch = false ∧ f.bad = false ∧ Good f.raw

theorem reach_inv {c : Cfg} {st : St} {fs : List Cand} (h : Reach c st fs) : Inv c st fs := by
  induction h with
  | empty => simp [Inv, St.count, St.used]
  | skip _ _ hne ih => exact ih
  | @add st fs f _ hw hadd ih =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    have hi := (offer_added_iff c st f).1 hadd
    obtain ⟨hb, hl, hc, hbad, hfit, hbytes⟩ := hi
    rw [offer_order c st f hadd]
    have hgood : Good f.raw := by
      rcases hw with h | h | h
      · simp_all
      · simp_all
      · exact h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [i1]
    · simp [St.count] at hc ⊢; omega
    · simp [St.used, Cand.n] at hbytes ⊢; omega
    · intro _
      simp [St.used, Cand.n] at hfit ⊢; omega
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact i5 g hg
      · exact ⟨hl, hb, hbad, hgood⟩

theorem used_eq {c : Cfg} {st : St} {fs : List Cand} (h : Reach c st fs) : st.used = (fs.map Cand.n).sum := by
  obtain ⟨i1, -⟩ := reach_inv h
  simp [St.used, i1, List.map_map, Function.comp_def]
  rfl

/-- At most `F` frames and `B` bytes of frames, in the buffer after the header room. -/
theorem pack_bounds {c : Cfg} {st : St} {fs : List Cand} (h : Reach c st fs) :
    st.count ≤ c.F ∧ st.used ≤ c.B ∧ st.used = (fs.map Cand.n).sum ∧
      (0 < st.count → c.head + st.used ≤ c.cap) := by
  obtain ⟨-, i2, i3, i4, -⟩ := reach_inv h
  exact ⟨i2, i3, used_eq h, i4⟩

/-- No member is a long-header packet, a BATCH, or a frame whose encoder failed. -/
theorem never_long {c : Cfg} {st : St} {fs : List Cand} (h : Reach c st fs) :
    ∀ f ∈ fs, f.long = false ∧ f.isBatch = false ∧ f.bad = false := by
  obtain ⟨-, -, -, -, i5⟩ := reach_inv h
  intro f hf
  obtain ⟨a, b, d, -⟩ := i5 f hf
  exact ⟨a, b, d⟩

/-! ## Finishing -/

theorem decode_nb {b : List Nat} (h : b.head? ≠ some 13) : decode b = decodeNB b := by
  rcases b with _ | ⟨ty, r⟩
  · simp [decode, decodeNB, decodeWith, liftW, rdU8, bind, Except.bind]
  · have : ty ≠ 13 := by simpa using h
    simp [decode, decodeNB, decodeWith, liftW, rdU8, this, bind, Except.bind]

theorem encodedLen_le3 (v : Nat) (h : v < 2097152) : Varint.encodedLen v ≤ 3 := by
  by_cases h1 : v < 128
  · rw [Varint.encodedLen_lt v h1]; omega
  · rw [Varint.encodedLen_ge v (by omega)]
    by_cases h2 : v / 128 < 128
    · rw [Varint.encodedLen_lt _ h2]; omega
    · rw [Varint.encodedLen_ge _ (by omega)]
      have h3 : v / 128 / 128 < 128 := by omega
      rw [Varint.encodedLen_lt _ h3]; omega

theorem lensBytes_length_le (ps : List (List Nat)) (h : ∀ p ∈ ps, p.length < 2097152) :
    (lensBytes ps).length ≤ 3 * ps.length := by
  induction ps with
  | nil => simp [lensBytes]
  | cons p ps ih =>
    have h1 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h2 := encodedLen_le3 p.length (h p (List.mem_cons_self ..))
    simp only [lensBytes, List.map_cons, List.flatten_cons, List.length_append, Varint.length_encodeBytes,
      List.length_cons] at h1 h2 ⊢
    omega

theorem member_le_used (st : St) (p : List Nat) (hp : p ∈ st.ps) : p.length ≤ st.used :=
  le_sum_of_mem (List.mem_map.2 ⟨p, hp, rfl⟩)

theorem kind_none {st : St} : kind st = .none ↔ st.ps = [] := by
  unfold kind; rcases hs : st.ps with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp

theorem kind_single {st : St} (hk : kind st = .single) : ∃ p, st.ps = [p] ∧ record st = p := by
  unfold kind at hk; unfold record
  rcases hs : st.ps with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [hs] at hk ⊢

theorem kind_batch {st : St} (hk : kind st = .batch) :
    2 ≤ st.ps.length ∧ record st = headBytes st.ps ++ st.ps.flatten := by
  unfold kind at hk; unfold record
  rcases hs : st.ps with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [hs] at hk ⊢

/-- The header fits the room kept for it. -/
theorem header_fits {c : Cfg} {st : St} {fs : List Cand} (h : Reach c st fs) (hB : c.B ≤ 16384)
    (hh : c.head = 2 + 3 * c.F) : headFits c st = true := by
  obtain ⟨-, i2, i3, -, -⟩ := reach_inv h
  have hlen := lensBytes_length_le st.ps (fun p hp => by have := member_le_used st p hp; omega)
  unfold headFits
  rcases hs : st.ps with _ | ⟨a, _ | ⟨b, r⟩⟩
  · simp
  · simp
  · rw [hs] at hlen
    simp only [St.count, hs, List.length_cons] at i2
    simp only [headBytes, List.length_cons]
    simp only [List.length_cons] at hlen
    apply decide_eq_true
    omega

/-- The record is the header and the frames. -/
theorem record_length {st : St} (hk : kind st = .batch) :
    (record st).length = (headBytes st.ps).length + st.used := by
  obtain ⟨-, hr⟩ := kind_batch hk
  rw [hr, List.length_append]
  simp [St.used, List.length_flatten]

/-- An empty batch finishes as nothing, one frame as itself, more as a BATCH frame that the decoder reads back as
the members in order. -/
theorem finish_readback {c : Cfg} {st : St} {fs : List Cand} (h : Reach c st fs) (hF : c.F ≤ 64) (hB : c.B ≤ 16384) :
    (kind st = .none ↔ fs = []) ∧
    (kind st = .single → ∃ f, fs = [f] ∧ record st = f.raw ∧ ∃ fr, decode f.raw = .ok fr) ∧
    (kind st = .batch → 2 ≤ fs.length ∧ fs.length ≤ c.F ∧
      decode (record st) = .ok ⟨13, (fs.map Cand.raw).map F.raw⟩) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := reach_inv h
  have hlen : st.ps.length = fs.length := by simp [i1]
  refine ⟨?_, ?_, ?_⟩
  · rw [kind_none, i1]; simp
  · intro hk
    obtain ⟨p, hp, hr⟩ := kind_single hk
    rw [i1] at hp
    rcases fs with _ | ⟨f, _ | ⟨g, fs'⟩⟩ <;> simp at hp
    subst hp
    obtain ⟨-, -, -, hg⟩ := i5 f (by simp)
    obtain ⟨-, hh, -, fr, hfr⟩ := hg
    exact ⟨f, rfl, by simpa using hr, fr, by rw [decode_nb hh]; exact hfr⟩
  · intro hk
    obtain ⟨hge, hr⟩ := kind_batch hk
    have hle : fs.length ≤ c.F := by have : st.count = fs.length := hlen; omega
    refine ⟨by omega, hle, ?_⟩
    have hparts : ((fs.map Cand.raw).map F.raw).map F.enc = fs.map Cand.raw := by
      simp [F.enc, List.map_map, Function.comp_def]
    have hrec : record st = (Fr.mk 13 ((fs.map Cand.raw).map F.raw)).bytes := by
      rw [hr, i1]
      simp only [Fr.bytes, Fr.parts, hparts, ↓reduceIte, List.length_map, headBytes, List.cons_append]
    rw [hrec]
    refine batch_roundtrip _ rfl ⟨fs.map Cand.raw, rfl, by simp; omega, by simp; unfold batchFrames; omega, ?_, ?_⟩
    · intro q hq
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hq
      obtain ⟨-, -, -, hg⟩ := i5 f hf
      exact hg
    · have : (List.map List.length st.ps).sum ≤ c.B := i3
      rw [i1] at this
      unfold batchBytes; omega

end Pinc.ConnPack
