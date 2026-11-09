import Vinc.ConnectFramePf

/-!
# The carrier frame codec: batches

`decode_batch` of `frame.rs`: a count of 2 to 64, that many nonzero varint lengths whose total is the rest of the
frame and at most 16384, and the member frames, none of which is a batch. A valid batch re-decodes
(`batch_roundtrip`), an accepted batch re-encodes to its input (`batch_inv`).
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

theorem rdVar_enc (v : Nat) (rest : List Nat) (hv : v < Varint.limit) :
    rdVar (Varint.encodeBytes v ++ rest) = .ok (v, rest) := by
  have := Varint.decode_encode v rest hv
  simp [rdVar, this]

theorem rdVar_inv {r v r'} (h : rdVar r = .ok (v, r')) (hb : Byte r) :
    r = Varint.encodeBytes v ++ r' ∧ v < Varint.limit := by
  cases hd : Varint.decode r with
  | error e => cases e <;> simp [rdVar, hd] at h
  | ok p =>
    obtain ⟨v0, n⟩ := p
    simp [rdVar, hd] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := Varint.decode_canonical r hb v0 n hd
    obtain ⟨hv, _⟩ := Varint.decode_bounds r hb v0 n hd
    refine ⟨?_, hv⟩
    rw [← h1]
    exact (List.take_append_drop n r).symm

/-- The lengths of a batch as varints. -/
def lensEnc (ls : List Nat) : List Nat := (ls.map Varint.encodeBytes).flatten

theorem lensBytes_eq (ps : List (List Nat)) : lensBytes ps = lensEnc (ps.map List.length) := by
  simp [lensBytes, lensEnc, List.map_map, Function.comp_def]

theorem lensEnc_byte (ls : List Nat) : Byte (lensEnc ls) := by
  intro b hb
  simp only [lensEnc, List.mem_flatten, List.mem_map] at hb
  obtain ⟨_, ⟨l, _, rfl⟩, hb⟩ := hb
  rw [Varint.encodeBytes_eq] at hb
  exact Varint.encRec_valid l b hb

theorem rdLens_enc (ls : List Nat) (hpos : ∀ l ∈ ls, 0 < l ∧ l < Varint.limit) :
    ∀ (total : Nat) (rest : List Nat), total + ls.sum < 2 ^ 64 →
      rdLens ls.length total (lensEnc ls ++ rest) = .ok (ls, rest) := by
  induction ls with
  | nil => intro total rest _; simp [rdLens, lensEnc]
  | cons l ls ih =>
    intro total rest hs
    have hl := hpos l (by simp)
    have e1 := rdVar_enc l (lensEnc ls ++ rest) hl.2
    have hcond : ¬ (2 ^ 64 ≤ total + l) := by simp at hs; omega
    have e2 := ih (fun x hx => hpos x (by simp [hx])) (total + l) rest (by simp at hs; omega)
    have hl0 : l ≠ 0 := by omega
    have hc : lensEnc (l :: ls) ++ rest = Varint.encodeBytes l ++ (lensEnc ls ++ rest) := by
      simp [lensEnc]
    rw [hc]
    simp [rdLens, e1, hl0, hcond, e2, bind, Except.bind, pure, Except.pure, liftW]

theorem rdLens_inv : ∀ (k total : Nat) {r ls r'}, rdLens k total r = .ok (ls, r') → Byte r → total < 2 ^ 64 →
    ls.length = k ∧ (∀ l ∈ ls, 0 < l ∧ l < Varint.limit) ∧ r = lensEnc ls ++ r' ∧ total + ls.sum < 2 ^ 64 := by
  intro k
  induction k with
  | zero =>
    intro total r ls r' h _ ht
    simp [rdLens] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [lensEnc, ht]
  | succ k ih =>
    intro total r ls r' h hb ht
    unfold rdLens at h
    simp only [bind_ok] at h
    obtain ⟨⟨len, r1⟩, h1, h⟩ := h
    have h1' := liftW_eq_ok h1
    obtain ⟨e1, hv⟩ := rdVar_inv h1' hb
    subst e1
    by_cases h0 : len = 0
    · subst h0; simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · by_cases hc : 2 ^ 64 ≤ total + len
      · simp [h0, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · simp only [h0, hc, ite_false] at h
        simp only [bind_ok, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨ls1, r2⟩, h2, rfl, rfl⟩ := h
        obtain ⟨_, hb1⟩ := byte_append hb
        obtain ⟨a, b, c, d⟩ := ih (total + len) h2 hb1 (by omega)
        refine ⟨by simp [a], ?_, ?_, ?_⟩
        · intro l hl
          simp only [List.mem_cons] at hl
          rcases hl with rfl | hl
          · exact ⟨by omega, hv⟩
          · exact b l hl
        · subst c
          simp [lensEnc]
        · simp at d ⊢; omega

theorem rdMembers_enc (ps : List (List Nat))
    (hok : ∀ p ∈ ps, p ≠ [] ∧ p.head? ≠ some 13 ∧ ∃ fr, decodeNB p = .ok fr) :
    rdMembers decodeNB (ps.map List.length) ps.flatten = .ok ps := by
  induction ps with
  | nil => simp [rdMembers]
  | cons p ps ih =>
    obtain ⟨hne, h13, fr, hd⟩ := hok p (by simp)
    have ih' := ih (fun x hx => hok x (by simp [hx]))
    have e1 : (p ++ ps.flatten).take p.length = p := by simp
    have e2 : (p ++ ps.flatten).drop p.length = ps.flatten := by simp
    simp [rdMembers, e1, e2, h13, hd, ih', bind, Except.bind, pure, Except.pure]

theorem rdMembers_inv (dec : List Nat → Except CErr Fr) :
    ∀ (ls body : List Nat) {ps}, rdMembers dec ls body = .ok ps → (∀ l ∈ ls, 0 < l) → ls.sum ≤ body.length →
      ps.map List.length = ls ∧ ps.flatten = body.take ls.sum ∧
        ∀ p ∈ ps, p ≠ [] ∧ p.head? ≠ some 13 ∧ ∃ fr, dec p = .ok fr := by
  intro ls
  induction ls with
  | nil =>
    intro body ps h _ _
    simp [rdMembers] at h
    subst h
    simp
  | cons l ls ih =>
    intro body ps h hpos hsum
    unfold rdMembers at h
    by_cases hc : (body.take l).head? = some 13
    · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp only [hc, ite_false, bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨fr, hd, ps1, h2, rfl⟩ := h
      simp only [List.sum_cons, List.length_cons] at hsum
      have hl : l ≤ body.length := by omega
      have hlen : (body.take l).length = l := by simp [hl]
      obtain ⟨a, b, c⟩ := ih (body.drop l) h2 (fun x hx => hpos x (by simp [hx])) (by simp; omega)
      refine ⟨by simp [hlen, a], ?_, ?_⟩
      · rw [List.sum_cons, List.take_add]
        simp [b]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨?_, hc, fr, hd⟩
          intro h0
          have := hpos l (by simp)
          rw [h0] at hlen
          simp at hlen; omega
        · exact c p hp

end Vinc.ConnCodec
