import Vinc.ConnectBase32

/-!
# The text form of a ticket: the theorems

* `Tk.text_roundtrip`: the text `to_text` writes reads back as the same ticket, in lower case and in upper case.
* `Tk.fromText_inv`: a text that reads is, up to the case of its letters, exactly the text `to_text` writes for the
  ticket it returned, and the ticket is a valid one; so a ticket has one spelling, and no other text is accepted.
* `Tk.toText_short`: a buffer that does not hold the text is refused with the length it needs.
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

theorem etail_lt (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) : ∀ s ∈ etail bs, s < 32 := by
  intro s hs
  match bs with
  | [] => simp [etail] at hs
  | [b0] =>
    have := hb b0 (by simp)
    simp only [etail, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> omega
  | [b0, b1] =>
    have := hb b0 (by simp); have := hb b1 (by simp)
    simp only [etail, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> omega
  | [b0, b1, b2] =>
    have := hb b0 (by simp); have := hb b1 (by simp); have := hb b2 (by simp)
    simp only [etail, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> omega
  | [b0, b1, b2, b3] =>
    have := hb b0 (by simp); have := hb b1 (by simp); have := hb b2 (by simp); have := hb b3 (by simp)
    simp only [etail, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | _ :: _ :: _ :: _ :: _ :: _ => simp [etail] at hs

theorem symsOf_lt (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) : ∀ s ∈ symsOf bs, s < 32 := by
  induction bs using symsOf.induct with
  | case1 b0 b1 b2 b3 b4 rest ih =>
    intro s hs
    simp only [symsOf, List.mem_append] at hs
    have h0 := hb b0 (by simp); have h1 := hb b1 (by simp); have h2 := hb b2 (by simp); have h3 := hb b3 (by simp)
    have h4 := hb b4 (by simp)
    rcases hs with hs | hs
    · simp only [e5, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · exact ih (fun b hb' => hb b (by simp [hb'])) s hs
  | case2 bs hne =>
    have : symsOf bs = etail bs := by
      rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl (hne b0 b1 b2 b3 b4 rest)
    rw [this]
    exact etail_lt bs hb

/-- The lower case of an ASCII letter (`to_ascii_lowercase`). -/
def lowerC (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c
/-- The upper case of an ASCII letter. -/
def upperC (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

theorem charSym_symChar (s : Nat) (h : s < 32) : charSym (symChar s) = some s := by
  have : ∀ s, s < 32 → charSym (symChar s) = some s := by decide
  exact this s h

theorem charSym_upper (s : Nat) (h : s < 32) : charSym (upperC (symChar s)) = some s := by
  have : ∀ s, s < 32 → charSym (upperC (symChar s)) = some s := by decide
  exact this s h

set_option maxRecDepth 100000 in
theorem charSym_tbl : ∀ c, c < 256 → (charSym c).all (fun s => decide (s < 32 ∧ lowerC c = symChar s)) = true := by
  decide

theorem charSym_big (c : Nat) (h : 256 ≤ c) : charSym c = none := by
  have h1 : ¬ (65 ≤ c ∧ c ≤ 90) := by omega
  have h2 : ¬ (97 ≤ c ∧ c ≤ 122) := by omega
  have h3 : ¬ (50 ≤ c ∧ c ≤ 55) := by omega
  simp [charSym, h1, h2, h3]

theorem charSym_inv (c s : Nat) (h : charSym c = some s) : s < 32 ∧ lowerC c = symChar s := by
  by_cases hc : c < 256
  · have := charSym_tbl c hc
    rw [h] at this
    simpa using this
  · rw [charSym_big c (by omega)] at h
    simp at h

theorem mapM_symChar (ss : List Nat) (h : ∀ s ∈ ss, s < 32) : (ss.map symChar).mapM charSym = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.mapM_cons, charSym_symChar s (h s (by simp)), ih']
    rfl

theorem mapM_upper (ss : List Nat) (h : ∀ s ∈ ss, s < 32) :
    ((ss.map symChar).map upperC).mapM charSym = some ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.mapM_cons, charSym_upper s (h s (by simp)), ih']
    rfl

theorem mapM_inv : ∀ (text ss : List Nat), text.mapM charSym = some ss →
    (∀ s ∈ ss, s < 32) ∧ text.map lowerC = ss.map symChar := by
  intro text
  induction text with
  | nil => intro ss h; simp [List.mapM_nil] at h; subst h; simp
  | cons c text ih =>
    intro ss h
    simp only [List.mapM_cons] at h
    cases hc : charSym c with
    | none => simp [hc] at h
    | some s =>
      cases ht : text.mapM charSym with
      | none => simp [hc, ht] at h
      | some ss' =>
        simp [hc, ht] at h
        subst h
        obtain ⟨h1, h2⟩ := charSym_inv c s hc
        obtain ⟨h3, h4⟩ := ih ss' ht
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact h1
          · exact h3 x hx
        · simp [h2, h4]

theorem Tk.bytes_byte (t : Tk) (hv : t.valid) : ∀ b ∈ t.bytes, b < 256 := by
  obtain ⟨hn, hbn, hhm, hna, hal⟩ := hv
  obtain ⟨node, home, addrs⟩ := t
  simp only at *
  intro b hb
  simp only [Tk.bytes, Tk.homeBytes, Tk.flags, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (((rfl | rfl) | hb) | hb) | hb
  · omega
  · cases home <;> simp [Tk.flags] <;> omega
  · exact hbn b hb
  · cases home with
    | none => simp at hb
    | some h => exact (hhm h rfl).2 b hb
  · simp only [List.mem_flatten] at hb
    obtain ⟨a, ha, hba⟩ := hb
    exact (hal a ha).2 b hba

theorem flatten_len_le : ∀ (addrs : List (List Nat)), (∀ a ∈ addrs, a.length ≤ 19) →
    addrs.flatten.length ≤ 19 * addrs.length
  | [], _ => by simp
  | a :: as, h => by
    have h1 := h a (by simp)
    have h2 := flatten_len_le as (fun x hx => h x (by simp [hx]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem Tk.bytes_length_le (t : Tk) (hv : t.valid) : t.bytes.length ≤ 144 := by
  obtain ⟨hn, hbn, hhm, hna, hal⟩ := hv
  obtain ⟨node, home, addrs⟩ := t
  simp only at *
  have hnl : node.length = 33 := by
    rcases node with _ | ⟨t0, bs⟩
    · exact absurd hn (by simp [NodeOk])
    · obtain ⟨_, _, h3⟩ := hn; simp [h3]
  have hhl : (home.getD []).length ≤ 33 := by
    cases home with
    | none => simp
    | some h =>
      obtain ⟨hh1, _⟩ := hhm h rfl
      rcases h with _ | ⟨t0, bs⟩
      · exact absurd hh1 (by simp [NodeOk])
      · obtain ⟨_, _, h3⟩ := hh1; simp [h3]
  have hal19 : ∀ a ∈ addrs, a.length ≤ 19 := by
    intro a ha
    obtain ⟨hk, _⟩ := hal a ha
    rcases hk with ⟨ip, pt, rfl, h1, h2⟩ | ⟨ip, pt, rfl, h1, h2⟩ <;> simp [h1, h2]
  have hsum : addrs.flatten.length ≤ 19 * addrs.length := flatten_len_le addrs hal19
  simp only [Tk.bytes, Tk.homeBytes, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Decoding the symbols of a byte string of at most 144 bytes returns it. -/
theorem b32_roundtrip (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (hl : bs.length ≤ 144) :
    b32dec (b32Of bs) 0 0 [] = .ok bs := by
  rw [b32Of_eq bs hb, dec_syms bs hb 0 [] (by simpa using hl)]
  simp

/-- A symbol string that decodes is the symbols of the bytes it returned. -/
theorem b32dec_inv (ss bs : List Nat) (hs : ∀ s ∈ ss, s < 32) (h : b32dec ss 0 0 [] = .ok bs) :
    (∀ b ∈ bs, b < 256) ∧ ss = b32Of bs := by
  obtain ⟨ts, hts, hb, hbs⟩ := dec_inv ss.length ss (Nat.le_refl _) hs 0 [] bs h
  simp only [List.nil_append] at hbs
  subst hbs
  exact ⟨hb, by rw [b32Of_eq _ hb]; exact hts⟩

/-- The text `to_text` writes. -/
theorem Tk.toText_ok (cap : Nat) (t : Tk) (hc : ((b32Of t.bytes).map symChar).length ≤ cap) :
    t.toText cap = .ok ((b32Of t.bytes).map symChar) := by
  have hc2 : (b32Of t.bytes).length ≤ cap := by simpa using hc
  simp [Tk.toText, hc2]

/-- A buffer too small is refused with the length it would need. -/
theorem Tk.toText_short (cap : Nat) (t : Tk) (hc : cap < ((b32Of t.bytes).map symChar).length) :
    t.toText cap = .error (.wire (.small (cap + 1))) := by
  simp only [Tk.toText]
  rw [if_neg (by omega)]

theorem Tk.fromText_of_syms (text : List Nat) (ss : List Nat) (t : Tk) (hs : text.mapM charSym = some ss)
    (hb : b32dec ss 0 0 [] = .ok t.bytes) (hp : Tk.parse t.bytes = .ok t) : Tk.fromText text = .ok t := by
  simp [Tk.fromText, hs, hb, hp, bind, Except.bind]

/-- The text of a ticket reads back as the ticket, in lower case and in upper case. -/
theorem Tk.text_roundtrip (t : Tk) (hv : t.valid) (cap : Nat) (hc : ((b32Of t.bytes).map symChar).length ≤ cap) :
    t.toText cap = .ok ((b32Of t.bytes).map symChar) ∧
      Tk.fromText ((b32Of t.bytes).map symChar) = .ok t ∧
      Tk.fromText (((b32Of t.bytes).map symChar).map upperC) = .ok t := by
  have hby := Tk.bytes_byte t hv
  have hsy := symsOf_lt t.bytes hby
  have hss : ∀ s ∈ b32Of t.bytes, s < 32 := by rw [b32Of_eq _ hby]; exact hsy
  have hdec := b32_roundtrip t.bytes hby (Tk.bytes_length_le t hv)
  have hpar := Tk.parse_bytes t hv
  refine ⟨Tk.toText_ok cap t hc, ?_, ?_⟩
  · exact Tk.fromText_of_syms _ _ t (mapM_symChar _ hss) hdec hpar
  · exact Tk.fromText_of_syms _ _ t (mapM_upper _ hss) hdec hpar

/-- A text that reads is, up to the case of its letters, the text of the ticket it returned, and the ticket is valid. -/
theorem Tk.fromText_inv (text : List Nat) (t : Tk) (h : Tk.fromText text = .ok t) :
    t.valid ∧ text.map lowerC = (b32Of t.bytes).map symChar := by
  unfold Tk.fromText at h
  cases hm : text.mapM charSym with
  | none => simp [hm] at h
  | some ss =>
    simp only [hm, bind, Except.bind] at h
    cases hd : b32dec ss 0 0 [] with
    | error e => simp [hd] at h
    | ok bs =>
      simp only [hd] at h
      obtain ⟨hs, hmap⟩ := mapM_inv text ss hm
      obtain ⟨hb, hss⟩ := b32dec_inv ss bs hs hd
      obtain ⟨hv, hbytes⟩ := Tk.parse_inv h hb
      refine ⟨hv, ?_⟩
      rw [hmap, hss, hbytes]

end Vinc.ConnCodec
