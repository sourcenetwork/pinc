import Vinc.MembershipCodec

/-!
# Hub stream codec: numbers and the reader

Big-endian numbers (`beBytes`, `beN`) and the reader of `vinc-wire`, the lemmas the codec theorems stand on:
`beBytes k` writes `k` bytes and `beN` reads them back, in both directions for bytes.
-/

namespace Vinc.MemCodec

theorem bind_ok {α β : Type} (x : Except Err α) (f : α → Except Err β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

theorem foldl_acc (x : Nat) (l : List Nat) :
    l.foldl (fun a b => a * 256 + b) x = x * 256 ^ l.length + beN l := by
  induction l generalizing x with
  | nil => simp [beN]
  | cons y l ih =>
    have h2 : beN (y :: l) = y * 256 ^ l.length + beN l := by
      simp only [beN, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
      exact ih y
    rw [List.foldl_cons, ih, h2, List.length_cons, Nat.pow_succ, Nat.add_mul]
    ac_rfl

theorem beN_append (a b : List Nat) : beN (a ++ b) = beN a * 256 ^ b.length + beN b := by
  simp only [beN, List.foldl_append]
  exact foldl_acc _ _

theorem beBytes_length (k v : Nat) : (beBytes k v).length = k := by
  induction k generalizing v with
  | zero => simp [beBytes]
  | succ k ih => simp [beBytes, ih]

theorem beBytes_byte (k v : Nat) : Byte (beBytes k v) := by
  induction k generalizing v with
  | zero => simp [beBytes, Byte]
  | succ k ih =>
    intro b hb
    simp only [beBytes, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact ih _ b hb
    · exact Nat.mod_lt _ (by omega)

theorem beN_beBytes (k v : Nat) : beN (beBytes k v) = v % 256 ^ k := by
  induction k generalizing v with
  | zero => simp [beBytes, beN, Nat.mod_one]
  | succ k ih =>
    simp only [beBytes]
    rw [beN_append, ih]
    simp only [List.length_singleton, beN, List.foldl_cons, List.foldl_nil, Nat.pow_succ]
    rw [Nat.mul_comm (256 ^ k) 256, Nat.mod_mul (a := 256) (b := 256 ^ k)]
    generalize v / 256 % 256 ^ k = q
    omega

theorem beBytes_beN (k : Nat) (bs : List Nat) (h : bs.length = k) (hb : Byte bs) :
    beBytes k (beN bs) = bs := by
  induction k generalizing bs with
  | zero => cases bs <;> simp_all [beBytes]
  | succ k ih =>
    rcases List.eq_nil_or_concat bs with rfl | ⟨L, b, rfl⟩
    · simp at h
    simp only [List.concat_eq_append] at h hb ⊢
    · have hL : L.length = k := by simpa using h
      have hbL : Byte L := fun x hx => hb x (by simp [hx])
      have hbb : b < 256 := hb b (by simp)
      have hn : beN (L ++ [b]) = beN L * 256 + b := by
        rw [beN_append]; simp [beN]
      simp only [beBytes, hn]
      have h1 : (beN L * 256 + b) / 256 = beN L := by omega
      have h2 : (beN L * 256 + b) % 256 = b := by omega
      rw [h1, h2, ih L hL hbL]

theorem rdBytes_app (a r : List Nat) : rdBytes a.length (a ++ r) = .ok (a, r) := by
  simp [rdBytes]

theorem rdBE_app (k : Nat) (a r : List Nat) (h : a.length = k) : rdBE k (a ++ r) = .ok (beN a, r) := by
  subst h; simp [rdBE, rdBytes_app, bind, Except.bind, pure, Except.pure]

theorem rdBE_beBytes (k v : Nat) (r : List Nat) :
    rdBE k (beBytes k v ++ r) = .ok (v % 256 ^ k, r) := by
  rw [rdBE_app k _ r (beBytes_length k v), beN_beBytes]

theorem rdBytes_zero (r : List Nat) : rdBytes 0 r = .ok ([], r) := by simp [rdBytes]
theorem rdBE_beBytes_lt (k v : Nat) (r : List Nat) (h : v < 256 ^ k) :
    rdBE k (beBytes k v ++ r) = .ok (v, r) := by
  rw [rdBE_beBytes, Nat.mod_eq_of_lt h]

/-- A successful `rdBytes` splits the input. -/
theorem rdBytes_ok {n r a r'} (h : rdBytes n r = .ok (a, r')) : r = a ++ r' ∧ a.length = n := by
  unfold rdBytes at h
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h
    simp_all
  · simp at h

theorem rdBE_ok {k r v r'} (h : rdBE k r = .ok (v, r')) : ∃ a, r = a ++ r' ∧ a.length = k ∧ v = beN a := by
  unfold rdBE at h
  cases hr : rdBytes k r with
  | error e => simp [hr, bind, Except.bind] at h
  | ok p =>
    obtain ⟨a, r2⟩ := p
    simp [hr, bind, Except.bind, pure, Except.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := rdBytes_ok hr
    exact ⟨a, h1, h2, rfl⟩

theorem rdU8_ok {r x r'} (h : rdU8 r = .ok (x, r')) : r = x :: r' := by
  cases r with
  | nil => simp [rdU8] at h
  | cons y t => simp [rdU8] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem beN_cons (y : Nat) (l : List Nat) : beN (y :: l) = y * 256 ^ l.length + beN l := by
  simp only [beN, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  exact foldl_acc y l

theorem beN_lt (bs : List Nat) (hb : Byte bs) : beN bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [beN]
  | cons y l ih =>
    have hy : y < 256 := hb y (by simp)
    have hl := ih (fun x hx => hb x (by simp [hx]))
    rw [beN_cons, List.length_cons, Nat.pow_succ]
    have h1 : y * 256 ^ l.length + beN l < y * 256 ^ l.length + 256 ^ l.length := by omega
    have h2 : y * 256 ^ l.length + 256 ^ l.length = (y + 1) * 256 ^ l.length := by
      rw [Nat.add_mul, Nat.one_mul]
    have h3 : (y + 1) * 256 ^ l.length ≤ 256 * 256 ^ l.length := Nat.mul_le_mul_right _ hy
    rw [Nat.mul_comm (256 ^ l.length) 256]
    omega

theorem p256_8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
theorem p256_2 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide
theorem p256_4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide

end Vinc.MemCodec
