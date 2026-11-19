import Pinc.Varint

/-!
# The value wire: errors, big-endian fields, the Reader and the Writer

The common part of the models of `crates/pinc-values/src/wire.rs`. A byte string is a `List Nat` whose
elements are below 256 (`Varint.ValidBytes`, the convention of `Pinc.Varint`). A field of `n` bytes is read and
written big-endian (`beVal`, `beBytes`), so a `u8`, `u16`, `u32` and `u64` field is a `Nat` below `256 ^ n` and the
machine arithmetic is exact: the code never adds, subtracts or shifts a field.

`Err` is `pinc_wire::WireError` as far as the value wire can reach it. `readBytes`, `readBe` and `readVarint` are the
`Reader` methods of `pinc-wire` (`read_bytes`, `read_u8` ... `read_u64`, `read_varint`) on the bytes not yet consumed;
`put` is a `Writer` write that checks the room first and changes nothing on failure.
-/

namespace Pinc.ValuesWire

open Pinc

/-- `WireError`: the variants the value wire produces. -/
inductive Err where
  | truncated (needed : Nat)
  | bufferTooSmall (needed : Nat)
  | tooLong
  | overflow
  | nonMinimal
  | unexpected (msg : String)
  deriving DecidableEq, Repr

/-- A varint error as the `WireError` the `Reader` reports; `varint::decode`'s `Truncated` always needs 1. -/
def varErr : Varint.Error → Err
  | .tooLong => .tooLong
  | .truncated => .truncated 1
  | .nonMinimal => .nonMinimal
  | .overflow => .overflow
  | .bufferTooSmall n => .bufferTooSmall n

/-! ## Big-endian fields -/

/-- `u64::from_be_bytes` and its narrower kin: the big-endian value of a byte string. -/
def beVal (bs : List Nat) : Nat := bs.foldl (fun a b => a * 256 + b) 0

/-- `v.to_be_bytes()` as `n` bytes (the value taken modulo `256 ^ n`, which the types of the code make a no-op). -/
def beBytes : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => beBytes n (v / 256) ++ [v % 256]

/-- Induction from the end of a list. -/
theorem snoc_ind {P : List Nat → Prop} (h0 : P []) (hs : ∀ l b, P l → P (l ++ [b])) : ∀ l, P l := by
  have key : ∀ n l, List.length l = n → P l := by
    intro n
    induction n with
    | zero => intro l h; rw [List.length_eq_zero_iff.mp h]; exact h0
    | succ n ih =>
      intro l h
      rcases List.eq_nil_or_concat l with rfl | ⟨l', b, rfl⟩
      · simp at h
      · rw [List.concat_eq_append] at h ⊢
        exact hs l' b (ih l' (by simpa using h))
  exact fun l => key _ l rfl

theorem beVal_nil : beVal [] = 0 := rfl

theorem beVal_append_single (bs : List Nat) (b : Nat) : beVal (bs ++ [b]) = beVal bs * 256 + b := by
  simp [beVal, List.foldl_append]

theorem length_beBytes (n v : Nat) : (beBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

theorem beBytes_valid (n v : Nat) : Varint.ValidBytes (beBytes n v) := by
  induction n generalizing v with
  | zero => intro b hb; simp [beBytes] at hb
  | succ n ih =>
    intro b hb
    simp only [beBytes, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | hb
    · exact ih _ b hb
    · omega

theorem beVal_beBytes (n v : Nat) : beVal (beBytes n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [beBytes, beVal, Nat.mod_one]
  | succ n ih =>
    rw [beBytes, beVal_append_single, ih, Nat.pow_succ', Nat.mod_mul]
    generalize v / 256 % 256 ^ n = q
    omega

/-- A byte string of `n` bytes is the big-endian bytes of its value. -/
theorem beBytes_beVal (bs : List Nat) (hv : Varint.ValidBytes bs) : beBytes bs.length (beVal bs) = bs := by
  induction bs using snoc_ind with
  | h0 => rfl
  | hs bs b ih =>
    have hb : b < 256 := hv b (by simp)
    have hbs : Varint.ValidBytes bs := fun c hc => hv c (by simp [hc])
    rw [List.length_append, List.length_singleton, beBytes, beVal_append_single]
    have e1 : (beVal bs * 256 + b) / 256 = beVal bs := by omega
    have e2 : (beVal bs * 256 + b) % 256 = b := by omega
    rw [e1, e2, ih hbs]

theorem beBytes_beVal_of_length (n : Nat) (bs : List Nat) (hv : Varint.ValidBytes bs) (hl : bs.length = n) :
    beBytes n (beVal bs) = bs := by
  subst hl; exact beBytes_beVal bs hv

theorem beVal_lt (bs : List Nat) (hv : Varint.ValidBytes bs) : beVal bs < 256 ^ bs.length := by
  induction bs using snoc_ind with
  | h0 => simp [beVal]
  | hs bs b ih =>
    have hb : b < 256 := hv b (by simp)
    have hbs : Varint.ValidBytes bs := fun c hc => hv c (by simp [hc])
    have := ih hbs
    rw [beVal_append_single, List.length_append, List.length_singleton, Nat.pow_succ]
    generalize 256 ^ bs.length = P at this ⊢
    have : (beVal bs + 1) * 256 ≤ P * 256 := Nat.mul_le_mul_right 256 this
    omega

/-- Two byte strings of the same length with the same big-endian value are equal. -/
theorem beVal_inj (a b : List Nat) (ha : Varint.ValidBytes a) (hb : Varint.ValidBytes b)
    (hl : a.length = b.length) (h : beVal a = beVal b) : a = b := by
  have h1 := beBytes_beVal a ha
  have h2 := beBytes_beVal b hb
  rw [← h1, ← h2, hl, h]

theorem beVal_single (b : Nat) : beVal [b] = b := by simp [beVal]

theorem beVal_take_one (l : List Nat) (h : 0 < l.length) : beVal (l.take 1) = l.getD 0 0 := by
  rcases l with _ | ⟨a, l⟩
  · simp at h
  · simp [beVal]

theorem getD_drop_zero (l : List Nat) (k : Nat) : (l.drop k).getD 0 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take {l : List Nat} {m i : Nat} (h : i < m) : (l.take m).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem take_one_eq (l : List Nat) (h : 0 < l.length) : l.take 1 = [l.getD 0 0] := by
  rcases l with _ | ⟨a, l⟩
  · simp at h
  · simp

/-! ## The Reader -/

/-- What a `Reader` method returns: the value and the bytes left, or the error (nothing consumed). -/
abbrev Rd (α : Type) := Except Err (α × List Nat)

/-- `Reader::read_bytes`. -/
def readBytes (n : Nat) (rest : List Nat) : Rd (List Nat) :=
  if n ≤ rest.length then .ok (rest.take n, rest.drop n) else .error (.truncated (n - rest.length))

/-- `read_u8` (`n = 1`), `read_u16`, `read_u32`, `read_u64`: `n` bytes, big-endian. -/
def readBe (n : Nat) (rest : List Nat) : Rd Nat :=
  match readBytes n rest with
  | .ok (b, r) => .ok (beVal b, r)
  | .error e => .error e

/-- `Reader::read_varint`: `varint::decode` over the bytes left, then the bytes it took are consumed. -/
def readVarint (rest : List Nat) : Rd Nat :=
  match Varint.decode rest with
  | .ok (v, n) =>
    match readBytes n rest with
    | .ok (_, r) => .ok (v, r)
    | .error e => .error e
  | .error e => .error (varErr e)

theorem readBytes_ok {n : Nat} {rest : List Nat} (h : n ≤ rest.length) :
    readBytes n rest = .ok (rest.take n, rest.drop n) := by
  simp [readBytes, h]

theorem readBytes_err {n : Nat} {rest : List Nat} (h : ¬ n ≤ rest.length) :
    readBytes n rest = .error (.truncated (n - rest.length)) := by
  simp [readBytes, h]

theorem readBe_ok {n : Nat} {rest : List Nat} (h : n ≤ rest.length) :
    readBe n rest = .ok (beVal (rest.take n), rest.drop n) := by
  simp [readBe, readBytes_ok h]

theorem readBe_err {n : Nat} {rest : List Nat} (h : ¬ n ≤ rest.length) :
    readBe n rest = .error (.truncated (n - rest.length)) := by
  simp [readBe, readBytes_err h]

theorem readBe_append {n : Nat} (bs rest : List Nat) (h : bs.length = n) :
    readBe n (bs ++ rest) = .ok (beVal bs, rest) := by
  subst h
  rw [readBe_ok (by simp)]
  simp

theorem readBe_single (x : Nat) : readBe 1 [x] = .ok (x, []) := by
  simp [readBe, readBytes, beVal]

theorem readBytes_append {n : Nat} (bs rest : List Nat) (h : bs.length = n) :
    readBytes n (bs ++ rest) = .ok (bs, rest) := by
  subst h
  rw [readBytes_ok (by simp)]
  simp

/-- A varint the decoder accepts is inside the input. -/
theorem decode_n_le (input : List Nat) (hv : Varint.ValidBytes input) (v n : Nat)
    (h : Varint.decode input = .ok (v, n)) : n ≤ input.length := by
  obtain ⟨h1, h2⟩ := Varint.decode_canonical input hv v n h
  have := congrArg List.length h1
  rw [List.length_take, Varint.length_encodeBytes, ← h2] at this
  omega

theorem readVarint_ok {rest : List Nat} (hv : Varint.ValidBytes rest) {v n : Nat}
    (h : Varint.decode rest = .ok (v, n)) : readVarint rest = .ok (v, rest.drop n) := by
  simp [readVarint, h, readBytes_ok (decode_n_le rest hv v n h)]

theorem readVarint_err {rest : List Nat} {e : Varint.Error} (h : Varint.decode rest = .error e) :
    readVarint rest = .error (varErr e) := by
  simp [readVarint, h]

/-! ## The Writer -/

/-- A write of `bytes` at the start of `out`: the room is checked first, so a failure changes nothing. Returns the
bytes written (or the error) and the buffer afterwards. -/
def put (bytes out : List Nat) : Except Err Nat × List Nat :=
  if bytes.length ≤ out.length then (.ok bytes.length, bytes ++ out.drop bytes.length)
  else (.error (.bufferTooSmall (bytes.length - out.length)), out)

theorem put_ok {bytes out : List Nat} (h : bytes.length ≤ out.length) :
    put bytes out = (.ok bytes.length, bytes ++ out.drop bytes.length) := by
  simp [put, h]

theorem put_err {bytes out : List Nat} (h : ¬ bytes.length ≤ out.length) :
    put bytes out = (.error (.bufferTooSmall (bytes.length - out.length)), out) := by
  simp [put, h]

end Pinc.ValuesWire

#audit_axioms Pinc.ValuesWire.beVal_beBytes
#audit_axioms Pinc.ValuesWire.beBytes_beVal
#audit_axioms Pinc.ValuesWire.beVal_lt
