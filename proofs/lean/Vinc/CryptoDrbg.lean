import Vinc.CryptoKdf

/-!
# The DRBG of `vinc-crypto` (`drbg.rs`) and its zeroization

A `ChaCha20` stream cipher with fast key erasure. The state is one 32-byte key. `fill n` reads the first `32 + n`
bytes of the stream of the key (zero nonce, counter 0): the first 32 bytes are the next key, the rest is the output.
`reseed e` XORs 32 bytes of entropy into the key. The stream is abstract (`stream key i` is byte `i` of
`ChaCha20(key, 0^12)`); the theorems are about how the code uses it.

The second part transcribes the control flow of `fill` and `reseed` as operations on named buffers, to show that no
buffer that held key material is left readable when they return (`Heap`).
-/

namespace Vinc.CryptoDrbg
open Vinc.CryptoKdf (Bytes)

/-- `MAX_FILL`. -/
def maxFill : Nat := 2 ^ 30

/-- The first `n` bytes of the stream of a key. -/
def ks (stream : Bytes → Nat → Nat) (key : Bytes) (n : Nat) : Bytes := (List.range n).map (stream key)

theorem ks_length (stream : Bytes → Nat → Nat) (key : Bytes) (n : Nat) : (ks stream key n).length = n := by
  simp [ks]

/-- The generator: the key. -/
structure D where
  key : Bytes
  deriving DecidableEq

/-- The only error of `fill`. -/
inductive Err where
  | inputTooLong
  deriving DecidableEq

/-- `Drbg::fill`: the new state and the result. -/
def fill (stream : Bytes → Nat → Nat) (d : D) (n : Nat) : D × Except Err Bytes :=
  if maxFill < n then (d, .error .inputTooLong)
  else
    let s := ks stream d.key (32 + n)
    (⟨s.take 32⟩, .ok (s.drop 32))

/-- `Drbg::reseed`. -/
def reseed (d : D) (e : Bytes) : D := ⟨List.zipWith (fun a b => a ^^^ b) d.key e⟩

/-- An operation of a run. -/
inductive Op where
  | fill (n : Nat)
  | reseed (e : Bytes)

/-- A run from a seed: the final state and the result of every `fill`. -/
def run (stream : Bytes → Nat → Nat) : List Op → D → D × List (Except Err Bytes)
  | [], d => (d, [])
  | .fill n :: ops, d =>
    let (d', r) := fill stream d n
    let (d'', rs) := run stream ops d'
    (d'', r :: rs)
  | .reseed e :: ops, d => run stream ops (reseed d e)

/-- The same seed and the same operations give the same state and the same outputs. -/
theorem run_deterministic (stream : Bytes → Nat → Nat) (ops : List Op) {d d' : D} (h : d = d') :
    run stream ops d = run stream ops d' := by subst h; rfl

/-! ## `fill` -/

/-- A request over `MAX_FILL` is refused with `InputTooLong` and the state is unchanged. -/
theorem fill_too_long (stream : Bytes → Nat → Nat) (d : D) (n : Nat) (h : maxFill < n) :
    fill stream d n = (d, .error .inputTooLong) := by simp [fill, h]

/-- Any other request succeeds, with exactly `n` bytes. -/
theorem fill_ok (stream : Bytes → Nat → Nat) (d : D) (n : Nat) (h : n ≤ maxFill) :
    ∃ out, (fill stream d n).2 = .ok out ∧ out.length = n := by
  refine ⟨(ks stream d.key (32 + n)).drop 32, ?_, ?_⟩
  · simp [fill, Nat.not_lt.mpr h]
  · simp [ks_length]

/-- The next key is the first 32 bytes of the stream; the output is the bytes after them, so no byte of the output
is a byte of the next key. -/
theorem fill_rekeys (stream : Bytes → Nat → Nat) (d : D) (n : Nat) (h : n ≤ maxFill) :
    (fill stream d n).1.key = ks stream d.key 32 ∧
    (fill stream d n).2 = .ok ((List.range n).map (fun i => stream d.key (32 + i))) := by
  simp only [fill, Nat.not_lt.mpr h, ite_false, ks]
  refine ⟨?_, ?_⟩
  · rw [List.range_add, List.map_append, List.take_left']
    simp
  · congr 1
    rw [List.range_add, List.map_append, List.drop_left']
    · simp [List.map_map, List.range_eq_range']
    · simp

/-- The `ChaCha20` stream wrapper serves `2^32 - 1` blocks of 64 bytes (it refuses the last block of its 32-bit
counter), and a call reads `32 + n` bytes at most: the `try_write_keystream` calls of `fill` cannot fail for a
request within `MAX_FILL`, so the error path that wipes the output is unreachable. -/
theorem fill_within_stream (n : Nat) (h : n ≤ maxFill) :
    32 + n ≤ (2 ^ 32 - 1) * 64 ∧ (32 + n + 63) / 64 ≤ 2 ^ 32 - 1 := by
  unfold maxFill at h
  constructor <;> omega

/-- The bound is tight in the other direction: the limit of the check is far below the stream's, and one byte over
the limit is refused before any block is made. -/
theorem maxFill_lt_stream : maxFill + 32 < (2 ^ 32 - 1) * 64 := by unfold maxFill; omega

/-- Two fills with the same key read the same bytes of the same stream: their outputs agree wherever both have a
byte, so an output can repeat only if a key repeats. -/
theorem same_key_same_output (stream : Bytes → Nat → Nat) (k : Bytes) (n m i : Nat) (hn : i < n) (hm : i < m) :
    ((ks stream k (32 + n)).drop 32)[i]? = ((ks stream k (32 + m)).drop 32)[i]? := by
  simp [ks, hn, hm]

/-! ## `reseed` -/

theorem xor_lt_256 {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  have := Nat.xor_lt_two_pow (n := 8) (by simpa using ha) (by simpa using hb)
  simpa using this

/-- Reseeding twice with the same entropy restores the key. -/
theorem reseed_involutive (d : D) (e : Bytes) (h : d.key.length = e.length) : reseed (reseed d e) e = d := by
  cases d with
  | mk key =>
    simp only [reseed, D.mk.injEq]
    induction key generalizing e with
    | nil => simp
    | cons k ks ih =>
      cases e with
      | nil => simp at h
      | cons x xs =>
        simp only [List.zipWith_cons_cons, List.cons.injEq]
        refine ⟨?_, ih xs (by simpa using h)⟩
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Entropy order does not matter. -/
theorem reseed_comm (d : D) (e f : Bytes) (h1 : d.key.length = e.length) (h2 : d.key.length = f.length) :
    reseed (reseed d e) f = reseed (reseed d f) e := by
  cases d with
  | mk key =>
    simp only [reseed, D.mk.injEq]
    induction key generalizing e f with
    | nil => simp
    | cons k ks ih =>
      cases e with
      | nil => simp at h1
      | cons x xs =>
        cases f with
        | nil => simp at h2
        | cons y ys =>
          simp only [List.zipWith_cons_cons, List.cons.injEq]
          refine ⟨?_, ih xs ys (by simpa using h1) (by simpa using h2)⟩
          rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm x y]

/-- Zero entropy leaves the key unchanged. -/
theorem reseed_zero (d : D) : reseed d (List.replicate d.key.length 0) = d := by
  cases d with
  | mk key =>
    simp only [reseed, D.mk.injEq]
    induction key with
    | nil => simp
    | cons k ks ih => simpa [List.replicate_succ, Nat.xor_zero] using ih

/-- Reseeding keeps the length of the key when the entropy has the same length. -/
theorem reseed_length (d : D) (e : Bytes) (h : d.key.length = e.length) : (reseed d e).key.length = d.key.length := by
  simp [reseed, h]

theorem xor_fixed_zero : ∀ (key e : Bytes), key.length = e.length → List.zipWith (fun a b => a ^^^ b) key e = key →
    ∀ b ∈ e, b = 0
  | [], e, h, _ => by cases e <;> simp_all
  | k :: ks, [], h, _ => by simp at h
  | k :: ks, x :: xs, h, hr => by
    simp only [List.zipWith_cons_cons, List.cons.injEq] at hr
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · have := congrArg (fun t => t ^^^ k) hr.1
      rw [Nat.xor_comm k b, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
      exact this
    · exact xor_fixed_zero ks xs (by simpa using h) hr.2 b hb

/-- A nonzero entropy always changes the key. -/
theorem reseed_nonzero_changes (d : D) (e : Bytes) (h : d.key.length = e.length) (hne : ∃ b ∈ e, b ≠ 0) :
    reseed d e ≠ d := by
  intro hr
  obtain ⟨b, hb, hb0⟩ := hne
  exact hb0 (xor_fixed_zero d.key e h (by simpa [reseed] using congrArg D.key hr) b hb)

/-- For fixed entropy, reseeding is a bijection of the keys: a uniformly random key stays uniformly random. -/
theorem reseed_injective_key (d d' : D) (e : Bytes) (h1 : d.key.length = e.length) (h2 : d'.key.length = e.length)
    (h : reseed d e = reseed d' e) : d = d' := by
  have := congrArg (fun x => reseed x e) h
  rw [reseed_involutive d e h1, reseed_involutive d' e h2] at this
  exact this

/-- The stream is a pseudo-random function of the key: bytes of output determine the key (a hypothesis on the
abstract stream, the collision resistance of `ChaCha20`'s output, never an axiom). -/
def StreamInj (stream : Bytes → Nat → Nat) : Prop :=
  ∀ k k' m, 1 ≤ m → (ks stream k (32 + m)).drop 32 = (ks stream k' (32 + m)).drop 32 → k = k'

/-- A reseed with nonzero entropy changes what the next `fill` returns: no output is repeated across a reseed. -/
theorem reseed_fresh_output {stream : Bytes → Nat → Nat} (hs : StreamInj stream) (d : D) (e : Bytes)
    (h : d.key.length = e.length) (hne : ∃ b ∈ e, b ≠ 0) (m : Nat) (hm : 1 ≤ m) (hmax : m ≤ maxFill) :
    (fill stream (reseed d e) m).2 ≠ (fill stream d m).2 := by
  intro heq
  simp only [fill, Nat.not_lt.mpr hmax, ite_false, Except.ok.injEq] at heq
  have := hs _ _ m hm heq
  have h2 : reseed d e = d := by
    cases d with
    | mk k =>
      simp only [reseed] at this ⊢
      rw [this]
  exact reseed_nonzero_changes d e h hne h2

/-! ## Zeroization

The buffers that hold key material in `fill` and `reseed` are the field `key` (a `Secret`, wiped when replaced or
dropped, `ZeroizeOnDrop`), the local `next`, the cipher state (wiped on drop: the `zeroize` feature of `chacha20`) and
the caller's `out`. A `Heap` maps a buffer name to its bytes, or to `none` once the buffer is dropped (and so wiped).
`set` writes a buffer (an assignment to a `Secret` field drops the old value, which wipes it), `wipe` is
`Zeroize::zeroize`, `drop` the end of the scope of a `ZeroizeOnDrop` value. -/

abbrev Heap := String → Option Bytes

def Heap.set (h : Heap) (c : String) (v : Bytes) : Heap := fun x => if x = c then some v else h x
def Heap.wipe (h : Heap) (c : String) : Heap := fun x => if x = c then (h c).map (fun v => List.replicate v.length 0) else h x
def Heap.drop (h : Heap) (c : String) : Heap := fun x => if x = c then none else h x

/-- Every buffer except those listed is dropped or all zeros. -/
def Clean (h : Heap) (keep : List String) : Prop := ∀ c, c ∉ keep → ∀ v, h c = some v → ∀ b ∈ v, b = 0

/-- `Drbg::fill`, successful path, with `s` the first `32 + n` bytes of the stream: the buffers afterwards. -/
def fillOk (h : Heap) (s : Bytes) : Heap :=
  let h := h.set "cipher" (h "key" |>.getD [])
  let h := h.set "next" (s.take 32)
  let h := h.set "out" (s.drop 32)
  let h := h.set "key" (s.take 32)
  let h := h.wipe "next"
  h.drop "cipher"

/-- `Drbg::fill`, the error path of `try_write_keystream` (unreachable, see `fill_within_stream`): the output is wiped
and so is `next`; the key is unchanged. -/
def fillErr (h : Heap) (s : Bytes) : Heap :=
  let h := h.set "cipher" (h "key" |>.getD [])
  let h := h.set "next" (s.take 32)
  let h := h.wipe "out"
  let h := h.wipe "next"
  h.drop "cipher"

/-- `Drbg::reseed`: copy the key, XOR the entropy, assign (the old key is dropped), wipe the copy. -/
def reseedHeap (h : Heap) (x : Bytes) : Heap :=
  let h := h.set "next" (h "key" |>.getD [])
  let h := h.set "next" x
  let h := h.set "key" x
  h.wipe "next"

/-- After a successful `fill`, only the key and the caller's output hold bytes: `next` is zero and the cipher is gone. -/
theorem fill_clean (h : Heap) (s : Bytes) (hc : Clean h ["key", "out"]) : Clean (fillOk h s) ["key", "out"] := by
  intro x hx w hw b hb
  have hk : x ≠ "key" := fun e => hx (by simp [e])
  have ho : x ≠ "out" := fun e => hx (by simp [e])
  by_cases e1 : x = "cipher"
  · simp [fillOk, Heap.drop, e1] at hw
  by_cases e2 : x = "next"
  · simp [fillOk, Heap.drop, Heap.wipe, Heap.set, e2, e1, hk, ho] at hw
    subst hw
    exact List.eq_of_mem_replicate hb
  · simp [fillOk, Heap.drop, Heap.wipe, Heap.set, e1, e2, hk, ho] at hw
    exact hc x hx w hw b hb

/-- After the error path, only the key holds bytes (the output is wiped too). -/
theorem fillErr_clean (h : Heap) (s : Bytes) (hc : Clean h ["key", "out"]) : Clean (fillErr h s) ["key"] := by
  intro x hx w hw b hb
  have hk : x ≠ "key" := fun e => hx (by simp [e])
  by_cases e1 : x = "cipher"
  · simp [fillErr, Heap.drop, e1] at hw
  by_cases e2 : x = "next"
  · simp [fillErr, Heap.drop, Heap.wipe, Heap.set, e2, e1, hk] at hw
    subst hw
    exact List.eq_of_mem_replicate hb
  by_cases e3 : x = "out"
  · simp [fillErr, Heap.drop, Heap.wipe, Heap.set, e3, e1, e2, hk] at hw
    obtain ⟨v, hv, hw⟩ := hw
    subst hw
    exact List.eq_of_mem_replicate hb
  · simp [fillErr, Heap.drop, Heap.wipe, Heap.set, e1, e2, e3, hk] at hw
    exact hc x (by simp [e3, hk]) w hw b hb

/-- After `reseed`, only the key holds bytes: the copy of the key is wiped. -/
theorem reseed_clean (h : Heap) (x : Bytes) (hc : Clean h ["key", "out"]) : Clean (reseedHeap h x) ["key", "out"] := by
  intro y hy w hw b hb
  have hk : y ≠ "key" := fun e => hy (by simp [e])
  by_cases e2 : y = "next"
  · simp [reseedHeap, Heap.wipe, Heap.set, e2, hk] at hw
    subst hw
    exact List.eq_of_mem_replicate hb
  · simp [reseedHeap, Heap.wipe, Heap.set, e2, hk] at hw
    exact hc y hy w hw b hb

end Vinc.CryptoDrbg

#audit_axioms Vinc.CryptoDrbg.fill_too_long
#audit_axioms Vinc.CryptoDrbg.fill_rekeys
#audit_axioms Vinc.CryptoDrbg.fill_within_stream
#audit_axioms Vinc.CryptoDrbg.same_key_same_output
#audit_axioms Vinc.CryptoDrbg.reseed_involutive
#audit_axioms Vinc.CryptoDrbg.reseed_comm
#audit_axioms Vinc.CryptoDrbg.reseed_nonzero_changes
#audit_axioms Vinc.CryptoDrbg.reseed_injective_key
#audit_axioms Vinc.CryptoDrbg.reseed_fresh_output
#audit_axioms Vinc.CryptoDrbg.fill_clean
#audit_axioms Vinc.CryptoDrbg.fillErr_clean
#audit_axioms Vinc.CryptoDrbg.reseed_clean
