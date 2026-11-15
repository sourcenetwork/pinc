import Pinc.Axioms

/-!
# The spill chunk of a range set

The story: a stream keeps the ranges of bytes it has stored (or that were acknowledged, or declared lost) in a small
array inside the stream. When scattered losses leave more holes than that array holds, the set moves into one 16 KiB
chunk of the session's buffer pool (`pinc-transport/src/stream/ranges.rs`, `RangeSet::edit`). There each interval is
written as 16 bytes: its start, then its end, each as eight little-endian bytes (`BytesMut::put`), and read back the
same way (`decode`). What must never happen: an interval read back differs from the one written, or the chunk is too
small for the intervals the set promises to hold.

This file models the bytes as `Nat`s below 256 and proves:
* `dec_enc`: eight little-endian bytes of a value below 2^64 read back as that value (`u64::to_le_bytes`, then
  `u64::from_le_bytes`);
* `enc_bytes`: the bytes written are bytes (below 256) and there are eight of them;
* `decodeIv_encodeIv`: an interval written as 16 bytes reads back as the same interval;
* `spill_fits`: [`SPILL`] intervals of 16 bytes fill one chunk exactly, so the spilled set never writes past it.
-/

namespace Pinc.TransportRangesSpill

/-- The bytes of one pool chunk (`CHUNK_SIZE`). -/
def chunkSize : Nat := 16384
/-- The bytes of one interval: two words of eight bytes (`IV`). -/
def iv : Nat := 16
/-- The intervals a spill chunk holds (`SPILL = CHUNK_SIZE / IV`). -/
def spill : Nat := chunkSize / iv

/-- The `k` low little-endian bytes of `w`: the lowest first, as `to_le_bytes` lays them out. -/
def enc : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, w => w % 256 :: enc k (w / 256)

/-- Read little-endian bytes back into a value, the lowest byte first, as `from_le_bytes` does. -/
def dec : List Nat → Nat
  | [] => 0
  | b :: rest => b + 256 * dec rest

/-- Reading back `k` written bytes gives the value modulo `256^k`: what `k` bytes can hold. -/
theorem dec_enc_mod (k w : Nat) : dec (enc k w) = w % 256 ^ k := by
  induction k generalizing w with
  | zero => simp [enc, dec, Nat.mod_one]
  | succ k ih =>
    -- the low byte, then the rest of the value one byte down
    simp only [enc, dec, ih]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

/-- `u64::to_le_bytes` then `u64::from_le_bytes`: a value below 2^64 reads back as itself. -/
theorem dec_enc (w : Nat) (h : w < 2 ^ 64) : dec (enc 8 w) = w := by
  rw [dec_enc_mod]
  -- 256^8 is 2^64, and a value below the modulus is its own remainder
  have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [this]
  exact Nat.mod_eq_of_lt h

/-- The written bytes are `k` bytes, each below 256. -/
theorem enc_bytes (k w : Nat) : (enc k w).length = k ∧ ∀ b ∈ enc k w, b < 256 := by
  induction k generalizing w with
  | zero => simp [enc]
  | succ k ih =>
    obtain ⟨hl, hb⟩ := ih (w / 256)
    refine ⟨by simp [enc, hl], ?_⟩
    intro b hm
    simp only [enc, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Nat.mod_lt _ (by decide)
    · exact hb b hm

/-- One interval as its 16 bytes: the start's eight, then the end's (`BytesMut::put`). -/
def encodeIv (s e : Nat) : List Nat := enc 8 s ++ enc 8 e

/-- The interval 16 bytes hold (`decode`): the first eight bytes are the start, the next eight the end. -/
def decodeIv (b : List Nat) : Nat × Nat := (dec (b.take 8), dec ((b.drop 8).take 8))

/-- An interval written into the chunk reads back as the same interval, for offsets below 2^64 (every `u64`). -/
theorem decodeIv_encodeIv (s e : Nat) (hs : s < 2 ^ 64) (he : e < 2 ^ 64) : decodeIv (encodeIv s e) = (s, e) := by
  -- each word is eight bytes
  have hl : (enc 8 s).length = 8 := (enc_bytes 8 s).1
  have hl2 : (enc 8 e).length = 8 := (enc_bytes 8 e).1
  unfold decodeIv encodeIv
  -- the first eight bytes are the start's, the rest are the end's, and the end's eight are all of them
  have h1 : (enc 8 s ++ enc 8 e).take 8 = enc 8 s := by
    first
      | exact List.take_left' hl
      | simp [List.take_append, hl]
  have h2 : (enc 8 s ++ enc 8 e).drop 8 = enc 8 e := by
    first
      | exact List.drop_left' hl
      | simp [List.drop_append, hl]
  have h3 : (enc 8 e).take 8 = enc 8 e := by
    first
      | exact List.take_of_length_le (Nat.le_of_eq hl2)
      | simp [hl2]
  rw [h1, h2, h3, dec_enc s hs, dec_enc e he]

/-- `SPILL` intervals of 16 bytes fill one chunk exactly: the spilled set never writes past its chunk. -/
theorem spill_fits : spill * iv = chunkSize ∧ spill = 1024 := by decide

end Pinc.TransportRangesSpill

#audit_axioms Pinc.TransportRangesSpill.dec_enc
#audit_axioms Pinc.TransportRangesSpill.enc_bytes
#audit_axioms Pinc.TransportRangesSpill.decodeIv_encodeIv
#audit_axioms Pinc.TransportRangesSpill.spill_fits
