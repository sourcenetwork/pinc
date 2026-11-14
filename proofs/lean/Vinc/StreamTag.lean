import Vinc.Axioms

/-!
# The stream tag

A step-for-step model of `write_tag` and `read_tag` of `vinc/src/protocol.rs`: a tag is written as one length byte
(1 to 64) followed by the tag bytes, at the start of a stream.

`write_tag` refuses (`Config`, nothing written) a tag that is empty or longer than 64 bytes. `read_tag` reads one byte
(`read_exact`; the stream ending first is the stream's error, `eof` here), refuses a length outside 1 to 64 as `Config`
having read only that byte, and otherwise reads exactly that many bytes (`eof` if the stream ends first). It never
reads past the tag: the bytes after it stay in the stream, which is why `readTag` returns them (`rest`). Trailing
bytes are therefore not refused, they are the next thing on the stream.

Bytes are `Nat`s (below 256 for a tag, as in `ValidBytes`), so the length byte `u8::try_from(tag.len())` is exact.
-/

namespace Vinc.StreamTag

/-- The longest stream tag (`MAX_TAG`). -/
def maxTag : Nat := 64

/-- The refusals of `read_tag`: the length byte is out of range (`Config`), or the stream ended first. -/
inductive Err where
  | config
  | eof
  deriving DecidableEq, Repr

/-- `write_tag`: the bytes written, or `none` for the `Config` refusal (nothing written). -/
def writeTag (tag : List Nat) : Option (List Nat) :=
  if 1 ≤ tag.length ∧ tag.length ≤ maxTag then some (tag.length :: tag) else none

/-- What `read_tag` returns on a stream that holds exactly the given bytes and then ends, with the bytes still
unread. -/
inductive Rd where
  | ok (tag rest : List Nat)
  | err (e : Err) (rest : List Nat)
  deriving DecidableEq, Repr

/-- `read_tag`. -/
def readTag : List Nat → Rd
  | [] => .err .eof []
  | n :: r =>
    if 1 ≤ n ∧ n ≤ maxTag then
      if n ≤ r.length then .ok (r.take n) (r.drop n) else .err .eof []
    else .err .config r

/-- `write_tag` refuses exactly the tags of length 0 and over 64. -/
theorem writeTag_isSome (t : List Nat) : (writeTag t).isSome = true ↔ 1 ≤ t.length ∧ t.length ≤ maxTag := by
  unfold writeTag
  split <;> simp_all

/-- Round trip: reading what `write_tag` wrote returns the tag and leaves whatever follows unread. -/
theorem readTag_writeTag (t : List Nat) (b rest : List Nat) (h : writeTag t = some b) :
    readTag (b ++ rest) = .ok t rest := by
  unfold writeTag at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h
    subst h
    simp [readTag, hl.1, hl.2]
  · simp at h

/-- One encoding: an accepted prefix is exactly what `write_tag` writes for the tag read, and the rest is what is
left, so the bytes read are the length byte and the tag, nothing more. -/
theorem readTag_ok (b t rest : List Nat) (h : readTag b = .ok t rest) :
    b = t.length :: (t ++ rest) ∧ writeTag t = some (t.length :: t) ∧ 1 ≤ t.length ∧ t.length ≤ maxTag := by
  cases b with
  | nil => simp [readTag] at h
  | cons n r =>
    simp only [readTag] at h
    split at h
    · rename_i hn
      split at h
      · rename_i hl
        simp only [Rd.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen : (r.take n).length = n := by simp; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlen]; simp
        · simp only [writeTag, hlen]; simp [hn.1, hn.2]
        · omega
        · omega
      · simp at h
    · simp at h

/-- Exactly the length byte and the tag are consumed: `1 + tag.length` bytes. -/
theorem readTag_consumed (b t rest : List Nat) (h : readTag b = .ok t rest) :
    b.length = rest.length + (1 + t.length) := by
  obtain ⟨e, _⟩ := readTag_ok b t rest h
  rw [e]; simp; omega

/-- Two streams that give the same tag and the same rest are the same bytes. -/
theorem readTag_unique (b1 b2 t rest : List Nat) (h1 : readTag b1 = .ok t rest) (h2 : readTag b2 = .ok t rest) :
    b1 = b2 := by
  rw [(readTag_ok b1 t rest h1).1, (readTag_ok b2 t rest h2).1]

/-- `write_tag` is injective: two tags with the same bytes written are equal. -/
theorem writeTag_injective (t u b : List Nat) (h1 : writeTag t = some b) (h2 : writeTag u = some b) : t = u := by
  have a := readTag_writeTag t b [] h1
  have c := readTag_writeTag u b [] h2
  simp only [List.append_nil] at a c
  rw [a] at c
  exact (Rd.ok.inj c).1

/-- A length byte outside 1 to 64 is refused as `Config` having read only that byte: the rest of the stream is
untouched, whatever it holds. -/
theorem readTag_config (n : Nat) (r : List Nat) (h : ¬(1 ≤ n ∧ n ≤ maxTag)) :
    readTag (n :: r) = .err .config r := by
  simp [readTag, h]

/-- A valid length byte with fewer bytes after it than it announces ends in the stream's error. -/
theorem readTag_eof (n : Nat) (r : List Nat) (h : 1 ≤ n ∧ n ≤ maxTag) (hl : r.length < n) :
    readTag (n :: r) = .err .eof [] := by
  simp [readTag, h, Nat.not_le.mpr hl]

/-- The empty stream is the stream's error. -/
theorem readTag_nil : readTag [] = .err .eof [] := rfl

/-- A tag read is a valid tag: 1 to 64 bytes, and never more bytes of the input than `1 + 64` are consumed. -/
theorem readTag_bound (b t rest : List Nat) (h : readTag b = .ok t rest) :
    1 ≤ t.length ∧ t.length ≤ maxTag ∧ b.length - rest.length ≤ maxTag + 1 := by
  obtain ⟨_, _, h1, h2⟩ := readTag_ok b t rest h
  have := readTag_consumed b t rest h
  refine ⟨h1, h2, ?_⟩
  omega

end Vinc.StreamTag

#audit_axioms Vinc.StreamTag.writeTag_isSome
#audit_axioms Vinc.StreamTag.readTag_writeTag
#audit_axioms Vinc.StreamTag.readTag_ok
#audit_axioms Vinc.StreamTag.readTag_consumed
#audit_axioms Vinc.StreamTag.readTag_unique
#audit_axioms Vinc.StreamTag.writeTag_injective
#audit_axioms Vinc.StreamTag.readTag_config
#audit_axioms Vinc.StreamTag.readTag_eof
#audit_axioms Vinc.StreamTag.readTag_bound
