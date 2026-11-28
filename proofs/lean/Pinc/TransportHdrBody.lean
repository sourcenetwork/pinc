import Pinc.Axioms
import Pinc.TransportHdrThm
import Pinc.TransportReasm
import Pinc.TransportReasmThm

/-!
# Handshake packet bodies, padding and the header protection sample

The three places where a datagram is put together or taken apart besides the headers of `Pinc.TransportHdr`, as
`proofs/tla/HdrOps.tla` has them, over lists of bytes and unbounded `Nat`:

* the body of a Handshake packet, `varint(total) varint(offset) fragment`: `hsWrite` is the puts of
  `Connection::write_handshake` (`conn/send.rs`: the long header with a body length of the three parts, then the two
  varints and the fragment, all on one writer over the window), `hsRead` is the parse `Handshake::on_fragment`
  (`conn/handshake.rs`) makes before the fragment reaches `Reassembly::add` (`Pinc.TransportReasm`), and `hsRecv` is
  the two together;
* `padTo` is `pad_to` (`packet/datagram.rs`): zero bytes appended in chunks of 64 until the writer holds `min_len`;
* `sampleAt` is `sample_at` (`packet/protect.rs`): the 16 bytes at `pn_off + SAMPLE_SKIP` the header protection mask
  is made from.

`Pinc.TraceHdr` replays the recorded calls of the real code through these functions.
-/

namespace Pinc.TransportHdrBody
open Pinc Pinc.TransportHdr Pinc.TransportReasm

/-! ## The body of a Handshake packet -/

/-- The three parts of a Handshake packet body: the message length, the offset, the fragment. -/
def hsBody (total off : Nat) (data : List Nat) : List Nat :=
  Varint.encodeBytes total ++ Varint.encodeBytes off ++ data

/-- The body length `write_handshake` puts in the header. -/
def hsBodyLen (total off n : Nat) : Nat := Varint.encodedLen total + Varint.encodedLen off + n

/-- The header `write_handshake` writes: a Handshake long header whose body is the three parts. -/
def hsHeader (dcid scid : List Nat) (total off n : Nat) : LongHeader :=
  ⟨.handshake, dcid, scid, hsBodyLen total off n⟩

/-- The puts of `write_handshake` after `next_fragment`: `header.write(&mut w, 0)`, `put_varint(total)`,
`put_varint(off)`, `put_slice(bytes)`, on a writer of `cap` bytes (the window); the code returns 0 if one failed, so
the result is the datagram only if `err = none`. -/
def hsWrite (dcid scid : List Nat) (total off : Nat) (data : List Nat) (cap : Nat) : WRes :=
  ((((writeLong (hsHeader dcid scid total off data.length) 0 cap).andThen (putVarint cap total)).andThen
    (putVarint cap off)).andThen (putSlice cap data))

/-- What `on_fragment` reads from the body of a packet: the two varints (`usize::try_from` of a `u64` is the identity on
the 64-bit targets) and the rest as the fragment (`read_bytes(remaining)` cannot fail). -/
def hsRead (body : List Nat) : Option (Nat × Nat × List Nat) :=
  match Varint.decode body with
  | .error _ => none
  | .ok (total, n1) =>
    match Varint.decode (body.drop n1) with
    | .error _ => none
    | .ok (off, n2) => some (total, off, body.drop (n1 + n2))

/-- `on_fragment`: a body that does not parse leaves the reassembly alone, any other goes to `Reassembly::add`
with the length of the fragment it carries. -/
def hsRecv (r : R) (mx nr : Nat) (body : List Nat) : Option Nat × R :=
  match hsRead body with
  | none => (none, r)
  | some (total, off, data) => add r mx nr total off data.length

theorem length_hsBody (total off : Nat) (data : List Nat) :
    (hsBody total off data).length = hsBodyLen total off data.length := by
  simp [hsBody, hsBodyLen, Varint.length_encodeBytes]; omega

theorem encodedLen_le_two (v : Nat) (h : v < 16384) : Varint.encodedLen v ≤ 2 := by
  by_cases h1 : v < 128
  · rw [Varint.encodedLen_lt v h1]; omega
  · rw [Varint.encodedLen_ge v (by omega), Varint.encodedLen_lt (v / 128) (by omega)]; omega

theorem limit_big : 16384 < Varint.limit := by unfold Varint.limit; decide

/-! ### Writing -/

/-- A write that has room and whose lengths a varint holds writes the header and the three parts, and nothing else. -/
theorem hsWrite_ok (dcid scid : List Nat) (total off : Nat) (data : List Nat) (cap : Nat)
    (hd : dcid.length ≤ maxCid) (hs : scid.length ≤ maxCid) (ht : total < Varint.limit) (ho : off < Varint.limit)
    (hb : hsBodyLen total off data.length < Varint.limit)
    (hc : headerLen (hsHeader dcid scid total off data.length) + Varint.encodedLen total + Varint.encodedLen off +
      data.length ≤ cap) :
    hsWrite dcid scid total off data cap =
      ⟨none, encodeLong (hsHeader dcid scid total off data.length) 0 ++ hsBody total off data⟩ := by
  have hw : (hsHeader dcid scid total off data.length).WF := ⟨hd, hs⟩
  have h0 := writeLong_ok (hsHeader dcid scid total off data.length) 0 cap 0 hw rfl hb (by omega)
  have hl := length_encodeLong (hsHeader dcid scid total off data.length) 0
  unfold hsWrite
  rw [h0, andThen_putVarint cap total _ ht (by simp only [hl]; omega)]
  rw [andThen_putVarint cap off _ ho (by simp only [List.length_append, hl, Varint.length_encodeBytes]; omega)]
  rw [andThen_putSlice cap data _ (by simp only [List.length_append, hl, Varint.length_encodeBytes]; omega)]
  simp [hsBody, List.append_assoc]

/-- A refused write: a length no varint holds, or no room for the header and the three parts. (The code then returns 0
and sends nothing; the writer is not read again.) -/
theorem hsWrite_err (dcid scid : List Nat) (total off : Nat) (data : List Nat) (cap : Nat)
    (hd : dcid.length ≤ maxCid) (hs : scid.length ≤ maxCid)
    (he : (hsWrite dcid scid total off data cap).err ≠ none) :
    Varint.limit ≤ total ∨ Varint.limit ≤ off ∨ Varint.limit ≤ hsBodyLen total off data.length ∨
      cap < headerLen (hsHeader dcid scid total off data.length) + Varint.encodedLen total + Varint.encodedLen off +
        data.length := by
  by_cases h1 : total < Varint.limit
  · by_cases h2 : off < Varint.limit
    · by_cases h3 : hsBodyLen total off data.length < Varint.limit
      · by_cases h4 : headerLen (hsHeader dcid scid total off data.length) + Varint.encodedLen total +
            Varint.encodedLen off + data.length ≤ cap
        · rw [hsWrite_ok dcid scid total off data cap hd hs h1 h2 h3 h4] at he
          exact absurd rfl he
        · omega
      · omega
    · omega
  · omega

/-- The room `write_handshake` leaves for the fragment: the window less the fixed part of the header, two bytes for the
body length and the two varints at the size of the offset the fragment starts at. -/
def hsRoom (win dl sl total off : Nat) : Nat :=
  win - ((1 + 1 + 1 + dl + 1 + sl) + 2 + (Varint.encodedLen total + Varint.encodedLen off))

/-- A fragment of at most the room the code computes always fits: with the two bytes it set aside for the body length
(a body length below 2^14 takes at most two) the writer never fails, so `write_handshake` returns 0 only when the
window cannot hold the fixed part. -/
theorem hsWrite_room (dcid scid : List Nat) (total off : Nat) (data : List Nat) (win : Nat)
    (hd : dcid.length ≤ maxCid) (hs : scid.length ≤ maxCid) (ht : total < Varint.limit) (ho : off < Varint.limit)
    (hb : hsBodyLen total off data.length < 16384)
    (hwin : (1 + 1 + 1 + dcid.length + 1 + scid.length) + 2 + (Varint.encodedLen total + Varint.encodedLen off) ≤ win)
    (hr : data.length ≤ hsRoom win dcid.length scid.length total off) :
    hsWrite dcid scid total off data win =
      ⟨none, encodeLong (hsHeader dcid scid total off data.length) 0 ++ hsBody total off data⟩ := by
  have e2 := encodedLen_le_two (hsBodyLen total off data.length) hb
  have hbig := limit_big
  unfold hsRoom at hr
  apply hsWrite_ok dcid scid total off data win hd hs ht ho (by omega)
  simp only [headerLen, hsHeader]
  omega

/-! ### Reading what was written -/

/-- Reading what `write_handshake` put: the message length, the offset and the fragment, whatever follows. -/
theorem hsRead_hsBody (total off : Nat) (data : List Nat) (ht : total < Varint.limit) (ho : off < Varint.limit) :
    hsRead (hsBody total off data) = some (total, off, data) := by
  unfold hsRead hsBody
  rw [List.append_assoc, Varint.decode_encode total _ ht, Varint.length_encodeBytes]
  simp only
  have e2 : (Varint.encodeBytes total ++ (Varint.encodeBytes off ++ data)).drop (Varint.encodedLen total) =
      Varint.encodeBytes off ++ data := List.drop_left' (by simp [Varint.length_encodeBytes])
  rw [e2, Varint.decode_encode off _ ho, Varint.length_encodeBytes]
  simp only
  rw [← List.append_assoc, List.drop_left' (by simp [Varint.length_encodeBytes])]

/-- A body that parses is the one encoding of the three parts it yields, and both numbers are below `2^63`. -/
theorem hsRead_canonical (body : List Nat) (hv : Varint.ValidBytes body) (total off : Nat) (data : List Nat)
    (h : hsRead body = some (total, off, data)) :
    body = hsBody total off data ∧ total < Varint.limit ∧ off < Varint.limit := by
  unfold hsRead at h
  cases h1 : Varint.decode body with
  | error e => rw [h1] at h; simp at h
  | ok p1 =>
    obtain ⟨t, n1⟩ := p1
    rw [h1] at h
    simp only at h
    cases h2 : Varint.decode (body.drop n1) with
    | error e => rw [h2] at h; simp at h
    | ok p2 =>
      obtain ⟨o, n2⟩ := p2
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hv2 : Varint.ValidBytes (body.drop n1) := fun b hb => hv b (List.mem_of_mem_drop hb)
      obtain ⟨c1, c1n⟩ := Varint.decode_canonical body hv t n1 h1
      obtain ⟨c2, c2n⟩ := Varint.decode_canonical (body.drop n1) hv2 o n2 h2
      obtain ⟨b1, _⟩ := Varint.decode_bounds body hv t n1 h1
      obtain ⟨b2, _⟩ := Varint.decode_bounds (body.drop n1) hv2 o n2 h2
      refine ⟨?_, b1, b2⟩
      calc body = body.take n1 ++ body.drop n1 := (List.take_append_drop n1 body).symm
        _ = body.take n1 ++ ((body.drop n1).take n2 ++ (body.drop n1).drop n2) := by congr 1; exact (List.take_append_drop n2 _).symm
        _ = hsBody t o (body.drop (n1 + n2)) := by
          rw [c1, c2]; simp [hsBody, List.drop_drop]

/-- A body does not parse exactly when the first varint fails, or the second does. -/
theorem hsRead_none_iff (body : List Nat) : hsRead body = none ↔
    (∃ e, Varint.decode body = .error e) ∨
      (∃ t n1, Varint.decode body = .ok (t, n1) ∧ ∃ e, Varint.decode (body.drop n1) = .error e) := by
  unfold hsRead
  cases h1 : Varint.decode body with
  | error e => simp
  | ok p =>
    obtain ⟨t, n1⟩ := p
    cases h2 : Varint.decode (body.drop n1) with
    | error e => simp only [h2]; exact ⟨fun _ => Or.inr ⟨t, n1, rfl, e, h2⟩, fun _ => trivial⟩
    | ok q => obtain ⟨o, n2⟩ := q; simp [h2]

/-- A body that does not parse is dropped before the reassembly sees it: nothing changes. -/
theorem hsRecv_unparsed (r : R) (mx nr : Nat) (body : List Nat) (h : hsRead body = none) :
    hsRecv r mx nr body = (none, r) := by
  simp [hsRecv, h]

/-- A body that parses is the fragment `add` is given, with the length of the bytes that follow the two varints. -/
theorem hsRecv_parsed (r : R) (mx nr : Nat) (body : List Nat) (total off : Nat) (data : List Nat)
    (h : hsRead body = some (total, off, data)) : hsRecv r mx nr body = add r mx nr total off data.length := by
  simp [hsRecv, h]

/-- A message length of 0 or above the largest message is refused and the reassembly is left as it was. -/
theorem hsRecv_bad_total (r : R) (mx nr : Nat) (body : List Nat) (total off : Nat) (data : List Nat)
    (h : hsRead body = some (total, off, data)) (ht : total = 0 ∨ mx < total) :
    hsRecv r mx nr body = (none, r) := by
  rw [hsRecv_parsed r mx nr body total off data h]; exact add_refused r mx nr total off data.length ht

/-- An offset at or past the message length is refused too, but a message of another length, with no runs held, has
by then started the count over (the length check passed, so the state is a fresh one for this length); with runs
held it is refused as of another length and changes nothing. -/
theorem hsRecv_past (r : R) (mx nr : Nat) (body : List Nat) (total off : Nat) (data : List Nat)
    (h : hsRead body = some (total, off, data)) (ht : ¬ (total = 0 ∨ mx < total)) (ho : total ≤ off) :
    hsRecv r mx nr body =
      (none, if total ≠ r.total ∧ r.runs = [] then { runs := [], total := total } else r) := by
  rw [hsRecv_parsed r mx nr body total off data h]
  unfold add
  have : min (off + data.length) total ≤ off := by omega
  rw [if_neg ht]
  by_cases ht2 : total = r.total
  · have n1 : ¬ (total ≠ r.total ∧ r.runs ≠ []) := fun h => h.1 ht2
    have n2 : ¬ (total ≠ r.total ∧ r.runs = []) := fun h => h.1 ht2
    have n3 : ¬ (total ≠ r.total) := fun h => h ht2
    rw [if_neg n1, if_neg n2]
    dsimp only
    rw [if_pos this, if_neg n3]
  · by_cases hr : r.runs = []
    · have n1 : ¬ (total ≠ r.total ∧ r.runs ≠ []) := fun h => h.2 hr
      have p2 : total ≠ r.total ∧ r.runs = [] := ⟨ht2, hr⟩
      rw [if_neg n1, if_pos p2]
      dsimp only
      rw [if_pos this, if_pos ht2]
    · have p1 : total ≠ r.total ∧ r.runs ≠ [] := ⟨ht2, hr⟩
      have n2 : ¬ (total ≠ r.total ∧ r.runs = []) := fun h => hr h.2
      rw [if_pos p1, if_neg n2]

/-- A fragment that runs past the message length is cut at it, not refused: `add` keeps `total - off` bytes of it. -/
theorem add_trim (r : R) (mx nr total off dlen : Nat) (ho : off < total) :
    add r mx nr total off dlen = add r mx nr total off (min dlen (total - off)) := by
  unfold add
  have : min (off + dlen) total = min (off + min dlen (total - off)) total := by omega
  simp only [this]

/-- What the writer put is what the reassembly is given: the datagram the writer built, cut where its header says the
packet ends, parses back to the same header, and the body after it is the three parts. -/
theorem write_read (dcid scid : List Nat) (total off : Nat) (data : List Nat) (cap : Nat) (tail : List Nat)
    (hd : dcid.length ≤ maxCid) (hs : scid.length ≤ maxCid) (ht : total < Varint.limit) (ho : off < Varint.limit)
    (hb : hsBodyLen total off data.length < Varint.limit)
    (hc : headerLen (hsHeader dcid scid total off data.length) + Varint.encodedLen total + Varint.encodedLen off +
      data.length ≤ cap) :
    parseLong ((hsWrite dcid scid total off data cap).out ++ tail) =
        .ok (hsHeader dcid scid total off data.length, headerLen (hsHeader dcid scid total off data.length)) ∧
      hsRead ((hsWrite dcid scid total off data cap).out.drop (headerLen (hsHeader dcid scid total off data.length))) =
        some (total, off, data) := by
  rw [hsWrite_ok dcid scid total off data cap hd hs ht ho hb hc]
  simp only
  constructor
  · rw [List.append_assoc]
    exact parse_write _ 0 _ ⟨hd, hs⟩ rfl hb (by simp [length_hsBody, hsHeader])
  · rw [List.drop_left' (length_encodeLong _ 0)]
    exact hsRead_hsBody total off data ht ho

/-- The whole path: the reassembly is handed exactly the fragment the writer put, at the offset it put it. -/
theorem hsRecv_write (r : R) (mx nr : Nat) (dcid scid : List Nat) (total off : Nat) (data : List Nat) (cap : Nat)
    (hd : dcid.length ≤ maxCid) (hs : scid.length ≤ maxCid) (ht : total < Varint.limit) (ho : off < Varint.limit)
    (hb : hsBodyLen total off data.length < Varint.limit)
    (hc : headerLen (hsHeader dcid scid total off data.length) + Varint.encodedLen total + Varint.encodedLen off +
      data.length ≤ cap) :
    hsRecv r mx nr ((hsWrite dcid scid total off data cap).out.drop
        (headerLen (hsHeader dcid scid total off data.length))) = add r mx nr total off data.length :=
  hsRecv_parsed r mx nr _ total off data (write_read dcid scid total off data cap [] hd hs ht ho hb hc).2

/-! ## Padding -/

/-- The loop of `pad_to`: chunks of at most 64 zero bytes while any are left. -/
def padLoop : Nat → Nat → List Nat → List Nat
  | 0, _, out => out
  | fuel + 1, left, out =>
    if left = 0 then out else padLoop fuel (left - min left 64) (out ++ List.replicate (min left 64) 0)

/-- `pad_to(w, min_len)` on a writer of `cap` bytes holding `out`: `ensure(left)` first, so a refusal writes nothing. -/
def padTo (cap minLen : Nat) (out : List Nat) : Except PErr (List Nat) :=
  let left := minLen - out.length
  if left > cap - out.length then .error (.bufferTooSmall (left - (cap - out.length)))
  else .ok (padLoop (left + 1) left out)

theorem padLoop_eq : ∀ (fuel left : Nat) (out : List Nat), left < fuel →
    padLoop fuel left out = out ++ List.replicate left 0
  | 0, left, out, h => by omega
  | fuel + 1, left, out, h => by
    unfold padLoop
    by_cases h0 : left = 0
    · simp [h0]
    · simp only [h0, ite_false]
      rw [padLoop_eq fuel (left - min left 64) _ (by omega), List.append_assoc, List.replicate_append_replicate]
      congr 2
      omega

/-- With room, `pad_to` appends exactly the zero bytes that bring the writer to `min_len`, and the writer then holds
`max (written, min_len)` bytes; the bytes written before are untouched. -/
theorem padTo_ok (cap minLen : Nat) (out : List Nat) (h : out.length ≤ cap) (hm : minLen ≤ cap) :
    padTo cap minLen out = .ok (out ++ List.replicate (minLen - out.length) 0) := by
  unfold padTo
  have : ¬ (minLen - out.length > cap - out.length) := by omega
  simp only [this, ite_false]
  rw [padLoop_eq _ _ _ (by omega)]

theorem padTo_length (cap minLen : Nat) (out o : List Nat) (h : out.length ≤ cap) (hm : minLen ≤ cap)
    (hr : padTo cap minLen out = .ok o) : o.length = max out.length minLen := by
  rw [padTo_ok cap minLen out h hm] at hr
  cases hr
  simp <;> omega

/-- A writer that already holds `min_len` bytes is left alone, whatever the room. -/
theorem padTo_noop (cap minLen : Nat) (out : List Nat) (h : out.length ≤ cap) (hm : minLen ≤ out.length) :
    padTo cap minLen out = .ok out := by
  rw [padTo_ok cap minLen out h (by omega)]
  simp <;> omega

/-- With no room for `min_len` bytes the call is refused with the shortfall and writes nothing. -/
theorem padTo_err (cap minLen : Nat) (out : List Nat) (h : out.length ≤ cap) (hm : cap < minLen) :
    padTo cap minLen out = .error (.bufferTooSmall (minLen - cap)) := by
  unfold padTo
  have : minLen - out.length > cap - out.length := by omega
  simp only [this, ite_true]
  congr 2
  omega

/-! ## The header protection sample -/

/-- `Aead::SAMPLE_LEN`. -/
def sampleLen : Nat := 16

/-- `sample_at`: the 16 bytes from `pn_off + SAMPLE_SKIP`, or `TooShort`. (`checked_add` fails only for an offset no
slice has room for, which is `TooShort` here too.) -/
def sampleAt (packet : List Nat) (pnOff : Nat) : Except PErr (List Nat) :=
  if pnOff + sampleSkip + sampleLen ≤ packet.length then .ok ((packet.drop (pnOff + sampleSkip)).take sampleLen)
  else .error .tooShort

theorem sampleAt_ok (packet : List Nat) (pnOff : Nat) (h : pnOff + sampleSkip + sampleLen ≤ packet.length) :
    sampleAt packet pnOff = .ok ((packet.drop (pnOff + sampleSkip)).take sampleLen) := by
  simp [sampleAt, h]

/-- Refused exactly when fewer than 16 bytes follow `pn_off + 4`. -/
theorem sampleAt_err (packet : List Nat) (pnOff : Nat) (h : packet.length < pnOff + sampleSkip + sampleLen) :
    sampleAt packet pnOff = .error .tooShort := by
  have : ¬ pnOff + sampleSkip + sampleLen ≤ packet.length := by omega
  simp [sampleAt, this]

theorem sampleAt_length (packet s : List Nat) (pnOff : Nat) (h : sampleAt packet pnOff = .ok s) :
    s.length = sampleLen := by
  unfold sampleAt at h
  split at h
  · cases h; simp [sampleLen] at *; omega
  · cases h

/-- Header protection changes the first byte and the packet-number field, at most `SAMPLE_SKIP = 4` bytes from
`pn_off` (`protect` refuses a field of 0 or 5 bytes, `HeaderProt.tla`): the sample starts right behind them, so
whatever the mask does, the sample taken from the protected packet is the one taken from the plain packet. This is
why `unprotect_header` can take the sample before it unmasks anything. -/
theorem sampleAt_unmasked (p q : List Nat) (pnOff : Nat) (hl : q.length = p.length)
    (hsame : ∀ i, i ≠ 0 → (i < pnOff ∨ pnOff + sampleSkip ≤ i) → q[i]? = p[i]?) :
    sampleAt q pnOff = sampleAt p pnOff := by
  unfold sampleAt
  rw [hl]
  split
  · congr 1
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
    split
    · exact hsame _ (by simp [sampleSkip]) (by right; simp [sampleSkip])
    · rfl
  · rfl

/-- `seal` refuses a packet whose packet number and payload together are under 4 bytes, and no other for being short:
that is exactly the packets of which a sample can be taken, since the tag is 16 bytes and the packet is `pn_off`,
the packet number, the payload and the tag. -/
theorem sealParts_sample (packet : List Nat) (pnOff pnLen payloadLen : Nat) (ps : Parts)
    (h : sealParts packet pnOff pnLen payloadLen = .ok ps) (q : List Nat) (hq : q.length = ps.total) :
    ∃ s, sampleAt q pnOff = .ok s := by
  unfold sealParts at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h
      refine ⟨_, sampleAt_ok q pnOff ?_⟩
      simp only at hq
      simp only [sampleSkip, sampleLen, tagLen] at *
      omega

theorem sealParts_tooShort_iff (packet : List Nat) (pnOff pnLen payloadLen : Nat) (q : List Nat)
    (hq : q.length = pnOff + pnLen + payloadLen + tagLen) :
    sealParts packet pnOff pnLen payloadLen = .error .tooShort ↔
      (sampleAt q pnOff = .error .tooShort ∧ pnLen + payloadLen < sampleSkip) := by
  constructor
  · intro h
    unfold sealParts at h
    split at h
    · rename_i hlt
      refine ⟨sampleAt_err q pnOff ?_, hlt⟩
      simp only [sampleSkip, sampleLen, tagLen] at *
      omega
    · dsimp only at h
      split at h <;> cases h
  · rintro ⟨_, hlt⟩
    simp [sealParts, hlt]

end Pinc.TransportHdrBody

#audit_axioms Pinc.TransportHdrBody.hsWrite_ok
#audit_axioms Pinc.TransportHdrBody.hsWrite_err
#audit_axioms Pinc.TransportHdrBody.hsWrite_room
#audit_axioms Pinc.TransportHdrBody.hsRead_hsBody
#audit_axioms Pinc.TransportHdrBody.hsRead_canonical
#audit_axioms Pinc.TransportHdrBody.hsRead_none_iff
#audit_axioms Pinc.TransportHdrBody.hsRecv_unparsed
#audit_axioms Pinc.TransportHdrBody.hsRecv_parsed
#audit_axioms Pinc.TransportHdrBody.hsRecv_bad_total
#audit_axioms Pinc.TransportHdrBody.hsRecv_past
#audit_axioms Pinc.TransportHdrBody.add_trim
#audit_axioms Pinc.TransportHdrBody.write_read
#audit_axioms Pinc.TransportHdrBody.hsRecv_write
#audit_axioms Pinc.TransportHdrBody.padLoop_eq
#audit_axioms Pinc.TransportHdrBody.padTo_ok
#audit_axioms Pinc.TransportHdrBody.padTo_length
#audit_axioms Pinc.TransportHdrBody.padTo_noop
#audit_axioms Pinc.TransportHdrBody.padTo_err
#audit_axioms Pinc.TransportHdrBody.sampleAt_ok
#audit_axioms Pinc.TransportHdrBody.sampleAt_err
#audit_axioms Pinc.TransportHdrBody.sampleAt_length
#audit_axioms Pinc.TransportHdrBody.sampleAt_unmasked
#audit_axioms Pinc.TransportHdrBody.sealParts_sample
#audit_axioms Pinc.TransportHdrBody.sealParts_tooShort_iff
