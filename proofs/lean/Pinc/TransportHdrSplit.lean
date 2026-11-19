import Pinc.TransportHdrThm

/-!
# Packet headers: the packets of a datagram

Theorems about `TransportHdr.packets`, the iterator of `packet/datagram.rs` run to its end, for every datagram and
every configured id length:

* `packets_shape`: every item but the last is a long packet, so a short packet or an error is the last item and
  nothing follows a short packet;
* `packets_ranges`: the ranges start at 0, each starts where the one before ends, a packet is not empty and lies
  inside the datagram, and a short packet runs to the end of the datagram (disjoint, in order, back to back);
* `packets_items`: each long packet is what `parseLong` finds at its offset, with the length the header declares;
  the short packet is what `shortDcid` accepts there; an error is the refusal of the step at its offset;
* `packets_end`: when no short packet and no error ends the list, only zero bytes follow the last long packet
  (padding), so the ranges cover the datagram up to the padding or up to the first refusal;
* `parseLong_fits`: the body of an accepted long header fits, so the split of the iterator never fails.
-/

namespace Pinc.TransportHdr
open Pinc

theorem decodeLoop_len : ∀ (bs : List Nat) (i value x n : Nat),
    Varint.decodeLoop i value bs = some (.ok (x, n)) → i < n ∧ n ≤ i + bs.length := by
  intro bs
  induction bs with
  | nil => intro i value x n h; simp [Varint.decodeLoop] at h
  | cons b bs ih =>
    intro i value x n h
    simp only [Varint.decodeLoop] at h
    split at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        simp only [List.length_cons]
        omega
    · have := ih _ _ _ _ h
      simp only [List.length_cons]
      omega

theorem decode_len (input : List Nat) (v n : Nat) (h : Varint.decode input = .ok (v, n)) :
    1 ≤ n ∧ n ≤ input.length := by
  unfold Varint.decode at h
  split at h
  · rename_i r hr
    subst h
    have := decodeLoop_len _ _ _ _ _ hr
    have h2 : (input.take Varint.maxLen).length ≤ input.length := by simp; omega
    omega
  · split at h <;> simp at h

/-- The body of an accepted long header fits in the input, and the header is at least five bytes. -/
theorem parseLong_fits (p : List Nat) (h : LongHeader) (n : Nat) (hok : parseLong p = .ok (h, n)) :
    5 ≤ n ∧ n + h.bodyLen ≤ p.length := by
  unfold parseLong at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  rename_i dcid r3 hdc
  split at hok
  · simp at hok
  rename_i scid r4 hsc
  split at hok
  · simp at hok
  rename_i bl n' hdecode
  split at hok
  · simp at hok
  rename_i hfit
  simp only [Except.ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  obtain ⟨rfl, _⟩ := readCid_ok _ _ _ hdc
  obtain ⟨rfl, _⟩ := readCid_ok _ _ _ hsc
  have := decode_len r4 bl n' hdecode
  simp
  omega

def Item.isLong : Item → Bool
  | .long .. => true
  | _ => false

def Item.isShort : Item → Bool
  | .short .. => true
  | _ => false

def Item.isErr : Item → Bool
  | .err .. => true
  | _ => false

/-- The offset of the bytes an item was found at. -/
def Item.start : Item → Nat
  | .long _ _ s _ => s
  | .short _ s _ => s
  | .err _ s => s

/-- The bytes a packet lends; an error lends none. -/
def Item.len : Item → Nat
  | .long _ _ _ n => n
  | .short _ _ n => n
  | .err _ _ => 0

/-- The step of the iterator at `rest` yields the error `e`: a zero byte followed somewhere by a byte that is not
zero, a byte without the top bit that `short_dcid` refuses, or a long header `LongHeader::parse` refuses. -/
def Refused (rest : List Nat) (dl : Nat) (e : PErr) : Prop :=
  match rest with
  | [] => False
  | first :: _ =>
    (first = 0 ∧ e = .form ∧ ∃ b ∈ rest, b ≠ 0) ∨
      (first ≠ 0 ∧ first &&& 0x80 = 0 ∧ shortDcid rest dl = .error e) ∨
      (first &&& 0x80 ≠ 0 ∧ parseLong rest = .error e)

/-- What the iterator yields from `rest`, which starts at offset `off`: nothing over padding (or at the end), one
error, one short packet that takes all of `rest`, or a long packet followed by what the bytes after it yield. -/
inductive Split (dl : Nat) : Nat → List Nat → List Item → Prop
  | pad (off : Nat) (rest : List Nat) (h : ∀ b ∈ rest, b = 0) : Split dl off rest []
  | bad (off : Nat) (rest : List Nat) (e : PErr) (h : Refused rest dl e) : Split dl off rest [.err e off]
  | short (off first : Nat) (rest d : List Nat) (h0 : first ≠ 0) (h7 : first &&& 0x80 = 0)
      (hd : shortDcid (first :: rest) dl = .ok d) : Split dl off (first :: rest) [.short d off (rest.length + 1)]
  | long (off first : Nat) (rest : List Nat) (h : LongHeader) (hl : Nat) (tail : List Item)
      (h7 : first &&& 0x80 ≠ 0) (hp : parseLong (first :: rest) = .ok (h, hl))
      (ht : Split dl (off + (hl + h.bodyLen)) ((first :: rest).drop (hl + h.bodyLen)) tail) :
      Split dl off (first :: rest) (.long h hl off (hl + h.bodyLen) :: tail)

/-- The iterator, with fuel above the bytes left, yields a `Split`: in particular the fuel never ends the list and
the split of a long packet never fails. -/
theorem packetsFrom_split (dl : Nat) : ∀ (fuel off : Nat) (rest : List Nat), rest.length < fuel →
    Split dl off rest (packetsFrom fuel off rest dl) := by
  intro fuel
  induction fuel with
  | zero => intro off rest h; omega
  | succ fuel ih =>
    intro off rest hlen
    cases rest with
    | nil => exact .pad off [] (by simp)
    | cons first r =>
      simp only [packetsFrom]
      by_cases h0 : first = 0
      · simp only [h0, ↓reduceIte]
        split
        · rename_i hany
          refine .bad off _ _ ?_
          refine Or.inl ⟨rfl, rfl, ?_⟩
          simp only [List.any_eq_true, bne_iff_ne, ne_eq] at hany
          exact hany
        · rename_i hany
          refine .pad off _ ?_
          intro b hb
          simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, Decidable.not_not] at hany
          exact hany b hb
      · simp only [h0, ↓reduceIte]
        by_cases h7 : first &&& 0x80 = 0
        · simp only [h7, ↓reduceIte]
          split
          · rename_i d hd
            exact .short off first r d h0 h7 hd
          · rename_i e he
            refine .bad off _ _ ?_
            exact Or.inr (Or.inl ⟨h0, h7, he⟩)
        · simp only [h7, ↓reduceIte]
          split
          · rename_i e he
            refine .bad off _ _ ?_
            exact Or.inr (Or.inr ⟨h7, he⟩)
          · rename_i h hl hp
            obtain ⟨h5, hfit⟩ := parseLong_fits _ _ _ hp
            have hnot : ¬ (first :: r).length < hl + h.bodyLen := by omega
            simp only [hnot, ↓reduceIte]
            refine .long off first r h hl _ h7 hp (ih _ _ ?_)
            simp only [List.length_drop]
            simp only [List.length_cons] at hlen hfit ⊢
            omega

theorem packets_split (d : List Nat) (dl : Nat) : Split dl 0 d (packets d dl) :=
  packetsFrom_split dl _ 0 d (by omega)

/-! ## What a split says -/

theorem split_shape (dl : Nat) (off : Nat) (rest : List Nat) (l : List Item) (h : Split dl off rest l) :
    ∀ i, i + 1 < l.length → ∃ it, l[i]? = some it ∧ it.isLong = true := by
  induction h with
  | pad => intro i hi; simp at hi
  | bad => intro i hi; simp at hi
  | short => intro i hi; simp at hi
  | long off first rest h hl tail h7 hp ht ih =>
    intro i hi
    cases i with
    | zero => exact ⟨_, rfl, rfl⟩
    | succ i =>
      simp only [List.length_cons] at hi
      simpa using ih i (by omega)

/-- The ranges of the items from `off` on, inside `[off, stop)`: each item starts where the one before ends, a
packet is not empty and ends inside, and a short packet ends at `stop`. -/
def Ranged (stop : Nat) : Nat → List Item → Prop
  | _, [] => True
  | off, it :: tl =>
    it.start = off ∧ off + it.len ≤ stop ∧ (it.isErr = false → 0 < it.len) ∧
      (it.isShort = true → off + it.len = stop) ∧ Ranged stop (off + it.len) tl

theorem split_ranged (dl : Nat) (off : Nat) (rest : List Nat) (l : List Item) (h : Split dl off rest l) :
    Ranged (off + rest.length) off l := by
  induction h with
  | pad => simp [Ranged]
  | bad => simp [Ranged, Item.start, Item.len, Item.isErr, Item.isShort]
  | short => simp [Ranged, Item.start, Item.len, Item.isErr, Item.isShort]
  | long off first rest h hl tail h7 hp ht ih =>
    obtain ⟨h5, hfit⟩ := parseLong_fits _ _ _ hp
    have e : off + (hl + h.bodyLen) + ((first :: rest).drop (hl + h.bodyLen)).length = off + (first :: rest).length := by
      simp only [List.length_drop]
      omega
    rw [e] at ih
    exact ⟨rfl, by simp only [Item.len]; omega, fun _ => by simp only [Item.len]; omega,
      fun h => by simp [Item.isShort] at h, ih⟩

/-- What an item says about the datagram `d` it was found in. -/
def ItemAt (d : List Nat) (dl : Nat) : Item → Prop
  | .long h hl s n => parseLong (d.drop s) = .ok (h, hl) ∧ n = hl + h.bodyLen
  | .short dc s n => shortDcid (d.drop s) dl = .ok dc ∧ n = (d.drop s).length
  | .err e s => Refused (d.drop s) dl e

theorem split_items (dl : Nat) (off : Nat) (rest : List Nat) (l : List Item) (h : Split dl off rest l) :
    ∀ d : List Nat, d.drop off = rest → ∀ it ∈ l, ItemAt d dl it := by
  induction h with
  | pad => intro d _ it hit; simp at hit
  | bad off rest e h =>
    intro d hd it hit
    simp only [List.mem_singleton] at hit
    subst hit
    simp only [ItemAt, hd]
    exact h
  | short off first rest dc h0 h7 hdc =>
    intro d hd it hit
    simp only [List.mem_singleton] at hit
    subst hit
    simp only [ItemAt, hd]
    exact ⟨hdc, by simp⟩
  | long off first rest h hl tail h7 hp ht ih =>
    intro d hd it hit
    simp only [List.mem_cons] at hit
    rcases hit with rfl | hit
    · show parseLong (d.drop off) = _ ∧ _
      rw [hd]
      exact ⟨hp, rfl⟩
    · refine ih d ?_ it hit
      rw [← hd, List.drop_drop]

theorem split_end (dl : Nat) (off : Nat) (rest : List Nat) (l : List Item) (h : Split dl off rest l) :
    (∀ it ∈ l, it.isLong = true) → ∀ b ∈ rest.drop (l.map Item.len).sum, b = 0 := by
  induction h with
  | pad off rest h => intro _ b hb; exact h b (by simpa using hb)
  | bad => intro hl; simp [Item.isLong] at hl
  | short => intro hl; simp [Item.isLong] at hl
  | long off first rest h hl tail h7 hp ht ih =>
    intro hall b hb
    refine ih (fun it hit => hall it (by simp [hit])) b ?_
    rw [List.drop_drop]
    simpa [Item.len] using hb

/-! ## The packets of a datagram -/

/-- Long packets, then at most one short packet or one error: every item but the last is a long packet. -/
theorem packets_shape (d : List Nat) (dl : Nat) (i : Nat) (hi : i + 1 < (packets d dl).length) :
    ∃ it, (packets d dl)[i]? = some it ∧ it.isLong = true :=
  split_shape dl 0 d _ (packets_split d dl) i hi

/-- The ranges are back to back from offset 0, not empty, inside the datagram, and a short packet runs to its end. -/
theorem packets_ranges (d : List Nat) (dl : Nat) : Ranged d.length 0 (packets d dl) := by
  simpa using split_ranged dl 0 d _ (packets_split d dl)

/-- Each packet is what the parser finds at its offset, and an error is the refusal of the step there. -/
theorem packets_items (d : List Nat) (dl : Nat) (it : Item) (hit : it ∈ packets d dl) : ItemAt d dl it :=
  split_items dl 0 d _ (packets_split d dl) d rfl it hit

/-- With no short packet and no error, only zero bytes follow the last long packet. -/
theorem packets_end (d : List Nat) (dl : Nat) (hall : ∀ it ∈ packets d dl, it.isLong = true) :
    ∀ b ∈ d.drop ((packets d dl).map Item.len).sum, b = 0 :=
  split_end dl 0 d _ (packets_split d dl) hall

/-- The associated data of a packet found in a datagram is the bytes of the datagram from the packet's offset to
the end of its packet number: `open` re-encodes nothing. -/
theorem packets_aad (d : List Nat) (start len pnOff pnLen : Nat) (o : Parts)
    (h : openParts ((d.drop start).take len) pnOff pnLen = .ok o) :
    o.aad = (d.drop start).take (pnOff + pnLen) := by
  have hlen : pnOff + pnLen ≤ len := by
    rw [openParts_eq] at h
    split at h
    · simp at h
    · rename_i hn
      simp only [List.length_take] at hn
      omega
  rw [(openParts_aad _ _ _ _ h).1, List.take_take, Nat.min_eq_left hlen]

#audit_axioms Pinc.TransportHdr.parseLong_fits
#audit_axioms Pinc.TransportHdr.packetsFrom_split
#audit_axioms Pinc.TransportHdr.packets_shape
#audit_axioms Pinc.TransportHdr.packets_ranges
#audit_axioms Pinc.TransportHdr.packets_items
#audit_axioms Pinc.TransportHdr.packets_end
#audit_axioms Pinc.TransportHdr.packets_aad

end Pinc.TransportHdr
