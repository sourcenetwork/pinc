/-!
# The size of a datagram

A model of how big `build_datagram` (`vinc-transport` `conn/send.rs`) makes one datagram for a path, as
`proofs/tla/DgramSize.tla` has it, for every input over unbounded sizes.

The story: a connection writes one datagram for a path it believes carries `p` bytes. The datagram may start with a
fragment of the handshake and then hold one application packet, or the zero padding the handshake still owes. Two
datagrams are built larger than `p` on purpose: a first flight sent whole (up to 1452 bytes, or the interface size
when smaller), and a path MTU probe of the probed size. Anything else larger than `p` can be dropped by a router or
black-holed with no ICMP back.

What it proves, with the guard of #554 (the application packet's room ends at `p`, or at the probe's size):
- an application packet that is not a probe ends at or before `p` (`app_fits`);
- a datagram is larger than `p` only as a probe or as a whole flight with no packet behind it (`size_ok`);
- a datagram never runs past the caller's buffer or the amplification room (`bounded`);
- every datagram but a whole flight's is exactly the one of the rule before #554 (`unchanged`);
- the rule before #554 broke `app_fits`: a 149-byte resumed Hello sent whole on a 1200-byte path had its early data
  run to 1452 bytes (`old_rule_breaks`).
-/

namespace Vinc.TransportDgramSize

/-- `MIN_ROOM` of the code: the smallest room worth a datagram. -/
def minRoom : Nat := 24
/-- `PROBE_MTU` of the code: the first probe size, and the most a whole flight takes. -/
def probeMtu : Nat := 1452

/-- What `build_datagram` reads for one datagram. -/
structure In where
  /-- The path's datagram size (`p.mtu.current`). -/
  p : Nat
  /-- The interface size (`p.info.interface_mtu`). -/
  f : Nat
  /-- The caller's buffer (`out.len()`). -/
  o : Nat
  /-- What the amplification budget still allows (`amp_room`). -/
  a : Nat
  /-- The probe size `probe_size` returned, 0 for none. -/
  q : Nat
  /-- Whether the first flight goes whole (`whole`). -/
  w : Bool
  /-- The handshake bytes `write_handshake` would write. -/
  hs : Nat
  /-- The bytes the application packet would take. -/
  app : Nat
  /-- The zero padding the handshake still owes. -/
  pad : Nat

/-- `base`: a whole flight may take the larger of the path's size and 1452 (or the interface size when smaller). -/
def base (i : In) : Nat := if i.w then max i.p (min probeMtu i.f) else i.p
/-- `max_len`: the probe's size or the base, cut to the buffer and to the amplification room. -/
def maxLen (i : In) : Nat := min (min (if i.q = 0 then base i else i.q) i.o) i.a
/-- The handshake fragment takes at most the datagram's room. -/
def hs (i : In) : Nat := min i.hs (maxLen i)
/-- `app_end`: where the application packet's room ends; `g` is the guard of #554. -/
def appEnd (g : Bool) (i : In) : Nat :=
  if g then min (if i.q = 0 then i.p else i.q) (maxLen i) else maxLen i
/-- The application packet takes at most the room behind the fragment (none when the fragment reaches the end). -/
def app (g : Bool) (i : In) : Nat := min i.app (appEnd g i - hs i)
/-- The handshake pads into the datagram's room only when no application packet rode in it. -/
def pad (g : Bool) (i : In) : Nat := if app g i = 0 then min i.pad (maxLen i - hs i) else 0
/-- Whether the datagram is the owed padding alone (no fragment left, padding owed). -/
def padOnly (i : In) : Prop := hs i = 0 ∧ 0 < i.pad
/-- The datagram's length: nothing when the room is under `MIN_ROOM`, the owed padding alone when no fragment is left,
else the fragment, the packet and the padding. -/
def len (g : Bool) (i : In) : Nat :=
  if maxLen i < minRoom then 0
  else if hs i = 0 ∧ 0 < i.pad then min i.pad (maxLen i)
  else hs i + app g i + pad g i
/-- The application packet the datagram carries: none without a datagram or in the owed padding alone. -/
def pkt (g : Bool) (i : In) : Nat :=
  if maxLen i < minRoom ∨ (hs i = 0 ∧ 0 < i.pad) then 0 else app g i

/-- With the guard and no probe, the packet's room ends at the path's size, so a packet behind the fragment fits. -/
theorem app_true_fits (i : In) (hq : i.q = 0) (h : 0 < app true i) : hs i + app true i ≤ i.p := by
  unfold app appEnd at *
  rw [if_pos rfl, if_pos hq] at *
  omega

/-- With the guard, an application packet that is not a probe ends at or before the path's size. -/
theorem app_fits (i : In) (hq : i.q = 0) (h : 0 < pkt true i) : hs i + pkt true i ≤ i.p := by
  by_cases hc : maxLen i < minRoom ∨ (hs i = 0 ∧ 0 < i.pad)
  · simp only [pkt, if_pos hc] at h
    omega
  · simp only [pkt, if_neg hc] at h ⊢
    exact app_true_fits i hq h

/-- The packet's room never runs past the datagram's room. -/
theorem appEnd_le (g : Bool) (i : In) : appEnd g i ≤ maxLen i := by
  unfold appEnd; cases g <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- `max_len` is at most the buffer and the amplification room. -/
theorem maxLen_le (i : In) : maxLen i ≤ min i.o i.a := by unfold maxLen; omega

/-- Never past the caller's buffer or the amplification room, with or without the guard. -/
theorem bounded (g : Bool) (i : In) : len g i ≤ min i.o i.a := by
  have h1 := maxLen_le i
  have h2 := appEnd_le g i
  unfold len pad app hs
  split <;> (try split) <;> (try split) <;> omega

/-- `max_len` of a whole flight with no probe is at most the size the whole flight was given. -/
theorem maxLen_whole (i : In) (hq : i.q = 0) : maxLen i ≤ base i := by
  unfold maxLen; simp only [hq, ite_true]; omega

/-- `max_len` of a probe is at most the probe's size. -/
theorem maxLen_probe (i : In) (hq : 0 < i.q) : maxLen i ≤ i.q := by
  unfold maxLen; simp only [Nat.pos_iff_ne_zero.mp hq, ite_false]; omega

/-- Without a whole flight and without a probe, `max_len` is at most the path's size. -/
theorem maxLen_path (i : In) (hq : i.q = 0) (hw : i.w = false) : maxLen i ≤ i.p := by
  unfold maxLen base; simp only [hq, hw, ite_true, Bool.false_eq_true, ite_false]; omega

/-- The datagram is at most `max_len`, with or without the guard. -/
theorem len_le_maxLen (g : Bool) (i : In) : len g i ≤ maxLen i := by
  have h2 := appEnd_le g i
  unfold len pad app hs
  split <;> (try split) <;> (try split) <;> omega

/-- With the guard, a datagram is larger than the path's size only as a probe of the probed size, or as a whole
flight with no application packet behind it, at most the size the whole flight was given. -/
theorem size_ok (i : In) :
    len true i ≤ i.p ∨ (0 < i.q ∧ len true i ≤ i.q) ∨ (i.w = true ∧ pkt true i = 0 ∧ len true i ≤ base i) := by
  have hl := len_le_maxLen true i
  by_cases hq : i.q = 0
  · have hb := maxLen_whole i hq
    cases hw : i.w
    · exact Or.inl (Nat.le_trans hl (maxLen_path i hq hw))
    · by_cases hp : pkt true i = 0
      · exact Or.inr (Or.inr ⟨rfl, hp, Nat.le_trans hl hb⟩)
      · left
        have hc : ¬ (maxLen i < minRoom ∨ (hs i = 0 ∧ 0 < i.pad)) := by
          intro hc
          apply hp
          simp only [pkt, if_pos hc]
        have ha : pkt true i = app true i := by simp only [pkt, if_neg hc]
        have hf := app_fits i hq (Nat.pos_of_ne_zero hp)
        rw [ha] at hf hp
        have hpad : pad true i = 0 := by simp only [pad, if_neg hp]
        have hc1 : ¬ maxLen i < minRoom := fun h => hc (Or.inl h)
        have hc2 : ¬ (hs i = 0 ∧ 0 < i.pad) := fun h => hc (Or.inr h)
        simp only [len, if_neg hc1, if_neg hc2, hpad]
        omega
  · exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero hq, Nat.le_trans hl (maxLen_probe i (Nat.pos_of_ne_zero hq))⟩)

/-- Off a whole flight the packet's room is the datagram's room, as before #554. -/
theorem appEnd_unchanged (i : In) (hw : i.w = false) : appEnd true i = appEnd false i := by
  unfold appEnd maxLen base
  simp only [hw, Bool.false_eq_true, ite_true, ite_false]
  split <;> omega

/-- The guard changes nothing but a whole flight's datagram: every other datagram is the one of the rule before #554. -/
theorem unchanged (i : In) (hw : i.w = false) : len true i = len false i ∧ pkt true i = pkt false i := by
  have he := appEnd_unchanged i hw
  exact ⟨by unfold len pad app; rw [he], by unfold pkt app; rw [he]⟩

/-- The input of #554: a resumed Hello of 149 bytes sent whole on a 1200-byte path, early data waiting behind it. -/
def hello : In := { p := 1200, f := 1500, o := 65536, a := 1000000, q := 0, w := true, hs := 149, app := 9000, pad := 0 }

/-- The rule before #554 ran the early data behind that Hello to 1452 bytes, past the path's size. -/
theorem old_rule_breaks : 0 < pkt false hello ∧ hs hello + pkt false hello = 1452 := by decide

/-- With the guard the same early data rides behind the Hello inside the path's size. -/
theorem guard_coalesces : 0 < pkt true hello ∧ hs hello + pkt true hello = 1200 := by decide

end Vinc.TransportDgramSize
