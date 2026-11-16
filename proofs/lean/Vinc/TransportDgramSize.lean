/-!
# The size of a datagram

A model of how big `build_datagram` (`vinc-transport` `conn/send.rs`) makes one datagram for a path, as
`proofs/tla/DgramSize.tla` has it, for every input over unbounded sizes.

The story: a connection writes one datagram for a path it believes carries `p` bytes. The datagram may start with a
fragment of the handshake and then hold one application packet, or the zero padding the handshake still owes. Two
datagrams are built larger than `p` on purpose: a first flight sent whole (up to 1452 bytes, and no more than the
interface carries on the path's address family: its MTU less the IP and UDP headers), and a path MTU probe of the probed size. Anything else larger than `p` can be dropped by a router or
black-holed with no ICMP back.

What it proves, with the guard of #554 (the application packet's room ends at `p`, or at the probe's size):
- an application packet that is not a probe ends at or before `p` (`app_fits`);
- a datagram is larger than `p` only as a probe or as a whole flight with no packet behind it (`size_ok`);
- a datagram never runs past the caller's buffer or the amplification room (`bounded`);
- every datagram but a whole flight's is exactly the one of the rule before #554 (`unchanged`);
- a datagram above `p` that is not a probe is no larger than the interface carries on the path's family
  (`iface_ok`); the rule before #584, which gave a whole flight the interface's MTU headers included, broke it: a
  1280-byte interface got a 1280-byte datagram on a link that carries 1252 (`old_iface_breaks`);
- the rule before #554 broke `app_fits`: a 149-byte resumed Hello sent whole on a 1200-byte path had its early data
  run to 1452 bytes (`old_rule_breaks`).
-/

namespace Vinc.TransportDgramSize

/-- `MIN_ROOM` of the code: the smallest room worth a datagram. -/
def minRoom : Nat := 24
/-- `PROBE_MTU` of the code: the first probe size, and the most a whole flight takes. -/
def probeMtu : Nat := 1452

/-- The IPv4 and UDP headers beyond a datagram's UDP payload. -/
def headersV4 : Nat := 28
/-- The IPv6 and UDP headers beyond a datagram's UDP payload. -/
def headersV6 : Nat := 48

/-- What `build_datagram` reads for one datagram. -/
structure In where
  /-- The path's datagram size (`p.mtu.current`). -/
  p : Nat
  /-- The interface MTU, IP and UDP headers included (`p.info.interface_mtu`). -/
  f : Nat
  /-- Whether the path is IPv6 (`p.info.v6`). -/
  v6 : Bool
  /-- The caller's buffer (`out.len()`). -/
  o : Nat
  /-- What the amplification budget still allows (`amp_room`). -/
  a : Nat
  /-- The probe size `probe_size` returned, 0 for none. -/
  q : Nat
  /-- The first flight with its framing (`whole_len() + FLIGHT_OVERHEAD`), 0 for none or when whole flights are off. -/
  fl : Nat
  /-- The handshake bytes `write_handshake` would write. -/
  hs : Nat
  /-- The bytes the application packet would take. -/
  app : Nat
  /-- The zero padding the handshake still owes. -/
  pad : Nat

/-- `interface_payload`: the largest UDP payload the interface carries on the path's address family. -/
def room (i : In) : Nat := i.f - (if i.v6 then headersV6 else headersV4)
/-- `whole`: the first flight goes whole when it fits 1452 bytes and the interface's room. -/
def whole (i : In) : Bool := decide (0 < i.fl ∧ i.fl ≤ min probeMtu (room i))
/-- `base`: a whole flight may take the larger of the path's size and 1452 (or the interface's room when smaller). -/
def base (i : In) : Nat := if whole i then max i.p (min probeMtu (room i)) else i.p
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
theorem maxLen_path (i : In) (hq : i.q = 0) (hw : whole i = false) : maxLen i ≤ i.p := by
  unfold maxLen base; simp only [hq, hw, ite_true, Bool.false_eq_true, ite_false]; omega

/-- The datagram is at most `max_len`, with or without the guard. -/
theorem len_le_maxLen (g : Bool) (i : In) : len g i ≤ maxLen i := by
  have h2 := appEnd_le g i
  unfold len pad app hs
  split <;> (try split) <;> (try split) <;> omega

/-- With the guard, a datagram is larger than the path's size only as a probe of the probed size, or as a whole
flight with no application packet behind it, at most the size the whole flight was given. -/
theorem size_ok (i : In) :
    len true i ≤ i.p ∨ (0 < i.q ∧ len true i ≤ i.q) ∨ (whole i = true ∧ pkt true i = 0 ∧ len true i ≤ base i) := by
  have hl := len_le_maxLen true i
  by_cases hq : i.q = 0
  · have hb := maxLen_whole i hq
    cases hw : whole i
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
theorem appEnd_unchanged (i : In) (hw : whole i = false) : appEnd true i = appEnd false i := by
  unfold appEnd maxLen base
  simp only [hw, Bool.false_eq_true, ite_true, ite_false]
  split <;> omega

/-- The guard changes nothing but a whole flight's datagram: every other datagram is the one of the rule before #554. -/
theorem unchanged (i : In) (hw : whole i = false) : len true i = len false i ∧ pkt true i = pkt false i := by
  have he := appEnd_unchanged i hw
  exact ⟨by unfold len pad app; rw [he], by unfold pkt app; rw [he]⟩

/-- The input of #554: a resumed Hello of 149 bytes sent whole on a 1200-byte path, early data waiting behind it. -/
def hello : In :=
  { p := 1200, f := 1500, v6 := true, o := 65536, a := 1000000, q := 0, fl := 149, hs := 149, app := 9000, pad := 0 }

/-- The rule before #554 ran the early data behind that Hello to 1452 bytes, past the path's size. -/
theorem old_rule_breaks : 0 < pkt false hello ∧ hs hello + pkt false hello = 1452 := by decide

/-- With the guard the same early data rides behind the Hello inside the path's size. -/
theorem guard_coalesces : 0 < pkt true hello ∧ hs hello + pkt true hello = 1200 := by decide

/-- A datagram above the path's size that is not a probe (a whole flight's) is no larger than the interface carries on
the path's address family. -/
theorem iface_ok (i : In) (hq : i.q = 0) (h : i.p < len true i) : len true i ≤ room i := by
  have hl := len_le_maxLen true i
  have hb := maxLen_whole i hq
  by_cases hw : whole i = true
  · have hbase : base i = max i.p (min probeMtu (room i)) := by simp [base, hw]
    omega
  · have hw' : whole i = false := by simpa using hw
    have := maxLen_path i hq hw'
    omega

/-- The rule before #584: a whole flight's room was the interface's MTU with the headers still in it. -/
def oldBase (i : In) : Nat := max i.p (min probeMtu i.f)

/-- A 1280-byte interface on IPv4 carries 1252 bytes, and the rule before #584 gave a whole flight 1280. -/
theorem old_iface_breaks :
    room { p := 1200, f := 1280, v6 := false, o := 0, a := 0, q := 0, fl := 1269, hs := 0, app := 0, pad := 0 } = 1252 ∧
    oldBase { p := 1200, f := 1280, v6 := false, o := 0, a := 0, q := 0, fl := 1269, hs := 0, app := 0, pad := 0 } = 1280 := by
  decide

/-- With the rule of #584 the same flight (1269 bytes with its framing) does not fit that interface, so it is cut at the
path's size from the start. -/
theorem new_rule_splits :
    whole { p := 1200, f := 1280, v6 := false, o := 0, a := 0, q := 0, fl := 1269, hs := 0, app := 0, pad := 0 } = false := by
  decide

end Vinc.TransportDgramSize
