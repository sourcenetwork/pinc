import Pinc.Axioms

/-!
# Relay path addresses

A step-for-step model of `pinc-core/src/relay_net.rs`: `relay_addr` writes the synthetic address of the path through
relay slot `relay` (a `u8`) to peer slot `peer` (a `u16`), and `relay_parts` reads them back, or returns `None` for
any other address.

An IPv4 address is four octets `240.relay.peer_hi.peer_lo`; an IPv6 address is eight 16-bit segments
`fd56:494e:43:0:0:relay:0:peer`. Octets and segments are `Nat`s below `256` and `65536` (`WellFormed`), so the `Nat`
arithmetic is the machine arithmetic of the code (`peer.to_be_bytes`, `u16::from_be_bytes`, `relay as u16`,
`s[5] as u8`, which the guard `s[5] <= 0xff` makes lossless).

The port is not part of the address a relay path names: `relay_addr` gives port `0` and `relay_parts` ignores the port
of its argument, so `relay_parts` is a left inverse of `relay_addr` (`relayParts_relayAddr`) and `relay_addr` is a left
inverse of `relay_parts` on the IP only (`relayAddr_relayParts`): an address of a relay path with another port is
still a relay path, and the address built from its parts has port `0`.
-/

namespace Pinc.RelayNet

/-- The first octet of an IPv4 relay path address (`RELAY_V4`). -/
def relayV4 : Nat := 240
/-- The first two segments of an IPv6 relay path address: `fd56:494e` (`RELAY_V6`). -/
def relayV6a : Nat := 0xfd56
def relayV6b : Nat := 0x494e

/-- An IP address: four octets or eight segments. -/
inductive Ip where
  | v4 (a b c d : Nat)
  | v6 (s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
  deriving DecidableEq, Repr

/-- Octets are bytes and segments are 16-bit words. -/
def WellFormed : Ip → Prop
  | .v4 a b c d => a < 256 ∧ b < 256 ∧ c < 256 ∧ d < 256
  | .v6 s0 s1 s2 s3 s4 s5 s6 s7 =>
      s0 < 65536 ∧ s1 < 65536 ∧ s2 < 65536 ∧ s3 < 65536 ∧ s4 < 65536 ∧ s5 < 65536 ∧ s6 < 65536 ∧ s7 < 65536

/-- `relay_addr`, the IP part. -/
def relayAddr (v6 : Bool) (relay peer : Nat) : Ip :=
  if v6 then .v6 relayV6a relayV6b 0x43 0 0 relay 0 peer
  else .v4 relayV4 relay (peer / 256) (peer % 256)

/-- `relay_parts`, on the IP part: the relay slot and the peer slot, or `none`. -/
def relayParts : Ip → Option (Nat × Nat)
  | .v4 o relay p0 p1 => if o = relayV4 then some (relay, p0 * 256 + p1) else none
  | .v6 s0 s1 s2 s3 s4 s5 s6 s7 =>
      if s0 = relayV6a ∧ s1 = relayV6b ∧ s2 = 0x43 ∧ s3 = 0 ∧ s4 = 0 ∧ s5 ≤ 0xff ∧ s6 = 0 then some (s5, s7)
      else none

/-- Whether the address is IPv6. -/
def Ip.isV6 : Ip → Bool
  | .v4 .. => false
  | .v6 .. => true

/-- A socket address: the IP and the port. -/
abbrev Sock := Ip × Nat

/-- `relay_addr`: port 0. -/
def relayAddrSock (v6 : Bool) (relay peer : Nat) : Sock := (relayAddr v6 relay peer, 0)

/-- `relay_parts` on a socket address: the port plays no part. -/
def relayPartsSock (a : Sock) : Option (Nat × Nat) := relayParts a.1

/-- `is_relay_addr`. -/
def isRelayAddr (a : Sock) : Bool := (relayPartsSock a).isSome

/-- Every address the encoder builds from a slot `< 256` and a peer `< 65536` is well formed. -/
theorem relayAddr_wf (v6 : Bool) (relay peer : Nat) (hr : relay < 256) (hp : peer < 65536) :
    WellFormed (relayAddr v6 relay peer) := by
  cases v6 <;> simp [relayAddr, WellFormed, relayV4, relayV6a, relayV6b] <;> omega

/-- The parts of the address `relay_addr` builds are the arguments, for every slot and peer. -/
theorem relayParts_relayAddr (v6 : Bool) (relay peer : Nat) (hr : relay < 256) (_hp : peer < 65536) :
    relayParts (relayAddr v6 relay peer) = some (relay, peer) := by
  cases v6
  · simp [relayAddr, relayParts, relayV4]
    omega
  · simp [relayAddr, relayParts, relayV6a, relayV6b]
    omega

/-- Whatever `relay_parts` finds in a well-formed address, `relay_addr` writes back as the same IP (of the same
family), and the slots are in range. -/
theorem relayAddr_relayParts (ip : Ip) (h : WellFormed ip) (relay peer : Nat)
    (hp : relayParts ip = some (relay, peer)) :
    relay < 256 ∧ peer < 65536 ∧ relayAddr ip.isV6 relay peer = ip := by
  cases ip with
  | v4 a b c d =>
    simp only [WellFormed] at h
    simp only [relayParts] at hp
    split at hp
    · rename_i ho
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨h.2.1, by omega, ?_⟩
      simp only [Ip.isV6, relayAddr, relayV4]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h1 : (c * 256 + d) / 256 = c := by omega
      have h2 : (c * 256 + d) % 256 = d := by omega
      rw [h1, h2, ho]
      rfl
    · simp at hp
  | v6 s0 s1 s2 s3 s4 s5 s6 s7 =>
    simp only [WellFormed] at h
    simp only [relayParts] at hp
    split at hp
    · rename_i ho
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ho
      refine ⟨by omega, h.2.2.2.2.2.2.2, ?_⟩
      simp only [Ip.isV6, relayAddr, ite_true]
      subst h0 h1 h2 h3 h4 h6
      rfl
    · simp at hp

/-- An address `relay_parts` refuses is not one `relay_addr` can build, in either family. -/
theorem relayParts_none (ip : Ip) (h : relayParts ip = none) (v6 : Bool) (relay peer : Nat) (hr : relay < 256)
    (hp : peer < 65536) : relayAddr v6 relay peer ≠ ip := by
  intro e
  have := relayParts_relayAddr v6 relay peer hr hp
  rw [e, h] at this
  cases this

/-- The family is kept. -/
theorem relayAddr_family (v6 : Bool) (relay peer : Nat) : (relayAddr v6 relay peer).isV6 = v6 := by
  cases v6 <;> simp [relayAddr, Ip.isV6]

/-- The port is not preserved: the address built has port 0, whatever port the address it was read from had. -/
theorem relayAddrSock_port (v6 : Bool) (relay peer : Nat) : (relayAddrSock v6 relay peer).2 = 0 := rfl

/-- `relay_parts` ignores the port: a relay path address is one at any port. -/
theorem relayPartsSock_port (ip : Ip) (p q : Nat) : relayPartsSock (ip, p) = relayPartsSock (ip, q) := rfl

/-- The socket address round trip: slots in range come back. -/
theorem relayPartsSock_relayAddrSock (v6 : Bool) (relay peer : Nat) (hr : relay < 256) (hp : peer < 65536) :
    relayPartsSock (relayAddrSock v6 relay peer) = some (relay, peer) :=
  relayParts_relayAddr v6 relay peer hr hp

/-- The other way, up to the port: a relay path address at port `p` is rebuilt from its parts as the same IP at
port `0`, so it equals the original exactly when `p = 0`. -/
theorem relayAddrSock_relayPartsSock (a : Sock) (h : WellFormed a.1) (relay peer : Nat)
    (hp : relayPartsSock a = some (relay, peer)) :
    (relayAddrSock a.1.isV6 relay peer).1 = a.1 ∧ ((relayAddrSock a.1.isV6 relay peer = a) ↔ a.2 = 0) := by
  obtain ⟨_, _, e⟩ := relayAddr_relayParts a.1 h relay peer hp
  refine ⟨e, ?_⟩
  constructor
  · intro h2
    rw [← h2]
    rfl
  · intro h0
    ext
    · exact e
    · exact h0.symm

/-- `is_relay_addr` is true of every address `relay_addr` builds and of no other. -/
theorem isRelayAddr_iff (a : Sock) (h : WellFormed a.1) :
    isRelayAddr a = true ↔ ∃ v6 relay peer, relay < 256 ∧ peer < 65536 ∧ (relayAddrSock v6 relay peer).1 = a.1 := by
  constructor
  · intro hi
    unfold isRelayAddr relayPartsSock at hi
    cases hr : relayParts a.1 with
    | none => rw [hr] at hi; simp at hi
    | some rp =>
      obtain ⟨relay, peer⟩ := rp
      obtain ⟨h1, h2, e⟩ := relayAddr_relayParts a.1 h relay peer hr
      exact ⟨a.1.isV6, relay, peer, h1, h2, e⟩
  · rintro ⟨v6, relay, peer, hr, hp, e⟩
    unfold isRelayAddr relayPartsSock
    rw [← e]
    simp [relayAddrSock, relayParts_relayAddr v6 relay peer hr hp]

end Pinc.RelayNet

#audit_axioms Pinc.RelayNet.relayParts_relayAddr
#audit_axioms Pinc.RelayNet.relayAddr_relayParts
#audit_axioms Pinc.RelayNet.relayParts_none
#audit_axioms Pinc.RelayNet.relayAddrSock_relayPartsSock
#audit_axioms Pinc.RelayNet.isRelayAddr_iff
