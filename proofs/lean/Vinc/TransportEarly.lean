/-!
# Packets that arrive before their keys: the model

A model of the buffer of early packets of `vinc-transport` (`conn/recv.rs` `on_packet`, `on_short`, `hold_early`,
`handle_inner`; `conn/drive.rs` `on_hs_event`, `drain_early`; `conn/life.rs` `begin_close`, `release_buffers`;
`stream/datagram.rs` `EarlyData`), as `proofs/tla/EarlyOps.tla` has it, over unbounded `Nat`. `Vinc.TraceEarly`
replays the recorded calls of real connections and of the real buffer through these functions; the theorems are
in `Vinc.TransportEarlyThm`.

A connection is the phase, whether the 0-RTT and the 1-RTT receive keys exist, the packets held (oldest first) and
the counters the code keeps. A packet has its place in the order of arrival, a kind (`z` a 0-RTT long packet, `s` a
1-RTT short one) and a fate when it is opened: it authenticates, it does not, or it authenticates and its frames
close the connection. Which keys open it is not modelled, only that its kind needs the keys the connection has;
the datagram length `dlen` is the one thing of the bytes that counts (toward the amplification budget).
-/

namespace Vinc.TransportEarly

inductive Kind | z | s
  deriving BEq, DecidableEq, Repr

inductive Fate | opens | fails | closes
  deriving BEq, DecidableEq, Repr

/-- `closed` stands for both `Closing` and `Closed`, which refuse alike. -/
inductive Ph | hs | up | closed
  deriving BEq, DecidableEq, Repr

inductive Out | held | full | undec | ok | closed
  deriving BEq, DecidableEq, Repr

structure Pkt where
  id : Nat
  kind : Kind
  fate : Fate
  deriving BEq, Repr

structure C where
  client : Bool
  ph : Ph := .hs
  er : Bool := false
  rv : Bool := false
  q : List Pkt := []
  nb : Nat := 0
  nd : Nat := 0
  nu : Nat := 0
  rx : Nat := 0
  deriving BEq, Repr

/-- `begin_close` and `silent_close`: `release_buffers` lets go of every packet held. -/
def shut (c : C) : C := { c with ph := .closed, q := [] }

/-- `hold_early`: `EarlyData::push` keeps the packet while fewer than `cap` are held and the pool has room. -/
def holdPkt (c : C) (cap : Nat) (room : Bool) (p : Pkt) : Out × C :=
  if c.q.length < cap ∧ room = true then (.held, { c with q := c.q ++ [p], nb := c.nb + 1 })
  else (.full, { c with nd := c.nd + 1 })

/-- `on_zero_rtt`, and `on_short` with the 1-RTT keys in place: opened or refused, never held. A 1-RTT packet that
opens ends the use of the early keys; one that fails is counted as undecryptable, a 0-RTT one is not. -/
def direct (c : C) (p : Pkt) : Out × C :=
  match p.kind with
  | .z =>
    if c.er = false ∨ p.fate = .fails then (.undec, c)
    else (.ok, if p.fate = .opens then c else shut c)
  | .s =>
    if p.fate = .fails then (.undec, { c with nu := c.nu + 1 })
    else
      let c1 := { c with er := false }
      (.ok, if p.fate = .opens then c1 else shut c1)

/-- Whether `on_packet` keeps the packet for want of keys: a 0-RTT packet on a server in its handshake that has no
early keys yet, a 1-RTT packet in a handshake before the 1-RTT keys exist. -/
def eligible (c : C) (p : Pkt) : Bool :=
  decide (c.ph = .hs) && (match p.kind with
    | .z => decide (c.er = false ∧ c.client = false)
    | .s => decide (c.rv = false))

/-- The packet of a datagram that is counted already: held if it is eligible, refused when a 1-RTT packet finds no
keys outside a handshake, opened or refused otherwise. -/
def live (c1 : C) (cap : Nat) (room : Bool) (p : Pkt) : Out × C :=
  if eligible c1 p then holdPkt c1 cap room p
  else if p.kind = .s ∧ c1.rv = false then (.undec, c1)
  else direct c1 p

/-- `handle_inner` counts the datagram before any packet of it is looked at; a closed connection refuses it first. -/
def recv (c : C) (cap : Nat) (room : Bool) (p : Pkt) (dlen : Nat) : Out × C :=
  if c.ph = .closed then (.closed, c) else live { c with rx := c.rx + dlen } cap room p

/-- `on_hs_event`, `EarlyKeys`: the server has the 0-RTT receive keys. -/
def earlyKeys (c : C) : C := { c with er := true }

/-- `drain_early`: the packets held, oldest first, each taken out and tried once; a close ends it and the packets
still held go with the rest. The ids tried come with the state. -/
def drainQ (c : C) : List Pkt → C × List Nat
  | [] => ({ c with q := [] }, [])
  | p :: t =>
    let x := direct c p
    if x.2.ph = .closed then (x.2, [p.id])
    else
      let r := drainQ x.2 t
      (r.1, p.id :: r.2)

/-- `on_hs_event`, `Established`: the 1-RTT keys are installed, then the held packets are drained. -/
def established (c : C) : C × List Nat := drainQ { c with ph := .up, rv := true } c.q

end Vinc.TransportEarly
