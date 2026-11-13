import Vinc.Record

/-!
# The protected carrier: the model

A model of `vinc-connect` `carrier/session.rs` (`ProtectedCarrier`), as `proofs/tla/ConnectCarrierOps.tla` has it,
over unbounded `Nat`: the unit framing of the byte stream (a 2-byte big-endian length, then that many bytes), the
bounded input buffer and its lazy release, the handshake units (the handshake machine is a step that yields keys: its
outputs are an input `Hs`, it is proved in `Vinc.Handshake*`), the record units opened at the receive packet number,
and the seal of a frame at the send packet number.

The host feeds the stream in order, so the input buffer is the stream segment `[rd, wr)`; `cons` is the length of the
last unit, dropped at the next `receive` or `poll`. The stream is given by `Strm`: `hdr o` is the value of the length
bytes at offset `o`, `opens o pn` whether the unit at `o` authenticates under the receive key at packet number `pn`
(its length bytes are the associated data), `fok o` whether its plaintext decodes as a frame (the frame codec is
proved in `Vinc.ConnectFrame*`).

The packet keys are `Vinc.Record`'s: the carrier calls `sealK` and `openK`, and the send key is kept as a
`Record.Sys`, the key with the (secret, packet number) of every seal it made, so `Record.no_nonce_reuse` applies to
it unchanged (`Vinc.ConnectCarrierThm`). `Vinc.TraceConnectCarrier` replays the recorded calls of the real code
through these functions.
-/

namespace Vinc.ConnectCarrier
open Vinc.Record (Key Sys sealK openK)

/-- `Stage`: dialing or accepting (the handshake), open, ended. -/
inductive Stage where
  | hs
  | open_
  | ended
  deriving DecidableEq, Repr

/-- The sizes: `IN_LEN`, `MAX_MESSAGE_LEN`, `MAX_UNIT_LEN`, `Aead::TAG_LEN`, `OUT_LEN`, `MAX_FRAME_LEN`, and the AEAD
and limits of the packet keys. -/
structure Konst where
  inl : Nat
  maxm : Nat
  maxu : Nat
  tag : Nat
  outn : Nat
  maxf : Nat
  aead : Record.Aead
  lim : Record.Limits

/-- `CarrierError`. -/
inductive Err where
  | unitSize
  | authentication
  | keyLimit
  | notOpen
  | outputFull
  | noRoom
  | frame
  | record
  | closed
  | handshake
  deriving DecidableEq, Repr

/-- What a call answered: `Poll` (with `opened` for `Poll::Open`), an error, or `ok` for a seal. -/
inductive Res where
  | idle
  | hs
  | kreq
  | opened
  | frame
  | ok
  | err (e : Err)
  deriving DecidableEq, Repr

/-- The state of one carrier. -/
structure C where
  st : Stage := .hs
  rd : Nat := 0
  wr : Nat := 0
  cons : Nat := 0
  out : Nat := 0
  spn : Nat := 0
  rpn : Nat := 0
  /-- The send key, with the log of its seals. -/
  sk : Option Sys := none
  rk : Option Key := none
  /-- The handshake machine waits for a key operation. -/
  kr : Bool := false

/-- The stream the host feeds, by offset. -/
structure Strm where
  hdr : Nat → Nat
  opens : Nat → Nat → Bool
  fok : Nat → Bool

/-- An output of the handshake machine. -/
inductive Out where
  | send (m : Nat)
  | est (kok : Bool)
  | fail

/-- A handshake step: the machine refused the input, or its outputs in order; whether a key operation is pending after
it; the names of the secrets it yields. -/
structure Hs where
  herr : Bool
  outs : List Out
  kreq : Bool
  sb : Nat
  rb : Nat

def inLen (c : C) : Nat := c.wr - c.rd
def free (k : Konst) (c : C) : Nat := k.inl - inLen c

/-- `release()`. -/
def release (c : C) : C := if c.cons > 0 then { c with rd := c.rd + c.cons, cons := 0 } else c

/-- `end()`. -/
def endC (c : C) : C := { c with st := .ended, sk := none, rk := none }

/-- `receive`: the bytes taken and the new state. -/
def receive (k : Konst) (c : C) (n : Nat) : Nat × C :=
  let c1 := release c
  let t := min n (k.inl - inLen c1)
  (t, { c1 with wr := c1.wr + t })

/-- `transmit`. -/
def transmit (c : C) (cap : Nat) : Nat × C :=
  let t := min cap c.out
  (t, { c with out := c.out - t })

/-- The outcome of `unit_len(max)`. -/
inductive UL where
  | idle
  | bad
  | unit (len : Nat)
  deriving DecidableEq

def unitLen (S : Strm) (c : C) (max : Nat) : UL :=
  if inLen c < 2 then .idle
  else
    let len := S.hdr c.rd
    if len = 0 ∨ max < len then .bad
    else if 2 + len ≤ inLen c then .unit len else .idle

/-- The outcome collected by `drive!`. -/
inductive DRes where
  | ok
  | est
  | estbad
  | err (e : Err)
  deriving DecidableEq

def driveR (k : Konst) : Nat → List Out → DRes → Nat × DRes
  | out, [], r => (out, r)
  | out, .send m :: t, r =>
    if 65535 < m then driveR k out t (.err .unitSize)
    else if k.outn < out + 2 + m then driveR k out t (.err .outputFull)
    else driveR k (out + 2 + m) t r
  | out, .est kok :: t, r =>
    driveR k out t (match r with
      | .ok | .est | .estbad => if kok then .est else .estbad
      | e => e)
  | out, .fail :: t, _ => driveR k out t (.err .handshake)

/-- The machine's step and the drain of its outputs. -/
def hsRun (k : Konst) (out : Nat) (hs : Hs) : Nat × DRes :=
  if hs.herr then (out, .err .handshake) else driveR k out hs.outs .ok

def newKey (k : Konst) (b : Nat) : Key := Key.fresh k.aead k.lim b

/-- `finish()`. -/
def finish (k : Konst) (c : C) (r : DRes) (hs : Hs) : C × Res :=
  match r with
  | .err e => (endC c, .err e)
  | .ok => ({ c with kr := hs.kreq }, if hs.kreq then .kreq else .hs)
  | .estbad => (endC c, .err .handshake)
  | .est => ({ c with st := .open_, sk := some ⟨newKey k hs.sb, []⟩, rk := some (newKey k hs.rb), kr := false },
             .opened)

def pollHs (k : Konst) (S : Strm) (c : C) (hs : Hs) : C × Res :=
  match unitLen S c k.maxm with
  | .idle => (c, .idle)
  | .bad => (endC c, .err .unitSize)
  | .unit len =>
    let d := hsRun k c.out hs
    finish k { c with cons := 2 + len, out := d.1 } d.2 hs

/-- `poll_record()`. -/
def pollRecord (k : Konst) (S : Strm) (c : C) : C × Res :=
  match unitLen S c k.maxu with
  | .idle => (c, .idle)
  | .bad => (endC c, .err .unitSize)
  | .unit len =>
    if len ≤ k.tag then (endC c, .err .unitSize)
    else match c.rk with
      | none => (endC c, .err .notOpen)
      | some key =>
        match openK key c.rpn (S.opens c.rd c.rpn) with
        | (_, some .authentication) => (endC c, .err .authentication)
        | (_, some .keyRollRequired) => (endC c, .err .keyLimit)
        | (_, some _) => (endC c, .err .record)
        | (key', none) =>
          ({ c with rk := some key', rpn := c.rpn + 1, cons := 2 + len }, if S.fok c.rd then .frame else .err .frame)

/-- `poll()`. -/
def poll (k : Konst) (S : Strm) (c : C) (hs : Hs) : C × Res :=
  let c1 := release c
  match c1.st with
  | .ended => (c1, .err .closed)
  | .open_ => pollRecord k S c1
  | .hs => pollHs k S c1 hs

/-- `key_response()`: refused with `Closed` (and the carrier ends) once the handshake is over. -/
def keyResponse (k : Konst) (c : C) (hs : Hs) : C × Res :=
  if c.st ≠ .hs then (endC c, .err .closed)
  else
    let d := hsRun k c.out hs
    finish k { c with out := d.1 } d.2 hs

/-- `answer_soft()`: with no key request outstanding the carrier ends with `Handshake`. -/
def answerSoft (k : Konst) (c : C) (hs : Hs) : C × Res :=
  if ¬ (c.st = .hs ∧ c.kr = true) then (endC c, .err .handshake) else keyResponse k c hs

/-- `seal_in_place(n)`: the unit length when it succeeds. -/
def sealIn (k : Konst) (c : C) (n cap : Nat) : C × Res × Nat :=
  if c.st ≠ .open_ then (c, .err (if c.st = .ended then .closed else .notOpen), 0)
  else if 65535 < n + k.tag then (c, .err .unitSize, 0)
  else match c.sk with
    | none => (c, .err .notOpen, 0)
    | some s =>
      if cap < 2 + n + k.tag then (c, .err .noRoom, 0)
      else match sealK s.key c.spn with
        | (_, none) => ({ c with sk := some (s.seal c.spn), spn := c.spn + 1 }, .ok, 2 + n + k.tag)
        | (_, some .keyRollRequired) => (endC c, .err .keyLimit, 0)
        | (_, some _) => (endC c, .err .record, 0)

/-- What the frame encoder does in `out[2..]`. -/
inductive Fe where
  | ok
  | wire
  | frame
  deriving DecidableEq

/-- `seal(frame)`: `plen` bytes encoded, or the encoder's refusal. -/
def sealFrame (k : Konst) (c : C) (plen cap : Nat) (fe : Fe) : C × Res × Nat :=
  if cap < 2 ∨ fe = .wire then (c, .err .noRoom, 0)
  else if fe = .frame then (c, .err .frame, 0)
  else sealIn k c plen cap

/-- `seal_bytes(plain)`. -/
def sealBytes (k : Konst) (c : C) (plen cap : Nat) : C × Res × Nat :=
  if plen = 0 ∨ k.maxf < plen then (c, .err .unitSize, 0)
  else if cap < 2 + plen then (c, .err .noRoom, 0)
  else sealIn k c plen cap

/-- `dial()`: the first handshake output is buffered at once. -/
def dial (k : Konst) (hs : Hs) : C × Res :=
  match hsRun k 0 hs with
  | (out, .ok) | (out, .est) | (out, .estbad) => ({ out, kr := hs.kreq }, .ok)
  | (_, .err e) => ({ st := .ended }, .err e)

/-- `accept()`. -/
def accept : C := {}

end Vinc.ConnectCarrier
