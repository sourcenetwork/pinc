import Pinc.Axioms

/-!
# The WebSocket framing of the carrier (`carrier/ws.rs`), the model

`encode` and `Decoder::decode` of `pinc-connect` `carrier/ws.rs` as total executable functions over unbounded `Nat`,
checks in the order the code makes them (`proofs/tla/ConnectWsOps.tla` is the TLA+ twin; the theorems are in
`ConnectWsThm.lean`). Bytes are `Nat`s, a buffer is a function `Nat → Nat` of which the first `n` positions are
held (so that "the same bytes with more behind them" is the same function with a larger `n`).

Where the code departs from RFC 6455, by design: text frames and the opcodes 3 to 7 and 11 to 15 are refused (a binary
carrier); a close with a one-byte payload is accepted and reports no status (the RFC calls it a protocol error); the
UTF-8 check of a close reason is not made; the decoder does not stop after a close (the host does); the encoder will
write a continuation opcode with FIN set (a frame its own decoder refuses unless a message is open).
-/

namespace Pinc.ConnectWs

inductive Peer where
  | client
  | server
  deriving DecidableEq, Repr

inductive Err where
  | reserved | opcode | mask | control | sequence | tooLong | lenForm | noRoom
  deriving DecidableEq, Repr

inductive Kind where
  | data | close | ping | pong
  deriving DecidableEq, Repr

/-- apply_mask: XOR with the key, repeated; `j` is the index of the first byte of the list. -/
def maskAt (k : List Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | j, b :: t => (b ^^^ k.getD (j % 4) 0) :: maskAt k (j + 1) t

def mask (k d : List Nat) : List Nat := maskAt k 0 d

def be16 (n : Nat) : List Nat := [n / 256, n % 256]

def isOp (o : Nat) : Bool := o == 0 || o == 2 || o == 8 || o == 9 || o == 10
def isCtl (o : Nat) : Bool := decide (8 ≤ o)

def kindOf (o : Nat) : Kind :=
  if o == 0 || o == 2 then .data else if o == 8 then .close else if o == 9 then .ping else .pong

/-! ## encode -/

/-- The header of a frame of `n` payload bytes: FIN and the opcode, the length in its shortest form with the mask bit,
and the mask key (the 7-bit field up to 125, else 126 and two bytes). -/
def encHdr (op n : Nat) (mk : Option (List Nat)) : List Nat :=
  let mb := if mk.isSome then 128 else 0
  (128 + op) :: ((if n ≤ 125 then [mb + n] else (mb + 126) :: be16 n) ++ mk.getD [])

/-- The payload as written: masked for a client. -/
def encBody (mk : Option (List Nat)) (pl : List Nat) : List Nat :=
  match mk with | some k => mask k pl | none => pl

/-- `encode(opcode, payload, mask, out)`: `mk` is the 4-byte key or none, `cap` is `out.len()`; the bytes written. -/
def encode (mp op : Nat) (pl : List Nat) (mk : Option (List Nat)) (cap : Nat) : Except Err (List Nat) :=
  let n := pl.length
  if n > mp then .error .tooLong
  else if isCtl op && n > 125 then .error .control
  else if (encHdr op n mk).length + n > cap then .error .noRoom
  else .ok (encHdr op n mk ++ encBody mk pl)

/-! ## decode -/

inductive DRes where
  | idle
  | err (e : Err)
  | frame (k : Kind) (pl : List Nat) (st : Option Nat) (used : Nat) (inm : Bool)
  deriving DecidableEq, Repr

/-- The bytes `[s, s + len)` of the buffer. -/
def slice (B : Nat → Nat) (s len : Nat) : List Nat := (List.range len).map fun j => B (s + j)

/-- The 64-bit big-endian value of the bytes 2 to 9. -/
def v64 (B : Nat → Nat) : Nat :=
  ((((((B 2 * 256 + B 3) * 256 + B 4) * 256 + B 5) * 256 + B 6) * 256 + B 7) * 256 + B 8) * 256 + B 9

/-- The length the header declares and the header size, when those bytes are held (`n` is the held length). -/
def declared (B : Nat → Nat) (n l7 : Nat) : Option (Nat × Nat) :=
  if l7 = 126 then (if n < 4 then none else some (B 2 * 256 + B 3, 4))
  else if l7 = 127 then (if n < 10 then none else some (v64 B, 10))
  else some (l7, 2)

/-- The length in its shortest form: the 7-bit field up to 125, the 16-bit form from 126, the 64-bit form from 65536. -/
def canon (l7 len : Nat) : Bool :=
  if l7 = 126 then decide (126 ≤ len) else if l7 = 127 then decide (65536 ≤ len) else true

/-- The frame `decode` returns once the whole frame is held: the payload unmasked, the bytes it took, the state after. -/
def accept (B : Nat → Nat) (b0 b1 len head : Nat) (inm : Bool) : DRes :=
  let o := b0 % 16
  let masked := decide (128 ≤ b1)
  let start := head + (if masked then 4 else 0)
  let raw := slice B start len
  let pl := if masked then mask (slice B head 4) raw else raw
  .frame (kindOf o) (if o == 8 then [] else pl)
    (if o == 8 && 2 ≤ len then some ((pl.getD 0 0) * 256 + pl.getD 1 0) else none) (start + len)
    (if isCtl o then inm else !decide (128 ≤ b0))

/-- `Decoder::decode` on the first `n` bytes of `B`, in the state `inm` (a fragmented message is open). -/
def decode (mp : Nat) (peer : Peer) (inm : Bool) (B : Nat → Nat) (n : Nat) : DRes :=
  if n < 2 then .idle
  else
    let b0 := B 0
    let b1 := B 1
    let o := b0 % 16
    let fin := decide (128 ≤ b0)
    let masked := decide (128 ≤ b1)
    let ctl := isCtl o
    if b0 / 16 % 8 ≠ 0 then .err .reserved
    else if !isOp o then .err .opcode
    else if masked != decide (peer = .client) then .err .mask
    else match declared B n (b1 % 128) with
      | none => .idle
      | some (len, head) =>
        if !canon (b1 % 128) len then .err .lenForm
        else if len > mp then .err .tooLong
        else if ctl && (!fin || len > 125) then .err .control
        else if !ctl && (decide (o = 0) != inm) then .err .sequence
        else if masked && n < head + 4 then .idle
        else if n < head + (if masked then 4 else 0) + len then .idle
        else accept B b0 b1 len head inm

/-- A list as a buffer (zero behind its end). -/
def bf (l : List Nat) : Nat → Nat := fun i => l.getD i 0

end Pinc.ConnectWs
