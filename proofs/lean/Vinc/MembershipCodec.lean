import Vinc.Axioms

/-!
# The hub stream codec: `len32 | type | topic_len | topic | rest`

A step-for-step model of `vinc-membership/src/codec.rs` (`Frame::parse`, `Frame::read`, `Frame::encode`, `Snap::new`,
`Proof::new`, `Proof::independent`, `entry`, `entry_bytes`).

Bytes are `Nat`s (below 256 for every input a theorem names, `Byte`); a node id is its 32 bytes. The reader of
`vinc-wire` is `rdU8` / `rdBytes` / `rdBE`; each fails with `short` exactly when the input is too short. The errors
carry the reason the code names (`Malformed("...")` is one constructor per reason) so the replay and the theorems
can say which refusal fired.

The membership frames own six type numbers; every other type passes through as `other` with its topic and rest
untouched. A snapshot holds its entries parsed (the code holds the bytes of whole alive entries; the two are the
same data, see `snapNew`).
-/

namespace Vinc.MemCodec

/-- The largest frame body. -/
def maxBody : Nat := 262144
/-- One roster entry on the wire. -/
def entryLen : Nat := 51
/-- A HELLO body after the header. -/
def helloLen : Nat := 19
/-- The most entries one SNAP frame carries. -/
def snapMax : Nat := 4096
/-- The entries a sender puts in one SNAP frame before it sets the continuation bit. -/
def snapChunk : Nat := 64
/-- The most probes a DOWN proof lists. -/
def maxProbes : Nat := 4
/-- The largest FLOOR body the broadcast layer may write (`consts::FLOOR_MAX`). -/
def floorMax : Nat := 4096

/-- The six frame types membership owns. -/
def isMem (t : Nat) : Bool := t == 1 || t == 2 || t == 3 || t == 4 || t == 12 || t == 13

/-- Every element is a byte. -/
def Byte (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

/-- Why bytes are not a frame, or a frame is not encoded. One constructor per refusal of `codec.rs`. -/
inductive Err where
  | short
  | tooLarge
  | topicOnMembership
  | helloFlag
  | helloLen
  | ackLen
  | probeLen
  | deltaLen
  | snapFlag
  | snapSize
  | snapNotAlive
  | aliveByte
  | probeCount
  | probePath
  | downLen
  | bufferSmall
  | topicLong
  deriving DecidableEq, Repr

/-- The state a DELTA entry reports. -/
inductive Alive where
  | down
  | alive
  | left
  deriving DecidableEq, Repr

def Alive.toNat : Alive → Nat
  | .down => 0
  | .alive => 1
  | .left => 2

/-- Which path carried a probe. -/
inductive Path where
  | session
  | direct
  | relay
  deriving DecidableEq, Repr

def Path.toNat : Path → Nat
  | .session => 0
  | .direct => 1
  | .relay => 2

/-- What a node announces about itself. -/
structure Rec where
  inc : Nat
  ver : Nat
  th : List Nat
  deriving DecidableEq, Repr

/-- One roster entry. -/
structure Entry where
  member : List Nat
  rc : Rec
  alive : Alive
  deriving DecidableEq, Repr

/-- One unanswered probe of a DOWN proof. -/
structure Probe where
  age : Nat
  path : Path
  deriving DecidableEq, Repr

/-- The evidence behind a DOWN. -/
structure Proof where
  sil : Nat
  probes : List Probe
  deriving DecidableEq, Repr

/-- `Proof::new`: one to `maxProbes` probes. -/
def Proof.new (sil : Nat) (ps : List Probe) : Option Proof :=
  if ps.length = 0 ∨ maxProbes < ps.length then none else some ⟨sil, ps⟩

/-- `Proof::independent`: probes went out on at least two different paths. -/
def Proof.independent (p : Proof) : Bool :=
  p.probes.any fun a => p.probes.any fun b => a.path != b.path

/-- A hub stream frame. A snapshot holds its entries (all alive). -/
inductive Frame where
  | hello (rc : Rec) (snap homed : Bool)
  | ack
  | delta (e : Entry)
  | snap (part more : Bool) (es : List Entry)
  | probe
  | down (member : List Nat) (inc : Nat) (pf : Proof)
  | other (ty : Nat) (topic rest : List Nat)
  deriving DecidableEq, Repr

/-! ## Numbers -/

/-- `k` big-endian bytes of `v`. -/
def beBytes : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v => beBytes k (v / 256) ++ [v % 256]

/-- The value of big-endian bytes. -/
def beN (bs : List Nat) : Nat := bs.foldl (fun a b => a * 256 + b) 0

def b2n (b : Bool) : Nat := if b then 1 else 0

/-! ## The reader of `vinc-wire` -/

/-- `read_u8`. -/
def rdU8 : List Nat → Except Err (Nat × List Nat)
  | [] => .error .short
  | x :: r => .ok (x, r)

/-- `read_bytes`. -/
def rdBytes (n : Nat) (r : List Nat) : Except Err (List Nat × List Nat) :=
  if n ≤ r.length then .ok (r.take n, r.drop n) else .error .short

/-- `read_u16`, `read_u32`, `read_u64` (`k` bytes). -/
def rdBE (k : Nat) (r : List Nat) : Except Err (Nat × List Nat) := do
  let (bs, r) ← rdBytes k r
  pure (beN bs, r)

/-- `only`: the reader is empty. -/
def only (e : Err) (r : List Nat) : Except Err Unit :=
  if r = [] then .ok () else .error e

/-! ## Parsing -/

/-- `entry` on the bytes of one entry (the reader's rest is dropped, as the code drops it). -/
def rdEntry (r : List Nat) : Except Err (Entry × List Nat) := do
  let (member, r) ← rdBytes 32 r
  let (inc, r) ← rdBE 8 r
  let (ver, r) ← rdBE 2 r
  let (th, r) ← rdBytes 8 r
  let (a, r) ← rdU8 r
  let alive ← match a with
    | 0 => pure Alive.down
    | 1 => pure Alive.alive
    | 2 => pure Alive.left
    | _ => throw Err.aliveByte
  pure (⟨member, ⟨inc, ver, th⟩, alive⟩, r)

def entryOf (b : List Nat) : Except Err Entry := do
  let (e, _) ← rdEntry b
  pure e

/-- `as_chunks::<ENTRY_LEN>().0`: the whole entries. -/
def chunks (bs : List Nat) : List (List Nat) :=
  if _ : entryLen ≤ bs.length then bs.take entryLen :: chunks (bs.drop entryLen) else []
termination_by bs.length
decreasing_by simp [entryLen] at *; omega

/-- One entry of a snapshot: it must be alive. -/
def snapEntry (c : List Nat) : Except Err Entry := do
  let e ← entryOf c
  if e.alive != .alive then throw Err.snapNotAlive
  pure e

/-- `Snap::new` over the entry bytes, returning the entries. -/
def snapNew (bs : List Nat) : Except Err (List Entry) :=
  if bs.length % entryLen ≠ 0 ∨ snapMax < (chunks bs).length then .error .snapSize
  else (chunks bs).mapM snapEntry

/-- The probes of a DOWN, `n` of them, each `age(4) path(1)`. -/
def rdProbes : Nat → List Nat → Except Err (List Probe × List Nat)
  | 0, r => .ok ([], r)
  | k + 1, r => do
    let (age, r) ← rdBE 4 r
    let (pb, r) ← rdU8 r
    let path ← match pb with
      | 0 => pure Path.session
      | 1 => pure Path.direct
      | 2 => pure Path.relay
      | _ => throw Err.probePath
    let (ps, r) ← rdProbes k r
    pure (⟨age, path⟩ :: ps, r)

/-- The body of a HELLO after the header. -/
def pHello (r : List Nat) : Except Err Frame := do
  let (inc, r) ← rdBE 8 r
  let (ver, r) ← rdBE 2 r
  let (th, r) ← rdBytes 8 r
  let (flags, r) ← rdU8 r
  if flags / 4 ≠ 0 then throw Err.helloFlag
  only Err.helloLen r
  pure (.hello ⟨inc, ver, th⟩ (flags % 2 == 1) (flags / 2 % 2 == 1))

/-- The body of a DELTA after the header. -/
def pDelta (r : List Nat) : Except Err Frame := do
  let (eb, r) ← rdBytes entryLen r
  let e ← entryOf eb
  only Err.deltaLen r
  pure (.delta e)

/-- The body of a SNAP after the header. -/
def pSnap (r : List Nat) : Except Err Frame := do
  let (flags, r) ← rdU8 r
  if flags / 4 ≠ 0 then throw Err.snapFlag
  let (eb, _) ← rdBytes r.length r
  let es ← snapNew eb
  pure (.snap (flags % 2 == 1) (flags / 2 % 2 == 1) es)

/-- The body of a DOWN after the header. -/
def pDown (r : List Nat) : Except Err Frame := do
  let (member, r) ← rdBytes 32 r
  let (inc, r) ← rdBE 8 r
  let (sil, r) ← rdBE 4 r
  let (n, r) ← rdU8 r
  if n = 0 ∨ maxProbes < n then throw Err.probeCount
  let (ps, r) ← rdProbes n r
  only Err.downLen r
  let some pf := Proof.new sil ps | throw Err.probeCount
  pure (.down member inc pf)

/-- What a frame of type `ty` with `topic` and the bytes `r` after the topic is. -/
def dispatch (ty : Nat) (topic r : List Nat) : Except Err Frame :=
  match ty with
  | 1 => pHello r
  | 2 => do only Err.ackLen r; pure .ack
  | 12 => do only Err.probeLen r; pure .probe
  | 3 => pDelta r
  | 4 => pSnap r
  | 13 => pDown r
  | _ => do
    let (rest, _) ← rdBytes r.length r
    pure (.other ty topic rest)

/-- `Frame::parse`: one frame body (the bytes after the length prefix). -/
def parse (body : List Nat) : Except Err Frame := do
  let (ty, r) ← rdU8 body
  let (tl, r) ← rdU8 r
  let (topic, r) ← rdBytes tl r
  if topic ≠ [] ∧ isMem ty then throw Err.topicOnMembership
  dispatch ty topic r

/-- `Frame::read`: the next frame of a stream buffer; `none` means more bytes are needed; the number is the bytes
used, the length prefix included. -/
def read (buf : List Nat) : Except Err (Option (Frame × Nat)) :=
  if buf.length < 4 then .ok none
  else
    let len := beN (buf.take 4)
    let rest := buf.drop 4
    if maxBody < len then .error .tooLarge
    else if rest.length < len then .ok none
    else do
      let f ← parse (rest.take len)
      pure (some (f, 4 + len))

/-! ## Encoding -/

def encEntry (e : Entry) : List Nat :=
  e.member ++ beBytes 8 e.rc.inc ++ beBytes 2 e.rc.ver ++ e.rc.th ++ [e.alive.toNat]

def encProbe (p : Probe) : List Nat := beBytes 4 p.age ++ [p.path.toNat]

/-- The topic a frame carries (membership frames carry none). -/
def Frame.topic : Frame → List Nat
  | .other _ t _ => t
  | _ => []

/-- The frame type number. -/
def Frame.ty : Frame → Nat
  | .hello .. => 1
  | .ack => 2
  | .delta _ => 3
  | .snap .. => 4
  | .probe => 12
  | .down .. => 13
  | .other t _ _ => t

/-- The frame body: `type | topic_len | topic | rest`. -/
def encBody : Frame → List Nat
  | .hello r s h => [1, 0] ++ beBytes 8 r.inc ++ beBytes 2 r.ver ++ r.th ++ [b2n s + 2 * b2n h]
  | .ack => [2, 0]
  | .probe => [12, 0]
  | .delta e => [3, 0] ++ encEntry e
  | .snap p m es => [4, 0, b2n p + 2 * b2n m] ++ es.flatMap encEntry
  | .down mb inc pf =>
    [13, 0] ++ mb ++ beBytes 8 inc ++ beBytes 4 pf.sil ++ [pf.probes.length] ++ pf.probes.flatMap encProbe
  | .other t tp rest => [t, tp.length] ++ tp ++ rest

/-- `Frame::body_len`. -/
def bodyLen : Frame → Nat
  | .hello .. => 2 + helloLen
  | .ack | .probe => 2
  | .delta _ => 2 + entryLen
  | .snap _ _ es => 2 + (1 + es.length * entryLen)
  | .down _ _ pf => 2 + (32 + 8 + 4 + 1 + 5 * pf.probes.length)
  | .other _ tp rest => 2 + (tp.length + rest.length)

/-- The length prefix and the body. -/
def enc (f : Frame) : List Nat := beBytes 4 (encBody f).length ++ encBody f

/-- `Frame::encode` into a buffer of `cap` bytes: the written bytes, or the refusal. The order of the checks is the
order of the writes of the code: the size limit, then the length prefix and the type byte (the buffer), then the
topic length, then the rest of the frame (the buffer). -/
def encode (cap : Nat) (f : Frame) : Except Err (List Nat) :=
  if maxBody < bodyLen f then .error .tooLarge
  else if cap < 5 then .error .bufferSmall
  else if 255 < f.topic.length then .error .topicLong
  else if cap < 4 + bodyLen f then .error .bufferSmall
  else .ok (enc f)

/-! ## Validity: the frames the code can hold -/

def Rec.valid (r : Rec) : Prop := r.inc < 2 ^ 64 ∧ r.ver < 2 ^ 16 ∧ r.th.length = 8 ∧ Byte r.th

def Entry.valid (e : Entry) : Prop := e.member.length = 32 ∧ Byte e.member ∧ e.rc.valid

def Frame.valid : Frame → Prop
  | .hello r _ _ => r.valid
  | .ack | .probe => True
  | .delta e => e.valid
  | .snap _ _ es => es.length ≤ snapMax ∧ ∀ e ∈ es, e.valid ∧ e.alive = .alive
  | .down mb inc pf =>
    mb.length = 32 ∧ Byte mb ∧ inc < 2 ^ 64 ∧ pf.sil < 2 ^ 32 ∧ 1 ≤ pf.probes.length ∧
      pf.probes.length ≤ maxProbes ∧ ∀ p ∈ pf.probes, p.age < 2 ^ 32
  | .other t tp rest => t < 256 ∧ isMem t = false ∧ tp.length ≤ 255 ∧ Byte tp ∧ Byte rest

end Vinc.MemCodec
