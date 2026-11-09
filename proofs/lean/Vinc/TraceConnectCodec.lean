import Vinc.Json
import Vinc.ConnectTicketText

/-!
# Replay of the wire format traces

The replay half of the trace validation of the wire formats of `vinc-connect` (the Rust test `trace_connect_codec`;
the TLA+ half is `TraceConnectCodec.tla`). Every recorded call of the real decoders and encoders is replayed through
the Lean functions the codec theorems are about (`decode`, `Fr.encode`, `decodeD`, `Fr.encodeD`, `Rec.parse`,
`Rec.prepare`, `Bcn.parse`, `Bcn.prepare`, `Ntc.parse`, `Ntc.prepare`, `sleepMessage`, `Tk.parse`, `Tk.encode`,
`Tk.toText`, `Tk.fromText`, `rdCands`, `encCands`): the model must return the fields the code returned, or the refusal
with the same tag, or the bytes the code wrote. Any difference exits with an error naming the line.
-/

namespace Vinc.TraceConnectCodec
open Vinc.Json Vinc.ConnCodec
open Vinc.MemCodec (beBytes beN)

/-- Whether an event belongs to this replay. -/
def isTag (t : String) : Bool :=
  ["consts", "fdec", "fenc", "ddec", "denc", "rdec", "rprep", "bdec", "bprep", "sdec", "sprep", "smsg", "tdec", "tenc",
    "ttext", "tfrom", "cdec", "cenc"].contains t

def Wt : W → String
  | .trunc n => s!"trunc:{n}"
  | .small n => s!"small:{n}"
  | .vLong => "vlong"
  | .vOver => "vover"
  | .vNonMin => "vnonmin"
  | .unexpected s => s!"unexpected:{s}"

/-- The tag of an error, the string the Rust test prints for the error it got. -/
def Et : CErr → String
  | .wire w => Wt w
  | .unknownType t => s!"type:{t}"
  | .trailing => "trailing"
  | .alias a => s!"alias:{a}"
  | .packetSize => "packet"
  | .bodySize => "body"
  | .status s => s!"status:{s}"
  | .batch w => s!"batch:{w}"
  | .noRoom => "noroom"
  | .magic => "magic"
  | .reach t => s!"reach:{t}"
  | .addrTag t => s!"addrtag:{t}"
  | .tooManyAddrs => "toomany"
  | .hintsTooLong => "hints"
  | .version v => s!"version:{v}"
  | .flags f => s!"flags:{f}"
  | .text => "text"
  | .tooLong => "toolong"
  | .dframe e => "frame/" ++ Et e
  | .daddr e => "addr/" ++ Et e
  | .taddr e => "taddr/" ++ Et e
  | .baddr e => "baddr/" ++ Et e

def mkF : K → List Nat → F
  | .node, b => .node b
  | .alias, b => .u8 (b.headD 0)
  | .u8, b => .u8 (b.headD 0)
  | .fixed _, b => .raw b
  | .addr _, b => .raw b

/-- The typed fields of a layout from their byte sequences: the fixed fields by kind, the tail raw. -/
def mkFs (pre : List K) (fs : List (List Nat)) : List F :=
  (pre.zip fs).map (fun p => mkF p.1 p.2) ++ (fs.drop pre.length).map F.raw

def frameFs (ty : Nat) (fs : List (List Nat)) : List F :=
  if ty = 13 then fs.map F.raw
  else if ty = 15 then mkFs [K.node, K.u8] fs
  else match layoutOf ty with
    | some l => mkFs l.pre fs
    | none => fs.map F.raw

def dgramFs (ty : Nat) (fs : List (List Nat)) : List F :=
  if ty = 4 then mkFs [K.node, K.u8] fs
  else match layoutD ty with
    | some l => mkFs l.pre fs
    | none => fs.map F.raw

def listList (j : J) : Except String (List (List Nat)) := do
  match j.arr? with
  | some a => a.toList.mapM natList
  | none => throw "expected an array of arrays"

def listListF (j : J) (k : String) : Except String (List (List Nat)) := do listList (← field j k)

/-- A refusal in the event: the tag. -/
def errOf (j : J) : Option String := (j.get? "err").bind (·.str?)

def sameErr (what : String) (e : CErr) (tag : String) : Except String Unit :=
  check (Et e == tag) s!"{what}: the model refuses with {Et e}, the code with {tag}"

/-- A result against the event: the same refusal or the same bytes. -/
def sameBytes (what : String) (j : J) (r : Except CErr (List Nat)) : Except String Unit := do
  match errOf j, r with
  | some tag, .error e => sameErr what e tag
  | some tag, .ok _ => throw s!"{what}: the model writes, the code refuses with {tag}"
  | none, .ok bs => check (bs == (← natList (← field j "b"))) s!"{what}: different bytes written"
  | none, .error e => throw s!"{what}: the model refuses with {Et e}, the code writes"

def fdec (j : J) : Except String Unit := do
  let r := decode (← natList (← field j "b"))
  match errOf j, r with
  | some tag, .error e => sameErr "frame" e tag
  | some tag, .ok _ => throw s!"frame: the model accepts, the code refuses with {tag}"
  | none, .ok f =>
    check (f.ty == (← natF j "ty")) "frame: different type"
    check (f.fs.map F.enc == (← listListF j "fs")) "frame: different fields"
  | none, .error e => throw s!"frame: the model refuses with {Et e}, the code accepts"

def fenc (j : J) : Except String Unit := do
  let ty ← natF j "ty"
  let f : Fr := ⟨ty, frameFs ty (← listListF j "fs")⟩
  sameBytes "frame encode" j (f.encode (← natF j "cap"))

def ddec (j : J) : Except String Unit := do
  let r := decodeD (← natList (← field j "b"))
  match errOf j, r with
  | some tag, .error e => sameErr "datagram" e tag
  | some tag, .ok _ => throw s!"datagram: the model accepts, the code refuses with {tag}"
  | none, .ok f =>
    check (f.ty == (← natF j "ty")) "datagram: different type"
    check (f.fs.map F.enc == (← listListF j "fs")) "datagram: different fields"
  | none, .error e => throw s!"datagram: the model refuses with {Et e}, the code accepts"

def denc (j : J) : Except String Unit := do
  let ty ← natF j "ty"
  let f : Fr := ⟨ty, dgramFs ty (← listListF j "fs")⟩
  sameBytes "datagram encode" j (f.encodeD (← natF j "cap"))

def rdec (j : J) : Except String Unit := do
  let r := Rec.parse (← natList (← field j "b"))
  match errOf j, r with
  | some tag, .error e => sameErr "record" e tag
  | some tag, .ok _ => throw s!"record: the model accepts, the code refuses with {tag}"
  | none, .ok r =>
    check (r.node == (← natList (← field j "node"))) "record: different node"
    check (r.home == (← natList (← field j "home"))) "record: different home"
    check (beBytes 8 r.seq == (← natList (← field j "seq"))) "record: different sequence number"
    check (r.reach == (← natF j "reach")) "record: different reach"
    check (r.addrs == (← listListF j "addrs")) "record: different addresses"
    check (r.hints == (← natList (← field j "hints"))) "record: different hints"
  | none, .error e => throw s!"record: the model refuses with {Et e}, the code accepts"

def rprep (j : J) : Except String Unit := do
  let r : Rec := ⟨← natList (← field j "node"), ← natList (← field j "home"), beN (← natList (← field j "seq")),
    ← natF j "reach", ← listListF j "addrs", ← natList (← field j "hints"), ← natList (← field j "pk"), []⟩
  sameBytes "record prepare" j (r.prepare (← natF j "cap"))

def bdec (j : J) : Except String Unit := do
  let r := Bcn.parse (← natList (← field j "b"))
  match errOf j, r with
  | some tag, .error e => sameErr "beacon" e tag
  | some tag, .ok _ => throw s!"beacon: the model accepts, the code refuses with {tag}"
  | none, .ok r =>
    check (r.node == (← natList (← field j "node"))) "beacon: different node"
    check (beBytes 8 r.seq == (← natList (← field j "seq"))) "beacon: different sequence number"
    check (r.addrs == (← listListF j "addrs")) "beacon: different addresses"
    check (r.hint == (← natList (← field j "hint"))) "beacon: different hint"
  | none, .error e => throw s!"beacon: the model refuses with {Et e}, the code accepts"

def bprep (j : J) : Except String Unit := do
  let r : Bcn := ⟨← natList (← field j "node"), beN (← natList (← field j "seq")), ← listListF j "addrs",
    ← natList (← field j "hint"), ← natList (← field j "pk"), []⟩
  sameBytes "beacon prepare" j (r.prepare (← natF j "cap"))

def sdec (j : J) : Except String Unit := do
  let r := Ntc.parse (← natList (← field j "b"))
  match errOf j, r with
  | some tag, .error e => sameErr "notice" e tag
  | some tag, .ok _ => throw s!"notice: the model accepts, the code refuses with {tag}"
  | none, .ok r =>
    check (r.node == (← natList (← field j "node"))) "notice: different node"
    check (beBytes 8 r.ts == (← natList (← field j "ts"))) "notice: different clock"
  | none, .error e => throw s!"notice: the model refuses with {Et e}, the code accepts"

def sprep (j : J) : Except String Unit := do
  let r : Ntc := ⟨← natList (← field j "node"), beN (← natList (← field j "ts")), ← natList (← field j "pk"), []⟩
  sameBytes "notice prepare" j (r.prepare (← natF j "cap"))

def smsg (j : J) : Except String Unit := do
  let m := sleepMessage (← natList (← field j "relay")) (← natList (← field j "node")) (beN (← natList (← field j "ts")))
  check (m == (← natList (← field j "b"))) "sleep message: different bytes"

def tkOf (j : J) : Except String Tk := do
  let home ← natList (← field j "home")
  pure ⟨← natList (← field j "node"), if home.isEmpty then none else some home, ← listListF j "addrs"⟩

def tdec (j : J) : Except String Unit := do
  let r := Tk.parse (← natList (← field j "b"))
  match errOf j, r with
  | some tag, .error e => sameErr "ticket" e tag
  | some tag, .ok _ => throw s!"ticket: the model accepts, the code refuses with {tag}"
  | none, .ok t => check (t == (← tkOf j)) "ticket: different fields"
  | none, .error e => throw s!"ticket: the model refuses with {Et e}, the code accepts"

def tenc (j : J) : Except String Unit := do
  sameBytes "ticket encode" j ((← tkOf j).encode (← natF j "cap"))

def ttext (j : J) : Except String Unit := do
  sameBytes "ticket text" j ((← tkOf j).toText (← natF j "cap"))

def tfrom (j : J) : Except String Unit := do
  let r := Tk.fromText (← natList (← field j "s"))
  match errOf j, r with
  | some tag, .error e => sameErr "ticket text" e tag
  | some tag, .ok _ => throw s!"ticket text: the model accepts, the code refuses with {tag}"
  | none, .ok t => check (t.bytes == (← natList (← field j "b"))) "ticket text: different ticket"
  | none, .error e => throw s!"ticket text: the model refuses with {Et e}, the code accepts"

def cdec (j : J) : Except String Unit := do
  match errOf j, rdCands (← natList (← field j "b")) with
  | some _, none => pure ()
  | some _, some _ => throw "candidates: the model accepts, the code refuses"
  | none, some cs => check (cs == (← listListF j "addrs")) "candidates: different addresses"
  | none, none => throw "candidates: the model refuses, the code accepts"

def cenc (j : J) : Except String Unit := do
  let bs := encCands (← listListF j "addrs")
  match errOf j with
  | some _ => check (decide ((← natF j "cap") < bs.length)) "candidates: the model writes, the code refuses"
  | none =>
    check (decide (bs.length ≤ (← natF j "cap"))) "candidates: the model refuses, the code writes"
    check (bs == (← natList (← field j "b"))) "candidates: different bytes"

/-- The numbers of the formats against the code's constants. -/
def consts (j : J) : Except String Unit := do
  check (maxRecordLen == (← natF j "rec")) "MAX_RECORD_LEN"
  check (maxPacket == (← natF j "pkt")) "MAX_PACKET_LEN"
  check (maxNotice == (← natF j "notice")) "MAX_NOTICE_LEN"
  check (batchFrames == (← natF j "frames")) "BATCH_MAX_FRAMES"
  check (batchBytes == (← natF j "bytes")) "BATCH_MAX_BYTES"
  check (maxFrame == (← natF j "frame")) "MAX_FRAME_LEN"
  check (maxTunnel == (← natF j "tunnel")) "MAX_TUNNEL_DATAGRAM"
  check (aliasMax == (← natF j "alias")) "ALIAS_MAX"
  check (8 + 33 + 8 + 2 + 4 * 19 + 8 + 1984 + 3373 == (← natF j "bcn")) "beacon MAX_LEN"
  check (33 + 8 + 1984 + 3373 == (← natF j "ntc")) "notice MAX_LEN"

def replayEvent (j : J) : Except String Unit := do
  match ← strF j "t" with
  | "consts" => consts j
  | "fdec" => fdec j
  | "fenc" => fenc j
  | "ddec" => ddec j
  | "denc" => denc j
  | "rdec" => rdec j
  | "rprep" => rprep j
  | "bdec" => bdec j
  | "bprep" => bprep j
  | "sdec" => sdec j
  | "sprep" => sprep j
  | "smsg" => smsg j
  | "tdec" => tdec j
  | "tenc" => tenc j
  | "ttext" => ttext j
  | "tfrom" => tfrom j
  | "cdec" => cdec j
  | "cenc" => cenc j
  | t => throw s!"unknown codec event {t}"

end Vinc.TraceConnectCodec
