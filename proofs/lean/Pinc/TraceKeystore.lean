import Pinc.Json
import Pinc.KeystoreStore
import Pinc.KeystoreTpm

/-!
# Replay of the `pinc-keystore` traces

The replay half of the trace validation of `pinc-keystore` (the Rust tests `trace_keystore` and `trace_keystore_tpm`;
the TLA+ half is `TraceKeystore.tla`). The software events (`t = "ks"`) are folded through the table model of
`Pinc.KeystoreStore` (handles, removal, the answer of every operation, the key host) and the sealed format of
`Pinc.KeystoreSealed`; the TPM events (`t = "kt"`) through `Pinc.KeystoreTpm` (the reading of a response, the layout of
every command, the program of every store operation and its handles, the sealed header and the order of the errors of
`unseal`). Any difference exits with an error naming the line.
-/

namespace Pinc.TraceKeystore
open Pinc.Json Pinc.CryptoKdf Pinc.KeystoreStore Pinc.KeystoreTpm
open Pinc.CryptoIdentity (Alg)

def isTag (t : String) : Bool := t == "ks" || t == "kt"

/-- The model state of the software trace. -/
structure W where
  world : World := World.empty
  idx : List (Nat × Nat) := []
  sealed : Nat → List (Bytes × Bytes) := fun _ => []
  host : World := ⟨100, fun _ => []⟩
  hbound : List (Nat × Nat) := []
  tsealed : List Bytes := []

instance : Inhabited W := ⟨{}⟩

def algOf (n : Nat) : Except String Alg :=
  match Alg.ofTag n with
  | some a => pure a
  | none => throw s!"algorithm tag {n}"

def bytesF (j : J) (k : String) : Except String Bytes := do natList (← field j k)

def errName : KErr → String
  | .unknownKey => "UnknownKey"
  | .wrongKeyKind => "WrongKeyKind"
  | .crypto .invalidLength => "Crypto(InvalidLength)"
  | .crypto _ => "Crypto(other)"
  | .entropy => "Entropy"

def hostWorld : World :=
  ⟨100, fun s => if s = 2 then [(1, .id .ed25519), (2, .id .ecdsaP256), (3, .id .mlDsa65), (4, .id .hybrid), (5, .kem)] else []⟩

def kindOf (kind : String) (alg : Nat) : Except String Kind :=
  match kind with
  | "kem" => pure .kem
  | _ => do pure (.id (← algOf alg))

/-- The handle of the model for a test index. -/
def handleOf (w : W) (h : Nat) : Except String Nat :=
  match w.idx.lookup h with
  | some m => pure m
  | none => throw s!"handle {h} was never made"

/-- Replay a software event. -/
def replaySoft (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "new" =>
    let s ← natF j "s"
    let kind ← kindOf (← strF j "kind") (← natF j "alg")
    check (← boolF j "distinct") "a handle repeats"
    let (world, hm) := add w.world s kind
    pure { w with world := world, idx := (← natF j "h", hm) :: w.idx }
  | "rm" =>
    let s ← natF j "s"
    let hm ← handleOf w (← natF j "h")
    let (world, found) := remove w.world s hm
    check (found == (← boolF j "res")) "remove: whether the key was there"
    pure { w with world := world }
  | "sign" =>
    let s ← natF j "s"
    let hm ← handleOf w (← natF j "h")
    let res ← strF j "res"
    match sign w.world s hm with
    | .ok a =>
      check (res == "ok" && (← natF j "alg") == a.tag && (← natF j "len") == a.sigLen && (← boolF j "ver")) "sign"
    | .error e => check (res == errName e) s!"sign: model {errName e}"
    pure w
  | "pub" =>
    let s ← natF j "s"
    let hm ← handleOf w (← natF j "h")
    let res ← strF j "res"
    match sign w.world s hm with
    | .ok a => check (res == "ok" && (← natF j "alg") == a.tag && (← natF j "len") == a.pkLen) "public"
    | .error .wrongKeyKind => check (res == "WrongKeyKind") "public: wrong kind"
    | .error e => check (res == errName e) "public"
    pure w
  | "nodeid" =>
    let s ← natF j "s"
    let hm ← handleOf w (← natF j "h")
    let res ← strF j "res"
    match sign w.world s hm with
    | .ok _ => check (res == "ok" && (← boolF j "same")) "node_id"
    | .error e => check (res == errName e && (← boolF j "same")) "node_id error"
    pure w
  | "dec" =>
    let s ← natF j "s"
    let hm ← handleOf w (← natF j "h")
    let res ← strF j "res"
    match decapsulate w.world s hm (← natF j "ctlen") with
    | .ok () => check (res == "ok" && (← boolF j "agree")) "decapsulate"
    | .error e => check (res == errName e) s!"decapsulate: model {errName e}"
    pure w
  | "bind" =>
    let sec ← natF j "sec"
    let k ← natF j "k"
    pure { w with host := hostWorld, hbound := bind w.hbound sec (k + 1) }
  | "hrm" =>
    let k ← natF j "k"
    let (host, found) := remove w.host 2 (k + 1)
    check found "host removal"
    pure { w with host := host }
  | "ans" =>
    let sec ← natF j "sec"
    let ans ← strF j "ans"
    let req ← match ← strF j "req" with
      | "sign" => pure (Req.sign sec (← algOf (← natF j "alg")) 0)
      | _ => pure (Req.decap sec)
    match answer w.host 2 w.hbound req with
    | .signature a n => check (ans == "sig" && (← natF j "alg") == a.tag && (← natF j "len") == n && (← boolF j "ok")) "host: signature"
    | .secret => check (ans == "secret" && (← boolF j "ok")) "host: secret"
    | .failed => check (ans == "failed") s!"host: the model refuses, the code answered {ans}"
    pure w
  | "seal" =>
    let s ← natF j "s"
    let blob ← bytesF j "blob"
    let pt ← bytesF j "pt"
    check (blob.head? == some 1 && blob.length == 1 + KeystoreSealed.nonceLen + pt.length + KeystoreSealed.tagLen) "seal layout"
    check (match KeystoreSealed.parse blob 1 with
      | .ok q => q.header == [1] && q.nonce.length == 12 && q.tag.length == 16
      | .error _ => false) "seal parses"
    check (!(w.sealed s).any (fun e => e.1 == blob)) "a nonce repeated"
    pure { w with sealed := fun t => if t = s then (blob, pt) :: w.sealed t else w.sealed t }
  | "unseal" =>
    let s ← natF j "s"
    let blob ← bytesF j "blob"
    let res ← strF j "res"
    let pt ← bytesF j "pt"
    let model : Option Bytes :=
      match blob with
      | [] => none
      | v :: _ =>
        if v ≠ 1 then none
        else match KeystoreSealed.parse blob 1 with
          | .error _ => none
          | .ok _ => ((w.sealed s).find? (fun e => e.1 == blob)).map Prod.snd
    match model with
    | some p => check (res == "ok" && p == pt) "unseal of a genuine blob"
    | none => check (res == "InvalidSealed" && pt.isEmpty) "unseal of anything else is InvalidSealed"
    pure w
  | op => throw s!"unknown keystore op {op}"

/-- The command's auth value for the method. -/
def authOf (m : M) (owner key : Bytes) : Bytes :=
  match m with
  | .createPrimary | .evictControl => owner
  | .sign | .unseal => key
  | _ => []

def mOfCc (cc : Nat) : Except String M :=
  match M.all.find? (fun m => m.cc == cc) with
  | some m => pure m
  | none => throw s!"unknown command code {cc}"

def sliceBe32 (b : Bytes) (i : Nat) : Nat := be32 ((b.drop i).take 4)

/-- The client sends a command again, with the same bytes, while the TPM answers `TPM_RC_RETRY`, `TPM_RC_YIELDED` or
`TPM_RC_TESTING`, at most 8 sends in all. The program is checked on the commands that took effect: a command answered
with one of those codes and followed by the same bytes is a resend, and a run of 8 resends is refused. -/
def resendCodes : List Nat := [0x922, 0x908, 0x90A]

def dropResent : List (M × Nat × Bytes × Bytes) → Except String (List (M × Nat × Bytes × Bytes))
  | [] => pure []
  | c :: rest => do
    let tail ← dropResent rest
    match rest with
    | d :: _ => if resendCodes.contains c.2.1 && d.2.2.1 == c.2.2.1 then pure tail else pure (c :: tail)
    | [] => pure (c :: tail)

def resendRunOk (cmds : List (M × Nat × Bytes × Bytes)) : Bool :=
  let flags := (cmds.zip (cmds.drop 1)).map fun (c, d) => resendCodes.contains c.2.1 && d.2.2.1 == c.2.2.1
  (flags.foldl (fun (run, ok) f => if f then (run + 1, ok && run + 1 < 8) else (0, ok)) (0, true)).2

/-- The commands of an event with the response codes. -/
def readCmds (j : J) (owner key : Bytes) : Except String (List (M × Nat × Bytes × Bytes)) := do
  match (← field j "cmds").arr? with
  | none => throw "cmds"
  | some a => a.toList.mapM fun c => do
    let cmd ← bytesF c "cmd"
    let rsp ← bytesF c "rsp"
    let m ← mOfCc (sliceBe32 cmd 6)
    check (canonical m (authOf m owner key) cmd) s!"command {m.cc}: not the canonical layout"
    check (rsp.length ≥ 10 && sliceBe32 rsp 2 == rsp.length) "response size"
    pure (m, sliceBe32 rsp 6, cmd, rsp)

def opOfName (name : String) (n calls : Nat) : Except String Op :=
  match name with
  | "open" => pure .open_
  | "generate" => pure .generate
  | "load_persistent" => pure .loadPersistent
  | "persist" => pure .persist
  | "sign" => pure .sign
  | "random" => pure (.random calls)
  | "seal" => pure .seal
  | "unseal" => pure .unseal
  | "generate_unsupported" => pure .publicOnly
  | _ => throw s!"unknown program {name}"

/-- A response code recorded as two 16-bit limbs, most significant first. -/
def codeF (j : J) : Except String Nat := do
  match ← natList (← field j "code") with
  | [hi, lo] => pure (hi * 65536 + lo)
  | _ => throw "code limbs"

/-- The program the model gives for the recorded commands, if any failure point matches. -/
def matchProgram (op : Op) (recorded : List (M × Bool)) : Option Int :=
  ([none, some 0, some 1, some 2] : List (Option Nat)).findSome? fun f =>
    if (program op f).1 == recorded then some (program op f).2 else none

def replayTpm (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "resp" =>
    let rsp ← bytesF j "rsp"
    let link ← strF j "link"
    let res ← strF j "res"
    if link ≠ "" then
      check (res == "Transport") "link failure"
    else
      match parseResp rsp (← boolF j "body_ok") with
      | .ok () => check (res == "ok") "response"
      | .error .protocol => check (res == "Protocol") s!"response: model Protocol, code {res}"
      | .error (.tpm c) => check (res == "Tpm" && (← codeF j) == c) s!"response: model Tpm {c}, code {res}"
    pure w
  | "prog" =>
    let owner ← bytesF j "owner"
    let key ← bytesF j "key"
    let sent ← readCmds j owner key
    check (resendRunOk sent) "at most 8 sends of one command"
    let cmds ← dropResent sent
    let recorded := cmds.map fun c => (c.1, decide (c.2.1 = 0))
    let name ← strF j "prog"
    let n ← natF j "n"
    let op ← opOfName name n recorded.length
    let res ← strF j "res"
    match matchProgram op recorded with
    | some d =>
      check (net recorded == d) "the net change of handles is the program's"
      let la ← natF j "live_after"
      let lb ← natF j "live_before"
      let sl ← natF j "slots"
      check ((la : Int) == (lb : Int) + d) "live handles after the operation"
      check (la == sl) "the TPM holds the handles the store tracks"
      let allOk := recorded.all (·.2)
      if name == "generate_unsupported" then check (res == "Unsupported") "unsupported algorithm"
      else check ((res == "ok") == allOk) s!"result {res} for commands {recorded.length}"
      match cmds.find? (fun c => c.2.1 != 0) with
      | some (_, rc, _, _) => if res == "Tpm" then check ((← codeF j) == rc) "the code is the TPM's" else pure ()
      | none => pure ()
      if name == "random" && allOk then check (recorded.length == randomCalls n) "random: one command per 32 bytes"
    | none => throw s!"program {name}: the commands are not the model's"
    pure w
  | "hnd" =>
    let h ← match ← natList (← field j "h") with
      | [hi, lo] => pure (hi * 65536 + lo)
      | _ => throw "handle limbs"
    let res ← strF j "res"
    let ncmds ← natF j "ncmds"
    match ← strF j "call" with
    | "persist_again" => check (res == "InvalidHandle" && ncmds == 0) "persist again"
    | _ =>
      if persistent h then check (res != "InvalidHandle" && ncmds ≥ 1) "a persistent handle is tried"
      else check (res == "InvalidHandle" && ncmds == 0) "a handle outside the persistent range sends nothing"
    pure w
  | "auth" =>
    let len ← natF j "len"
    let res ← strF j "res"
    let ncmds ← natF j "ncmds"
    if len > maxAuth then check (res == "InvalidAuth" && ncmds == 0) "over-long auth"
    else check (res != "InvalidAuth") "auth within the limit"
    pure w
  | "dropped" =>
    check ((← natF j "live_after") == 0) "dropping the store"
    pure w
  | "seal" =>
    let blob ← bytesF j "blob"
    let pt ← bytesF j "pt"
    let libOk ← boolF j "lib_ok"
    match parseHeader blob libOk with
    | .ok h => check (h == (← natF j "hdr") && blob.length == h + 12 + pt.length + 16) "tpm seal layout"
    | .error _ => throw "the sealed blob does not parse"
    pure { w with tsealed := blob :: w.tsealed }
  | "unseal" =>
    let blob ← bytesF j "blob"
    let res ← strF j "res"
    let sent ← readCmds j (← bytesF j "owner") (← bytesF j "key")
    check (resendRunOk sent) "at most 8 sends of one command"
    let cmds ← dropResent sent
    let recorded := cmds.map fun c => (c.1, decide (c.2.1 = 0))
    let rcOf (m : M) : Nat := ((cmds.find? (fun c => c.1 == m)).map (·.2.1)).getD 0
    let dekLen : Nat := match cmds.find? (fun c => c.1 == .unseal) with
      | some (_, 0, _, rsp) => (rsp.getD 14 0) * 256 + rsp.getD 15 0
      | _ => 0
    let (parseOk, hdr) := match parseHeader blob (← boolF j "lib_ok") with
      | .ok h => (true, h)
      | .error _ => (false, 0)
    if parseOk then check (hdr == (← natF j "hdr")) "header length"
    check (match matchProgram .unseal recorded with | some _ => true | none => recorded.isEmpty) "the unseal program"
    check (recorded.isEmpty == !parseOk) "commands are sent exactly for a header that parses"
    let aeadOk := w.tsealed.contains blob
    let model := unsealResult parseOk (rcOf .load) (rcOf .unseal) (rcOf .flush) dekLen aeadOk
    match model with
    | .ok () => check (res == "ok" && (← boolF j "genuine")) "unseal"
    | .error .invalidSealed => check (res == "InvalidSealed") s!"unseal: model InvalidSealed, code {res}"
    | .error (.tpm c) => check (res == "Tpm" && (← codeF j) == c) s!"unseal: model Tpm {c}, code {res}"
    check ((← natF j "live_after") == (← natF j "live_before")) "unseal leaves no handle"
    pure w
  | op => throw s!"unknown tpm op {op}"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "t" with
  | "ks" => replaySoft j w
  | _ => replayTpm j w

end Pinc.TraceKeystore
