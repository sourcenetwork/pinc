import Vinc.Json
import Vinc.CryptoSecret
import Vinc.CryptoProvider

/-!
# Replay of the `vinc-crypto` traces

The replay half of the trace validation of `vinc-crypto` (the Rust test `trace_crypto`; the TLA+ half is
`TraceCrypto.tla`). Every event (`t = "cr"`) is one call of the real code with the answers of the primitive libraries
the test called directly (the oracle). The replay recomputes the answer with the proved model from the recorded inputs
and requires it to equal the recorded one; the oracle values enter the model as the abstract primitive of the event.
Any difference exits with an error naming the line.
-/

namespace Vinc.TraceCrypto
open Vinc.Json Vinc.CryptoKdf Vinc.CryptoIdentity Vinc.CryptoProvider Vinc.CryptoSecret
open Vinc.CryptoDrbg (D fill reseed maxFill)
open Vinc.CryptoDrbg renaming Err → DErr

def isTag (t : String) : Bool := t == "cr"

def strList (j : J) : Except String (List String) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.str? with
    | some s => pure s
    | none => throw "expected a string"
  | none => throw "expected an array"

def bytesF (j : J) (k : String) : Except String Bytes := do natList (← field j k)

def flagsF (j : J) (k : String) : Except String (List Bool) := do
  match (← field j k).arr? with
  | some a => a.toList.mapM fun v => match v.bool? with
    | some b => pure b
    | none => throw "expected a bool"
  | none => throw "expected an array"

/-- A byte field that is empty when the oracle was not used. -/
def optBytesF (j : J) (k : String) : Except String (Option Bytes) := do
  let b ← natList (← field j k)
  pure (if b.isEmpty then none else some b)

/-- The node id oracle of an event: its output, and the check that it was computed on the model's call. -/
def nidOracle (j : J) (a : Alg) (pk : Bytes) : Except String (Option Bytes) := do
  let orc ← optBytesF j "orc"
  match orc with
  | some o =>
    check ((← bytesF j "orc_in") == (nodeIdCall a.tag pk).material) "the node id oracle was fed another input than the model's"
    check (o.length == 32) "oracle length"
    pure orc
  | none =>
    check ((← bytesF j "orc_in").isEmpty) "orc_in without orc"
    pure none

/-- The hybrid digest oracle of an event: the message it was computed on is the model's call material. -/
def digOracle (j : J) (msg : Bytes) : Except String (Option (Bytes × Bytes)) := do
  if ← boolF j "hyb" then
    check ((← bytesF j "dig_in") == (hybridCall msg).material) "the digest oracle was fed another input than the model's"
    let d ← bytesF j "dig"
    check (d.length == 32) "digest length"
    pure (some (msg, d))
  else
    pure none

def errName : Vinc.CryptoIdentity.Err → String
  | .invalidLength => "InvalidLength"
  | .authentication => "Authentication"
  | .inputTooLong => "InputTooLong"
  | .nonContributory => "NonContributory"
  | .invalidEncapsulationKey => "InvalidEncapsulationKey"
  | .invalidSecretKey => "InvalidSecretKey"
  | .invalidPublicKey => "InvalidPublicKey"
  | .invalidSignature => "InvalidSignature"
  | .highS => "HighS"
  | .nodeIdMismatch => "NodeIdMismatch"

def resName {α : Type} : Except Vinc.CryptoIdentity.Err α → String
  | .ok _ => "ok"
  | .error e => errName e

def algOf (n : Nat) : Except String Alg :=
  match Alg.ofTag n with
  | some a => pure a
  | none => throw s!"unknown algorithm tag {n}"

/-- The primitive for one event: the flags `[pkOk, sigOk, lowS, ok]` of the Ed25519 (or P-256) side and the ML-DSA side. -/
def primOf (fe fm : List Bool) : Prim :=
  let g := fun (l : List Bool) (i : Nat) => l.getD i false
  { edPk := fun _ => g fe 0, edVer := fun _ _ _ => g fe 3, pPk := fun _ => g fe 0, pSig := fun _ => g fe 1,
    pLow := fun _ => g fe 2, pVer := fun _ _ _ => g fe 3, mSig := fun _ => g fm 1, mVer := fun _ _ _ _ => g fm 3 }

/-- The derivation primitive of one event: the node id call and the hybrid digest call have the recorded outputs. -/
def hashOf (nid : Option (Nat × Bytes × Bytes)) (dig : Option (Bytes × Bytes)) : Call → Bytes := fun c =>
  match nid with
  | some (tag, pk, o) => if c = nodeIdCall tag pk then o else (match dig with
      | some (m, d) => if c = hybridCall m then d else []
      | none => [])
  | none => match dig with
      | some (m, d) => if c = hybridCall m then d else []
      | none => []

def u64Limbs (j : J) (k : String) : Except String Nat := do
  match ← natList (← field j k) with
  | [a, b, c, d] => pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw s!"field {k} is not four limbs"

/-- The oracle's stream for a mask: its bytes at `off ..`. -/
def windowStream (off : Nat) (orc : Bytes) : Bytes → Bytes → Nat → Nat := fun _ _ pos =>
  if off ≤ pos then orc.getD (pos - off) 0 else 0

/-- Replay a DRBG run. -/
def replayDrbg (j : J) : Except String Unit := do
  let seed ← bytesF j "seed"
  check (seed.length == 32) "seed length"
  check ((← natF j "max") == maxFill) "MAX_FILL"
  let ops ← match (← field j "ops").arr? with
    | some a => pure a.toList
    | none => throw "ops"
  let mut d : D := ⟨seed⟩
  for o in ops do
    match ← strF o "k" with
    | "fill" =>
      let n ← natF o "n"
      match o.get? "err" with
      | some _ =>
        let stream : Bytes → Nat → Nat := fun _ _ => 0
        let (d', r) := fill stream d n
        check (decide (maxFill < n)) s!"fill {n} is within MAX_FILL"
        check ((match r with | .error DErr.inputTooLong => true | _ => false) && d' == d) "the refusal leaves the state"
      | none =>
        let out ← bytesF o "out"
        let orc ← bytesF o "orc"
        check (orc.length == 32 + n && out.length == n) s!"fill {n}: lengths"
        let key := d.key
        let stream : Bytes → Nat → Nat := fun k i => if k == key then orc.getD i 0 else 0
        let (d', r) := fill stream d n
        check (decide (n ≤ maxFill)) s!"fill {n} is over MAX_FILL"
        check (match r with | .ok o => o == out | .error _ => false) s!"fill {n}: the output is not the model's"
        check (32 + n ≤ (2 ^ 32 - 1) * 64) "stream bound"
        d := d'
    | "reseed" =>
      let e ← bytesF o "e"
      check (e.length == 32) "entropy length"
      d := reseed d e
    | k => throw s!"unknown drbg op {k}"
  check (d.key.length == 32) "key length"

/-- Replay one event. -/
def replayEvent (j : J) : Except String Unit := do
  match ← strF j "op" with
  | "lbl" =>
    check ((← strF j "prefix") == Labels.prefix_) "prefix"
    check ((← strList (← field j "sec")) == Labels.all) "security labels"
    check ((← strList (← field j "crypto")) == cryptoLabels) "crypto labels"
    check ((← strList (← field j "dtn")) == dtnLabels) "dtn labels"
    check (decide (registry = Labels.all ++ cryptoLabels ++ dtnLabels)) "registry"
  | "expand" =>
    let label ← strF j "label"
    let prk ← bytesF j "prk"
    let ctx ← bytesF j "ctx"
    let n ← natF j "n"
    let out ← bytesF j "out"
    let orcIn ← bytesF j "orc_in"
    let orc ← bytesF j "orc"
    let orc32 ← bytesF j "orc32"
    let call := expandCall prk (bytes label) ctx
    check (prk.length == 32) "prk length"
    check (call.material == orcIn && call.mode == .derive && call.label == bytes label) s!"{label}: the call differs from the oracle's"
    let xof : Call → Nat → Nat := fun c i => if c == call then orc.getD i 0 else 0
    check (CryptoKdf.out xof call n == out) s!"{label}: the output is not the first {n} bytes of the oracle's"
    check (orc.length == n && out.length == n) "output length"
    check (orc.take (min n 32) == orc32.take (min n 32)) "32-byte output and the XOF disagree"
  | "extract" =>
    let salt ← bytesF j "salt"
    let ikm ← bytesF j "ikm"
    let call := extractCall salt ikm
    check (salt.length == 32) "salt length"
    check ((← bytesF j "orc_key") == call.label && (← bytesF j "orc_in") == call.material && call.mode == .keyed)
      "extract: the call differs from the oracle's"
    check ((← bytesF j "out") == (← bytesF j "orc") && (← bytesF j "out").length == 32) "extract output"
  | "tags" =>
    let res ← natList (← field j "res")
    check (res.length == 256) "tags length"
    for t in List.range 256 do
      check (res.getD t 999 == ((Alg.ofTag t).map Alg.tag).getD 0) s!"from_tag {t}"
  | "alg" =>
    let a ← algOf (← natF j "alg")
    check ((← natF j "pk") == a.pkLen && (← natF j "sig") == a.sigLen && (← natF j "seed") == a.seedLen) s!"lengths of {a.tag}"
    check ((← natF j "maxpk") == maxPk && (← natF j "maxsig") == maxSig) "maxima"
  | "nid" =>
    let a ← algOf (← natF j "alg")
    let pk ← bytesF j "pk"
    let orc ← nidOracle j a pk
    let H := hashOf (orc.map fun o => (a.tag, pk, o)) none
    let r := fromPublic H a pk
    let rj ← field j "res"
    match rj.get? "ok" with
    | some b =>
      let want ← natList b
      check (match r with | .ok id => id.bytes == want && id.alg == a | .error _ => false) "nid: the id"
    | none => check (resName r == (← strF rj "err")) s!"nid: model {resName r}"
    if a != .ed25519 && pk.length == a.pkLen then check orc.isSome "the oracle is missing"
  | "kpid" =>
    let a ← algOf (← natF j "alg")
    let pk ← bytesF j "pk"
    let orc ← nidOracle j a pk
    let H := hashOf (orc.map fun o => (a.tag, pk, o)) none
    check (pk.length == a.pkLen) "pk length"
    let want ← bytesF j "id"
    check (match fromPublic H a pk with | .ok id => id.bytes == want | .error _ => false) "node_id of a key pair"
  | "match" =>
    let ij ← field j "id"
    let id : NodeId := ⟨← algOf (← natF ij "alg"), ← bytesF ij "bytes"⟩
    let a ← algOf (← natF j "alg")
    let pk ← bytesF j "pk"
    let orc ← nidOracle j a pk
    let H := hashOf (orc.map fun o => (a.tag, pk, o)) none
    check (matches' H id a pk == (← boolF j "res")) "matches"
  | "ver" =>
    let a ← algOf (← natF j "alg")
    let pk ← bytesF j "pk"
    let msg ← bytesF j "msg"
    let sig ← bytesF j "sig"
    let dig ← digOracle j msg
    let P := primOf (← flagsF j "fe") (← flagsF j "fm")
    let H := hashOf none dig
    check (resName (verify H P a pk msg sig) == (← strF j "res")) s!"verify {a.tag}: model {resName (verify H P a pk msg sig)}"
    check (dig.isSome == (a == .hybrid)) "the digest oracle is for the hybrid only"
  | "mlv" =>
    let pk ← bytesF j "pk"
    let msg ← bytesF j "msg"
    let sig ← bytesF j "sig"
    let ctx := List.replicate (← natF j "ctx") 9
    let P := primOf [] (← flagsF j "fm")
    check (resName (mlVerify P pk ctx msg sig) == (← strF j "res")) "verify_ml_dsa_65"
  | "vnode" =>
    let ij ← field j "id"
    let id : NodeId := ⟨← algOf (← natF ij "alg"), ← bytesF ij "bytes"⟩
    let pk ← bytesF j "pk"
    let msg ← bytesF j "msg"
    let sig ← bytesF j "sig"
    let orc ← nidOracle j id.alg pk
    let dig ← digOracle j msg
    let P := primOf (← flagsF j "fe") (← flagsF j "fm")
    let H := hashOf (orc.map fun o => (id.alg.tag, pk, o)) dig
    check (resName (verifyNode H P id pk msg sig) == (← strF j "res")) s!"verify_node: model {resName (verifyNode H P id pk msg sig)}"
  | "kp" =>
    let a ← algOf (← natF j "alg")
    check (resName (fromSeed a (← bytesF j "seed")) == (← strF j "res")) "Keypair::from_seed"
  | "write" =>
    let a ← algOf (← natF j "alg")
    let need := if (← strF j "kind") == "pub" then a.pkLen else a.sigLen
    let r := writeOut need (← natF j "out")
    let n ← natF j "n"
    check (resName r == (← strF j "res")) "write"
    check (match r with | .ok m => m == n | .error _ => n == 0) "write: length"
  | "drbg" => replayDrbg j
  | "key" =>
    let alg := if (← natF j "alg") == 0 then Aead.chacha20Poly1305 else Aead.aes128Gcm
    check ((← natF j "keylen") == alg.keyLen) "key_len"
    let r := keySetup alg (List.replicate (← natF j "len") 0)
    check (resName r == (← strF j "res")) "key setup"
  | "aead" =>
    check ((← natF j "clen") == (← natF j "plen") && (← natF j "tag") == tagLen) "AEAD shape"
    let A : AeadImpl := ⟨fun _ _ _ _ => none, fun _ _ _ _ _ => none⟩
    let auth := resName (openW A [] [] [] [] [])
    check ((← strF j "open") == "ok" && (← strF j "badtag") == auth && (← strF j "badnonce") == auth) "AEAD errors"
  | "hpc" =>
    let key ← bytesF j "key"
    let sample ← bytesF j "sample"
    let orc ← bytesF j "orc"
    let off ← u64Limbs j "orc_off"
    check (key.length == 32 && sample.length == sampleLen && orc.length == maskLen) "hpc lengths"
    check (off == le32 sample * 64) "the stream offset is counter * 64"
    check (decide (off + maskLen ≤ 2 ^ 32 * 64)) "the mask is inside the stream"
    check (hpMaskChaCha (windowStream off orc) key sample == (← bytesF j "mask")) "hp mask (ChaCha20)"
  | "hpa" =>
    let key ← bytesF j "key"
    let sample ← bytesF j "sample"
    let block ← bytesF j "orc"
    check (key.length == 16 && sample.length == sampleLen && block.length == 16) "hpa lengths"
    check (hpMaskAes (fun _ _ => block) key sample == (← bytesF j "mask")) "hp mask (AES)"
  | "dh" =>
    let orc ← bytesF j "orc"
    let r := dh (fun _ _ => orc) [] []
    let rj ← field j "res"
    match rj.get? "ok" with
    | some b =>
      let want ← natList b
      check (match r with | .ok o => o == want | .error _ => false) "x25519_dh result"
    | none => check (resName r == (← strF rj "err")) "x25519_dh error"
  | "kemkey" =>
    let m ← boolF j "mod"
    let b := List.replicate (← natF j "len") 0
    check (resName (kemEncapsKey (fun _ => m) b) == (← strF j "res")) "kem_encaps_key"
  | "kemct" =>
    check (resName (kemCiphertext (List.replicate (← natF j "len") 0)) == (← strF j "res")) "kem_ciphertext"
  | "cteq" =>
    check (ctEq (← bytesF j "a") (← bytesF j "b") == (← boolF j "eq")) "ct_eq"
  | "secret" =>
    let a ← bytesF j "a"
    let b ← bytesF j "b"
    let c ← bytesF j "c"
    check (ctEq a b == (← boolF j "ab") && ctEq a c == (← boolF j "ac")) "Secret equality"
    check ((← strF j "debug") == debug a && debug a == debug c) "Secret debug"
  | "drop" =>
    let after ← bytesF j "after"
    check (after.length == (← natF j "n") && after.all (· == 0)) "bytes after drop"
    check (zeroize after == after) "zeroize"
  | op => throw s!"unknown crypto op {op}"

end Vinc.TraceCrypto
