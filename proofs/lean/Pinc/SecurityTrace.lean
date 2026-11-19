import Pinc.Json
import Pinc.Labels
import Pinc.Credit
import Pinc.Amp
import Pinc.Padding

/-!
# Replay of the security traces

The replay half of the trace validation of the labels, the credit record, the anti-amplification budget and the
padding sizes: it reads the events the Rust test `trace_security` records and checks each against the proved model
functions. A `u64` is written as four 16-bit limbs, least significant first.

* `lbl`: the labels of `labels::ALL`, the prefix and the labels of `pinc-crypto` must equal `Labels.all`,
  `Labels.prefix_` and `Labels.cryptoLabels`.
* `cred`: `op = new` is `CreditRecord::new` of a window request, a stream limit and a datagram limit, with the record,
  the window in bytes and the 6 bytes it built; `op = dec` is `decode` of 6 bytes and the re-encoded bytes; `op = cov`
  is `covers` of two records. Each must equal `Credit.new`, `Credit.windowBytes`, `Credit.encode`, `Credit.decode` and
  `Credit.covers`.
* `amp`: one `on_receive`, `on_send`, `validate` or `can_send` of an `AmpBudget`; `seq = 0` starts a fresh budget. The
  getters after the call (and the answer of `can_send`) must equal the model's, `Amp.onReceive`, `Amp.onSend` (both
  saturating) and `Amp.canSend`.
* `pad`: `op = min` is `min_initial_len` and `reply_len` of an algorithm (with its key and signature lengths) and a
  form; `op = const` is the size constants. Each must equal `Padding.minInitialLen`, `Padding.replyLen` and the
  constants of `Padding`.
-/

namespace Pinc.SecurityTrace
open Pinc.Json

/-- The model state of the current budget run. -/
structure SecState where
  arun : Nat := 0
  amp : Amp.Budget := Amp.Budget.new

instance : Inhabited SecState := ⟨{}⟩

/-- A `u64` field written as four 16-bit limbs. -/
def u64F (j : J) (k : String) : Except String Nat := do
  match ← natList (← field j k) with
  | [a, b, c, d] =>
    check (a < 65536 && b < 65536 && c < 65536 && d < 65536) s!"limb of {k} out of range"
    pure (a + 65536 * (b + 65536 * (c + 65536 * d)))
  | _ => throw s!"field {k} is not four limbs"

/-- The strings of an array field. -/
def strList (j : J) : Except String (List String) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.str? with
    | some s => pure s
    | none => throw "expected a string"
  | none => throw "expected an array"

/-- Replay the labels event. -/
def replayLabels (j : J) : Except String Unit := do
  check ((← strList (← field j "all")) == Labels.all) "the labels of the code are not the labels of the model"
  check ((← strF j "prefix") == Labels.prefix_) "the label prefix of the code is not the model's"
  check ((← strList (← field j "crypto")) == Labels.cryptoLabels) "the labels of pinc-crypto are not the model's"

/-- The record of a three-number array. -/
def recordF (j : J) (k : String) : Except String Credit.Record := do
  match ← natList (← field j k) with
  | [w, s, d] => pure ⟨w, s, d⟩
  | _ => throw s!"field {k} is not a credit record"

/-- Replay one credit-record event. -/
def replayCredit (j : J) : Except String Unit := do
  let op ← strF j "op"
  match op with
  | "new" =>
    let w ← u64F j "w"
    let s ← natF j "s"
    let d ← natF j "d"
    let r := Credit.new w s d
    let rr ← recordF j "rec"
    check (r == rr) s!"credit new {w} {s} {d}: model {r.windowUnits} {r.maxStreams} {r.maxDatagram}"
    check (Credit.windowBytes r == (← natF j "wb")) s!"credit window_bytes of {w}"
    check (Credit.encode r == (← natList (← field j "enc"))) s!"credit encode of new {w} {s} {d}"
    check (Credit.decode (Credit.encode r) == r) s!"credit decode of encode of {w}"
  | "dec" =>
    let b ← natList (← field j "b")
    check (b.length == 6) "credit bytes are not 6"
    let r := Credit.decode b
    check (r == (← recordF j "rec")) s!"credit decode {b}: model {r.windowUnits} {r.maxStreams} {r.maxDatagram}"
    check (Credit.encode r == (← natList (← field j "enc"))) s!"credit re-encode of {b}"
    check (Credit.encode r == b) s!"credit encode (decode {b}) differs from the bytes"
  | "cov" =>
    let a ← recordF j "a"
    let b ← recordF j "b"
    check (Credit.covers a b == (← boolF j "ok"))
      s!"credit covers {a.windowUnits},{a.maxStreams},{a.maxDatagram} / {b.windowUnits},{b.maxStreams},{b.maxDatagram}: model {Credit.covers a b}"
  | _ => throw s!"unknown credit op {op}"

/-- Replay one amplification-budget event. -/
def replayAmp (j : J) (st : SecState) : Except String SecState := do
  let run ← natF j "run"
  let seq ← natF j "seq"
  let st := if seq == 0 then { st with arun := run, amp := Amp.Budget.new } else st
  check (run == st.arun) s!"amp event of run {run} outside its run {st.arun}"
  let op ← strF j "op"
  let n ← u64F j "n"
  let b := st.amp
  let next ← match op with
    | "rx" => pure (Amp.onReceive b n)
    | "tx" => pure (Amp.onSend b n)
    | "val" => pure (Amp.validate b)
    | "can" => do
      let can ← boolF j "can"
      check (Amp.canSend b n == can) s!"amp can_send {n} (run {run}, seq {seq}): model {Amp.canSend b n}, code {can}"
      pure b
    | _ => throw s!"unknown amp op {op}"
  check (next.rx == (← u64F j "rx") && next.tx == (← u64F j "tx") && next.validated == (← boolF j "valid"))
    s!"amp {op} {n} (run {run}, seq {seq}): model rx {next.rx} tx {next.tx} valid {next.validated}"
  pure { st with amp := next }

/-- The algorithm of a wire tag. -/
def algOf (tag : Nat) : Except String Padding.Alg :=
  match tag with
  | 1 => pure .ed25519
  | 2 => pure .ecdsaP256
  | 3 => pure .mlDsa65
  | 4 => pure .hybrid
  | t => throw s!"unknown identity algorithm tag {t}"

/-- Replay one padding event. -/
def replayPad (j : J) : Except String Unit := do
  let op ← strF j "op"
  match op with
  | "min" =>
    let a ← algOf (← natF j "alg")
    let form ← match (← strF j "form") with
      | "full" => pure Padding.Form.full
      | "short" => pure Padding.Form.short
      | f => throw s!"unknown Initial form {f}"
    check ((← natF j "pk") == a.publicKeyLen && (← natF j "sig") == a.signatureLen)
      s!"pad key or signature length of {repr a}: model {a.publicKeyLen}/{a.signatureLen}"
    check ((← natF j "reply") == Padding.replyLen a) s!"pad reply_len of {repr a}: model {Padding.replyLen a}"
    check ((← natF j "dgs") == Padding.replyDatagrams (Padding.replyLen a))
      s!"pad reply_datagrams of {repr a}: model {Padding.replyDatagrams (Padding.replyLen a)}"
    check ((← natF j "min") == Padding.minInitialLen form a)
      s!"pad min_initial_len {repr form} {repr a}: model {Padding.minInitialLen form a}, code {← natF j "min"}"
  | "const" =>
    check ((← natF j "full") == Padding.fullInitialMin && (← natF j "short") == Padding.shortInitialMin &&
        (← natF j "dg") == Padding.minDatagram && (← natF j "frag") == Padding.fragmentHeader &&
        (← natF j "whole") == Padding.wholeReplyMax && (← natF j "splitcid") == Padding.splitCidMax)
      "pad: the Initial floors, MIN_DATAGRAM, FRAGMENT_HEADER, WHOLE_REPLY_MAX or SPLIT_CID_MAX differ from the model"
    check ((← natF j "txcid") ≤ Padding.splitCidMax && (← natF j "epcid") ≤ Padding.splitCidMax)
      "pad: a default connection id is longer than SPLIT_CID_MAX"
    check ((← natF j "idsig") == Padding.maxIdSigLen && (← natF j "sealed") == Padding.maxSealedLen &&
        (← natF j "msg") == Padding.maxMessageLen)
      s!"pad: MAX_ID_SIG_LEN/MAX_SEALED_LEN/MAX_MESSAGE_LEN differ from the model ({Padding.maxIdSigLen}/{Padding.maxSealedLen}/{Padding.maxMessageLen})"
    check ((← natF j "overhead") == Amp.overhead && (← natF j "factor") == Amp.factor)
      "pad: OVERHEAD or FACTOR differ from the model"
    check ((← natF j "maxpk") == Padding.maxPublicKeyLen && (← natF j "maxsig") == Padding.maxSignatureLen &&
        (← natF j "kemct") == Padding.kemCiphertextLen && (← natF j "tag") == Padding.tagLen &&
        (← natF j "credit") == Credit.recordLen && (← natF j "cid") == Padding.maxCidLen)
      "pad: a length constant differs from the model"
  | _ => throw s!"unknown pad op {op}"

/-- Replay one security event (`lbl`, `cred`, `amp` or `pad`) against the model state. -/
def replayEvent (j : J) (st : SecState) : Except String SecState := do
  match (← strF j "t") with
  | "lbl" => do replayLabels j; pure st
  | "cred" => do replayCredit j; pure st
  | "amp" => replayAmp j st
  | "pad" => do replayPad j; pure st
  | t => throw s!"unknown security event {t}"

end Pinc.SecurityTrace
