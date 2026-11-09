import Vinc.KeystoreSealed

/-!
# The TPM store of `vinc-keystore` (`tpm/client.rs`, `tpm/store.rs`)

The pure parts of the TPM backend: how a response is read (`TpmClient::execute`), how a command is laid out (the header
and the password authorization area), the command each client method sends, the program of commands each store
operation runs with the handles it holds, the sealed blob header, and the order in which the errors of `unseal` are
reported. The marshaling of the parameters and of the response bodies is the `tpm2-protocol` library's; its verdict
(does the body parse) is an input of the model, like a primitive's.

Transport contract (an assumption, not proved): one `transmit` is one command and its own response. A response carries
no echo of the command code, so a transport that answered with another command's response would be read as the
expected type; the client sends one command at a time (`&mut self`), so the pairing is the transport's.
-/

namespace Vinc.KeystoreTpm
open Vinc.CryptoKdf (Bytes)

/-! ## Reading a response -/

/-- The error of `execute`: a malformed message, a TPM refusal with its code. -/
inductive RErr where
  | protocol
  | tpm (code : Nat)
  deriving DecidableEq

def be32 (b : Bytes) : Nat := b.foldl (fun a x => a * 256 + x) 0

/-- The checks of `execute`, in order: a header of 10 bytes, the size field equal to the length, a zero response code
(else `Tpm { code }`), then the body (the library's verdict). -/
def parseResp (rsp : Bytes) (bodyOk : Bool) : Except RErr Unit :=
  if rsp.length < 10 then .error .protocol
  else if be32 ((rsp.drop 2).take 4) ≠ rsp.length then .error .protocol
  else if be32 ((rsp.drop 6).take 4) ≠ 0 then .error (.tpm (be32 ((rsp.drop 6).take 4)))
  else if ¬bodyOk then .error .protocol
  else .ok ()

theorem parseResp_short (rsp : Bytes) (b : Bool) (h : rsp.length < 10) : parseResp rsp b = .error .protocol := by
  simp [parseResp, h]

/-- A response whose size field is not its length is a protocol error, whatever its code says. -/
theorem parseResp_size (rsp : Bytes) (b : Bool) (h1 : 10 ≤ rsp.length) (h2 : be32 ((rsp.drop 2).take 4) ≠ rsp.length) :
    parseResp rsp b = .error .protocol := by
  simp [parseResp, h2]

/-- A well-sized refusal carries exactly the TPM's code. -/
theorem parseResp_code (rsp : Bytes) (b : Bool) (h1 : 10 ≤ rsp.length) (h2 : be32 ((rsp.drop 2).take 4) = rsp.length)
    (h3 : be32 ((rsp.drop 6).take 4) ≠ 0) : parseResp rsp b = .error (.tpm (be32 ((rsp.drop 6).take 4))) := by
  simp [parseResp, h2, h3]; omega

theorem parseResp_ok_iff (rsp : Bytes) (b : Bool) :
    parseResp rsp b = .ok () ↔ 10 ≤ rsp.length ∧ be32 ((rsp.drop 2).take 4) = rsp.length ∧
      be32 ((rsp.drop 6).take 4) = 0 ∧ b = true := by
  unfold parseResp
  by_cases h1 : rsp.length < 10
  · simp only [h1, ite_true]
    constructor
    · intro e; cases e
    · intro h; omega
  by_cases h2 : be32 ((rsp.drop 2).take 4) = rsp.length
  · by_cases h3 : be32 ((rsp.drop 6).take 4) = 0
    · by_cases h4 : b = true
      · simp [h1, h2, h3, h4]; omega
      · simp [h1, h2, h3, h4]
    · simp [h1, h2, h3]
  · simp [h1, h2]

/-! ## Commands -/

inductive M where
  | startup | getRandom | createPrimary | create | load | evictControl | readPublic | sign | unseal | flush
  deriving DecidableEq

/-- `TPM_CC_*`. -/
def M.cc : M → Nat
  | .startup => 0x144
  | .getRandom => 0x17B
  | .createPrimary => 0x131
  | .create => 0x153
  | .load => 0x157
  | .evictControl => 0x120
  | .readPublic => 0x173
  | .sign => 0x15D
  | .unseal => 0x15E
  | .flush => 0x165

/-- Whether the command carries a password session: those that ask for authorization. -/
def M.sessions : M → Bool
  | .createPrimary | .create | .load | .evictControl | .sign | .unseal => true
  | _ => false

/-- The handles in the handle area. -/
def M.handles : M → Nat
  | .evictControl => 2
  | .startup | .getRandom | .flush => 0
  | _ => 1

def M.all : List M := [.startup, .getRandom, .createPrimary, .create, .load, .evictControl, .readPublic, .sign, .unseal, .flush]

theorem cc_injective : ∀ a ∈ M.all, ∀ b ∈ M.all, a.cc = b.cc → a = b := by decide

/-- The length of the password authorization area for an auth value of `n` bytes: its 4-byte size, the session handle
(4), the empty nonce (2), the attributes (1), the auth value with its 2-byte size. -/
def authAreaLen (n : Nat) : Nat := 4 + (4 + 2 + 1 + 2 + n)

/-- The size field of the area is the bytes after it. -/
def authAreaSize (n : Nat) : Nat := 4 + 2 + 1 + 2 + n

theorem authArea_consistent (n : Nat) : authAreaLen n = 4 + authAreaSize n := rfl

/-- The header length. -/
def headerLen : Nat := 10

/-- The least length of a command: header, handles, the authorization area when there is one. -/
def minLen (m : M) (auth : Nat) : Nat := headerLen + 4 * m.handles + (if m.sessions then authAreaLen auth else 0)

/-- A command is canonical when its tag says whether it has sessions, its size field is its length and its code is the
method's, and (with sessions) the area after the handles is the password session. `cmd` is the command, `auth` the
auth value presented. -/
def canonical (m : M) (auth : Bytes) (cmd : Bytes) : Bool :=
  let tag := if m.sessions then [0x80, 0x02] else [0x80, 0x01]
  let area := cmd.drop (headerLen + 4 * m.handles)
  decide (cmd.length ≥ minLen m auth.length) && decide (cmd.take 2 = tag) &&
    decide (be32 ((cmd.drop 2).take 4) = cmd.length) && decide (be32 ((cmd.drop 6).take 4) = m.cc) &&
    (!m.sessions ||
      (decide (be32 (area.take 4) = authAreaSize auth.length) && decide ((area.drop 4).take 4 = [0x40, 0, 0, 9]) &&
       decide ((area.drop 8).take 2 = [0, 0]) && decide ((area.drop 10).take 1 = [1]) &&
       decide ((area.drop 11).take 2 = [auth.length / 256, auth.length % 256]) && decide ((area.drop 13).take auth.length = auth)))

/-- An auth value longer than a digest is refused before anything is sent (`InvalidAuth`). -/
def maxAuth : Nat := 64

/-! ## The commands of each store operation, with the live transient handles

A program is the list of commands the store sends for an operation and whether each succeeded. `net` is the change in
the number of transient handles the TPM holds: creating the primary or loading an object adds one, flushing removes
one. `slots` is the change in the number of transient entries the store tracks (the primary and the non-persistent
keys). The invariant: after every operation, successful or not, `net = slots`. (A flush that itself fails is a TPM
failure: the handle stays on both sides until the resource manager reclaims it; it is not a case of this model.) -/

def delta : M × Bool → Int
  | (.createPrimary, true) => 1
  | (.load, true) => 1
  | (.flush, true) => -1
  | _ => 0

def net (p : List (M × Bool)) : Int := (p.map delta).sum

/-- An operation with the point of failure: `none` means every command succeeds. -/
inductive Op where
  | open_ | generate | loadPersistent | persist | sign | random (calls : Nat) | seal | unseal | publicOnly
  deriving DecidableEq

/-- The program an operation runs when the command at index `fail` (if any) is refused by the TPM, and the change
in the store's transient entries. Commands after the failure are not sent, except the cleanup flush. -/
def program : Op → Option Nat → List (M × Bool) × Int
  | .open_, none => ([(.createPrimary, true)], 1)
  | .open_, some _ => ([(.createPrimary, false)], 0)
  | .generate, none => ([(.create, true), (.load, true), (.readPublic, true)], 1)
  | .generate, some 0 => ([(.create, false)], 0)
  | .generate, some 1 => ([(.create, true), (.load, false)], 0)
  | .generate, some _ => ([(.create, true), (.load, true), (.readPublic, false), (.flush, true)], 0)
  | .loadPersistent, none => ([(.readPublic, true)], 0)
  | .loadPersistent, some _ => ([(.readPublic, false)], 0)
  | .persist, none => ([(.evictControl, true), (.flush, true)], -1)
  | .persist, some 0 => ([(.evictControl, false)], 0)
  | .persist, some _ => ([(.evictControl, true), (.flush, false)], 0)
  | .sign, none => ([(.sign, true)], 0)
  | .sign, some _ => ([(.sign, false)], 0)
  | .random n, none => ((List.replicate n (.getRandom, true)), 0)
  | .random n, some i => ((List.replicate i (.getRandom, true) ++ [(.getRandom, false)]), 0)
  | .seal, none => ([(.getRandom, true), (.getRandom, true), (.create, true)], 0)
  | .seal, some 0 => ([(.getRandom, false)], 0)
  | .seal, some 1 => ([(.getRandom, true), (.getRandom, false)], 0)
  | .seal, some _ => ([(.getRandom, true), (.getRandom, true), (.create, false)], 0)
  | .unseal, none => ([(.load, true), (.unseal, true), (.flush, true)], 0)
  | .unseal, some 0 => ([(.load, false)], 0)
  | .unseal, some _ => ([(.load, true), (.unseal, false), (.flush, true)], 0)
  | .publicOnly, _ => ([], 0)

/-- Every operation at every failure point, as a list of cases. -/
def cases : List (Op × Option Nat) :=
  [(.open_, none), (.open_, some 0), (.generate, none), (.generate, some 0), (.generate, some 1), (.generate, some 2),
   (.loadPersistent, none), (.loadPersistent, some 0), (.persist, none), (.persist, some 0), (.persist, some 1),
   (.sign, none), (.sign, some 0), (.seal, none), (.seal, some 0), (.seal, some 1), (.seal, some 2), (.unseal, none),
   (.unseal, some 0), (.unseal, some 1), (.unseal, some 2), (.random 3, none), (.random 3, some 0), (.random 3, some 2),
   (.publicOnly, none)]

/-- After every operation and every failure point, the TPM's transient handles are exactly the store's entries: a
handle loaded is flushed on every path, also when the command after it fails. -/
theorem programs_balance : ∀ c ∈ cases, net (program c.1 c.2).1 = (program c.1 c.2).2 := by decide

/-- A random fill of `n` bytes sends `ceil(n / 32)` commands when the TPM gives all it is asked for. -/
def randomCalls (n : Nat) : Nat := (n + 31) / 32

/-! ## The sealed blob -/

def tpmVersion : Nat := 2

/-- A TPM2B: the 2-byte size and that many bytes. -/
def tpm2bLen (b : Bytes) : Option Nat :=
  if b.length < 2 then none else
    let n := (b.getD 0 0) * 256 + b.getD 1 0
    if b.length < 2 + n then none else some (2 + n)

/-- `parse_sealed`: the version byte, then two TPM2B (the library also checks the public area inside; its verdict is
`pubOk`), and the header length. -/
def parseHeader (s : Bytes) (pubOk : Bool) : Except KeystoreSealed.Err Nat :=
  match s with
  | [] => .error .invalidSealed
  | v :: body =>
    if v ≠ tpmVersion then .error .invalidSealed
    else match tpm2bLen body with
      | none => .error .invalidSealed
      | some a => match tpm2bLen (body.drop a) with
        | none => .error .invalidSealed
        | some b => if pubOk then .ok (1 + a + b) else .error .invalidSealed

theorem parseHeader_version (s : Bytes) (p : Bool) (v : Nat) (rest : Bytes) (h : v ≠ tpmVersion) :
    parseHeader (v :: rest) p = .error .invalidSealed := by simp [parseHeader, h]

theorem parseHeader_empty (p : Bool) : parseHeader [] p = .error .invalidSealed := rfl

/-- The order in which `unseal` reports: a malformed header; the load; the unseal (before the flush); the flush; a
secret of the wrong length; the authentication of the body. -/
inductive UErr where
  | invalidSealed
  | tpm (code : Nat)
  deriving DecidableEq

def unsealResult (parseOk : Bool) (loadRc unsealRc flushRc dekLen : Nat) (aeadOk : Bool) : Except UErr Unit :=
  if ¬parseOk then .error .invalidSealed
  else if loadRc ≠ 0 then .error (.tpm loadRc)
  else if unsealRc ≠ 0 then .error (.tpm unsealRc)
  else if flushRc ≠ 0 then .error (.tpm flushRc)
  else if dekLen ≠ 32 then .error .invalidSealed
  else if ¬aeadOk then .error .invalidSealed
  else .ok ()

theorem unsealResult_ok_iff (p : Bool) (l u f d : Nat) (a : Bool) :
    unsealResult p l u f d a = .ok () ↔ p = true ∧ l = 0 ∧ u = 0 ∧ f = 0 ∧ d = 32 ∧ a = true := by
  unfold unsealResult
  by_cases hp : p = true <;> by_cases hl : l = 0 <;> by_cases hu : u = 0 <;> by_cases hf : f = 0 <;>
    by_cases hd : d = 32 <;> by_cases ha : a = true <;> simp [hp, hl, hu, hf, hd, ha]

/-- A refused unseal command is reported before a refused flush. -/
theorem unseal_error_first (l f d : Nat) (a : Bool) (u : Nat) (hl : l = 0) (hu : u ≠ 0) :
    unsealResult true l u f d a = .error (.tpm u) := by simp [unsealResult, hl, hu]

/-- Persistent handles: `0x8100_0000 ..= 0x81FF_FFFF`. -/
def persistent (h : Nat) : Bool := decide (0x81000000 ≤ h ∧ h ≤ 0x81FFFFFF)

end Vinc.KeystoreTpm

#audit_axioms Vinc.KeystoreTpm.parseResp_ok_iff
#audit_axioms Vinc.KeystoreTpm.cc_injective
#audit_axioms Vinc.KeystoreTpm.unsealResult_ok_iff
