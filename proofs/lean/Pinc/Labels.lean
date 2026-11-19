import Pinc.Axioms

/-!
# Domain-separation labels

The 23 labels of `pinc-security/src/labels.rs`, copied verbatim, and the facts the key schedule relies on: they are
pairwise distinct, all start with the protocol prefix, and none equals a label of `pinc-crypto`. The labels are
ASCII, so the byte string of a label is its list of character codes (`bytes`), which is also its UTF-8 encoding.
-/

namespace Pinc.Labels

def prefix_ : String := "PINC 2026 v1 "
def handshake : String := "PINC 2026 v1 handshake"
def resumeHandshake : String := "PINC 2026 v1 resume handshake"
def chain : String := "PINC 2026 v1 chain"
def kemKeyHash : String := "PINC 2026 v1 prekey hash"
def signatureResponder : String := "PINC 2026 v1 responder"
def signatureInitiator : String := "PINC 2026 v1 initiator"
def handshakeInitiator : String := "PINC 2026 v1 handshake secret initiator"
def handshakeResponder : String := "PINC 2026 v1 handshake secret responder"
def applicationInitiator : String := "PINC 2026 v1 application secret initiator"
def applicationResponder : String := "PINC 2026 v1 application secret responder"
def resumption : String := "PINC 2026 v1 resumption secret"
def ticket : String := "PINC 2026 v1 ticket"
def binder : String := "PINC 2026 v1 binder"
def earlyData : String := "PINC 2026 v1 early data"
def resumeConfirm : String := "PINC 2026 v1 resume confirm"
def subSession : String := "PINC 2026 v1 sub session"
def subSessionContext : String := "PINC 2026 v1 sub session context"
def packetKey : String := "PINC 2026 v1 packet key"
def packetIv : String := "PINC 2026 v1 packet iv"
def headerKey : String := "PINC 2026 v1 header key"
def keyRoll : String := "PINC 2026 v1 key roll"
def keyRollId : String := "PINC 2026 v1 key roll id"
def cidSecret : String := "PINC 2026 v1 connection id secret"

/-- `labels::ALL`. -/
def all : List String :=
  [handshake, resumeHandshake, chain, kemKeyHash, signatureResponder, signatureInitiator, handshakeInitiator,
   handshakeResponder, applicationInitiator, applicationResponder, resumption, ticket, binder, earlyData,
   resumeConfirm, subSession, subSessionContext, packetKey, packetIv, headerKey, keyRoll, keyRollId, cidSecret]

/-- The labels of `pinc-crypto` (`NODE_ID`, `HYBRID_SIGNATURE`). -/
def cryptoLabels : List String := ["PINC 2026 v1 node id", "PINC 2026 v1 hybrid signature"]

/-- The bytes of an ASCII label. -/
def bytes (s : String) : List Nat := s.toList.map Char.toNat

theorem all_length : all.length = 23 := rfl

/-- All 23 labels are pairwise distinct. -/
theorem all_nodup : all.Nodup := by decide

/-- Every label starts with the prefix. -/
theorem all_prefix : ∀ l ∈ all, prefix_.toList <+: l.toList := by decide

/-- No label of the security layer is a label of `pinc-crypto`. -/
theorem disjoint_crypto : ∀ l ∈ all, l ∉ cryptoLabels := by decide

/-- Every label is ASCII, so its UTF-8 bytes are its character codes and `bytes` is the byte string the code hashes. -/
theorem all_ascii : ∀ l ∈ all, ∀ c ∈ l.toList, c.toNat < 128 := by decide

/-- The labels of the removed key update and token are no longer in the list, and the two that replaced them are. -/
theorem removed_and_added :
    "PINC 2026 v1 key update" ∉ all ∧ "PINC 2026 v1 token" ∉ all ∧ keyRoll ∈ all ∧ cidSecret ∈ all := by decide

/-- The byte string of an ASCII label determines it (characters are determined by their codes below `2^21`
unless they are surrogates, which cannot occur in a `String`). Only the concrete labels are needed: they are
pairwise distinct as byte strings. -/
theorem bytes_nodup : (all.map bytes).Nodup := by decide

end Pinc.Labels

#audit_axioms Pinc.Labels.all_length
#audit_axioms Pinc.Labels.all_nodup
#audit_axioms Pinc.Labels.all_ascii
#audit_axioms Pinc.Labels.removed_and_added
#audit_axioms Pinc.Labels.all_prefix
#audit_axioms Pinc.Labels.disjoint_crypto
#audit_axioms Pinc.Labels.bytes_nodup
