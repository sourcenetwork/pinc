import Vinc.Axioms

/-!
# Domain-separation labels

The 22 labels of `vinc-security/src/labels.rs`, copied verbatim, and the facts the key schedule relies on: they are
pairwise distinct, all start with the protocol prefix, and none equals a label of `vinc-crypto`. The labels are
ASCII, so the byte string of a label is its list of character codes (`bytes`), which is also its UTF-8 encoding.
-/

namespace Vinc.Labels

def prefix_ : String := "VINC 2026 v1 "
def handshake : String := "VINC 2026 v1 handshake"
def resumeHandshake : String := "VINC 2026 v1 resume handshake"
def chain : String := "VINC 2026 v1 chain"
def kemKeyHash : String := "VINC 2026 v1 prekey hash"
def signatureResponder : String := "VINC 2026 v1 responder"
def signatureInitiator : String := "VINC 2026 v1 initiator"
def handshakeInitiator : String := "VINC 2026 v1 handshake secret initiator"
def handshakeResponder : String := "VINC 2026 v1 handshake secret responder"
def applicationInitiator : String := "VINC 2026 v1 application secret initiator"
def applicationResponder : String := "VINC 2026 v1 application secret responder"
def resumption : String := "VINC 2026 v1 resumption secret"
def ticket : String := "VINC 2026 v1 ticket"
def binder : String := "VINC 2026 v1 binder"
def earlyData : String := "VINC 2026 v1 early data"
def resumeConfirm : String := "VINC 2026 v1 resume confirm"
def subSession : String := "VINC 2026 v1 sub session"
def subSessionContext : String := "VINC 2026 v1 sub session context"
def packetKey : String := "VINC 2026 v1 packet key"
def packetIv : String := "VINC 2026 v1 packet iv"
def headerKey : String := "VINC 2026 v1 header key"
def keyUpdate : String := "VINC 2026 v1 key update"
def token : String := "VINC 2026 v1 token"

/-- `labels::ALL`. -/
def all : List String :=
  [handshake, resumeHandshake, chain, kemKeyHash, signatureResponder, signatureInitiator, handshakeInitiator,
   handshakeResponder, applicationInitiator, applicationResponder, resumption, ticket, binder, earlyData,
   resumeConfirm, subSession, subSessionContext, packetKey, packetIv, headerKey, keyUpdate, token]

/-- The labels of `vinc-crypto` (`NODE_ID`, `HYBRID_SIGNATURE`). -/
def cryptoLabels : List String := ["VINC 2026 v1 node id", "VINC 2026 v1 hybrid signature"]

/-- The bytes of an ASCII label. -/
def bytes (s : String) : List Nat := s.toList.map Char.toNat

theorem all_length : all.length = 22 := rfl

/-- All 22 labels are pairwise distinct. -/
theorem all_nodup : all.Nodup := by decide

/-- Every label starts with the prefix. -/
theorem all_prefix : ∀ l ∈ all, prefix_.toList <+: l.toList := by decide

/-- No label of the security layer is a label of `vinc-crypto`. -/
theorem disjoint_crypto : ∀ l ∈ all, l ∉ cryptoLabels := by decide

/-- The byte string of an ASCII label determines it (characters are determined by their codes below `2^21`
unless they are surrogates, which cannot occur in a `String`). Only the concrete labels are needed: they are
pairwise distinct as byte strings. -/
theorem bytes_nodup : (all.map bytes).Nodup := by decide

end Vinc.Labels

#audit_axioms Vinc.Labels.all_nodup
#audit_axioms Vinc.Labels.all_prefix
#audit_axioms Vinc.Labels.disjoint_crypto
#audit_axioms Vinc.Labels.bytes_nodup
