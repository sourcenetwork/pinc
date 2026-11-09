import Vinc.Axioms
import Vinc.ConnectMailbox
import Vinc.TraceConnectMailbox

/-! Axiom audit of the main theorems of the connectivity proofs. -/

#audit_axioms Vinc.ConnectMailbox.mailbox_bounds
#audit_axioms Vinc.ConnectMailbox.conservation
#audit_axioms Vinc.ConnectMailbox.fifo_once
#audit_axioms Vinc.ConnectMailbox.push_fresh
#audit_axioms Vinc.ConnectMailbox.pop_spec
#audit_axioms Vinc.ConnectMailbox.drop_oldest
#audit_axioms Vinc.ConnectMailbox.push_first
#audit_axioms Vinc.ConnectMailbox.wake_first
#audit_axioms Vinc.ConnectMailbox.wake_spaced
#audit_axioms Vinc.ConnectMailbox.wake_quiet
