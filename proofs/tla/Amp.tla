-------------------------------- MODULE Amp --------------------------------
(***************************************************************************)
(* Model of the anti-amplification budget of pinc-security amp.rs.         *)
(*                                                                         *)
(* The counters rx and tx saturate at U (u64::MAX in the code, a small    *)
(* parameter here so that TLC reaches saturation: U = 100 is checked); the *)
(* operations are AmpOps.tla, the same definitions the trace check uses.   *)
(* OVERHEAD is 48 and FACTOR 3, as in the code.                            *)
(*                                                                         *)
(* THE REACHABLE SET. Next lets the environment receive any number of bytes*)
(* at any time, validate the path, and send n bytes only in a state where  *)
(* can_send(n) holds. That is the definition of the behaviours checked,    *)
(* not an assumption about a caller: the bound is a statement about every  *)
(* operation sequence in which each send obeyed can_send, and says nothing *)
(* about a caller that sends without asking.                               *)
(*                                                                         *)
(* Checked, in every reachable state: before validation tx <= 3 * rx; the  *)
(* margin tx = 0 or tx + 48 <= 3 * rx (can_send counts the overhead that   *)
(* on_send does not record); the counters stay in 0..U; can_send equals an *)
(* independent definition on every n in 0..U (validated, or the exact sum  *)
(* tx + n + 48 within three times rx, and the equivalent statement that a  *)
(* send which can_send allows leaves the margin intact); saturating_add is *)
(* the exact sum below U and U above it. As actions: counters never        *)
(* decrease and validation is sticky.                                      *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/Amp.lean (amplification_bound,       *)
(* reach_margin, canSend_iff, u128_no_overflow). TraceSecurity.tla checks  *)
(* the recorded events of the real AmpBudget against AmpOps.tla.           *)
(***************************************************************************)
EXTENDS Integers

CONSTANT U
VARIABLE b

IPlus(a, c) == a + c
ILeq(a, c) == a <= c
ITimes3(a) == 3 * a

A == INSTANCE AmpOps WITH Zero <- 0, Top <- U, Ovh <- 48, Plus <- IPlus, Leq <- ILeq, Times3 <- ITimes3

Init == b = A!New

Receive == \E n \in 0..U : b' = A!Recv(b, n)
Send == \E n \in 0..U : A!CanSend(b.valid, b.tx, b.rx, n) /\ b' = A!Send(b, n)
Validate == b' = A!Validate(b)

Next == Receive \/ Send \/ Validate
Spec == Init /\ [][Next]_b

TypeOK == b.rx \in 0..U /\ b.tx \in 0..U /\ b.valid \in BOOLEAN

(* before validation a sender that obeyed can_send has sent at most three times what it received *)
AmplificationBound == ~b.valid => b.tx <= 3 * b.rx
Margin == ~b.valid => (b.tx = 0 \/ b.tx + 48 <= 3 * b.rx)

(* the independent definition of can_send *)
IndepCanSend(n) == b.valid \/ b.tx + n + 48 <= 3 * b.rx
CanSendExact == \A n \in 0..U : A!CanSend(b.valid, b.tx, b.rx, n) = IndepCanSend(n)
(* ... and what it means: an allowed send keeps the margin even if the counter saturates, a refused one would break
   it while the sum is exact *)
CanSendMeaning ==
    ~b.valid => \A n \in 0..U :
        (A!CanSend(b.valid, b.tx, b.rx, n) => A!Send(b, n).tx + 48 <= 3 * b.rx)
        /\ (~A!CanSend(b.valid, b.tx, b.rx, n) => b.tx + n + 48 > 3 * b.rx)

SatAddExact == \A a, n \in 0..U : A!SatAdd(a, n) = IF a + n <= U THEN a + n ELSE U

CountersMonotone == [][b'.rx >= b.rx /\ b'.tx >= b.tx]_b
ValidSticky == [][b.valid => b'.valid]_b
=============================================================================
