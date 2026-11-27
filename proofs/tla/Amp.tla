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
(* THE TRUE TOTALS. The ghosts got and sent count, without saturation, the *)
(* bytes received and the bytes sent before validation; TrueBound checks   *)
(* sent <= 3 * got. The bound over the saturated counters alone let the    *)
(* saturation bug through: once tx stopped at U it no longer grew, so a    *)
(* send that can_send allowed at tx = U was never counted (the fixed code  *)
(* refuses any unvalidated send at tx = u64::MAX). Guard = FALSE checks    *)
(* the old gate, which Amp_unguarded.cfg expects to violate TrueBound. The *)
(* ghosts are bounded by the state constraint GhostBound.                  *)
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

CONSTANTS U, Guard
VARIABLES b, got, sent
vars == <<b, got, sent>>

IPlus(a, c) == a + c
ILeq(a, c) == a <= c
ITimes3(a) == 3 * a

A == INSTANCE AmpOps WITH Zero <- 0, Top <- U, Ovh <- 48, Plus <- IPlus, Leq <- ILeq, Times3 <- ITimes3

\* the gate of AmpBudget::can_send; Guard = FALSE is the gate before the saturation check
Gate(v, tx, rx, n) == IF Guard THEN A!BudgetCanSend(v, tx, rx, n) ELSE A!CanSend(v, tx, rx, n)

Init == b = A!New /\ got = 0 /\ sent = 0

Receive == \E n \in 0..U : b' = A!Recv(b, n) /\ got' = got + n /\ sent' = sent
Send == \E n \in 0..U : Gate(b.valid, b.tx, b.rx, n) /\ b' = A!Send(b, n) /\ got' = got
            /\ sent' = IF b.valid THEN sent ELSE sent + n
Validate == b' = A!Validate(b) /\ UNCHANGED <<got, sent>>

Next == Receive \/ Send \/ Validate
Spec == Init /\ [][Next]_vars

\* the ghosts grow without bound; past a few times U nothing new is reachable for the counters
GhostBound == got <= 2 * U /\ sent <= 7 * U

TypeOK == b.rx \in 0..U /\ b.tx \in 0..U /\ b.valid \in BOOLEAN

(* before validation a sender that obeyed can_send has sent at most three times what it received *)
AmplificationBound == ~b.valid => b.tx <= 3 * b.rx
(* ... and over the true totals, which the saturated counters may hide *)
TrueBound == ~b.valid => sent <= 3 * got
Margin == ~b.valid => (b.tx = 0 \/ b.tx + 48 <= 3 * b.rx)

(* the independent definition of can_send *)
IndepCanSend(n) == b.valid \/ (b.tx < U /\ b.tx + n + 48 <= 3 * b.rx)
CanSendExact == \A n \in 0..U : Gate(b.valid, b.tx, b.rx, n) = IndepCanSend(n)
(* ... and what it means: an allowed send keeps the margin even if the counter saturates, a refused one would break
   it while the sum is exact *)
CanSendMeaning ==
    ~b.valid => \A n \in 0..U :
        (Gate(b.valid, b.tx, b.rx, n) => A!Send(b, n).tx + 48 <= 3 * b.rx)
        /\ (~Gate(b.valid, b.tx, b.rx, n) => (b.tx = U \/ b.tx + n + 48 > 3 * b.rx))

SatAddExact == \A a, n \in 0..U : A!SatAdd(a, n) = IF a + n <= U THEN a + n ELSE U

CountersMonotone == [][b'.rx >= b.rx /\ b'.tx >= b.tx]_vars
ValidSticky == [][b.valid => b'.valid]_vars
=============================================================================
