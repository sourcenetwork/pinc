------------------------------- MODULE AmpOps -------------------------------
(***************************************************************************)
(* The operations of pinc-security amp.rs (AmpBudget), over an abstract    *)
(* number type so that one definition serves two uses: Amp.tla instantiates*)
(* it with TLC integers and a small saturation maximum (exhaustive model   *)
(* checking), TraceSecurity.tla with the 80-bit words of U64.tla and the   *)
(* real u64::MAX (the recorded events of the real code).                   *)
(*                                                                         *)
(*  SatAdd   u64::saturating_add (on_receive, on_send)                     *)
(*  CanSend  validated || tx + n + OVERHEAD <= rx * FACTOR, the sum and    *)
(*           the product exact (the code compares in 128 bits); the gate   *)
(*           of the pinc-core ledger (LedgerOps.tla)                       *)
(*  BudgetCanSend  AmpBudget::can_send: CanSend, and before validation     *)
(*           nothing once tx is saturated (tx = u64::MAX may hide any true *)
(*           total, so the comparison would no longer bound what was sent) *)
(*  Times3   rx * FACTOR, FACTOR = 3                                       *)
(*                                                                         *)
(* A budget is the record [rx, tx, valid].                                 *)
(***************************************************************************)
CONSTANTS Zero, Top, Ovh, Plus(_, _), Leq(_, _), Times3(_)

SatAdd(a, n) == IF Leq(Plus(a, n), Top) THEN Plus(a, n) ELSE Top
CanSend(v, tx, rx, n) == v \/ Leq(Plus(Plus(tx, n), Ovh), Times3(rx))
BudgetCanSend(v, tx, rx, n) == v \/ (tx /= Top /\ CanSend(FALSE, tx, rx, n))

New == [rx |-> Zero, tx |-> Zero, valid |-> FALSE]
Recv(b, n) == [b EXCEPT !.rx = SatAdd(b.rx, n)]
Send(b, n) == [b EXCEPT !.tx = SatAdd(b.tx, n)]
Validate(b) == [b EXCEPT !.valid = TRUE]
=============================================================================
