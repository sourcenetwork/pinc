------------------------------ MODULE CreditOps ------------------------------
(***************************************************************************)
(* The operations of vinc-security credit.rs (CreditRecord), over the     *)
(* field width W (bits, even; the byte width is W / 2) and the window unit *)
(* Unit. Credit.tla checks them exhaustively at small widths; the trace   *)
(* check (TraceSecurity.tla) instantiates the real width W = 16 and       *)
(* Unit = 16384 and compares the recorded results of the real code with    *)
(* the same operators. No set of records is defined here, so instantiating *)
(* the real width enumerates nothing.                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS W, Unit

Bs == 2 ^ (W \div 2)            \* the number of byte values
MaxF == 2 ^ W - 1               \* u16::MAX
None == [wu |-> 0, ms |-> 0, md |-> 0]

Encode(r) == <<r.wu \div Bs, r.wu % Bs, r.ms \div Bs, r.ms % Bs, r.md \div Bs, r.md % Bs>>
Decode(b) == [wu |-> b[1] * Bs + b[2], ms |-> b[3] * Bs + b[4], md |-> b[5] * Bs + b[6]]

(* CreditRecord::new on the quotient q = window_bytes / WINDOW_UNIT *)
NewFromUnits(q, s, d) == [wu |-> IF q > MaxF THEN MaxF ELSE q, ms |-> s, md |-> d]
New(w, s, d) == NewFromUnits(w \div Unit, s, d)
WindowBytes(r) == r.wu * Unit
Covers(a, b) == a.wu >= b.wu /\ a.ms >= b.ms /\ a.md >= b.md
=============================================================================
