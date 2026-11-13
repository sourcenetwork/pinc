import Vinc.ConnectTicket

/-!
# The text form of a ticket

`Ticket::to_text` and `Ticket::from_text` of `ticket.rs`: the binary ticket in base32 (RFC 4648 alphabet, lowercase,
no padding), read back in either case. The functions are the loops of the code over the accumulator: the encoder
takes a byte into the accumulator and emits a symbol for every 5 bits it holds, then emits the leftover bits padded
with zeros; the decoder takes a symbol and emits a byte for every 8 bits it holds, and at the end refuses 5 or more
leftover bits or any leftover bit that is not zero. The accumulator of the code is a `u32` whose high bits nothing
reads; it is a `Nat` modulo `2^32` here, as in the code.

Theorems: `b32_roundtrip` (decoding the symbols of a byte string returns it), `b32dec_inv` (an accepted symbol string
is the symbols of the bytes it returned, so the text has one accepted spelling up to case), `Tk.text_roundtrip` and
`Tk.fromText_inv` for tickets (both in `ConnectTicketTextPf`).
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-- The emit loop of the encoder: a symbol for every 5 bits the accumulator holds. -/
def b32drain (acc : Nat) : Nat → List Nat → Nat × List Nat
  | bits, out =>
    if h : 5 ≤ bits then b32drain acc (bits - 5) (out ++ [(acc / 2 ^ (bits - 5)) % 32]) else (bits, out)
termination_by bits => bits
decreasing_by omega

/-- `to_text` over the bytes: the symbols (0 to 31) it emits. -/
def b32enc : List Nat → Nat → Nat → List Nat → List Nat
  | [], acc, bits, out => if 0 < bits then out ++ [(acc * 2 ^ (5 - bits)) % 32] else out
  | b :: bs, acc, bits, out =>
    let a := (acc * 256) % 2 ^ 32 + b
    let d := b32drain a (bits + 8) out
    b32enc bs a d.1 d.2

/-- The symbols of a byte string. -/
def b32Of (bs : List Nat) : List Nat := b32enc bs 0 0 []

/-- `from_text` over the symbols: the bytes, or the refusal. The buffer of the code holds `MAX_LEN` = 144 bytes. -/
def b32dec : List Nat → Nat → Nat → List Nat → Except CErr (List Nat)
  | [], acc, bits, out => if 5 ≤ bits ∨ acc % 2 ^ bits ≠ 0 then .error .text else .ok out
  | s :: ss, acc, bits, out =>
    let a := (acc * 32) % 2 ^ 32 + s
    if 8 ≤ bits + 5 then
      if 144 ≤ out.length then .error .text
      else b32dec ss a (bits + 5 - 8) (out ++ [(a / 2 ^ (bits + 5 - 8)) % 256])
    else b32dec ss a (bits + 5) out

/-- The symbol of a character, in either case. -/
def charSym (c : Nat) : Option Nat :=
  let l := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c
  if 97 ≤ l ∧ l ≤ 122 then some (l - 97) else if 50 ≤ l ∧ l ≤ 55 then some (l - 50 + 26) else none

/-- The character of a symbol (`ALPHABET`). -/
def symChar (s : Nat) : Nat := if s < 26 then 97 + s else 50 + (s - 26)

/-- `Ticket::to_text` into a buffer of `cap` bytes. -/
def Tk.toText (cap : Nat) (t : Tk) : Except CErr (List Nat) :=
  let cs := (b32Of t.bytes).map symChar
  if cs.length ≤ cap then .ok cs else .error (.wire (.small (cap + 1)))

/-- `Ticket::from_text`. -/
def Tk.fromText (text : List Nat) : Except CErr Tk :=
  match text.mapM charSym with
  | none => .error .text
  | some ss => do
    let bs ← b32dec ss 0 0 []
    Tk.parse bs

end Vinc.ConnCodec
