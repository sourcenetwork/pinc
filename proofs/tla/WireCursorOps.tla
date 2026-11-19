---------------------------- MODULE WireCursorOps ----------------------------
(***************************************************************************)
(* The bounded cursors of pinc-wire as pure operators on their state,      *)
(* written call for call:                                                  *)
(*                                                                         *)
(* Reader (reader.rs): the state is [rest, pos], the fields of the struct  *)
(* (`rest` the bytes not consumed, `pos` the bytes consumed). RPeek is     *)
(* `peek_u8`, RReadBytes `read_bytes` (split_at_checked, the needed count  *)
(* by saturating_sub, pos by saturating_add), RReadArray `read_array`      *)
(* (first_chunk, then read_bytes), RReadUN `read_u8` (N = 1), `read_u16`,  *)
(* `read_u32`, `read_u64` (from_be_bytes), RReadVarint `read_varint`       *)
(* (varint::decode of the rest, then read_bytes of its length).            *)
(*                                                                         *)
(* Writer (writer.rs): the state is [buf, pos], the caller's buffer and    *)
(* the bytes written. A cell never written holds -1, which stands for      *)
(* whatever byte the caller's buffer held there. WEnsure is `ensure`,      *)
(* WPutSlice `put_slice` (ensure, then the range pos..end of the buffer),  *)
(* WPutU8 `put_u8`, WPutUN `put_u16`, `put_u32`, `put_u64` (to_be_bytes),  *)
(* WPutVarint `put_varint` (varint::encode into buf[pos..]).               *)
(*                                                                         *)
(* A call returns [res, st]: the Result and the state after it. res is     *)
(* [kind |-> "ok", ...] or the error: "truncated" and "small" with the     *)
(* needed count as a U64 word (WireError::Truncated, BufferTooSmall),      *)
(* "toolong", "nonminimal", "overflow" (the varint errors). A usize is a   *)
(* word of U64.tla (a 64-bit usize), so read_bytes(usize::MAX) is in the   *)
(* domain. The varint is Varint.tla's, already checked there.              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

U == INSTANCE U64
V == INSTANCE Varint WITH SmallMax <- 0, c <- 0

(* the big-endian value of a byte string of at most 8 bytes (u16::from_be_bytes and its kin) *)
RECURSIVE BeWord(_)
BeWord(bs) == IF Len(bs) = 0 THEN U!Zero
              ELSE U!Add(U!Shl(BeWord(SubSeq(bs, 1, Len(bs) - 1)), 8), U!W(bs[Len(bs)]))

(* the n-byte big-endian form of a word (u16::to_be_bytes and its kin) *)
BeBytes(a, n) == [i \in 1..n |-> U!Val(U!Low(U!Shr(a, 8 * (n - i)), 8))]

Trunc(n) == [kind |-> "truncated", needed |-> n]
Small(n) == [kind |-> "small", needed |-> n]
Ok == [kind |-> "ok"]

(* usize::saturating_sub on words *)
SatSub(a, b) == IF U!Lt(a, b) THEN U!Zero ELSE U!Sub(a, b)

(* ---- Reader ---- *)

(* Reader::new *)
RNew(buf) == [rest |-> buf, pos |-> 0]

(* Reader::peek_u8: first().copied().ok_or(Truncated { needed: 1 }); nothing is consumed *)
RPeek(r) == IF Len(r.rest) = 0 THEN Trunc(U!One) ELSE [kind |-> "ok", b |-> r.rest[1]]

(* Reader::read_bytes(n), n a usize word *)
RReadBytes(r, n) ==
    IF U!Lt(U!W(Len(r.rest)), n)
    THEN [res |-> Trunc(SatSub(n, U!W(Len(r.rest)))), st |-> r]
    ELSE LET k == U!Val(n)
         IN [res |-> [kind |-> "ok", bytes |-> SubSeq(r.rest, 1, k)],
             st |-> [rest |-> SubSeq(r.rest, k + 1, Len(r.rest)), pos |-> r.pos + k]]

(* Reader::read_array::<N>: first_chunk, else Truncated { needed: N.saturating_sub(rest.len()) }; then read_bytes(N)? *)
RReadArray(r, N) ==
    IF N > Len(r.rest) THEN [res |-> Trunc(U!W(N - Len(r.rest))), st |-> r]
    ELSE LET arr == SubSeq(r.rest, 1, N)
             x == RReadBytes(r, U!W(N))
         IN IF x.res.kind # "ok" THEN x ELSE [res |-> [kind |-> "ok", bytes |-> arr], st |-> x.st]

(* read_u8 (N = 1, the one byte of the array), read_u16, read_u32, read_u64 (N = 2, 4, 8, from_be_bytes) *)
RReadUN(r, N) ==
    LET x == RReadArray(r, N)
    IN IF x.res.kind # "ok" THEN x ELSE [res |-> [kind |-> "ok", v |-> BeWord(x.res.bytes)], st |-> x.st]

(* Reader::read_varint: varint::decode(rest)?, then read_bytes(len)? *)
RReadVarint(r) ==
    LET d == V!Decode(r.rest)
    IN IF d.kind = "truncated" THEN [res |-> Trunc(U!One), st |-> r]
       ELSE IF d.kind # "ok" THEN [res |-> [kind |-> d.kind], st |-> r]
       ELSE LET x == RReadBytes(r, U!W(d.n))
            IN IF x.res.kind # "ok" THEN x ELSE [res |-> [kind |-> "ok", v |-> d.v], st |-> x.st]

(* one reader call: [op |-> "peek"], [op |-> "bytes", n |-> usize word], [op |-> "uN", n |-> 1, 2, 4 or 8],
   [op |-> "varint"]; peek_u8 takes &self and leaves the state as it was *)
RCall(r, cl) ==
    CASE cl.op = "peek" -> [res |-> RPeek(r), st |-> r]
      [] cl.op = "bytes" -> RReadBytes(r, cl.n)
      [] cl.op = "uN" -> RReadUN(r, cl.n)
      [] cl.op = "varint" -> RReadVarint(r)

(* ---- Writer ---- *)

(* Writer::new over a caller buffer of cap bytes *)
WNew(cap) == [buf |-> [i \in 1..cap |-> -1], pos |-> 0]

(* Writer::remaining: buf.len().saturating_sub(pos) *)
WRemaining(w) == IF w.pos > Len(w.buf) THEN 0 ELSE Len(w.buf) - w.pos

(* Writer::written: buf[..pos] *)
WWritten(w) == SubSeq(w.buf, 1, w.pos)

(* Writer::ensure(n), n a usize word *)
WEnsure(w, n) ==
    IF U!Le(n, U!W(WRemaining(w))) THEN Ok ELSE Small(U!Sub(n, U!W(WRemaining(w))))

(* the buffer with bytes copied into the cells after p *)
Splice(buf, p, bytes) == [i \in 1..Len(buf) |-> IF i > p /\ i <= p + Len(bytes) THEN bytes[i - p] ELSE buf[i]]

(* Writer::put_slice: ensure(len)?, then get_mut(pos..end), else BufferTooSmall { needed: len } *)
WPutSlice(w, bytes) ==
    LET e == WEnsure(w, U!W(Len(bytes)))
        end == w.pos + Len(bytes)
    IN IF e.kind # "ok" THEN [res |-> e, st |-> w]
       ELSE IF end > Len(w.buf) THEN [res |-> Small(U!W(Len(bytes))), st |-> w]
       ELSE [res |-> Ok, st |-> [buf |-> Splice(w.buf, w.pos, bytes), pos |-> end]]

(* put_u8: put_slice(&[v]) *)
WPutU8(w, b) == WPutSlice(w, <<b>>)

(* put_u16, put_u32, put_u64: put_slice(&v.to_be_bytes()) *)
WPutUN(w, a, n) == WPutSlice(w, BeBytes(a, n))

(* Writer::put_varint: varint::encode(v, buf[pos..])?, then pos.saturating_add(n) *)
WPutVarint(w, v) ==
    LET e == V!Encode(v, WRemaining(w))
    IN IF e.kind = "overflow" THEN [res |-> [kind |-> "overflow"], st |-> w]
       ELSE IF e.kind = "small" THEN [res |-> Small(U!W(e.needed)), st |-> w]
       ELSE [res |-> Ok, st |-> [buf |-> Splice(w.buf, w.pos, e.bytes), pos |-> w.pos + Len(e.bytes)]]

(* one writer call: [op |-> "slice", b], [op |-> "uN", n |-> 1, 2, 4 or 8, v |-> word], [op |-> "varint", v],
   [op |-> "ensure", n |-> usize word]; ensure takes &self and leaves the state as it was *)
WCall(w, cl) ==
    CASE cl.op = "slice" -> WPutSlice(w, cl.b)
      [] cl.op = "uN" -> (IF cl.n = 1 THEN WPutU8(w, U!Val(cl.v)) ELSE WPutUN(w, cl.v, cl.n))
      [] cl.op = "varint" -> WPutVarint(w, cl.v)
      [] cl.op = "ensure" -> [res |-> WEnsure(w, cl.n), st |-> w]

=============================================================================
