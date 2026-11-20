--------------------------- MODULE TraceFacadeState ---------------------------
(***************************************************************************)
(* Trace validation of crates/pinc/src/engine/state.rs (`parse`,           *)
(* `export_state`, `restore_state`, with `add_address` of engine/ops.rs)   *)
(* against FacadeStateOps.tla at the real widths, composed with the core's *)
(* parse of CoreStateOps.tla.                                              *)
(*                                                                         *)
(* The unit test `engine::state::tests::trace_state` (both builds of the   *)
(* crate `pinc`, file facade_state.ndjson) restores inputs into live cores *)
(* and records, per input: the bytes, what `parse` returned, whether       *)
(* `restore_state` accepted and what it reported, and the live state       *)
(* before and after (the export bytes, the book sorted by node, the record *)
(* number as 8 bytes). Checked:                                            *)
(*  - the parse is the model's;                                            *)
(*  - restore accepts exactly when the framing parses and the core's parse *)
(*    (CoreStateOps, the model CoreState.tla checks) reads its bytes;      *)
(*  - a refusal leaves the export bytes, the book and the record number;   *)
(*  - after an accepted restore the book is the model's merge of the book  *)
(*    before and the input's, the record number is the larger one (version *)
(*    2) or unchanged (version 1), and `addresses` counts the input's      *)
(*    entries the book kept an address of (fix F14);                       *)
(*  - every export parses back as the book and record number it was taken  *)
(*    from, and its core bytes are read by the core's parse.               *)
(* One event summarises a full book of 4096 nodes (`full`): its size before *)
(* and after an input with new nodes, that none of them was added and that *)
(* `addresses` is 0 (the test records it as "addresses"); its              *)
(* 4096 entries are not parsed here (the recursion would be 4096 deep).    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds facade_state.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLE x

F == INSTANCE FacadeStateOps WITH NB <- 32, IP4 <- 4, IP6 <- 16, PORT <- 2, CLEN <- 4, CNT <- 2, SEQ <- 8,
                                  BOOKMAX <- 4096, ADDRSMAX <- 8
\* only CS!Parse is used here, which reads none of the table bounds
CS == INSTANCE CoreStateOps WITH CT <- 32, KR <- 256, EK <- 256, LAZY <- FALSE, LAXTAIL <- FALSE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_state.ndjson")

\* a recorded book: [{alg, bytes, addrs}] -> the model's <<node, addresses>>
Book(b) == [k \in 1..Len(b) |-> <<[alg |-> b[k].alg, bytes |-> b[k].bytes], b[k].addrs>>]
Parsed(r) == IF r.ok THEN [ok |-> TRUE, ver |-> r.ver, core |-> r.core, book |-> Book(r.book), seq |-> r.seq]
             ELSE F!PFail
\* a live state as recorded: the export parses, its core is read by the core, and it holds the book and number
LiveOK(l) == LET p == F!Parse(l.export)
             IN /\ p.ok /\ p.ver = 2 /\ CS!Parse(p.core).ok
                /\ F!Range(p.book) = F!Range(Book(l.book)) /\ Len(p.book) = Len(l.book)
                /\ p.seq = l.seq

EvOK(ev) ==
    CASE ev.op = "restore" ->
           LET p == F!Parse(ev.bs)
               bb == Book(ev.before.book)
           IN /\ Parsed(ev.parse) = p
              /\ ev.ok = (p.ok /\ CS!Parse(p.core).ok)
              /\ LiveOK(ev.before) /\ LiveOK(ev.after)
              /\ ~ev.ok => ev.after = ev.before
              /\ ev.ok => /\ F!Range(Book(ev.after.book)) = F!Range(F!Merge(bb, p.book))
                          /\ ev.after.seq = (IF p.ver = 2 THEN F!MaxBE(ev.before.seq, p.seq) ELSE ev.before.seq)
                          /\ ev.res[4] = F!MergeN(bb, p.book, 0).n
      \* a full book refuses every new node, and the restore counts none of them (fix F14)
      [] ev.op = "full" -> /\ ev.before = 4096 /\ ev.after = 4096 /\ ev.ok /\ ev.added = 0 /\ ev.addresses = 0
      [] OTHER -> FALSE

Init == x = 0
Next == UNCHANGED x
TraceSpec == Init /\ [][Next]_x

AllOK == /\ \A k \in DOMAIN Trace : Trace[k].t = "state" /\ EvOK(Trace[k])
         \* both versions accepted, and a refusal by the core after a good framing, were seen
         /\ \E k \in DOMAIN Trace : Trace[k].op = "restore" /\ Trace[k].ok /\ Trace[k].parse.ver = 1
         /\ \E k \in DOMAIN Trace : Trace[k].op = "restore" /\ Trace[k].ok /\ Trace[k].parse.ver = 2
         /\ \E k \in DOMAIN Trace : Trace[k].op = "restore" /\ Trace[k].parse.ok /\ ~Trace[k].ok
=============================================================================
