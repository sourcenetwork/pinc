---------------------------- MODULE TraceMachines ----------------------------
(***************************************************************************)
(* Trace validation of the pool of handshake machine boxes,                *)
(* pinc-transport conn/handshake.rs (Machines with `alloc`, 64 cells), on  *)
(* real dialing connections that share one pool.                           *)
(*                                                                         *)
(* The Rust test tests/trace_machines.rs opens client connections whose    *)
(* resources share one Machines (more at once than the pool has cells) and *)
(* drops them in seeded orders, so boxes are taken from the pool,          *)
(* allocated when it is empty, returned, and freed when it is full. After  *)
(* each call it records the pool's cells and the box each connection       *)
(* holds, through Machines::trace_cells and Connection::trace_machine      *)
(* (cargo feature `trace`); boxes are named by small ids the test gives    *)
(* their addresses on first sight (0 for an empty cell or no machine, -1   *)
(* for a connection not open). Every call must be the step of Machines.tla:*)
(* an open takes the first idle box, or a box neither idle nor held when   *)
(* the pool is empty; a drop puts the box in the first empty cell, or      *)
(* leaves it in no cell (freed) when the pool is full.                     *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds machines.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLES i, cells, conns
vars == <<i, cells, conns>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/machines.ndjson")
Ev0 == Trace[i]

Ids(s) == {s[k] : k \in DOMAIN s} \ {0, -1}
FirstFull(s) == IF \E k \in DOMAIN s : s[k] # 0
                THEN CHOOSE k \in DOMAIN s : s[k] # 0 /\ \A m \in DOMAIN s : m < k => s[m] = 0
                ELSE 0
FirstEmpty(s) == IF \E k \in DOMAIN s : s[k] = 0
                 THEN CHOOSE k \in DOMAIN s : s[k] = 0 /\ \A m \in DOMAIN s : m < k => s[m] # 0
                 ELSE 0

InitEv == /\ Ev0.op = "init"
          /\ cells' = Ev0.v.cells /\ conns' = Ev0.v.conns
          /\ \A k \in DOMAIN cells' : cells'[k] = 0
          /\ \A k \in DOMAIN conns' : conns'[k] = -1
OpenEv == LET n == Ev0.conn
              b == Ev0.v.conns[n]
              j == FirstFull(cells)
          IN /\ Ev0.op = "open" /\ conns[n] = -1 /\ b > 0
             /\ conns' = [conns EXCEPT ![n] = b]
             /\ IF j > 0 THEN b = cells[j] /\ cells' = [cells EXCEPT ![j] = 0]
                ELSE b \notin Ids(cells) \cup Ids(conns) /\ cells' = cells
DropEv == LET n == Ev0.conn
              b == conns[n]
              j == FirstEmpty(cells)
          IN /\ Ev0.op = "drop" /\ b >= 0
             /\ conns' = [conns EXCEPT ![n] = -1]
             /\ cells' = IF b > 0 /\ j > 0 THEN [cells EXCEPT ![j] = b] ELSE cells

Init == i = 1 /\ cells = <<>> /\ conns = <<>>
Step == /\ i <= Len(Trace) /\ Ev0.t = "machines"
        /\ (InitEv \/ OpenEv \/ DropEv)
        /\ cells' = Ev0.v.cells /\ conns' = Ev0.v.conns
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* a box is in one place at most: one cell or one connection
Inv == /\ \A j, k \in DOMAIN cells : (j # k /\ cells[j] # 0) => cells[j] # cells[k]
       /\ \A j, k \in DOMAIN conns : (j # k /\ conns[j] > 0) => conns[j] # conns[k]
       /\ Ids(cells) \cap Ids(conns) = {}
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
