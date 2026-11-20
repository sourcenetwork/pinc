------------------------------- MODULE TraceEnd -------------------------------
(***************************************************************************)
(* The end check of a trace replay. TLC ending with no error proves the    *)
(* recorded trace is a behaviour of a spec only if some behaviour of the   *)
(* replay consumed its last line: a replay that cannot match a line can    *)
(* still end with no error when a step that consumes no line (a hidden     *)
(* step of the code) stays enabled, when the config does not check         *)
(* deadlock, or when the trace has no line at all.                         *)
(*                                                                         *)
(* Every trace spec extends this module and defines                        *)
(*   ReplayAtEnd == ReplaySeen(<every line of the trace is consumed>)      *)
(*   ReplayEnded == ReplayRead(Len(Trace))                                 *)
(* and its config names INVARIANT ReplayAtEnd and POSTCONDITION            *)
(* ReplayEnded. ReplayAtEnd is TRUE in every state, so it constrains       *)
(* nothing; a state where every line is consumed records that in a TLC     *)
(* register. ReplayEnded, evaluated once after the search, holds only when *)
(* the trace has a line and some reached state recorded the end; otherwise *)
(* TLC reports the postcondition false and exits with an error. A spec     *)
(* that checks every line in one state (a pure function per line) names    *)
(* that state, or TRUE when its only state checks them all. A spec that    *)
(* replays independent runs of the trace marks the end of each run with    *)
(* ReplayMark and asks for all of them with ReplayReadAll.                 *)
(*                                                                         *)
(* TLC keeps one list of registers per worker and reads the first          *)
(* worker's after the search, so a trace check runs with one worker.       *)
(***************************************************************************)
EXTENDS Integers, TLC

LOCAL Reg == 731

\* the marks of the ends reached; before the search, on every worker, none
ASSUME TLCSet(Reg, {})

\* TRUE; when p holds, adds the mark m
ReplayMark(p, m) == p => TLCSet(Reg, TLCGet(Reg) \cup {m})
ReplaySeen(atEnd) == ReplayMark(atEnd, "end")

\* after the search: the trace has a line and every mark of marks was added
ReplayReadAll(lines, marks) == lines > 0 /\ marks \subseteq TLCGet(Reg)
ReplayRead(lines) == ReplayReadAll(lines, {"end"})
=============================================================================
