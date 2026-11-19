------------------------- MODULE TraceFacadeStreamDoc -------------------------
(***************************************************************************)
(* The documented behaviour of the stream and datagram handles against the *)
(* fixed scenarios of tests/trace_facade_stream.rs that reach the findings  *)
(* of FacadeStreamOps.tla (facade_stream_doc.ndjson): a write and a finish  *)
(* after reset, a RecvStream dropped with TRACKED discarded streams listed  *)
(* (seen by the "held" probe), and datagrams held when the connection      *)
(* ends. The stop-sending after a drop is not visible to a call and stays  *)
(* FacadeStream_stale's. It fails on the code as written until the         *)
(* findings are fixed. Its own module only because a trace check reads     *)
(* <Spec>.cfg.                                                             *)
(***************************************************************************)
EXTENDS TraceFacadeStream
=============================================================================
