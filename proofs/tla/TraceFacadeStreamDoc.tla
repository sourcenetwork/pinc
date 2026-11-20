------------------------- MODULE TraceFacadeStreamDoc -------------------------
(***************************************************************************)
(* The documented behaviour of the stream and datagram handles against the *)
(* fixed scenarios of tests/trace_facade_stream.rs that reached the        *)
(* findings of FacadeStreamOps.tla (facade_stream_doc.ndjson): a write and *)
(* a finish after reset answer the reset (F2); a RecvStream dropped after  *)
(* 128 other dropped streams of its session (the old TRACKED bound; the    *)
(* list is now bounded by the 200 stream slots, F1) holds nothing, its     *)
(* "held" probe after the drop is 0; datagrams held when the connection    *)
(* ends go with it (F4, the doc now says so). The stop-sending after a     *)
(* drop is not visible to a call and stays FacadeStream_stale's (F6,       *)
(* open), so with the fixes in this trace passes on the code. Its own      *)
(* module only because a trace check reads <Spec>.cfg.                     *)
(***************************************************************************)
EXTENDS TraceFacadeStream
=============================================================================
