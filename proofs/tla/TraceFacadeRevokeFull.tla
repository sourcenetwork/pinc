------------------------ MODULE TraceFacadeRevokeFull ------------------------
(***************************************************************************)
(* TraceFacadeRevoke on the run that fills the revoked set first          *)
(* (facade_revoke_full.ndjson): its own config sets MAXREV 1, the one     *)
(* place left for the traced peers after 4095 other ids were revoked.     *)
(***************************************************************************)
EXTENDS TraceFacadeRevoke
=============================================================================
