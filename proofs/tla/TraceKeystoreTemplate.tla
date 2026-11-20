------------------------- MODULE TraceKeystoreTemplate -------------------------
(***************************************************************************)
(* Trace validation of the TPM store's object templates (pinc-keystore     *)
(* tpm/template.rs) against KeystoreTemplate.tla.                          *)
(*                                                                         *)
(* The Rust test tests/trace_keystore_template.rs runs the real TpmStore   *)
(* against a software TPM through a recording transport: it opens stores   *)
(* under three pairs of auth values, generates P-256 keys and seals data,  *)
(* and from every TPM2_CreatePrimary (command code 0x131) and TPM2_Create  *)
(* (0x153) the client sent it cuts the inPublic parameter out of the       *)
(* command bytes. One event per such command: the kind of object (from    *)
(* the command and the store call it ran in), the command code, the store *)
(* call, the TPM2B_PUBLIC bytes and the protocol library's verdict when it *)
(* unmarshals them. Each event must be exactly Template(kind) of the model *)
(* and satisfy every property of the model on the bytes themselves.        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* keystore_template.ndjson.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

KT == INSTANCE KeystoreTemplate WITH SEALATTRS <- 82, x <- "storage"

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/keystore_template.ndjson")

\* TPM_CC_CreatePrimary and TPM_CC_Create.
CcCreatePrimary == 305
CcCreate == 339

Init == c = [t |-> "root"]

\* One recorded command: the code belongs to the kind (the primary by CreatePrimary, a key and a sealed object by
\* Create under it), the bytes are the model's template, the library read them whole, and every property holds of
\* the bytes as recorded.
EvOK(ev) ==
    /\ ev.t = "ktpl"
    /\ ev.kind \in KT!Kinds
    /\ ev.cc = (IF ev.kind = "storage" THEN CcCreatePrimary ELSE CcCreate)
    /\ ev.op = (CASE ev.kind = "storage" -> "open" [] ev.kind = "sign" -> "generate" [] ev.kind = "seal" -> "seal")
    /\ ev.b = KT!Template(ev.kind)
    /\ ev.lib = 1
    /\ KT!WellFormedB(ev.b)
    /\ KT!TypeOKB(ev.kind, ev.b)
    /\ KT!FixedB(ev.b)
    /\ KT!NoPolicyB(ev.b)
    /\ KT!RoleB(ev.kind, ev.b)
    /\ Len(ev.b) = KT!SizeOf[ev.kind]

(* Every event is an independent check, so the events are the states of one machine: the root state has one successor
   per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded template is the model's, and the trace is not empty and has every kind
EventsOK == /\ c.t = "root" => /\ Len(Trace) > 0
                               /\ \A k \in KT!Kinds : \E j \in 1..Len(Trace) : Trace[j].kind = k
            /\ c.t = "event" => EvOK(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
