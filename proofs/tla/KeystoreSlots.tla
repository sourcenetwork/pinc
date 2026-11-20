---------------------------- MODULE KeystoreSlots ----------------------------
(***************************************************************************)
(* The object slots of a TPM under a TPM key store: pinc-keystore          *)
(* tpm/store.rs after the slot fix (keystore-slots design): `room`,        *)
(* `reclaim`, `discard`, `adopt`, `least_used`, `unload`, `handle_of`,     *)
(* `generate`, `load_persistent`, `persist`, `sign`, `seal`, `unseal` and   *)
(* `Drop`. KeystoreTpm.tla checks the bytes and the programs of a TPM with *)
(* room; this model checks what the store does when the TPM has none.      *)
(*                                                                         *)
(* The TPM holds at most Slots objects, at handle numbers of 1..NP that    *)
(* it gives out again once freed (any free number). The primary is at 1    *)
(* and Foreign objects of other users of the TPM at 2..Foreign+1; they     *)
(* stay. A command that needs a slot (a Create's scratch object, a Load,   *)
(* a persistent key read or used) is refused with TPM_RC_OBJECT_MEMORY     *)
(* when the TPM is full; the rest (Sign or ReadPublic on a loaded key,      *)
(* EvictControl of a loaded key, Unseal of a loaded object) take no new    *)
(* slot. A flush is answered ok, refused with the object kept              *)
(* (FlushRefused) or answered with an error after the TPM freed the object *)
(* (FlushLost: the answer was lost). The stale list is a set: the store    *)
(* holds at most MAX_STALE (8) numbers and NP is below that here.          *)
(*                                                                         *)
(* A key's place is NONE (not in the store), UN (unloaded to make room,    *)
(* loaded again from its blob on its next use), PERS (persistent) or the   *)
(* handle it is loaded at. lru is the order of the keys' last uses (the    *)
(* store's use counter): `least_used` takes the first loaded key of it     *)
(* that the command does not keep. A room loop step is one send of the     *)
(* command: on a refusal it retries the stale flushes once (only when the  *)
(* list was not empty when the loop began), then unloads the least used   *)
(* loaded key and sends again. A flush the TPM refuses frees no slot: the  *)
(* next least used key is tried (pc "unload"); with none left the loop     *)
(* fails with the refusal ("refused") when a flush was refused, with       *)
(* TpmFull otherwise. Loading an unloaded key again retries the stale      *)
(* flushes first. `persist` records the key persistent once EvictControl  *)
(* ran; a refused or lost flush of the transient copy is remembered on the *)
(* stale list (it has room here) and persist answers Ok.                   *)
(* `tpm_handle` (variant B: None for an unloaded key) sends nothing and is *)
(* not modelled.                                                           *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - Agree: a key the store records as loaded at h is the TPM's object at *)
(*    h, and the primary stays at its handle until the store is dropped;   *)
(*  - StaleNotLive: no number on the stale list is the primary, a foreign  *)
(*    object or a loaded key (`adopt`: a number the TPM gave out again is  *)
(*    not flushed by a later retry);                                       *)
(*  - LeakedOnStale: every object a refused flush left is on the stale     *)
(*    list, so `reclaim` and `Drop` try it again;                          *)
(*  - NoFalseFull: TpmFull only when the TPM is full and no loaded key     *)
(*    other than the one the command keeps is left;                        *)
(*  - NoFalseRefusal: a refused unload is the error only when no loaded    *)
(*    key other than the one the command keeps is left;                    *)
(*  - PersistTruthful: persist answers Ok exactly when the key is          *)
(*    persistent;                                                          *)
(*  - Usable: with Foreign + 2 <= Slots no operation ends in TpmFull       *)
(*    unless a refused flush left an object in the TPM;                    *)
(*  - Bounded: a room loop sends its command at most the number of keys    *)
(*    loaded when it began plus two times;                                 *)
(*  - NoLeakOnDrop: after Drop the TPM holds only foreign objects and the  *)
(*    objects whose flush was refused.                                     *)
(* Not modelled: foreign objects that come and go (a number on the stale   *)
(* list could then name another user's object).                            *)
(* Configs: KeystoreSlots.cfg, KeystoreSlots_persist.cfg; witnesses        *)
(* KeystoreSlots_w_unload.cfg (NeverUnloaded: the room loop unloads a key) *)
(* and KeystoreSlots_w_full.cfg (NeverFull: TpmFull is reached when other  *)
(* users hold the room).                                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Slots, NK, Foreign, NP, FlushRefused, FlushLost, PERSIST

ASSUME /\ Slots \in 2..4 /\ NK \in 1..3 /\ Foreign \in 0..(Slots - 1) /\ NP \in Slots..6
       /\ FlushRefused \in BOOLEAN /\ FlushLost \in BOOLEAN /\ PERSIST \in BOOLEAN

Keys == 1..NK
Pool == 1..NP
\* the TPM's object at a handle: a key's number, or one of these
FREE == 0
PRIMARY == -1
FOREIGN == -2
SEALED == -3
\* a key's place: a handle, or one of these
NONE == 0
UN == -1
PERS == -2
PH == 1
Outs == {"ok"} \cup (IF FlushRefused THEN {"kept"} ELSE {}) \cup (IF FlushLost THEN {"lost"} ELSE {})

VARIABLES tpm, place, lru, stale, leaked, pc, op, rm, res, dropped, unloaded
vars == <<tpm, place, lru, stale, leaked, pc, op, rm, res, dropped, unloaded>>

Objects == {h \in Pool : tpm[h] # FREE}
HasRoom == Cardinality(Objects) < Slots
Loaded == {k \in Keys : place[k] > 0}
Pos(k) == CHOOSE i \in 1..Len(lru) : lru[i] = k
\* touch: the key becomes the most recently used
Touch(k) == Append(SelectSeq(lru, LAMBDA x : x # k), k)

NoRoom == [cmd |-> "none", obj |-> 0, keep |-> 0, rec |-> TRUE, sends |-> 0, base |-> 0, then |-> "idle", ref |-> FALSE]
\* a room loop for cmd (its object obj for a Load), keeping key keep, begun with the stale list st
Room(cmd, obj, keep, then, st) ==
    [cmd |-> cmd, obj |-> obj, keep |-> keep, rec |-> st = {}, sends |-> 0, base |-> Cardinality(Loaded), then |-> then,
     ref |-> FALSE]

Init == /\ tpm = [h \in Pool |-> IF h = PH THEN PRIMARY ELSE IF h <= Foreign + 1 THEN FOREIGN ELSE FREE]
        /\ place = [k \in Keys |-> NONE]
        /\ lru = <<>>
        /\ stale = {}
        /\ leaked = {}
        /\ pc = "idle"
        /\ op = [kind |-> "none", key |-> 0, h |-> 0]
        /\ rm = NoRoom
        /\ res = "none"
        /\ dropped = FALSE
        /\ unloaded = FALSE

(* reclaim: every number on the stale list flushed once; a refused flush (or one of a number already free) keeps it *)
Reclaim == \E f \in [stale -> Outs] :
    LET gone == {h \in stale : tpm[h] # FREE /\ f[h] # "kept"}
    IN /\ tpm' = [h \in Pool |-> IF h \in gone THEN FREE ELSE tpm[h]]
       /\ stale' = {h \in stale : tpm[h] = FREE \/ f[h] # "ok"}
       /\ leaked' = leaked \ gone

Idle == pc = "idle" /\ ~dropped
Begin(kind, k, h) == op' = [kind |-> kind, key |-> k, h |-> h] /\ res' = "busy"

Generate(k) == /\ Idle /\ place[k] = NONE
               /\ Reclaim
               /\ Begin("gen", k, 0)
               /\ rm' = Room("create", 0, 0, "gen_load", stale')
               /\ pc' = "room"
               /\ UNCHANGED <<place, lru, dropped, unloaded>>
GenLoad == /\ pc = "gen_load"
           /\ rm' = Room("load", op.key, 0, "gen_reg", stale)
           /\ pc' = "room"
           /\ UNCHANGED <<tpm, place, lru, stale, leaked, op, res, dropped, unloaded>>
\* adopt, then register (ReadPublic of the loaded key takes no slot)
GenReg == /\ pc = "gen_reg"
          /\ stale' = stale \ {op.h}
          /\ place' = [place EXCEPT ![op.key] = op.h]
          /\ lru' = Touch(op.key)
          /\ pc' = "idle" /\ res' = "ok"
          /\ UNCHANGED <<tpm, leaked, op, rm, dropped, unloaded>>

LoadPersistent(k) == /\ PERSIST /\ Idle /\ place[k] = NONE
                     /\ Begin("lp", k, 0)
                     /\ rm' = Room("slot", 0, 0, "lp_reg", stale)
                     /\ pc' = "room"
                     /\ UNCHANGED <<tpm, place, lru, stale, leaked, dropped, unloaded>>
LpReg == /\ pc = "lp_reg"
         /\ place' = [place EXCEPT ![op.key] = PERS]
         /\ lru' = Touch(op.key)
         /\ pc' = "idle" /\ res' = "ok"
         /\ UNCHANGED <<tpm, stale, leaked, op, rm, dropped, unloaded>>

\* handle_of (an unloaded key is loaded again, kept, after the stale flushes are retried), then Sign (a persistent
\* key takes a slot while it signs)
Sign(k) == /\ Idle /\ place[k] # NONE
           /\ lru' = Touch(k)
           /\ Begin("sign", k, 0)
           /\ CASE place[k] = UN -> Reclaim /\ rm' = Room("load", k, k, "adopt", stale') /\ pc' = "room"
                [] place[k] = PERS -> rm' = Room("slot", 0, k, "done", stale) /\ pc' = "room"
                                     /\ UNCHANGED <<tpm, stale, leaked>>
                [] OTHER -> rm' = rm /\ pc' = "done" /\ UNCHANGED <<tpm, stale, leaked>>
           /\ UNCHANGED <<place, dropped, unloaded>>
\* handle_of after its Load: adopt, record the handle
Adopt == /\ pc = "adopt"
         /\ stale' = stale \ {op.h}
         /\ place' = [place EXCEPT ![op.key] = op.h]
         /\ pc' = IF op.kind = "persist" THEN "evict" ELSE "done"
         /\ UNCHANGED <<tpm, lru, leaked, op, rm, res, dropped, unloaded>>
Done == /\ pc = "done" /\ pc' = "idle" /\ res' = "ok"
        /\ UNCHANGED <<tpm, place, lru, stale, leaked, op, rm, dropped, unloaded>>

Seal == /\ Idle
        /\ Begin("seal", 0, 0)
        /\ rm' = Room("create", 0, 0, "done", stale)
        /\ pc' = "room"
        /\ UNCHANGED <<tpm, place, lru, stale, leaked, dropped, unloaded>>

Unseal == /\ Idle
          /\ Reclaim
          /\ Begin("unseal", 0, 0)
          /\ rm' = Room("load", SEALED, 0, "unseal_flush", stale')
          /\ pc' = "room"
          /\ UNCHANGED <<place, lru, dropped, unloaded>>
\* adopt, Unseal, then discard the sealed object
UnsealFlush == /\ pc = "unseal_flush"
               /\ \E o \in Outs :
                    /\ tpm' = [tpm EXCEPT ![op.h] = IF o = "kept" THEN @ ELSE FREE]
                    /\ stale' = IF o = "ok" THEN stale \ {op.h} ELSE stale \cup {op.h}
                    /\ leaked' = IF o = "kept" THEN leaked \cup {op.h} ELSE leaked
                    /\ res' = IF o = "ok" THEN "ok" ELSE "err"
               /\ pc' = "idle"
               /\ UNCHANGED <<place, lru, op, rm, dropped, unloaded>>

Persist(k) == /\ PERSIST /\ Idle /\ place[k] \notin {NONE, PERS}
              /\ lru' = Touch(k)
              /\ Begin("persist", k, IF place[k] > 0 THEN place[k] ELSE 0)
              /\ IF place[k] = UN THEN Reclaim /\ rm' = Room("load", k, k, "adopt", stale') /\ pc' = "room"
                 ELSE rm' = rm /\ pc' = "evict" /\ UNCHANGED <<tpm, stale, leaked>>
              /\ UNCHANGED <<place, dropped, unloaded>>
\* EvictControl, then the key is persistent; a plain flush of the transient object, whose refusal (or lost answer)
\* is remembered on the stale list (discard), and persist answers Ok
Evict == /\ pc = "evict"
         /\ \E o \in Outs :
              /\ tpm' = [tpm EXCEPT ![op.h] = IF o = "kept" THEN @ ELSE FREE]
              /\ stale' = IF o = "ok" THEN stale ELSE stale \cup {op.h}
              /\ leaked' = IF o = "kept" THEN leaked \cup {op.h} ELSE leaked
         /\ place' = [place EXCEPT ![op.key] = PERS]
         /\ res' = "ok"
         /\ pc' = "idle"
         /\ UNCHANGED <<lru, op, rm, dropped, unloaded>>

(* one send of the room loop's command *)
RoomSend ==
    /\ pc = "room"
    /\ IF HasRoom
       THEN /\ IF rm.cmd = "load"
               THEN \E h \in Pool : tpm[h] = FREE /\ tpm' = [tpm EXCEPT ![h] = rm.obj] /\ op' = [op EXCEPT !.h = h]
               ELSE UNCHANGED <<tpm, op>>
            /\ pc' = rm.then /\ rm' = NoRoom
            /\ UNCHANGED <<place, lru, stale, leaked, res, dropped, unloaded>>
       ELSE IF ~rm.rec
       THEN /\ Reclaim
            /\ rm' = [rm EXCEPT !.rec = TRUE, !.sends = @ + 1]
            /\ UNCHANGED <<place, lru, pc, op, res, dropped, unloaded>>
       ELSE /\ pc' = "unload"
            /\ rm' = [rm EXCEPT !.sends = @ + 1, !.ref = FALSE]
            /\ UNCHANGED <<tpm, place, lru, stale, leaked, op, res, dropped, unloaded>>

(* the unload of the room loop: the least used loaded key the command does not keep; a refused flush (or a lost
   answer) frees no slot as far as the store knows, so the next one is tried; with none left the loop ends with the
   refusal, or TpmFull when nothing was refused *)
RoomUnload ==
    /\ pc = "unload"
    /\ LET cand == Loaded \ {rm.keep}
       IN IF cand = {}
          THEN /\ pc' = "idle" /\ res' = IF rm.ref THEN "refused" ELSE "full"
               /\ UNCHANGED <<tpm, place, lru, stale, leaked, op, rm, dropped, unloaded>>
          ELSE LET k == CHOOSE x \in cand : \A y \in cand : Pos(x) <= Pos(y)
                   h == place[k]
               IN /\ \E o \in Outs :
                       /\ tpm' = [tpm EXCEPT ![h] = IF o = "kept" THEN @ ELSE FREE]
                       /\ stale' = IF o = "ok" THEN stale ELSE stale \cup {h}
                       /\ leaked' = IF o = "kept" THEN leaked \cup {h} ELSE leaked
                       /\ pc' = IF o = "ok" THEN "room" ELSE "unload"
                       /\ rm' = IF o = "ok" THEN rm ELSE [rm EXCEPT !.ref = TRUE]
                  /\ place' = [place EXCEPT ![k] = UN]
                  /\ unloaded' = TRUE
                  /\ UNCHANGED <<lru, op, res, dropped>>

(* Drop: flush every loaded key, the primary and the stale list, each answered on its own *)
Drop == /\ Idle
        /\ \E f \in [Pool -> Outs] :
             LET try == {h \in {place[k] : k \in Loaded} \cup {PH} \cup stale : tpm[h] # FREE}
                 gone == {h \in try : f[h] # "kept"}
             IN /\ tpm' = [h \in Pool |-> IF h \in gone THEN FREE ELSE tpm[h]]
                /\ leaked' = try \ gone
        /\ dropped' = TRUE
        /\ UNCHANGED <<place, lru, stale, pc, op, rm, res, unloaded>>

Next == \/ \E k \in Keys : Generate(k) \/ LoadPersistent(k) \/ Sign(k) \/ Persist(k)
        \/ Seal \/ Unseal
        \/ RoomSend \/ RoomUnload \/ GenLoad \/ GenReg \/ LpReg \/ Adopt \/ Done \/ UnsealFlush \/ Evict
        \/ Drop
Spec == Init /\ [][Next]_vars

TypeOK == /\ tpm \in [Pool -> {FREE, PRIMARY, FOREIGN, SEALED} \cup Keys]
          /\ place \in [Keys -> {NONE, UN, PERS} \cup Pool]
          /\ stale \subseteq Pool /\ leaked \subseteq Pool
          /\ res \in {"none", "busy", "ok", "err", "full", "refused"}

\* after Drop the store is gone: its records name nothing (NoLeakOnDrop covers that state)
Agree == ~dropped => /\ \A k \in Keys : place[k] > 0 => tpm[place[k]] = k
                     /\ tpm[PH] = PRIMARY
StaleNotLive == \A h \in stale : h # PH /\ tpm[h] # FOREIGN /\ \A k \in Keys : place[k] # h
LeakedOnStale == ~dropped => leaked \subseteq stale
NoFalseFull == ~dropped /\ pc = "idle" /\ res = "full" => ~HasRoom /\ Loaded \subseteq {rm.keep}
NoFalseRefusal == ~dropped /\ pc = "idle" /\ res = "refused" => Loaded \subseteq {rm.keep}
PersistTruthful == pc = "idle" /\ op.kind = "persist" /\ res # "busy" => (res = "ok" <=> place[op.key] = PERS)
Usable == ~dropped /\ pc = "idle" /\ res = "full" /\ Foreign + 2 <= Slots => leaked # {}
Bounded == pc \in {"room", "unload"} => rm.sends <= rm.base + 2 /\ (pc = "room" => rm.sends <= rm.base + 1)
NoLeakOnDrop == dropped => \A h \in Pool : tpm[h] = FOREIGN \/ tpm[h] = FREE \/ h \in leaked

Inv == TypeOK /\ Agree /\ StaleNotLive /\ LeakedOnStale /\ NoFalseFull /\ NoFalseRefusal /\ PersistTruthful /\ Usable
       /\ Bounded /\ NoLeakOnDrop

\* witnesses
NeverUnloaded == ~unloaded
NeverFull == res # "full"
=============================================================================
