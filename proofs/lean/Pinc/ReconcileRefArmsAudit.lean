import Pinc.ReconcileRefBridge

/-!
# Reconcile refinement of the part arms: summary and audit

PROVED (unbounded), on the bytes of an honest part (`WP.enc`, the encoding `putHead` and the payload writers produce),
for a sorted receiver index whose items fit the item limit (`HCtx`):

* `procPart_eq`, `procPart_head`: `procPart` is `readHead` then `tailPart`, and the head of an encoded part is read back;
* FP arm: `tailPart_fp` with `tailPart_fp_equal`, `fpDiffer_full`, `fpDiffer_ids`, `fpDiffer_split` (the split writes
  exactly `splitIvs`, at a fan 2 to 16, via `splitFit_spec` and `splitParts_spec`);
* IDS arm of the responder: `tailPart_ids`, `idsArm_leaf` (bitmap by `rposition`, extras by id), `idsArm_split`;
* FULL arm of the responder: `tailPart_full`, `fullArm_leaf` (bitmap of held items, extras), `fullArm_split` (with the
  drain of the unread list);
* FULL and COLD arm of the initiator: `tailPart_initFull`, `initFullArm_spec` (the report arenas grow by the peer's
  items we lack and ours it lacks, given room in the report limit);
* REPLY arm of the initiator: `tailPart_reply`, `replyArm_spec` (clear bits to `there`, extras to `here`, the padding
  check accepts a bitmap with clear padding);
* CHECK and MISS arms: `tailPart_check`, `tailPart_miss`;
* the lazy merge is the textbook merge: `mergeGo_spec`, `merge_spec`, `mergeEv_spec`, `drain_stream`;
* the bridges to the abstract part system: `ids_reply_bridge` (the machine's bitmap and extras are `idsThere` and
  `idsHere`), `exact_reply_bridge` (the exact reply is `exactThere` and `exactHere`), `rpos_map_beBytes`.

NOT PROVED here (covered by TLC and trace validation only): `answerLoop` with its rollback, `turn` and the frames, the
handlers, the driver; that the parts a message carries are the honest parts of the abstract system (the invariant of the
whole session); the arms for dishonest input (their errors are the wire theorems and the replay).
-/

namespace Pinc.Reconcile

#audit_axioms Pinc.Reconcile.procPart_eq
#audit_axioms Pinc.Reconcile.procPart_head
#audit_axioms Pinc.Reconcile.tailPart_fp
#audit_axioms Pinc.Reconcile.tailPart_fp_equal
#audit_axioms Pinc.Reconcile.fpDiffer_full
#audit_axioms Pinc.Reconcile.fpDiffer_ids
#audit_axioms Pinc.Reconcile.fpDiffer_split
#audit_axioms Pinc.Reconcile.tailPart_ids
#audit_axioms Pinc.Reconcile.idsArm_leaf
#audit_axioms Pinc.Reconcile.idsArm_split
#audit_axioms Pinc.Reconcile.tailPart_full
#audit_axioms Pinc.Reconcile.fullArm_leaf
#audit_axioms Pinc.Reconcile.fullArm_split
#audit_axioms Pinc.Reconcile.tailPart_initFull
#audit_axioms Pinc.Reconcile.initFullArm_spec
#audit_axioms Pinc.Reconcile.tailPart_reply
#audit_axioms Pinc.Reconcile.replyArm_spec
#audit_axioms Pinc.Reconcile.tailPart_check
#audit_axioms Pinc.Reconcile.tailPart_miss
#audit_axioms Pinc.Reconcile.mergeGo_spec
#audit_axioms Pinc.Reconcile.merge_spec
#audit_axioms Pinc.Reconcile.mergeEv_spec
#audit_axioms Pinc.Reconcile.ids_reply_bridge
#audit_axioms Pinc.Reconcile.exact_reply_bridge

end Pinc.Reconcile
