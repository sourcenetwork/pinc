# The model checks of the key stores and the handshake machines added with the trace tests of the PR line, sourced by scripts/proofs.sh after
# tlc.sh (which holds the models before them): one line per TLC config under proofs/tla.
par run_tlc outbox Outbox Outbox
par run_tlc outbox_torn Outbox Outbox_torn
par witness_tlc outbox_full Outbox Outbox_full NotAllQueued
par run_tlc secids SecIds SecIds
par run_tlc softprekeys SoftPrekeys SoftPrekeys
par witness_tlc softprekeys_wrap SoftPrekeys SoftPrekeys_wrap RotatedOutRefused
par witness_tlc softprekeys_rot SoftPrekeys SoftPrekeys_rot NeverRotated
par run_tlc keystore_template KeystoreTemplate KeystoreTemplate
par witness_tlc keystore_template_nofixed KeystoreTemplate KeystoreTemplate_nofixed Fixed
par run_tlc keystore_refresh KeystoreRefresh KeystoreRefresh
par witness_tlc keystore_refresh_mix KeystoreRefresh KeystoreRefresh_mix NeverReseeded
par run_tlc keystore_slots KeystoreSlots KeystoreSlots
par run_tlc keystore_slots_persist KeystoreSlots KeystoreSlots_persist
par witness_tlc keystore_slots_w_unload KeystoreSlots KeystoreSlots_w_unload NeverUnloaded
par witness_tlc keystore_slots_w_full KeystoreSlots KeystoreSlots_w_full NeverFull
