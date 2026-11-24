-- `#print axioms` for the headline theorems (run by scripts/check-proofs.sh).
import LeanSync
import LeanCrdt
open LeanSync
#print axioms decodeState_encodeState
#print axioms encodeState_of_decodeState
#print axioms wireOk_of_decodeState
#print axioms encodeState_inj
#print axioms decodeMessage_encodeMessage
#print axioms encodeMessage_of_decodeMessage
#print axioms sent_state_acked
#print axioms save_before_send
#print axioms persist_tag_unique
#print axioms persist_one_in_flight
#print axioms effects_executable
#print axioms step_inv
#print axioms step_settles
#print axioms step_plans_blobs
#print axioms step_no_owed_have
#print axioms step_detects_rollback
#print axioms rollback_no_state
#print axioms rollback_rejects_local
#print axioms process_output_decodes
#print axioms decodeEffects_encodeEffects
#print axioms step_effects_ok
#print axioms persistFailed_no_retry_in_step
#print axioms held_no_persist
#print axioms persistFailed_no_persist_until_retry
#print axioms retrySave_releases
#print axioms retrySave_persists
#print axioms retrySave_not_held
#print axioms blobStoreFailed_parks
#print axioms step_received_state
#print axioms step_putMany
#print axioms step_current_grows
#print axioms LeanCrdt.State.merge_comm
#print axioms LeanCrdt.State.putMany_eq_putSeq
