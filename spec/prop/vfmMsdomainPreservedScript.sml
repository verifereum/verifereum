(*
 * Exact msdomain preservation through handle_step.
 *
 * `handle_step` does not modify `msdomain`: every primitive it invokes
 * (reraise, context getters, pop/push/unuse/set_rollback, push_stack,
 * push_logs, update_gas_refund, inc_pc, write_memory,
 * pop_and_incorporate_context) leaves `s.msdomain` unchanged. This is
 * a strictly stronger property than `msdomain_compatible` (the
 * monotonicity property built into `same_frame_rel`), and is what
 * downstream proofs use to equate `s'.msdomain = s1.msdomain` when
 * handle_step is applied after a push.
 *
 * All 18 lemmas are marked `[simp]` and consumed compositionally by
 * `SND_handle_step_msdomain`.
 *)
Theory vfmMsdomainPreserved
Ancestors
  combin list pair
  vfmState vfmContext vfmExecution vfmDomainSeparation
Libs
  BasicProvers

(* handle_step does not modify msdomain. All its primitives
   (consume_gas, set_return_data, pop/push context, unuse_gas,
   push_logs, update_gas_refund, set_rollback, inc_pc, push_stack,
   write_memory, update_accounts) leave msdomain unchanged. *)
Theorem SND_reraise_msdomain[simp]:
  ∀e s. (SND (reraise e s)).msdomain = s.msdomain
Proof
  rw[reraise_def, return_def, fail_def] >> rw[]
QED

Theorem SND_get_current_context_msdomain[simp]:
  (SND (get_current_context s)).msdomain = s.msdomain
Proof
  rw[get_current_context_def, return_def, fail_def] >> rw[]
QED

Theorem SND_get_num_contexts_msdomain[simp]:
  (SND (get_num_contexts s)).msdomain = s.msdomain
Proof
  rw[get_num_contexts_def, return_def]
QED

Theorem SND_get_gas_left_msdomain[simp]:
  (SND (get_gas_left s)).msdomain = s.msdomain
Proof
  rw[get_gas_left_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_get_return_data_msdomain[simp]:
  (SND (get_return_data s)).msdomain = s.msdomain
Proof
  rw[get_return_data_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_get_output_to_msdomain[simp]:
  (SND (get_output_to s)).msdomain = s.msdomain
Proof
  rw[get_output_to_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_pop_context_msdomain[simp]:
  (SND (pop_context s)).msdomain = s.msdomain
Proof
  rw[pop_context_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_num_contexts_def, get_current_context_def]
  >> rw[]
QED

Theorem SND_unuse_gas_msdomain[simp]:
  ∀n s. (SND (unuse_gas n s)).msdomain = s.msdomain
Proof
  rw[unuse_gas_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_current_context_def, set_current_context_def]
  >> rw[]
QED

Theorem SND_push_logs_msdomain[simp]:
  ∀ls s. (SND (push_logs ls s)).msdomain = s.msdomain
Proof
  rw[push_logs_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_update_gas_refund_msdomain[simp]:
  ∀p s. (SND (update_gas_refund p s)).msdomain = s.msdomain
Proof
  Cases_on `p`
  >> rw[update_gas_refund_def, bind_def, return_def, get_current_context_def,
        set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_set_rollback_msdomain[simp]:
  ∀r s. (SND (set_rollback r s)).msdomain = s.msdomain
Proof
  rw[set_rollback_def, return_def]
QED

Theorem SND_pop_and_incorporate_context_msdomain[simp]:
  ∀b s. (SND (pop_and_incorporate_context b s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[pop_and_incorporate_context_def, bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

Theorem SND_inc_pc_msdomain[simp]:
  (SND (inc_pc s)).msdomain = s.msdomain
Proof
  rw[inc_pc_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_push_stack_msdomain[simp]:
  ∀v s. (SND (push_stack v s)).msdomain = s.msdomain
Proof
  rw[push_stack_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_current_context_def, set_current_context_def]
  >> rw[]
QED

Theorem SND_write_memory_msdomain[simp]:
  ∀a bs s. (SND (write_memory a bs s)).msdomain = s.msdomain
Proof
  rw[write_memory_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_handle_exception_msdomain[simp]:
  ∀e s. (SND (handle_exception e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[handle_exception_def, bind_def, ignore_bind_def, return_def,
          fail_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

Theorem SND_handle_create_msdomain[simp]:
  ∀e s. (SND (handle_create e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[handle_create_def, bind_def, ignore_bind_def, return_def,
          fail_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

(* handle_step does not modify msdomain. *)
Theorem SND_handle_step_msdomain[simp]:
  ∀e s. (SND (handle_step e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> rw[handle_step_def, handle_def, bind_def, return_def, fail_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED
