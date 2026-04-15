(*
 * txParams preservation through VFM execution.
 *
 * txParams is the only field of execution_state that is never written.
 * Every monadic operation modifies only contexts, rollback, and/or msdomain.
 * Proved compositionally: monad combinators preserve the property,
 * leaf operations trivially preserve it, and all opcodes inherit it.
 *
 * Main exported theorems:
 *   step_preserves_txParams:  ∀s. (SND (step s)).txParams = s.txParams
 *   run_preserves_txParams:   ∀s rs. run s = SOME rs ⇒ (SND rs).txParams = s.txParams
 *)
Theory vfmTxParams
Ancestors
  combin pair list While
  vfmExecution
Libs
  BasicProvers

val _ = Parse.hide "add"

(* ================================================================ *)
(* Layer 1: Monad combinator preservation rules                     *)
(* ================================================================ *)

Theorem bind_preserves_txParams:
  (∀s. (SND (g s)).txParams = s.txParams) ∧
  (∀x s. (SND (f x s)).txParams = s.txParams) ⇒
  ∀s. (SND (bind g f s)).txParams = s.txParams
Proof
  rw[bind_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  \\ first_x_assum(qspec_then`s`mp_tac) >> gvs[]
QED

Theorem ignore_bind_preserves_txParams:
  (∀s. (SND (g s)).txParams = s.txParams) ∧
  (∀s. (SND (f s)).txParams = s.txParams) ⇒
  ∀s. (SND (ignore_bind g f s)).txParams = s.txParams
Proof
  rw[ignore_bind_def]
  \\ irule bind_preserves_txParams \\ rw[]
QED

Theorem handle_preserves_txParams:
  (∀s. (SND (f s)).txParams = s.txParams) ∧
  (∀e s. (SND (h e s)).txParams = s.txParams) ⇒
  ∀s. (SND (handle f h s)).txParams = s.txParams
Proof
  rw[handle_def]
  \\ CASE_TAC
  \\ first_x_assum(qspec_then`s`mp_tac) >> gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem domain_check_preserves_txParams:
  (∀s. (SND (cont s)).txParams = s.txParams) ⇒
  ∀s. (SND (domain_check err chk add cont s)).txParams = s.txParams
Proof
  rw[domain_check_def]
  \\ CASE_TAC \\ gvs[]
  \\ rw[ignore_bind_def, bind_def, set_domain_def, return_def, fail_def]
QED

(* Tactic: repeatedly decompose through bind/ignore_bind *)
val ptx_tac = rpt (
  (irule bind_preserves_txParams \\ rw[]) ORELSE
  (irule ignore_bind_preserves_txParams \\ rw[])
)

(* Leaf tactic: unfold into record updates and simplify *)
val ptx_leaf = simp[return_def, fail_def, finish_def, revert_def,
  assert_def, reraise_def, COND_RAND, COND_RATOR]

(* ================================================================ *)
(* Layer 2: Leaf / primitive operations                             *)
(* ================================================================ *)

Theorem return_preserves_txParams[simp]:
  ∀x s. (SND (return x s)).txParams = s.txParams
Proof ptx_leaf
QED

Theorem fail_preserves_txParams[simp]:
  ∀e s. (SND (fail e s)).txParams = s.txParams
Proof ptx_leaf
QED

Theorem finish_preserves_txParams[simp]:
  ∀s. (SND (finish s)).txParams = s.txParams
Proof ptx_leaf
QED

Theorem revert_preserves_txParams[simp]:
  ∀s. (SND (revert s)).txParams = s.txParams
Proof ptx_leaf
QED

Theorem assert_preserves_txParams[simp]:
  ∀b e s. (SND (assert b e s)).txParams = s.txParams
Proof ptx_leaf
QED

Theorem reraise_preserves_txParams[simp]:
  ∀e s. (SND (reraise e s)).txParams = s.txParams
Proof ptx_leaf
QED

Theorem get_current_context_preserves_txParams[simp]:
  ∀s. (SND (get_current_context s)).txParams = s.txParams
Proof
  rw[get_current_context_def] \\ ptx_leaf
QED

Theorem set_current_context_preserves_txParams[simp]:
  ∀c s. (SND (set_current_context c s)).txParams = s.txParams
Proof
  rw[set_current_context_def] \\ ptx_leaf
QED

Theorem get_num_contexts_preserves_txParams[simp]:
  ∀s. (SND (get_num_contexts s)).txParams = s.txParams
Proof
  rw[get_num_contexts_def] \\ ptx_leaf
QED

Theorem push_context_preserves_txParams[simp]:
  ∀crb s. (SND (push_context crb s)).txParams = s.txParams
Proof
  rw[push_context_def] \\ ptx_leaf
QED

Theorem pop_context_preserves_txParams[simp]:
  ∀s. (SND (pop_context s)).txParams = s.txParams
Proof
  rw[pop_context_def] \\ ptx_leaf
QED

Theorem get_tx_params_preserves_txParams[simp]:
  ∀s. (SND (get_tx_params s)).txParams = s.txParams
Proof
  rw[get_tx_params_def] \\ ptx_leaf
QED

Theorem get_accounts_preserves_txParams[simp]:
  ∀s. (SND (get_accounts s)).txParams = s.txParams
Proof
  rw[get_accounts_def] \\ ptx_leaf
QED

Theorem update_accounts_preserves_txParams[simp]:
  ∀f s. (SND (update_accounts f s)).txParams = s.txParams
Proof
  rw[update_accounts_def] \\ ptx_leaf
QED

Theorem get_tStorage_preserves_txParams[simp]:
  ∀s. (SND (get_tStorage s)).txParams = s.txParams
Proof
  rw[get_tStorage_def] \\ ptx_leaf
QED

Theorem set_tStorage_preserves_txParams[simp]:
  ∀x s. (SND (set_tStorage x s)).txParams = s.txParams
Proof
  rw[set_tStorage_def] \\ ptx_leaf
QED

Theorem get_rollback_preserves_txParams[simp]:
  ∀s. (SND (get_rollback s)).txParams = s.txParams
Proof
  rw[get_rollback_def] \\ ptx_leaf
QED

Theorem set_rollback_preserves_txParams[simp]:
  ∀r s. (SND (set_rollback r s)).txParams = s.txParams
Proof
  rw[set_rollback_def] \\ ptx_leaf
QED

Theorem get_original_preserves_txParams[simp]:
  ∀s. (SND (get_original s)).txParams = s.txParams
Proof
  rw[get_original_def] \\ ptx_leaf
QED

Theorem set_original_preserves_txParams[simp]:
  ∀a s. (SND (set_original a s)).txParams = s.txParams
Proof
  rw[set_original_def] \\ ptx_leaf
QED

Theorem get_gas_left_preserves_txParams[simp]:
  ∀s. (SND (get_gas_left s)).txParams = s.txParams
Proof
  rw[get_gas_left_def] \\ ptx_tac
QED

Theorem set_domain_preserves_txParams[simp]:
  ∀d s. (SND (set_domain d s)).txParams = s.txParams
Proof
  rw[set_domain_def] \\ ptx_leaf
QED

Theorem add_to_delete_preserves_txParams[simp]:
  ∀a s. (SND (add_to_delete a s)).txParams = s.txParams
Proof
  rw[add_to_delete_def] \\ ptx_leaf
QED

(* ================================================================ *)
(* Layer 3: Mid-level operations                                    *)
(* ================================================================ *)

Theorem consume_gas_preserves_txParams[simp]:
  ∀n s. (SND (consume_gas n s)).txParams = s.txParams
Proof
  rw[consume_gas_def] \\ ptx_tac
QED

Theorem inc_pc_preserves_txParams[simp]:
  ∀s. (SND (inc_pc s)).txParams = s.txParams
Proof
  rw[inc_pc_def] \\ ptx_tac
QED

Theorem push_stack_preserves_txParams[simp]:
  ∀w s. (SND (push_stack w s)).txParams = s.txParams
Proof
  rw[push_stack_def] \\ ptx_tac
QED

Theorem pop_stack_preserves_txParams[simp]:
  ∀n s. (SND (pop_stack n s)).txParams = s.txParams
Proof
  rw[pop_stack_def] \\ ptx_tac
QED

Theorem write_memory_preserves_txParams[simp]:
  ∀off bytes s. (SND (write_memory off bytes s)).txParams = s.txParams
Proof
  rw[write_memory_def] \\ ptx_tac
QED

Theorem read_memory_preserves_txParams[simp]:
  ∀off sz s. (SND (read_memory off sz s)).txParams = s.txParams
Proof
  rw[read_memory_def] \\ ptx_tac
QED

Theorem expand_memory_preserves_txParams[simp]:
  ∀n s. (SND (expand_memory n s)).txParams = s.txParams
Proof
  rw[expand_memory_def] \\ ptx_tac
QED

Theorem set_return_data_preserves_txParams[simp]:
  ∀rd s. (SND (set_return_data rd s)).txParams = s.txParams
Proof
  rw[set_return_data_def] \\ ptx_tac
QED

Theorem get_return_data_preserves_txParams[simp]:
  ∀s. (SND (get_return_data s)).txParams = s.txParams
Proof
  rw[get_return_data_def] \\ ptx_tac
QED

Theorem get_return_data_check_preserves_txParams[simp]:
  ∀off sz s. (SND (get_return_data_check off sz s)).txParams = s.txParams
Proof
  rw[get_return_data_check_def] \\ ptx_tac
QED

Theorem get_output_to_preserves_txParams[simp]:
  ∀s. (SND (get_output_to s)).txParams = s.txParams
Proof
  rw[get_output_to_def] \\ ptx_tac
QED

Theorem unuse_gas_preserves_txParams[simp]:
  ∀n s. (SND (unuse_gas n s)).txParams = s.txParams
Proof
  rw[unuse_gas_def] \\ ptx_tac
QED

Theorem push_logs_preserves_txParams[simp]:
  ∀ls s. (SND (push_logs ls s)).txParams = s.txParams
Proof
  rw[push_logs_def] \\ ptx_tac
QED

Theorem update_gas_refund_preserves_txParams[simp]:
  ∀p s. (SND (update_gas_refund p s)).txParams = s.txParams
Proof
  Cases \\ rw[update_gas_refund_def] \\ ptx_tac
QED

Theorem memory_expansion_info_preserves_txParams[simp]:
  ∀off sz s. (SND (memory_expansion_info off sz s)).txParams = s.txParams
Proof
  rw[memory_expansion_info_def, LET_THM] \\ ptx_tac
QED

Theorem access_address_preserves_txParams[simp]:
  ∀a s. (SND (access_address a s)).txParams = s.txParams
Proof
  rw[access_address_def]
  \\ irule domain_check_preserves_txParams
  \\ rw[LET_THM, return_def]
QED

Theorem access_slot_preserves_txParams[simp]:
  ∀x s. (SND (access_slot x s)).txParams = s.txParams
Proof
  rw[access_slot_def]
  \\ irule domain_check_preserves_txParams
  \\ rw[LET_THM, return_def]
QED

Theorem ensure_storage_in_domain_preserves_txParams[simp]:
  ∀a s. (SND (ensure_storage_in_domain a s)).txParams = s.txParams
Proof
  rw[ensure_storage_in_domain_def]
  \\ irule domain_check_preserves_txParams
  \\ rw[return_def]
QED

Theorem write_storage_preserves_txParams[simp]:
  ∀a k v s. (SND (write_storage a k v s)).txParams = s.txParams
Proof
  rw[write_storage_def, LET_THM] \\ ptx_leaf
QED

Theorem write_transient_storage_preserves_txParams[simp]:
  ∀a k v s. (SND (write_transient_storage a k v s)).txParams = s.txParams
Proof
  rw[write_transient_storage_def] \\ ptx_tac
QED

Theorem step_sstore_gas_consumption_preserves_txParams[simp]:
  ∀a k v s. (SND (step_sstore_gas_consumption a k v s)).txParams = s.txParams
Proof
  rw[step_sstore_gas_consumption_def, LET_THM, GSYM get_gas_left_def]
  \\ ptx_tac
QED

Theorem assert_not_static_preserves_txParams[simp]:
  ∀s. (SND (assert_not_static s)).txParams = s.txParams
Proof
  rw[assert_not_static_def, get_static_def] \\ ptx_tac
QED

Theorem get_call_data_preserves_txParams[simp]:
  ∀s. (SND (get_call_data s)).txParams = s.txParams
Proof
  rw[get_call_data_def] \\ ptx_tac
QED

Theorem get_callee_preserves_txParams[simp]:
  ∀s. (SND (get_callee s)).txParams = s.txParams
Proof
  rw[get_callee_def] \\ ptx_tac
QED

Theorem get_caller_preserves_txParams[simp]:
  ∀s. (SND (get_caller s)).txParams = s.txParams
Proof
  rw[get_caller_def] \\ ptx_tac
QED

Theorem get_value_preserves_txParams[simp]:
  ∀s. (SND (get_value s)).txParams = s.txParams
Proof
  rw[get_value_def] \\ ptx_tac
QED

Theorem get_static_preserves_txParams[simp]:
  ∀s. (SND (get_static s)).txParams = s.txParams
Proof
  rw[get_static_def] \\ ptx_tac
QED

Theorem get_code_preserves_txParams[simp]:
  ∀a s. (SND (get_code a s)).txParams = s.txParams
Proof
  rw[get_code_def] \\ ptx_tac
QED

Theorem get_current_code_preserves_txParams[simp]:
  ∀s. (SND (get_current_code s)).txParams = s.txParams
Proof
  rw[get_current_code_def] \\ ptx_tac
QED

Theorem set_jump_dest_preserves_txParams[simp]:
  ∀d s. (SND (set_jump_dest d s)).txParams = s.txParams
Proof
  rw[set_jump_dest_def] \\ ptx_tac
QED

Theorem copy_to_memory_preserves_txParams[simp]:
  (∀gs s. getSource = SOME gs ⇒ (SND (gs s)).txParams = s.txParams) ⇒
  ∀s. (SND (copy_to_memory gas off soff sz getSource s)).txParams = s.txParams
Proof
  rw[copy_to_memory_def, LET_THM] \\ ptx_tac
  \\ TRY pairarg_tac \\ gvs[] \\ ptx_tac
  \\ Cases_on `getSource` \\ gvs[] \\ ptx_tac
QED

Theorem copy_to_memory_NONE_preserves_txParams[simp]:
  ∀s. (SND (copy_to_memory gas off soff sz NONE s)).txParams = s.txParams
Proof
  rw[copy_to_memory_def, LET_THM]
  \\ Cases_on `max_expansion_range (off,sz) (soff,sz)`
  \\ rw[] \\ ptx_tac
QED

Theorem copy_to_memory_SOME_preserves_txParams[simp]:
  (∀s. (SND (gs s)).txParams = s.txParams) ⇒
  ∀s. (SND (copy_to_memory gas off soff sz (SOME gs) s)).txParams = s.txParams
Proof
  rw[] \\ irule copy_to_memory_preserves_txParams \\ rw[]
QED

Theorem pop_and_incorporate_context_preserves_txParams[simp]:
  ∀b s. (SND (pop_and_incorporate_context b s)).txParams = s.txParams
Proof
  rw[pop_and_incorporate_context_def, GSYM get_gas_left_def] \\ ptx_tac
QED

Theorem abort_unuse_preserves_txParams[simp]:
  ∀n s. (SND (abort_unuse n s)).txParams = s.txParams
Proof
  rw[abort_unuse_def] \\ ptx_tac
QED

Theorem abort_create_exists_preserves_txParams[simp]:
  ∀a s. (SND (abort_create_exists a s)).txParams = s.txParams
Proof
  rw[abort_create_exists_def] \\ ptx_tac
QED

Theorem abort_call_value_preserves_txParams[simp]:
  ∀n s. (SND (abort_call_value n s)).txParams = s.txParams
Proof
  rw[abort_call_value_def] \\ ptx_tac
QED

(* ================================================================ *)
(* Layer 4: Opcode-level operations                                 *)
(* ================================================================ *)

Theorem step_binop_preserves_txParams[simp]:
  ∀op f s. (SND (step_binop op f s)).txParams = s.txParams
Proof
  rw[step_binop_def, LET_THM] \\ ptx_tac
QED

Theorem step_monop_preserves_txParams[simp]:
  ∀op f s. (SND (step_monop op f s)).txParams = s.txParams
Proof
  rw[step_monop_def, LET_THM] \\ ptx_tac
QED

Theorem step_modop_preserves_txParams[simp]:
  ∀op f s. (SND (step_modop op f s)).txParams = s.txParams
Proof
  rw[step_modop_def, LET_THM] \\ ptx_tac
QED

Theorem step_context_preserves_txParams[simp]:
  ∀op f s. (SND (step_context op f s)).txParams = s.txParams
Proof
  rw[step_context_def, LET_THM] \\ ptx_tac
QED

Theorem step_msgParams_preserves_txParams[simp]:
  ∀op f s. (SND (step_msgParams op f s)).txParams = s.txParams
Proof
  rw[step_msgParams_def]
QED

Theorem step_txParams_preserves_txParams[simp]:
  ∀op f s. (SND (step_txParams op f s)).txParams = s.txParams
Proof
  rw[step_txParams_def, LET_THM] \\ ptx_tac
QED

Theorem step_exp_preserves_txParams[simp]:
  ∀s. (SND (step_exp s)).txParams = s.txParams
Proof
  rw[step_exp_def, LET_THM] \\ ptx_tac
QED

Theorem step_keccak256_preserves_txParams[simp]:
  ∀s. (SND (step_keccak256 s)).txParams = s.txParams
Proof
  rw[step_keccak256_def, LET_THM] \\ ptx_tac
QED

Theorem step_sload_preserves_txParams[simp]:
  ∀b s. (SND (step_sload b s)).txParams = s.txParams
Proof
  rw[step_sload_def, LET_THM] \\ ptx_tac
  \\ IF_CASES_TAC \\ gvs[] \\ ptx_tac
QED

Theorem step_sstore_preserves_txParams[simp]:
  ∀b s. (SND (step_sstore b s)).txParams = s.txParams
Proof
  rw[step_sstore_def, LET_THM] \\ ptx_tac
  \\ IF_CASES_TAC \\ gvs[] \\ ptx_tac
QED

Theorem step_balance_preserves_txParams[simp]:
  ∀s. (SND (step_balance s)).txParams = s.txParams
Proof
  rw[step_balance_def, LET_THM] \\ ptx_tac
QED

Theorem step_call_data_load_preserves_txParams[simp]:
  ∀s. (SND (step_call_data_load s)).txParams = s.txParams
Proof
  rw[step_call_data_load_def, LET_THM] \\ ptx_tac
QED

Theorem step_copy_to_memory_preserves_txParams[simp]:
  (∀gs s. getSource = SOME gs ⇒ (SND (gs s)).txParams = s.txParams) ⇒
  ∀s. (SND (step_copy_to_memory op getSource s)).txParams = s.txParams
Proof
  rw[step_copy_to_memory_def, LET_THM] \\ ptx_tac
  \\ irule copy_to_memory_preserves_txParams \\ rw[]
QED

Theorem step_return_data_copy_preserves_txParams[simp]:
  ∀s. (SND (step_return_data_copy s)).txParams = s.txParams
Proof
  rw[step_return_data_copy_def, LET_THM] \\ ptx_tac
  \\ irule copy_to_memory_SOME_preserves_txParams \\ rw[]
QED

Theorem step_ext_code_size_preserves_txParams[simp]:
  ∀s. (SND (step_ext_code_size s)).txParams = s.txParams
Proof
  rw[step_ext_code_size_def, LET_THM] \\ ptx_tac
QED

Theorem step_ext_code_copy_preserves_txParams[simp]:
  ∀s. (SND (step_ext_code_copy s)).txParams = s.txParams
Proof
  rw[step_ext_code_copy_def, LET_THM] \\ ptx_tac
  \\ irule copy_to_memory_SOME_preserves_txParams \\ rw[]
QED

Theorem step_ext_code_hash_preserves_txParams[simp]:
  ∀s. (SND (step_ext_code_hash s)).txParams = s.txParams
Proof
  rw[step_ext_code_hash_def, LET_THM] \\ ptx_tac
QED

Theorem step_block_hash_preserves_txParams[simp]:
  ∀s. (SND (step_block_hash s)).txParams = s.txParams
Proof
  rw[step_block_hash_def, LET_THM] \\ ptx_tac
QED

Theorem step_blob_hash_preserves_txParams[simp]:
  ∀s. (SND (step_blob_hash s)).txParams = s.txParams
Proof
  rw[step_blob_hash_def, LET_THM] \\ ptx_tac
QED

Theorem step_self_balance_preserves_txParams[simp]:
  ∀s. (SND (step_self_balance s)).txParams = s.txParams
Proof
  rw[step_self_balance_def, LET_THM] \\ ptx_tac
QED

Theorem step_pop_preserves_txParams[simp]:
  ∀s. (SND (step_pop s)).txParams = s.txParams
Proof
  rw[step_pop_def] \\ ptx_tac
QED

Theorem step_mload_preserves_txParams[simp]:
  ∀s. (SND (step_mload s)).txParams = s.txParams
Proof
  rw[step_mload_def, LET_THM] \\ ptx_tac
QED

Theorem step_mstore_preserves_txParams[simp]:
  ∀op s. (SND (step_mstore op s)).txParams = s.txParams
Proof
  rw[step_mstore_def, LET_THM] \\ ptx_tac
QED

Theorem step_jump_preserves_txParams[simp]:
  ∀s. (SND (step_jump s)).txParams = s.txParams
Proof
  rw[step_jump_def, LET_THM] \\ ptx_tac
QED

Theorem step_jumpi_preserves_txParams[simp]:
  ∀s. (SND (step_jumpi s)).txParams = s.txParams
Proof
  rw[step_jumpi_def, LET_THM] \\ ptx_tac
QED

Theorem step_push_preserves_txParams[simp]:
  ∀n ws s. (SND (step_push n ws s)).txParams = s.txParams
Proof
  rw[step_push_def, LET_THM] \\ ptx_tac
QED

Theorem step_dup_preserves_txParams[simp]:
  ∀n s. (SND (step_dup n s)).txParams = s.txParams
Proof
  rw[step_dup_def, LET_THM] \\ ptx_tac
QED

Theorem step_swap_preserves_txParams[simp]:
  ∀n s. (SND (step_swap n s)).txParams = s.txParams
Proof
  rw[step_swap_def, LET_THM] \\ ptx_tac
QED

Theorem step_log_preserves_txParams[simp]:
  ∀n s. (SND (step_log n s)).txParams = s.txParams
Proof
  rw[step_log_def, LET_THM] \\ ptx_tac
QED

Theorem step_return_preserves_txParams[simp]:
  ∀b s. (SND (step_return b s)).txParams = s.txParams
Proof
  rw[step_return_def, LET_THM] \\ ptx_tac
  \\ IF_CASES_TAC \\ gvs[]
QED

Theorem step_self_destruct_preserves_txParams[simp]:
  ∀s. (SND (step_self_destruct s)).txParams = s.txParams
Proof
  rw[step_self_destruct_def, LET_THM] \\ ptx_tac
  \\ IF_CASES_TAC \\ gvs[] \\ ptx_tac
QED

(* Precompiles *)

(*
 * All precompiles follow the same pattern: read input, consume gas,
 * compute result, case-split on outcome, set_return_data/finish/fail.
 * The tactic ptx_tac handles the monadic structure; every_case_tac
 * handles pure case-splits; IF_CASES_TAC handles conditionals.
 * All branches reduce to operations already in the simp set.
 *)

val precompile_ptx_tac =
  rpt (ptx_tac
       \\ TRY (every_case_tac \\ gvs[])
       \\ TRY (IF_CASES_TAC \\ gvs[]))

Theorem precompile_ecrecover_preserves_txParams[simp]:
  ∀s. (SND (precompile_ecrecover s)).txParams = s.txParams
Proof
  rw[precompile_ecrecover_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_sha2_256_preserves_txParams[simp]:
  ∀s. (SND (precompile_sha2_256 s)).txParams = s.txParams
Proof
  rw[precompile_sha2_256_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_ripemd_160_preserves_txParams[simp]:
  ∀s. (SND (precompile_ripemd_160 s)).txParams = s.txParams
Proof
  rw[precompile_ripemd_160_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_identity_preserves_txParams[simp]:
  ∀s. (SND (precompile_identity s)).txParams = s.txParams
Proof
  rw[precompile_identity_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_modexp_preserves_txParams[simp]:
  ∀s. (SND (precompile_modexp s)).txParams = s.txParams
Proof
  rw[precompile_modexp_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_ecadd_preserves_txParams[simp]:
  ∀s. (SND (precompile_ecadd s)).txParams = s.txParams
Proof
  rw[precompile_ecadd_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_ecmul_preserves_txParams[simp]:
  ∀s. (SND (precompile_ecmul s)).txParams = s.txParams
Proof
  rw[precompile_ecmul_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_ecpairing_preserves_txParams[simp]:
  ∀s. (SND (precompile_ecpairing s)).txParams = s.txParams
Proof
  rw[precompile_ecpairing_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_blake2f_preserves_txParams[simp]:
  ∀s. (SND (precompile_blake2f s)).txParams = s.txParams
Proof
  rw[precompile_blake2f_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_point_eval_preserves_txParams[simp]:
  ∀s. (SND (precompile_point_eval s)).txParams = s.txParams
Proof
  rw[precompile_point_eval_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_g1add_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_g1add s)).txParams = s.txParams
Proof
  rw[precompile_bls_g1add_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_g1msm_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_g1msm s)).txParams = s.txParams
Proof
  rw[precompile_bls_g1msm_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_g2add_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_g2add s)).txParams = s.txParams
Proof
  rw[precompile_bls_g2add_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_g2msm_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_g2msm s)).txParams = s.txParams
Proof
  rw[precompile_bls_g2msm_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_pairing_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_pairing s)).txParams = s.txParams
Proof
  rw[precompile_bls_pairing_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_map_fp_to_g1_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_map_fp_to_g1 s)).txParams = s.txParams
Proof
  rw[precompile_bls_map_fp_to_g1_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_bls_map_fp2_to_g2_preserves_txParams[simp]:
  ∀s. (SND (precompile_bls_map_fp2_to_g2 s)).txParams = s.txParams
Proof
  rw[precompile_bls_map_fp2_to_g2_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem precompile_p256verify_preserves_txParams[simp]:
  ∀s. (SND (precompile_p256verify s)).txParams = s.txParams
Proof
  rw[precompile_p256verify_def, LET_THM] \\ precompile_ptx_tac
QED

Theorem dispatch_precompiles_preserves_txParams[simp]:
  ∀a s. (SND (dispatch_precompiles a s)).txParams = s.txParams
Proof
  rw[dispatch_precompiles_def]
  \\ rpt IF_CASES_TAC \\ gvs[]
QED

(* proceed_create and proceed_call *)

Theorem proceed_create_preserves_txParams[simp]:
  ∀sa a v c g s. (SND (proceed_create sa a v c g s)).txParams = s.txParams
Proof
  rw[proceed_create_def, LET_THM] \\ ptx_tac
QED

Theorem proceed_call_preserves_txParams[simp]:
  ∀op se a v ao as' c sp ot s.
    (SND (proceed_call op se a v ao as' c sp ot s)).txParams = s.txParams
Proof
  rw[proceed_call_def, LET_THM] \\ ptx_tac
  \\ rpt IF_CASES_TAC \\ gvs[] \\ ptx_tac
QED

Theorem step_create_preserves_txParams[simp]:
  ∀b s. (SND (step_create b s)).txParams = s.txParams
Proof
  rw[step_create_def, LET_THM] \\ ptx_tac
  \\ rpt IF_CASES_TAC \\ gvs[] \\ ptx_tac
QED

Theorem step_call_preserves_txParams[simp]:
  ∀op s. (SND (step_call op s)).txParams = s.txParams
Proof
  rw[step_call_def, LET_THM, pairTheory.UNCURRY] \\ ptx_tac
  \\ TRY pairarg_tac >> gvs[] \\ ptx_tac
  \\ every_case_tac \\ gvs[] \\ ptx_tac
QED

(* ================================================================ *)
(* Layer 5: Exception handling, step_inst, step, run                *)
(* ================================================================ *)

Theorem handle_create_preserves_txParams[simp]:
  ∀e s. (SND (handle_create e s)).txParams = s.txParams
Proof
  rw[handle_create_def, LET_THM] \\ ptx_tac
  \\ every_case_tac \\ gvs[] \\ ptx_tac
QED

Theorem handle_exception_preserves_txParams[simp]:
  ∀e s. (SND (handle_exception e s)).txParams = s.txParams
Proof
  rw[handle_exception_def, LET_THM] \\ ptx_tac
  \\ every_case_tac \\ gvs[] \\ ptx_tac
QED

Theorem handle_step_preserves_txParams[simp]:
  ∀e s. (SND (handle_step e s)).txParams = s.txParams
Proof
  rw[handle_step_def]
  \\ irule handle_preserves_txParams \\ rw[]
QED

Theorem inc_pc_or_jump_preserves_txParams[simp]:
  ∀op s. (SND (inc_pc_or_jump op s)).txParams = s.txParams
Proof
  rw[inc_pc_or_jump_def, LET_THM] \\ ptx_tac
  \\ CASE_TAC \\ ptx_tac \\ gvs[]
QED

Theorem step_inst_preserves_txParams[simp]:
  ∀op s. (SND (step_inst op s)).txParams = s.txParams
Proof
  Cases \\ rw[step_inst_def] \\ ptx_tac
QED

Theorem step_preserves_txParams:
  ∀s. (SND (step s)).txParams = s.txParams
Proof
  gen_tac \\ simp[step_def]
  \\ irule handle_preserves_txParams \\ rw[]
  \\ ptx_tac
  \\ CASE_TAC \\ gvs[] \\ ptx_tac
QED

Theorem run_preserves_txParams:
  ∀s rs. run s = SOME rs ⇒ (SND rs).txParams = s.txParams
Proof
  rpt strip_tac
  \\ gvs[run_def]
  \\ qsuff_tac
    `∀s s'. OWHILE (ISL o FST) (step o SND) s = SOME s' ⇒
            (SND s').txParams = (SND s).txParams`
  >- (disch_then drule \\ simp[])
  \\ ho_match_mp_tac WhileTheory.OWHILE_IND \\ rw[]
  \\ Cases_on `step (SND s1)` \\ gvs[]
  \\ metis_tac[step_preserves_txParams, pairTheory.SND]
QED
