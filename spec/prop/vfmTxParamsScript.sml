(*
 * txParams preservation through VFM execution.
 *
 * txParams is the only field of execution_state that is never written.
 * Every monadic operation modifies only contexts, rollback, and/or msdomain.
 * Proved compositionally: monad combinators preserve the property,
 * leaf operations trivially preserve it, and all opcodes inherit it.
 *
 * Uses the generic preserves/preserves_when framework from vfmPreserves:
 *   preserves_txParams m  <=>  preserves txParams_rel m
 * Composition rules derived from preserves_bind/ignore_bind/handle/cond.
 *
 * Main exported theorems:
 *   step_preserves_txParams:  ∀s. (SND (step s)).txParams = s.txParams
 *   run_preserves_txParams:   ∀s rs. run s = SOME rs ⇒ (SND rs).txParams = s.txParams
 *)
Theory vfmTxParams
Ancestors
  combin pair list While
  vfmExecution vfmPreserves
Libs
  BasicProvers

val _ = Parse.hide "add"

(* ================================================================ *)
(* State relation and predicate definition                           *)
(* ================================================================ *)

Definition txParams_rel_def:
  txParams_rel s s' ⇔ s'.txParams = s.txParams
End

Definition preserves_txParams_def:
  preserves_txParams m ⇔
    ∀s r s'. m s = ((r:α + exception option), s') ⇒ s'.txParams = s.txParams
End

Theorem preserves_txParams_eq_preserves:
  preserves_txParams m ⇔ preserves txParams_rel m
Proof
  rw[preserves_txParams_def, preserves_def, txParams_rel_def]
QED

Theorem txParams_rel_refl[simp]:
  txParams_rel s s
Proof
  rw[txParams_rel_def]
QED

Theorem txParams_rel_trans:
  txParams_rel s1 s2 ∧ txParams_rel s2 s3 ⇒ txParams_rel s1 s3
Proof
  rw[txParams_rel_def]
QED

(* ================================================================ *)
(* Layer 1: Composition rules (derived from generic framework)       *)
(* ================================================================ *)

Theorem preserves_txParams_bind[simp]:
  preserves_txParams g ∧ (∀x. preserves_txParams (f x)) ⇒
  preserves_txParams (bind g f)
Proof
  rw[preserves_txParams_eq_preserves]
  >> match_mp_tac preserves_bind
  >> simp[] >> metis_tac[txParams_rel_trans]
QED

Theorem preserves_txParams_ignore_bind[simp]:
  preserves_txParams g ∧ preserves_txParams f ⇒
  preserves_txParams (ignore_bind g f)
Proof
  rw[preserves_txParams_eq_preserves]
  >> match_mp_tac preserves_ignore_bind
  >> simp[] >> metis_tac[txParams_rel_trans]
QED

Theorem preserves_txParams_handle[simp]:
  preserves_txParams f ∧ (∀e. preserves_txParams (h e)) ⇒
  preserves_txParams (handle f h)
Proof
  rw[preserves_txParams_eq_preserves]
  >> match_mp_tac preserves_handle
  >> simp[] >> metis_tac[txParams_rel_trans]
QED

Theorem preserves_txParams_cond[simp]:
  preserves_txParams m1 ∧ preserves_txParams m2 ⇒
  preserves_txParams (if b then m1 else m2)
Proof
  rw[preserves_txParams_eq_preserves, preserves_cond]
QED

Theorem preserves_txParams_domain_check:
  (preserves_txParams cont) ⇒
  preserves_txParams (domain_check err chk add cont)
Proof
  rw[preserves_txParams_def, domain_check_def, ignore_bind_def, bind_def,
     set_domain_def, return_def, fail_def, AllCaseEqs()]
  >> gvs[]
  >> first_x_assum drule >> simp[]
QED

(* Tactic: repeatedly decompose through bind/ignore_bind *)
val ptx_tac = rpt (
  (irule preserves_txParams_bind >> rw[]) ORELSE
  (irule preserves_txParams_ignore_bind >> rw[])
)

(* ================================================================ *)
(* Layer 2: Leaf / primitive operations                             *)
(* ================================================================ *)

Theorem preserves_txParams_return[simp]:
  preserves_txParams (return x)
Proof
  rw[preserves_txParams_eq_preserves]
  >> irule preserves_return
  >> simp[txParams_rel_refl]
QED

Theorem preserves_txParams_fail[simp]:
  preserves_txParams (fail e)
Proof
  rw[preserves_txParams_eq_preserves]
  >> irule preserves_fail
  >> simp[txParams_rel_refl]
QED

Theorem preserves_txParams_finish[simp]:
  preserves_txParams finish
Proof
  rw[preserves_txParams_def, finish_def]
QED

Theorem preserves_txParams_revert[simp]:
  preserves_txParams revert
Proof
  rw[preserves_txParams_def, revert_def]
QED

Theorem preserves_txParams_assert[simp]:
  preserves_txParams (assert b e)
Proof
  rw[preserves_txParams_eq_preserves]
  >> irule preserves_assert
  >> simp[txParams_rel_refl]
QED

Theorem preserves_txParams_reraise[simp]:
  preserves_txParams (reraise e)
Proof
  rw[preserves_txParams_eq_preserves]
  >> irule preserves_reraise
  >> simp[txParams_rel_refl]
QED

Theorem preserves_txParams_get_current_context[simp]:
  preserves_txParams get_current_context
Proof
  rw[preserves_txParams_def, get_current_context_def, bind_def,
     return_def, fail_def, AllCaseEqs()]
QED

Theorem preserves_txParams_set_current_context[simp]:
  preserves_txParams (set_current_context c)
Proof
  simp[preserves_txParams_def, set_current_context_def, return_def]
  >> rw[] >> gvs[fail_def]
QED

Theorem preserves_txParams_get_num_contexts[simp]:
  preserves_txParams get_num_contexts
Proof
  rw[preserves_txParams_def, get_num_contexts_def, return_def]
QED

Theorem preserves_txParams_push_context[simp]:
  preserves_txParams (push_context crb)
Proof
  rw[preserves_txParams_def, push_context_def, return_def]
QED

Theorem preserves_txParams_pop_context[simp]:
  preserves_txParams pop_context
Proof
  rw[preserves_txParams_def, pop_context_def,
     return_def, fail_def, AllCaseEqs()] >> rw[]
QED

Theorem preserves_txParams_get_tx_params[simp]:
  preserves_txParams get_tx_params
Proof
  rw[preserves_txParams_def, get_tx_params_def, return_def]
QED

Theorem preserves_txParams_get_accounts[simp]:
  preserves_txParams get_accounts
Proof
  rw[preserves_txParams_def, get_accounts_def, bind_def,
     get_rollback_def, return_def, AllCaseEqs()]
QED

Theorem preserves_txParams_update_accounts[simp]:
  preserves_txParams (update_accounts f)
Proof
  rw[preserves_txParams_def, update_accounts_def, return_def]
QED

Theorem preserves_txParams_get_tStorage[simp]:
  preserves_txParams get_tStorage
Proof
  rw[preserves_txParams_def, get_tStorage_def, return_def]
QED

Theorem preserves_txParams_set_tStorage[simp]:
  preserves_txParams (set_tStorage x)
Proof
  rw[preserves_txParams_def, set_tStorage_def, return_def]
QED

Theorem preserves_txParams_get_rollback[simp]:
  preserves_txParams get_rollback
Proof
  rw[preserves_txParams_def, get_rollback_def, return_def]
QED

Theorem preserves_txParams_set_rollback[simp]:
  preserves_txParams (set_rollback r)
Proof
  rw[preserves_txParams_def, set_rollback_def, return_def]
QED

Theorem preserves_txParams_get_original[simp]:
  preserves_txParams get_original
Proof
  rw[preserves_txParams_def, get_original_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem preserves_txParams_set_original[simp]:
  preserves_txParams (set_original a)
Proof
  rw[preserves_txParams_def, set_original_def,
     return_def, fail_def, AllCaseEqs()] >> rw[]
QED

Theorem preserves_txParams_get_gas_left[simp]:
  preserves_txParams get_gas_left
Proof
  rw[get_gas_left_def] >> ptx_tac
QED

Theorem preserves_txParams_set_domain[simp]:
  preserves_txParams (set_domain d)
Proof
  rw[preserves_txParams_def, set_domain_def, return_def]
QED

Theorem preserves_txParams_add_to_delete[simp]:
  preserves_txParams (add_to_delete a)
Proof
  rw[preserves_txParams_def, add_to_delete_def, return_def]
QED

(* ================================================================ *)
(* Layer 3: Mid-level operations                                    *)
(* ================================================================ *)

Theorem preserves_txParams_consume_gas[simp]:
  preserves_txParams (consume_gas n)
Proof
  rw[consume_gas_def] >> ptx_tac
QED

Theorem preserves_txParams_inc_pc[simp]:
  preserves_txParams inc_pc
Proof
  rw[inc_pc_def] >> ptx_tac
QED

Theorem preserves_txParams_push_stack[simp]:
  preserves_txParams (push_stack w)
Proof
  rw[push_stack_def] >> ptx_tac
QED

Theorem preserves_txParams_pop_stack[simp]:
  preserves_txParams (pop_stack n)
Proof
  rw[pop_stack_def] >> ptx_tac
QED

Theorem preserves_txParams_write_memory[simp]:
  preserves_txParams (write_memory off bytes)
Proof
  rw[write_memory_def] >> ptx_tac
QED

Theorem preserves_txParams_read_memory[simp]:
  preserves_txParams (read_memory off sz)
Proof
  rw[read_memory_def] >> ptx_tac
QED

Theorem preserves_txParams_expand_memory[simp]:
  preserves_txParams (expand_memory n)
Proof
  rw[expand_memory_def] >> ptx_tac
QED

Theorem preserves_txParams_set_return_data[simp]:
  preserves_txParams (set_return_data rd)
Proof
  rw[set_return_data_def] >> ptx_tac
QED

Theorem preserves_txParams_get_return_data[simp]:
  preserves_txParams get_return_data
Proof
  rw[get_return_data_def] >> ptx_tac
QED

Theorem preserves_txParams_get_return_data_check[simp]:
  preserves_txParams (get_return_data_check off sz)
Proof
  rw[get_return_data_check_def] >> ptx_tac
QED

Theorem preserves_txParams_get_output_to[simp]:
  preserves_txParams get_output_to
Proof
  rw[get_output_to_def] >> ptx_tac
QED

Theorem preserves_txParams_unuse_gas[simp]:
  preserves_txParams (unuse_gas n)
Proof
  rw[unuse_gas_def] >> ptx_tac
QED

Theorem preserves_txParams_push_logs[simp]:
  preserves_txParams (push_logs ls)
Proof
  rw[push_logs_def] >> ptx_tac
QED

Theorem preserves_txParams_update_gas_refund[simp]:
  preserves_txParams (update_gas_refund p)
Proof
  Cases_on`p` >> rw[update_gas_refund_def] >> ptx_tac
QED

Theorem preserves_txParams_memory_expansion_info[simp]:
  preserves_txParams (memory_expansion_info off sz)
Proof
  rw[memory_expansion_info_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_access_address[simp]:
  preserves_txParams (access_address a)
Proof
  rw[access_address_def]
  >> irule preserves_txParams_domain_check
  >> rw[LET_THM, return_def]
  >> rw[preserves_txParams_def]
QED

Theorem preserves_txParams_access_slot[simp]:
  preserves_txParams (access_slot x)
Proof
  rw[access_slot_def]
  >> irule preserves_txParams_domain_check
  >> rw[LET_THM, return_def]
  >> rw[preserves_txParams_def]
QED

Theorem preserves_txParams_ensure_storage_in_domain[simp]:
  preserves_txParams (ensure_storage_in_domain a)
Proof
  rw[ensure_storage_in_domain_def]
  >> irule preserves_txParams_domain_check
  >> rw[return_def]
  >> rw[preserves_txParams_def]
QED

Theorem preserves_txParams_write_storage[simp]:
  preserves_txParams (write_storage a k v)
Proof
  rw[preserves_txParams_def, write_storage_def, LET_THM]
  >> gvs[return_def, fail_def, finish_def, revert_def,
         assert_def, reraise_def, COND_RAND, update_accounts_def]
QED

Theorem preserves_txParams_write_transient_storage[simp]:
  preserves_txParams (write_transient_storage a k v)
Proof
  rw[write_transient_storage_def] >> ptx_tac
QED

Theorem preserves_txParams_step_sstore_gas_consumption[simp]:
  preserves_txParams (step_sstore_gas_consumption a k v)
Proof
  rw[step_sstore_gas_consumption_def, LET_THM, GSYM get_gas_left_def] >> ptx_tac
QED

Theorem preserves_txParams_assert_not_static[simp]:
  preserves_txParams assert_not_static
Proof
  rw[assert_not_static_def, get_static_def] >> ptx_tac
QED

Theorem preserves_txParams_get_call_data[simp]:
  preserves_txParams get_call_data
Proof
  rw[get_call_data_def] >> ptx_tac
QED

Theorem preserves_txParams_get_callee[simp]:
  preserves_txParams get_callee
Proof
  rw[get_callee_def] >> ptx_tac
QED

Theorem preserves_txParams_get_caller[simp]:
  preserves_txParams get_caller
Proof
  rw[get_caller_def] >> ptx_tac
QED

Theorem preserves_txParams_get_value[simp]:
  preserves_txParams get_value
Proof
  rw[get_value_def] >> ptx_tac
QED

Theorem preserves_txParams_get_static[simp]:
  preserves_txParams get_static
Proof
  rw[get_static_def] >> ptx_tac
QED

Theorem preserves_txParams_get_code[simp]:
  preserves_txParams (get_code a)
Proof
  rw[get_code_def] >> ptx_tac
QED

Theorem preserves_txParams_get_current_code[simp]:
  preserves_txParams get_current_code
Proof
  rw[get_current_code_def] >> ptx_tac
QED

Theorem preserves_txParams_set_jump_dest[simp]:
  preserves_txParams (set_jump_dest d)
Proof
  rw[set_jump_dest_def] >> ptx_tac
QED

Theorem preserves_txParams_copy_to_memory:
  (∀gs. getSource = SOME gs ⇒ preserves_txParams gs) ⇒
  preserves_txParams (copy_to_memory gas off soff sz getSource)
Proof
  rw[copy_to_memory_def, LET_THM] >> ptx_tac
  >> TRY pairarg_tac >> gvs[] >> ptx_tac
  >> Cases_on `getSource` >> gvs[] >> ptx_tac
QED

Theorem preserves_txParams_copy_to_memory_NONE[simp]:
  preserves_txParams (copy_to_memory gas off soff sz NONE)
Proof
  rw[copy_to_memory_def, LET_THM]
  >> Cases_on `max_expansion_range (off,sz) (soff,sz)`
  >> rw[] >> ptx_tac
QED

Theorem preserves_txParams_copy_to_memory_SOME[simp]:
  preserves_txParams gs ⇒
  preserves_txParams (copy_to_memory gas off soff sz (SOME gs))
Proof
  rw[] >> irule preserves_txParams_copy_to_memory >> rw[] >> gvs[]
QED

Theorem preserves_txParams_pop_and_incorporate_context[simp]:
  preserves_txParams (pop_and_incorporate_context b)
Proof
  rw[pop_and_incorporate_context_def, GSYM get_gas_left_def] >> ptx_tac
QED

Theorem preserves_txParams_abort_unuse[simp]:
  preserves_txParams (abort_unuse n)
Proof
  rw[abort_unuse_def] >> ptx_tac
QED

Theorem preserves_txParams_abort_create_exists[simp]:
  preserves_txParams (abort_create_exists a)
Proof
  rw[abort_create_exists_def] >> ptx_tac
QED

Theorem preserves_txParams_abort_call_value[simp]:
  preserves_txParams (abort_call_value n)
Proof
  rw[abort_call_value_def] >> ptx_tac
QED

(* ================================================================ *)
(* Layer 4: Opcode-level operations                                 *)
(* ================================================================ *)

Theorem preserves_txParams_step_binop[simp]:
  preserves_txParams (step_binop op f)
Proof
  rw[step_binop_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_monop[simp]:
  preserves_txParams (step_monop op f)
Proof
  rw[step_monop_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_modop[simp]:
  preserves_txParams (step_modop op f)
Proof
  rw[step_modop_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_context[simp]:
  preserves_txParams (step_context op f)
Proof
  rw[step_context_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_msgParams[simp]:
  preserves_txParams (step_msgParams op f)
Proof
  rw[step_msgParams_def]
QED

Theorem preserves_txParams_step_txParams[simp]:
  preserves_txParams (step_txParams op f)
Proof
  rw[step_txParams_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_exp[simp]:
  preserves_txParams step_exp
Proof
  rw[step_exp_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_keccak256[simp]:
  preserves_txParams step_keccak256
Proof
  rw[step_keccak256_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_sload[simp]:
  preserves_txParams (step_sload b)
Proof
  rw[step_sload_def, LET_THM] >> ptx_tac
  >> IF_CASES_TAC >> gvs[] >> ptx_tac
QED

Theorem preserves_txParams_step_sstore[simp]:
  preserves_txParams (step_sstore b)
Proof
  rw[step_sstore_def, LET_THM] >> ptx_tac
  >> IF_CASES_TAC >> gvs[] >> ptx_tac
QED

Theorem preserves_txParams_step_balance[simp]:
  preserves_txParams step_balance
Proof
  rw[step_balance_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_call_data_load[simp]:
  preserves_txParams step_call_data_load
Proof
  rw[step_call_data_load_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_copy_to_memory[simp]:
  (∀gs. getSource = SOME gs ⇒ preserves_txParams gs) ⇒
  preserves_txParams (step_copy_to_memory op getSource)
Proof
  rw[step_copy_to_memory_def, LET_THM] >> ptx_tac
  >> irule preserves_txParams_copy_to_memory >> rw[]
QED

Theorem preserves_txParams_step_return_data_copy[simp]:
  preserves_txParams step_return_data_copy
Proof
  rw[step_return_data_copy_def, LET_THM] >> ptx_tac
  >> irule preserves_txParams_copy_to_memory_SOME >> rw[]
QED

Theorem preserves_txParams_step_ext_code_size[simp]:
  preserves_txParams step_ext_code_size
Proof
  rw[step_ext_code_size_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_ext_code_copy[simp]:
  preserves_txParams step_ext_code_copy
Proof
  rw[step_ext_code_copy_def, LET_THM] >> ptx_tac
  >> irule preserves_txParams_copy_to_memory_SOME >> rw[]
QED

Theorem preserves_txParams_step_ext_code_hash[simp]:
  preserves_txParams step_ext_code_hash
Proof
  rw[step_ext_code_hash_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_block_hash[simp]:
  preserves_txParams step_block_hash
Proof
  rw[step_block_hash_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_blob_hash[simp]:
  preserves_txParams step_blob_hash
Proof
  rw[step_blob_hash_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_self_balance[simp]:
  preserves_txParams step_self_balance
Proof
  rw[step_self_balance_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_pop[simp]:
  preserves_txParams step_pop
Proof
  rw[step_pop_def] >> ptx_tac
QED

Theorem preserves_txParams_step_mload[simp]:
  preserves_txParams step_mload
Proof
  rw[step_mload_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_mstore[simp]:
  preserves_txParams (step_mstore op)
Proof
  rw[step_mstore_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_jump[simp]:
  preserves_txParams step_jump
Proof
  rw[step_jump_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_jumpi[simp]:
  preserves_txParams step_jumpi
Proof
  rw[step_jumpi_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_push[simp]:
  preserves_txParams (step_push n ws)
Proof
  rw[step_push_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_dup[simp]:
  preserves_txParams (step_dup n)
Proof
  rw[step_dup_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_swap[simp]:
  preserves_txParams (step_swap n)
Proof
  rw[step_swap_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_log[simp]:
  preserves_txParams (step_log n)
Proof
  rw[step_log_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_step_return[simp]:
  preserves_txParams (step_return b)
Proof
  rw[step_return_def, LET_THM] >> ptx_tac
  >> IF_CASES_TAC >> gvs[]
QED

Theorem preserves_txParams_step_self_destruct[simp]:
  preserves_txParams step_self_destruct
Proof
  rw[step_self_destruct_def, LET_THM] >> ptx_tac
  >> IF_CASES_TAC >> gvs[] >> ptx_tac
QED

(* Precompiles *)

val precompile_ptx_tac =
  rpt (ptx_tac
       >> TRY (every_case_tac >> gvs[])
       >> TRY (IF_CASES_TAC >> gvs[]))

Theorem preserves_txParams_precompile_ecrecover[simp]:
  preserves_txParams precompile_ecrecover
Proof
  rw[precompile_ecrecover_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_sha2_256[simp]:
  preserves_txParams precompile_sha2_256
Proof
  rw[precompile_sha2_256_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_ripemd_160[simp]:
  preserves_txParams precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_identity[simp]:
  preserves_txParams precompile_identity
Proof
  rw[precompile_identity_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_modexp[simp]:
  preserves_txParams precompile_modexp
Proof
  rw[precompile_modexp_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_ecadd[simp]:
  preserves_txParams precompile_ecadd
Proof
  rw[precompile_ecadd_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_ecmul[simp]:
  preserves_txParams precompile_ecmul
Proof
  rw[precompile_ecmul_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_ecpairing[simp]:
  preserves_txParams precompile_ecpairing
Proof
  rw[precompile_ecpairing_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_blake2f[simp]:
  preserves_txParams precompile_blake2f
Proof
  rw[precompile_blake2f_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_point_eval[simp]:
  preserves_txParams precompile_point_eval
Proof
  rw[precompile_point_eval_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_g1add[simp]:
  preserves_txParams precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_g1msm[simp]:
  preserves_txParams precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_g2add[simp]:
  preserves_txParams precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_g2msm[simp]:
  preserves_txParams precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_pairing[simp]:
  preserves_txParams precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_map_fp_to_g1[simp]:
  preserves_txParams precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_bls_map_fp2_to_g2[simp]:
  preserves_txParams precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_precompile_p256verify[simp]:
  preserves_txParams precompile_p256verify
Proof
  rw[precompile_p256verify_def, LET_THM] >> precompile_ptx_tac
QED

Theorem preserves_txParams_dispatch_precompiles[simp]:
  preserves_txParams (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def]
  >> rpt (IF_CASES_TAC >> gvs[])
QED

(* proceed_create and proceed_call *)

Theorem preserves_txParams_proceed_create[simp]:
  preserves_txParams (proceed_create sa a v c g)
Proof
  rw[proceed_create_def, LET_THM] >> ptx_tac
QED

Theorem preserves_txParams_proceed_call[simp]:
  preserves_txParams (proceed_call op se a v ao as' c sp ot)
Proof
  rw[proceed_call_def, LET_THM] >> ptx_tac
  >> rpt (IF_CASES_TAC >> gvs[]) >> ptx_tac
QED

Theorem preserves_txParams_step_create[simp]:
  preserves_txParams (step_create b)
Proof
  rw[step_create_def, LET_THM] >> ptx_tac
  >> rpt (IF_CASES_TAC >> gvs[]) >> ptx_tac
QED

Theorem preserves_txParams_step_call[simp]:
  preserves_txParams (step_call op)
Proof
  rw[step_call_def, LET_THM, pairTheory.UNCURRY] >> ptx_tac
  >> TRY pairarg_tac >> gvs[] >> ptx_tac
  >> every_case_tac >> gvs[] >> ptx_tac
QED

(* ================================================================ *)
(* Layer 5: Exception handling, step_inst, step, run                *)
(* ================================================================ *)

Theorem preserves_txParams_handle_create[simp]:
  preserves_txParams (handle_create e)
Proof
  rw[handle_create_def, LET_THM] >> ptx_tac
  >> every_case_tac >> gvs[] >> ptx_tac
QED

Theorem preserves_txParams_handle_exception[simp]:
  preserves_txParams (handle_exception e)
Proof
  rw[handle_exception_def, LET_THM] >> ptx_tac
  >> every_case_tac >> gvs[] >> ptx_tac
QED

Theorem preserves_txParams_handle_step[simp]:
  preserves_txParams (handle_step e)
Proof
  rw[handle_step_def]
  >> irule preserves_txParams_handle >> rw[]
QED

Theorem preserves_txParams_inc_pc_or_jump[simp]:
  preserves_txParams (inc_pc_or_jump op)
Proof
  rw[inc_pc_or_jump_def, LET_THM] >> ptx_tac
  >> CASE_TAC >> ptx_tac >> gvs[]
QED

Theorem preserves_txParams_step_inst[simp]:
  preserves_txParams (step_inst op)
Proof
  Cases_on`op` >> rw[step_inst_def] >> ptx_tac
QED

Theorem preserves_txParams_step:
  preserves_txParams step
Proof
  rw[step_def]
  >> irule preserves_txParams_handle >> rw[]
  >> ptx_tac
  >> CASE_TAC >> gvs[] >> ptx_tac
QED

(* Backward-compatible raw-form theorems for downstream consumers *)

Theorem step_preserves_txParams:
  ∀s. (SND (step s)).txParams = s.txParams
Proof
  gen_tac >> Cases_on `step s`
  >> drule (preserves_txParams_step |> REWRITE_RULE[preserves_txParams_def])
  >> simp[]
QED

Theorem handle_step_preserves_txParams:
  ∀e s. (SND (handle_step e s)).txParams = s.txParams
Proof
  rpt gen_tac >> Cases_on `handle_step e s`
  >> drule (preserves_txParams_handle_step |> REWRITE_RULE[preserves_txParams_def])
  >> simp[]
QED

Theorem step_call_preserves_txParams:
  ∀op s. (SND (step_call op s)).txParams = s.txParams
Proof
  rpt gen_tac >> Cases_on `step_call op s`
  >> drule (preserves_txParams_step_call |> REWRITE_RULE[preserves_txParams_def])
  >> simp[]
QED

Theorem run_preserves_txParams:
  ∀s rs. run s = SOME rs ⇒ (SND rs).txParams = s.txParams
Proof
  rpt strip_tac
  >> gvs[run_def]
  >> qsuff_tac
    `∀s s'. OWHILE (ISL o FST) (step o SND) s = SOME s' ⇒
            (SND s').txParams = (SND s).txParams`
  >- (disch_then drule >> simp[])
  >> ho_match_mp_tac WhileTheory.OWHILE_IND >> rw[]
  >> Cases_on `step (SND s1)` >> gvs[]
  >> metis_tac[step_preserves_txParams, pairTheory.SND]
QED
