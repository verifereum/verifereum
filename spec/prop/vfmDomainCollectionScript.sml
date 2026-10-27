Theory vfmDomainCollection
Ancestors
  pair pred_set finite_set
  vfmTypes vfmContext vfmExecution vfmDomainSeparation
Libs
  BasicProvers

Definition computes_minimal_domain_def:
  computes_minimal_domain m =
  ∀s r t d. m s = (r, t) ∧ s.msdomain = Collect d ⇒
  (* no outside domain errors when collecting *)
  (∀x. r ≠ INR (SOME (OutsideDomain x))) ∧
  (* collection always produces the same result and an extended domain *)
  (∀d'. ∃d''.
     m (s with msdomain := Collect d') =
     (r, t with msdomain := Collect d'') ∧
     subdomain d' d'') ∧
  (* the result of collection is enforceable *)
  (∀d' d''. t.msdomain = Collect d' ∧ subdomain d' d'' ⇒
     m (s with msdomain := Enforce d'') =
     (r, t with msdomain := Enforce d'')) ∧
  (* anything less than collection fails, i.e. it is minimal *)
  (∀d' d''. t.msdomain = Collect d' ∧ subdomain d d'' ∧ ¬subdomain d' d'' ⇒
           ∃x s'. m (s with msdomain := Enforce d'') =
                 (INR (SOME (OutsideDomain x)), s'))
End

Theorem fail_computes_minimal_domain[simp]:
  (∀x. e ≠ OutsideDomain x) ⇒
  computes_minimal_domain (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem return_computes_minimal_domain[simp]:
  computes_minimal_domain (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_current_context_computes_minimal_domain[simp]:
  computes_minimal_domain get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem with_same_msdomain[simp]:
  d = s.msdomain ⇒
  (s with msdomain := d) = s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem eq_with_msdomain[simp]:
  (s = s with msdomain := d) ⇔
  s.msdomain = d
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_computes_minimal_domain:
  computes_minimal_domain f ∧ (∀x. computes_minimal_domain (g x))
  ⇒
  computes_minimal_domain (bind f g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignore_bind_computes_minimal_domain:
  computes_minimal_domain f ∧
  computes_minimal_domain g
  ⇒
  computes_minimal_domain (ignore_bind f g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_computes_minimal_domain:
  computes_minimal_domain f ∧
  (∀s t x. f s = (INR (SOME (OutsideDomain x)), t) ⇒
           FST $ g (SOME (OutsideDomain x)) t = INR (SOME (OutsideDomain x))) ∧
  (∀e. (∀x. e ≠ SOME (OutsideDomain x)) ⇒ computes_minimal_domain (g e))
  ⇒
  computes_minimal_domain (handle f g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem reraise_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_gas_left_computes_minimal_domain[simp]:
  computes_minimal_domain get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_computes_minimal_domain[simp]:
  (¬b ⇒ ∀x. e ≠ (OutsideDomain x)) ⇒
  computes_minimal_domain (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_current_context_computes_minimal_domain[simp]:
  computes_minimal_domain (set_current_context x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem consume_gas_computes_minimal_domain[simp]:
  computes_minimal_domain (consume_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_return_data_computes_minimal_domain[simp]:
  computes_minimal_domain (set_return_data x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_num_contexts_computes_minimal_domain[simp]:
  computes_minimal_domain get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_return_data_computes_minimal_domain[simp]:
  computes_minimal_domain get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_output_to_computes_minimal_domain[simp]:
  computes_minimal_domain get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_context_computes_minimal_domain[simp]:
  computes_minimal_domain pop_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem unuse_gas_computes_minimal_domain[simp]:
  computes_minimal_domain (unuse_gas x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_rollback_computes_minimal_domain[simp]:
  computes_minimal_domain (set_rollback x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_logs_computes_minimal_domain[simp]:
  computes_minimal_domain (push_logs x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_gas_refund_computes_minimal_domain[simp]:
  computes_minimal_domain (update_gas_refund x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_and_incorporate_context_computes_minimal_domain[simp]:
  computes_minimal_domain (pop_and_incorporate_context x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_computes_minimal_domain[simp]:
  computes_minimal_domain inc_pc
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_stack_computes_minimal_domain[simp]:
  computes_minimal_domain (push_stack x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_memory_computes_minimal_domain[simp]:
  computes_minimal_domain (write_memory x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_exception e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_accounts_computes_minimal_domain[simp]:
  computes_minimal_domain (update_accounts x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_create e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_computes_minimal_domain[simp]:
  (∀x. e ≠ SOME (OutsideDomain x)) ⇒
  computes_minimal_domain (handle_step e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_or_jump_computes_minimal_domain[simp]:
  computes_minimal_domain (inc_pc_or_jump x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem finish_computes_minimal_domain[simp]:
  computes_minimal_domain finish
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_stack_computes_minimal_domain[simp]:
  computes_minimal_domain (pop_stack x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_binop_computes_minimal_domain[simp]:
  computes_minimal_domain (step_binop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_modop_computes_minimal_domain[simp]:
  computes_minimal_domain (step_modop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_exp_computes_minimal_domain[simp]:
  computes_minimal_domain step_exp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_monop_computes_minimal_domain[simp]:
  computes_minimal_domain (step_monop x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem memory_expansion_info_computes_minimal_domain[simp]:
  computes_minimal_domain (memory_expansion_info x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem expand_memory_computes_minimal_domain[simp]:
  computes_minimal_domain (expand_memory x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem read_memory_computes_minimal_domain[simp]:
  computes_minimal_domain (read_memory x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_keccak256_computes_minimal_domain[simp]:
  computes_minimal_domain step_keccak256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_context_computes_minimal_domain[simp]:
  computes_minimal_domain (step_context x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_msgParams_computes_minimal_domain[simp]:
  computes_minimal_domain (step_msgParams x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem domain_check_computes_minimal_domain:
  computes_minimal_domain f ∧
  (∀d. subdomain d (up d)) ∧
  (∀d. ch (up d)) ∧
  (∀d d'. ¬ch d ∧ subdomain d d' ∧ ¬subdomain (up d) d' ⇒ ¬ch d') ∧
  (∀d. ch d ⇒ up d = d) ∧
  (∀d d'. ch d ∧ subdomain d d' ⇒ ch d') ∧
  (∀s x. FST (f s) ≠ INR (SOME (OutsideDomain x)))
  ⇒
  computes_minimal_domain (domain_check err ch up f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_address_computes_minimal_domain[simp]:
  computes_minimal_domain (access_address x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_accounts_computes_minimal_domain[simp]:
  computes_minimal_domain get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_balance_computes_minimal_domain[simp]:
  computes_minimal_domain step_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_tx_params_computes_minimal_domain[simp]:
  computes_minimal_domain get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_txParams_computes_minimal_domain[simp]:
  computes_minimal_domain (step_txParams x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_call_data_computes_minimal_domain[simp]:
  computes_minimal_domain get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_data_load_computes_minimal_domain[simp]:
  computes_minimal_domain step_call_data_load
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ext_code_size_computes_minimal_domain[simp]:
  computes_minimal_domain step_ext_code_size
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem copy_to_memory_computes_minimal_domain[simp]:
  (∀f. b = SOME f ⇒ computes_minimal_domain f) ⇒
  computes_minimal_domain (copy_to_memory x y z a b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_code_computes_minimal_domain[simp]:
  computes_minimal_domain (get_code x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ext_code_copy_computes_minimal_domain[simp]:
  computes_minimal_domain step_ext_code_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_current_code_computes_minimal_domain[simp]:
  computes_minimal_domain get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_copy_to_memory_computes_minimal_domain[simp]:
  (∀f. b = SOME f ⇒ computes_minimal_domain f) ⇒
  computes_minimal_domain (step_copy_to_memory x b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_return_data_check_computes_minimal_domain[simp]:
  computes_minimal_domain (get_return_data_check x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_return_data_copy_computes_minimal_domain[simp]:
  computes_minimal_domain step_return_data_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_ext_code_hash_computes_minimal_domain[simp]:
  computes_minimal_domain step_ext_code_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_block_hash_computes_minimal_domain[simp]:
  computes_minimal_domain step_block_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_blob_hash_computes_minimal_domain[simp]:
  computes_minimal_domain step_blob_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_callee_computes_minimal_domain[simp]:
  computes_minimal_domain get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_balance_computes_minimal_domain[simp]:
  computes_minimal_domain step_self_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_pop_computes_minimal_domain[simp]:
  computes_minimal_domain step_pop
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_mload_computes_minimal_domain[simp]:
  computes_minimal_domain step_mload
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_mstore_computes_minimal_domain[simp]:
  computes_minimal_domain (step_mstore x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_tStorage_computes_minimal_domain[simp]:
  computes_minimal_domain get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_slot_computes_minimal_domain[simp]:
  computes_minimal_domain (access_slot x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sload_computes_minimal_domain[simp]:
  computes_minimal_domain (step_sload x)
Proof
  cheat  (* SCAFFOLD *)
QED

val tac = rpt (
  (irule ignore_bind_computes_minimal_domain \\ rw[])
  ORELSE
  (irule bind_computes_minimal_domain \\ rw[]));

Theorem get_original_computes_minimal_domain[simp]:
  computes_minimal_domain get_original
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_gas_consumption_computes_minimal_domain[simp]:
  computes_minimal_domain (step_sstore_gas_consumption x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_static_computes_minimal_domain[simp]:
  computes_minimal_domain get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_not_static_computes_minimal_domain[simp]:
  computes_minimal_domain assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_storage_computes_minimal_domain[simp]:
  computes_minimal_domain (write_storage x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_tStorage_computes_minimal_domain[simp]:
  computes_minimal_domain (set_tStorage x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_transient_storage_computes_minimal_domain[simp]:
  computes_minimal_domain (write_transient_storage x y z)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_computes_minimal_domain[simp]:
  computes_minimal_domain (step_sstore x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_jump_dest_computes_minimal_domain[simp]:
  computes_minimal_domain (set_jump_dest x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_jump_computes_minimal_domain[simp]:
  computes_minimal_domain step_jump
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_jumpi_computes_minimal_domain[simp]:
  computes_minimal_domain step_jumpi
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_push_computes_minimal_domain[simp]:
  computes_minimal_domain (step_push x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_swap_computes_minimal_domain[simp]:
  computes_minimal_domain (step_swap n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_dup_computes_minimal_domain[simp]:
  computes_minimal_domain (step_dup n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_dupn_computes_minimal_domain[simp]:
  computes_minimal_domain step_dupn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_swapn_computes_minimal_domain[simp]:
  computes_minimal_domain step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_exchange_computes_minimal_domain[simp]:
  computes_minimal_domain step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_log_computes_minimal_domain[simp]:
  computes_minimal_domain (step_log x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_unuse_computes_minimal_domain[simp]:
  computes_minimal_domain (abort_unuse x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ensure_storage_in_domain_computes_minimal_domain[simp]:
  computes_minimal_domain (ensure_storage_in_domain x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_create_exists_computes_minimal_domain[simp]:
  computes_minimal_domain (abort_create_exists x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_rollback_computes_minimal_domain[simp]:
  computes_minimal_domain get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_context_computes_minimal_domain[simp]:
  computes_minimal_domain (push_context x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_original_computes_minimal_domain[simp]:
  computes_minimal_domain (set_original a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_computes_minimal_domain[simp]:
  computes_minimal_domain (proceed_create a b c d e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_computes_minimal_domain[simp]:
  computes_minimal_domain (step_create x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_call_value_computes_minimal_domain[simp]:
  computes_minimal_domain (abort_call_value x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_caller_computes_minimal_domain[simp]:
  computes_minimal_domain get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_value_computes_minimal_domain[simp]:
  computes_minimal_domain get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem revert_computes_minimal_domain[simp]:
  computes_minimal_domain revert
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem precompiles_compute_minimal_domain[simp]:
  computes_minimal_domain precompile_sha2_256 ∧
  computes_minimal_domain precompile_ripemd_160 ∧
  computes_minimal_domain precompile_identity ∧
  computes_minimal_domain precompile_modexp ∧
  computes_minimal_domain precompile_ecadd ∧
  computes_minimal_domain precompile_ecmul ∧
  computes_minimal_domain precompile_ecpairing ∧
  computes_minimal_domain precompile_blake2f ∧
  computes_minimal_domain precompile_ecrecover ∧
  computes_minimal_domain precompile_point_eval ∧
  computes_minimal_domain precompile_bls_g1add ∧
  computes_minimal_domain precompile_bls_g1msm ∧
  computes_minimal_domain precompile_bls_g2add ∧
  computes_minimal_domain precompile_bls_g2msm ∧
  computes_minimal_domain precompile_bls_pairing ∧
  computes_minimal_domain precompile_bls_map_fp_to_g1 ∧
  computes_minimal_domain precompile_bls_map_fp2_to_g2 ∧
  computes_minimal_domain precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem dispatch_precompiles_computes_minimal_domain[simp]:
  computes_minimal_domain (dispatch_precompiles x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_computes_minimal_domain[simp]:
  computes_minimal_domain (proceed_call a b c d e f g h i)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_computes_minimal_domain[simp]:
  computes_minimal_domain (step_call x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_return_computes_minimal_domain[simp]:
  computes_minimal_domain (step_return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem add_to_delete_computes_minimal_domain[simp]:
  computes_minimal_domain (add_to_delete x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_destruct_computes_minimal_domain[simp]:
  computes_minimal_domain step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_computes_minimal_domain[simp]:
  computes_minimal_domain (step_inst x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_computes_minimal_domain[simp]:
  computes_minimal_domain step
Proof
  cheat  (* SCAFFOLD *)
QED

(* Domain collection mode is never left. *)
Theorem step_preserves_collect:
  (∃d. s.msdomain = Collect d) ∧ step s = (r, s') ⇒
  ∃d. s'.msdomain = Collect d
Proof
  cheat  (* SCAFFOLD *)
QED
