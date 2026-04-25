(*
 * jumpDest preservation through VFM execution.
 *
 * Only step_jump and step_jumpi modify the jumpDest field of the current
 * context. All other operations preserve it. This is proved compositionally:
 * monad combinators preserve the property, leaf operations trivially preserve
 * it, and all non-Jump/JumpI opcodes inherit it.
 *
 * Main exported theorem:
 *   step_inst_non_jump_preserves_jumpDest:
 *     step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧
 *     ¬is_call op ∧ op ≠ Jump ∧ op ≠ JumpI ⇒
 *     (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
 *)
Theory vfmJumpDest
Ancestors
  combin pair list
  vfmExecution
Libs
  BasicProvers

val _ = Parse.hide "add"

(* ================================================================ *)
(* Definition                                                        *)
(* ================================================================ *)

Definition preserves_jumpDest_def:
  preserves_jumpDest m ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒ s'.contexts ≠ [] ∧
      (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
End

(* ================================================================ *)
(* Layer 1: Monad combinator preservation rules                     *)
(* ================================================================ *)

Theorem preserves_jumpDest_bind[simp]:
  preserves_jumpDest g ∧ (∀x. preserves_jumpDest (f x)) ⇒
  preserves_jumpDest (bind g f)
Proof
  rw[preserves_jumpDest_def, bind_def, AllCaseEqs()]
  >> first_x_assum drule >> gvs[]
  >> first_x_assum drule >> gvs[]
  >> res_tac >> gvs[]
QED

Theorem preserves_jumpDest_ignore_bind[simp]:
  preserves_jumpDest g ∧ preserves_jumpDest f ⇒
  preserves_jumpDest (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule preserves_jumpDest_bind >> simp[]
QED

Theorem preserves_jumpDest_handle[simp]:
  preserves_jumpDest f ∧ (∀e. preserves_jumpDest (h e)) ⇒
  preserves_jumpDest (handle f h)
Proof
  rw[preserves_jumpDest_def, handle_def, AllCaseEqs()]
  >> first_x_assum drule >> gvs[]
  >> first_x_assum drule >> gvs[]
QED

(* ================================================================ *)
(* Layer 2: Leaf / primitive operations                             *)
(* ================================================================ *)

Theorem preserves_jumpDest_return[simp]:
  preserves_jumpDest (return x)
Proof
  rw[preserves_jumpDest_def, return_def]
QED

Theorem preserves_jumpDest_fail[simp]:
  preserves_jumpDest (fail e)
Proof
  rw[preserves_jumpDest_def, fail_def]
QED

Theorem preserves_jumpDest_assert[simp]:
  preserves_jumpDest (assert b e)
Proof
  rw[preserves_jumpDest_def, assert_def, return_def, fail_def]
QED

Theorem preserves_jumpDest_finish[simp]:
  preserves_jumpDest finish
Proof
  rw[preserves_jumpDest_def, finish_def]
QED

Theorem preserves_jumpDest_revert[simp]:
  preserves_jumpDest revert
Proof
  rw[preserves_jumpDest_def, revert_def]
QED

(* ================================================================ *)
(* Layer 3: State-accessing primitives that don't touch jumpDest    *)
(* ================================================================ *)

(* Operations that only read state *)
Theorem preserves_jumpDest_get_current_context[simp]:
  preserves_jumpDest get_current_context
Proof
  rw[preserves_jumpDest_def, get_current_context_def, bind_def,
     return_def, fail_def, AllCaseEqs()] >> rw[]
QED

Theorem preserves_jumpDest_get_gas_left[simp]:
  preserves_jumpDest get_gas_left
Proof
  rw[preserves_jumpDest_def, get_gas_left_def, bind_def,
     get_current_context_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_get_callee[simp]:
  preserves_jumpDest get_callee
Proof
  rw[preserves_jumpDest_def, get_callee_def, bind_def,
     get_current_context_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_get_accounts[simp]:
  preserves_jumpDest get_accounts
Proof
  rw[preserves_jumpDest_def, get_accounts_def, bind_def,
     get_rollback_def, return_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_get_rollback[simp]:
  preserves_jumpDest get_rollback
Proof
  rw[preserves_jumpDest_def, get_rollback_def, return_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_get_static[simp]:
  preserves_jumpDest get_static
Proof
  rw[preserves_jumpDest_def, get_static_def, bind_def,
     get_current_context_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_get_num_contexts[simp]:
  preserves_jumpDest get_num_contexts
Proof
  rw[preserves_jumpDest_def, get_num_contexts_def, return_def]
QED

Theorem preserves_jumpDest_get_original[simp]:
  preserves_jumpDest get_original
Proof
  rw[preserves_jumpDest_def, get_original_def, return_def, AllCaseEqs()] >> gvs[]
QED

(* Operations that modify rollback but not contexts *)
Theorem preserves_jumpDest_set_rollback[simp]:
  preserves_jumpDest (set_rollback rb)
Proof
  rw[preserves_jumpDest_def, set_rollback_def, return_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_update_accounts[simp]:
  preserves_jumpDest (update_accounts f)
Proof
  rw[preserves_jumpDest_def, update_accounts_def, return_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_set_original[simp]:
  preserves_jumpDest (set_original orig)
Proof
  rw[preserves_jumpDest_def, set_original_def, return_def, fail_def, AllCaseEqs()]
  >> gvs[set_last_accounts_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[]
QED

Theorem preserves_jumpDest_set_domain[simp]:
  preserves_jumpDest (set_domain d)
Proof
  rw[preserves_jumpDest_def, set_domain_def, return_def, AllCaseEqs()] >> gvs[]
QED

(* Operations that modify context fields OTHER than jumpDest *)

(* Key lemma: set_current_context preserves jumpDest if the new context has same jumpDest *)
Theorem preserves_jumpDest_set_current_context_if:
  (∀c. (f c).jumpDest = c.jumpDest) ⇒
  preserves_jumpDest (bind get_current_context (λc. set_current_context (f c)))
Proof
  rw[preserves_jumpDest_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

(* Most context-modifying ops use a pattern like:
   context <- get_current_context;
   set_current_context $ context with <field> := <value>
   where <field> ≠ jumpDest. We capture this with a specialized lemma. *)

Theorem preserves_jumpDest_update_context_field:
  (∀c. (f c).jumpDest = c.jumpDest) ⇒
  preserves_jumpDest (bind get_current_context (λc. set_current_context (f c)))
Proof
  rw[preserves_jumpDest_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
QED

(* Derived: pop_stack preserves jumpDest *)
Theorem preserves_jumpDest_pop_stack[simp]:
  preserves_jumpDest (pop_stack n)
Proof
  rw[preserves_jumpDest_def, pop_stack_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, AllCaseEqs()]
  >> gvs[]
QED

(* Derived: push_stack preserves jumpDest *)
Theorem preserves_jumpDest_push_stack[simp]:
  preserves_jumpDest (push_stack ws)
Proof
  rw[preserves_jumpDest_def, push_stack_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, AllCaseEqs()]
  >> gvs[]
QED

(* Derived: consume_gas preserves jumpDest *)
Theorem preserves_jumpDest_consume_gas[simp]:
  preserves_jumpDest (consume_gas g)
Proof
  rw[preserves_jumpDest_def, consume_gas_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: unuse_gas preserves jumpDest *)
Theorem preserves_jumpDest_unuse_gas[simp]:
  preserves_jumpDest (unuse_gas g)
Proof
  rw[preserves_jumpDest_def, unuse_gas_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: set_return_data preserves jumpDest *)
Theorem preserves_jumpDest_set_return_data[simp]:
  preserves_jumpDest (set_return_data rd)
Proof
  rw[preserves_jumpDest_def, set_return_data_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: push_logs preserves jumpDest *)
Theorem preserves_jumpDest_push_logs[simp]:
  preserves_jumpDest (push_logs ls)
Proof
  rw[preserves_jumpDest_def, push_logs_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: update_gas_refund preserves jumpDest *)
Theorem preserves_jumpDest_update_gas_refund[simp]:
  preserves_jumpDest (update_gas_refund (a, sb))
Proof
  rw[preserves_jumpDest_def, update_gas_refund_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: expand_memory preserves jumpDest *)
Theorem preserves_jumpDest_expand_memory[simp]:
  preserves_jumpDest (expand_memory n)
Proof
  rw[preserves_jumpDest_def, expand_memory_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: write_memory preserves jumpDest *)
Theorem preserves_jumpDest_write_memory[simp]:
  preserves_jumpDest (write_memory off bytes)
Proof
  rw[preserves_jumpDest_def, write_memory_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: read_memory preserves jumpDest *)
Theorem preserves_jumpDest_read_memory[simp]:
  preserves_jumpDest (read_memory off len)
Proof
  rw[read_memory_def]
  >> irule preserves_jumpDest_bind >> rw[]
QED

(* Derived: memory_expansion_info preserves jumpDest *)
Theorem preserves_jumpDest_memory_expansion_info[simp]:
  preserves_jumpDest (memory_expansion_info off len)
Proof
  rw[memory_expansion_info_def]
QED

(* domain_check preserves jumpDest when cont does *)
Theorem preserves_jumpDest_domain_check[simp]:
  preserves_jumpDest cont ⇒
  preserves_jumpDest (domain_check err check add cont)
Proof
  rw[preserves_jumpDest_def, domain_check_def, ignore_bind_def, bind_def,
     set_domain_def, return_def, fail_def, AllCaseEqs()]
  >> gvs[]
  >> first_x_assum drule >> simp[]
QED

(* Derived: access_address preserves jumpDest *)
Theorem preserves_jumpDest_access_address[simp]:
  preserves_jumpDest (access_address a)
Proof
  rw[preserves_jumpDest_def, access_address_def, domain_check_def,
     ignore_bind_def, bind_def, set_domain_def, set_rollback_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: access_slot preserves jumpDest *)
Theorem preserves_jumpDest_access_slot[simp]:
  preserves_jumpDest (access_slot sk)
Proof
  rw[preserves_jumpDest_def, access_slot_def, domain_check_def,
     ignore_bind_def, bind_def, set_domain_def, set_rollback_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: assert_not_static preserves jumpDest *)
Theorem preserves_jumpDest_assert_not_static[simp]:
  preserves_jumpDest assert_not_static
Proof
  rw[preserves_jumpDest_def, assert_not_static_def, bind_def,
     get_static_def, get_current_context_def, assert_def,
     return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: ensure_storage_in_domain preserves jumpDest *)
Theorem preserves_jumpDest_ensure_storage_in_domain[simp]:
  preserves_jumpDest (ensure_storage_in_domain a)
Proof
  rw[preserves_jumpDest_def, ensure_storage_in_domain_def, domain_check_def,
     ignore_bind_def, bind_def, set_domain_def, set_rollback_def,
     get_rollback_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

(* Derived: write_storage preserves jumpDest *)
Theorem preserves_jumpDest_write_storage[simp]:
  preserves_jumpDest (write_storage a k v)
Proof
  rw[write_storage_def]
QED

(* More primitives needed for step_* functions *)
Theorem preserves_jumpDest_get_tx_params[simp]:
  preserves_jumpDest get_tx_params
Proof
  rw[preserves_jumpDest_def, get_tx_params_def, return_def]
QED

Theorem preserves_jumpDest_get_tStorage[simp]:
  preserves_jumpDest get_tStorage
Proof
  rw[preserves_jumpDest_def, get_tStorage_def, return_def]
QED

Theorem preserves_jumpDest_set_tStorage[simp]:
  preserves_jumpDest (set_tStorage x)
Proof
  rw[preserves_jumpDest_def, set_tStorage_def, return_def]
QED

Theorem preserves_jumpDest_write_transient_storage[simp]:
  preserves_jumpDest (write_transient_storage a k v)
Proof
  rw[preserves_jumpDest_def, write_transient_storage_def, bind_def,
     get_tStorage_def, set_tStorage_def, return_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_add_to_delete[simp]:
  preserves_jumpDest (add_to_delete a)
Proof
  rw[preserves_jumpDest_def, add_to_delete_def, return_def]
QED

Theorem preserves_jumpDest_get_call_data[simp]:
  preserves_jumpDest get_call_data
Proof
  rw[get_call_data_def]
QED

Theorem preserves_jumpDest_get_return_data[simp]:
  preserves_jumpDest get_return_data
Proof
  rw[get_return_data_def]
QED

Theorem preserves_jumpDest_get_current_code[simp]:
  preserves_jumpDest get_current_code
Proof
  rw[get_current_code_def]
QED

Theorem preserves_jumpDest_get_output_to[simp]:
  preserves_jumpDest get_output_to
Proof
  rw[get_output_to_def]
QED

Theorem preserves_jumpDest_get_return_data_check[simp]:
  preserves_jumpDest (get_return_data_check off sz)
Proof
  rw[get_return_data_check_def]
QED

Theorem preserves_jumpDest_get_code[simp]:
  preserves_jumpDest (get_code a)
Proof
  rw[get_code_def]
QED

(* ================================================================ *)
(* Layer 4: Step helper functions                                   *)
(* ================================================================ *)

(* Tactic: repeatedly decompose through bind/ignore_bind *)
val pjd_tac = rpt (
  (irule preserves_jumpDest_bind >> rw[]) ORELSE
  (irule preserves_jumpDest_ignore_bind >> rw[]) ORELSE
  (irule preserves_jumpDest_handle >> rw[])
)

Theorem preserves_jumpDest_step_binop[simp]:
  preserves_jumpDest (step_binop op f)
Proof
  rw[step_binop_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_monop[simp]:
  preserves_jumpDest (step_monop op f)
Proof
  rw[step_monop_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_modop[simp]:
  preserves_jumpDest (step_modop op f)
Proof
  rw[step_modop_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_context[simp]:
  preserves_jumpDest (step_context op f)
Proof
  rw[step_context_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_msgParams[simp]:
  preserves_jumpDest (step_msgParams op f)
Proof
  rw[step_msgParams_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_txParams[simp]:
  preserves_jumpDest (step_txParams op f)
Proof
  rw[step_txParams_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_exp[simp]:
  preserves_jumpDest step_exp
Proof
  rw[step_exp_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_keccak256[simp]:
  preserves_jumpDest step_keccak256
Proof
  rw[step_keccak256_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_balance[simp]:
  preserves_jumpDest step_balance
Proof
  rw[step_balance_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_call_data_load[simp]:
  preserves_jumpDest step_call_data_load
Proof
  rw[step_call_data_load_def] >> pjd_tac
QED

Theorem preserves_jumpDest_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_jumpDest f) ⇒
  preserves_jumpDest (copy_to_memory g off srcoff sz src)
Proof
  strip_tac
  >> rw[copy_to_memory_def, pairTheory.UNCURRY]
  >> Cases_on `src` >> gvs[]
  >> `preserves_jumpDest x` by (first_x_assum irule >> simp[])
  >> pjd_tac
QED

Theorem preserves_jumpDest_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_jumpDest f) ⇒
  preserves_jumpDest (step_copy_to_memory op src)
Proof
  rw[step_copy_to_memory_def]
QED

Theorem preserves_jumpDest_step_return_data_copy[simp]:
  preserves_jumpDest step_return_data_copy
Proof
  rw[step_return_data_copy_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_ext_code_size[simp]:
  preserves_jumpDest step_ext_code_size
Proof
  rw[step_ext_code_size_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_ext_code_copy[simp]:
  preserves_jumpDest step_ext_code_copy
Proof
  rw[step_ext_code_copy_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_ext_code_hash[simp]:
  preserves_jumpDest step_ext_code_hash
Proof
  rw[step_ext_code_hash_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_block_hash[simp]:
  preserves_jumpDest step_block_hash
Proof
  rw[step_block_hash_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_blob_hash[simp]:
  preserves_jumpDest step_blob_hash
Proof
  rw[step_blob_hash_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_self_balance[simp]:
  preserves_jumpDest step_self_balance
Proof
  rw[step_self_balance_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_pop[simp]:
  preserves_jumpDest step_pop
Proof
  rw[step_pop_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_mload[simp]:
  preserves_jumpDest step_mload
Proof
  rw[step_mload_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_mstore[simp]:
  preserves_jumpDest (step_mstore op)
Proof
  rw[step_mstore_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_sload[simp]:
  preserves_jumpDest (step_sload b)
Proof
  rw[step_sload_def] >> pjd_tac
  >> Cases_on `b` >> gvs[] >> pjd_tac
QED

Theorem preserves_jumpDest_step_sstore_gas_consumption[simp]:
  preserves_jumpDest (step_sstore_gas_consumption a k v)
Proof
  rw[step_sstore_gas_consumption_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_sstore[simp]:
  preserves_jumpDest (step_sstore b)
Proof
  rw[step_sstore_def] >> pjd_tac
  >> Cases_on `b` >> gvs[] >> pjd_tac
QED

Theorem preserves_jumpDest_step_push[simp]:
  preserves_jumpDest (step_push n ws)
Proof
  rw[step_push_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_dup[simp]:
  preserves_jumpDest (step_dup n)
Proof
  rw[preserves_jumpDest_def, step_dup_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def, consume_gas_def,
     push_stack_def, assert_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_step_swap[simp]:
  preserves_jumpDest (step_swap n)
Proof
  rw[preserves_jumpDest_def, step_swap_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def, consume_gas_def,
     assert_def, return_def, fail_def, AllCaseEqs()] >> gvs[]
QED

Theorem preserves_jumpDest_step_log[simp]:
  preserves_jumpDest (step_log n)
Proof
  rw[step_log_def] >> pjd_tac
QED

Theorem preserves_jumpDest_step_return[simp]:
  preserves_jumpDest (step_return b)
Proof
  rw[step_return_def] >> pjd_tac
  >> Cases_on `b` >> gvs[] >> pjd_tac
QED

Theorem preserves_jumpDest_step_self_destruct[simp]:
  preserves_jumpDest step_self_destruct
Proof
  rw[step_self_destruct_def] >> pjd_tac
  >> IF_CASES_TAC >> gvs[] >> pjd_tac
QED

Theorem preserves_jumpDest_inc_pc[simp]:
  preserves_jumpDest (inc_pc)
Proof
  rw[inc_pc_def] >> irule preserves_jumpDest_set_current_context_if
  >> rw[]
QED

Theorem preserves_jumpDest_abort_call_value[simp]:
  preserves_jumpDest (abort_call_value x)
Proof
  rw[abort_call_value_def] >> pjd_tac
QED

Theorem preserves_jumpDest_abort_unuse[simp]:
  preserves_jumpDest (abort_unuse x)
Proof
  rw[abort_unuse_def]
QED

(* ================================================================ *)
(* Main theorem: non-Jump/JumpI step_inst preserves jumpDest        *)
(* ================================================================ *)

(* The proof works by case analysis on the opcode. For each non-Jump/JumpI
   opcode, step_inst expands to a combination of the primitives we've
   proved preserve jumpDest. *)
Theorem step_inst_non_jump_preserves_jumpDest:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧
  ¬is_call op ∧ op ≠ Jump ∧ op ≠ JumpI ⇒
  (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
Proof
  strip_tac >>
  `preserves_jumpDest (step_inst op)` suffices_by (
    rw[preserves_jumpDest_def] >>
    first_x_assum drule >> rw[] ) >>
  ntac 3 (pop_assum mp_tac) >>
  rpt (pop_assum kall_tac) >>
  Cases_on `op` >> rw[step_inst_def]
  >> gs[is_call_def]
QED

(* Contrapositive form useful for the main application *)
Theorem step_inst_jumpDest_changed_imp_jump:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧ ¬is_call op ∧
  (FST (HD s'.contexts)).jumpDest ≠ (FST (HD s.contexts)).jumpDest ⇒
  op = Jump ∨ op = JumpI
Proof
  strip_tac
  >> spose_not_then strip_assume_tac
  >> drule_all step_inst_non_jump_preserves_jumpDest
  >> rw[]
QED

(* Specialized form: if jumpDest is SOME after step_inst and was NONE before,
   then op = Jump or JumpI *)
Theorem step_inst_jumpDest_NONE_to_SOME_imp_jump:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧ ¬is_call op ∧
  (FST (HD s.contexts)).jumpDest = NONE ∧
  (FST (HD s'.contexts)).jumpDest = SOME pc ⇒
  op = Jump ∨ op = JumpI
Proof
  rw[] >> irule step_inst_jumpDest_changed_imp_jump >> rw[] >>
  goal_assum $ drule_at(Pat`step_inst`) >> gvs[]
QED
