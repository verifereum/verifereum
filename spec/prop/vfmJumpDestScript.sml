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
  vfmExecution vfmContext vfmSameFrame
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
(* all_jumpDest_NONE: strengthened property for full stack          *)
(* ================================================================ *)

Definition all_jumpDest_NONE_def:
  all_jumpDest_NONE s ⇔ EVERY (λc. (FST c).jumpDest = NONE) s.contexts
End

Definition preserves_all_jumpDest_NONE_def:
  preserves_all_jumpDest_NONE m ⇔
    ∀s r s'. m s = (r, s') ∧ all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
End

(* Bridge lemma: primitives that preserve jumpDest and don't change
   contexts structure also preserve all_jumpDest_NONE *)
Theorem preserves_jumpDest_same_contexts_imp_all:
  preserves_jumpDest m ∧
  (∀s r s'. m s = (r, s') ⇒ s'.contexts = s.contexts) ⇒
  preserves_all_jumpDest_NONE m
Proof
  rw[preserves_jumpDest_def, preserves_all_jumpDest_NONE_def,
  all_jumpDest_NONE_def] >> first_x_assum drule >>
  first_x_assum drule >> rw[]
QED

(* Bridge lemma: use existing preserves_jumpDest and preserves_same_frame.
   The extra condition handles the empty contexts case. *)
Theorem preserves_jumpDest_and_same_frame_imp_all:
  preserves_jumpDest m ∧ preserves_same_frame m ∧
  (∀s r s'. m s = (r, s') ∧ s.contexts = [] ⇒ s'.contexts = []) ⇒
  preserves_all_jumpDest_NONE m
Proof
  rw[preserves_jumpDest_def, preserves_same_frame_def,
     preserves_all_jumpDest_NONE_def, all_jumpDest_NONE_def] >>
  rpt(first_x_assum drule) >> rw[] >>
  Cases_on `s.contexts` >> gvs[] >>
  gvs[same_frame_rel_def] >>
  Cases_on `s'.contexts` >> gvs[]
QED

(* Combinator lemmas for preserves_all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_bind[simp]:
  preserves_all_jumpDest_NONE g ∧ (∀x. preserves_all_jumpDest_NONE (f x)) ⇒
  preserves_all_jumpDest_NONE (bind g f)
Proof
  rw[preserves_all_jumpDest_NONE_def, bind_def, AllCaseEqs()]
  >> first_x_assum drule >> gvs[]
  >> first_x_assum drule >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_ignore_bind[simp]:
  preserves_all_jumpDest_NONE g ∧ preserves_all_jumpDest_NONE f ⇒
  preserves_all_jumpDest_NONE (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule preserves_all_jumpDest_NONE_bind >> simp[]
QED

Theorem preserves_all_jumpDest_NONE_handle[simp]:
  preserves_all_jumpDest_NONE f ∧ (∀e. preserves_all_jumpDest_NONE (h e)) ⇒
  preserves_all_jumpDest_NONE (handle f h)
Proof
  rw[preserves_all_jumpDest_NONE_def, handle_def, AllCaseEqs()]
  >> first_x_assum drule >> gvs[]
  >> first_x_assum drule >> gvs[]
QED

(* Leaf operations for preserves_all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_return[simp]:
  preserves_all_jumpDest_NONE (return x)
Proof
  rw[preserves_all_jumpDest_NONE_def, return_def]
QED

Theorem preserves_all_jumpDest_NONE_fail[simp]:
  preserves_all_jumpDest_NONE (fail e)
Proof
  rw[preserves_all_jumpDest_NONE_def, fail_def]
QED

Theorem preserves_all_jumpDest_NONE_assert[simp]:
  preserves_all_jumpDest_NONE (assert b e)
Proof
  rw[preserves_all_jumpDest_NONE_def, assert_def, return_def, fail_def]
QED

Theorem preserves_all_jumpDest_NONE_finish[simp]:
  preserves_all_jumpDest_NONE finish
Proof
  rw[preserves_all_jumpDest_NONE_def, finish_def, all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_revert[simp]:
  preserves_all_jumpDest_NONE revert
Proof
  rw[preserves_all_jumpDest_NONE_def, revert_def, all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_reraise[simp]:
  preserves_all_jumpDest_NONE (reraise e)
Proof
  rw[preserves_all_jumpDest_NONE_def, reraise_def]
QED

(* State-reading operations that don't change contexts *)
Theorem preserves_all_jumpDest_NONE_get_current_context[simp]:
  preserves_all_jumpDest_NONE get_current_context
Proof
  rw[preserves_all_jumpDest_NONE_def, get_current_context_def, bind_def,
     return_def, fail_def, AllCaseEqs()] >> rw[]
QED

Theorem preserves_all_jumpDest_NONE_get_gas_left[simp]:
  preserves_all_jumpDest_NONE get_gas_left
Proof
  rw[get_gas_left_def]
QED

Theorem preserves_all_jumpDest_NONE_get_callee[simp]:
  preserves_all_jumpDest_NONE get_callee
Proof
  rw[get_callee_def]
QED

Theorem preserves_all_jumpDest_NONE_get_accounts[simp]:
  preserves_all_jumpDest_NONE get_accounts
Proof
  rw[preserves_all_jumpDest_NONE_def, get_accounts_def, bind_def,
     get_rollback_def, return_def]
QED

Theorem preserves_all_jumpDest_NONE_get_rollback[simp]:
  preserves_all_jumpDest_NONE get_rollback
Proof
  rw[preserves_all_jumpDest_NONE_def, get_rollback_def, return_def]
QED

Theorem preserves_all_jumpDest_NONE_get_static[simp]:
  preserves_all_jumpDest_NONE get_static
Proof
  rw[get_static_def]
QED

Theorem preserves_all_jumpDest_NONE_get_num_contexts[simp]:
  preserves_all_jumpDest_NONE get_num_contexts
Proof
  rw[preserves_all_jumpDest_NONE_def, get_num_contexts_def, return_def]
QED

Theorem preserves_all_jumpDest_NONE_get_original[simp]:
  preserves_all_jumpDest_NONE get_original
Proof
  rw[preserves_all_jumpDest_NONE_def, get_original_def, return_def]
  >> gvs[AllCaseEqs(),fail_def]
QED

Theorem preserves_all_jumpDest_NONE_get_tx_params[simp]:
  preserves_all_jumpDest_NONE get_tx_params
Proof
  rw[preserves_all_jumpDest_NONE_def, get_tx_params_def, return_def]
QED

Theorem preserves_all_jumpDest_NONE_get_tStorage[simp]:
  preserves_all_jumpDest_NONE get_tStorage
Proof
  rw[preserves_all_jumpDest_NONE_def, get_tStorage_def, return_def]
QED

Theorem preserves_all_jumpDest_NONE_get_call_data[simp]:
  preserves_all_jumpDest_NONE get_call_data
Proof
  rw[get_call_data_def]
QED

Theorem preserves_all_jumpDest_NONE_get_return_data[simp]:
  preserves_all_jumpDest_NONE get_return_data
Proof
  rw[get_return_data_def]
QED

Theorem preserves_all_jumpDest_NONE_get_current_code[simp]:
  preserves_all_jumpDest_NONE get_current_code
Proof
  rw[get_current_code_def]
QED

Theorem preserves_all_jumpDest_NONE_get_output_to[simp]:
  preserves_all_jumpDest_NONE get_output_to
Proof
  rw[get_output_to_def]
QED

Theorem preserves_all_jumpDest_NONE_get_value[simp]:
  preserves_all_jumpDest_NONE get_value
Proof
  rw[get_value_def]
QED

Theorem preserves_all_jumpDest_NONE_get_caller[simp]:
  preserves_all_jumpDest_NONE get_caller
Proof
  rw[get_caller_def]
QED

Theorem preserves_all_jumpDest_NONE_get_return_data_check[simp]:
  preserves_all_jumpDest_NONE (get_return_data_check off sz)
Proof
  rw[get_return_data_check_def]
QED

Theorem preserves_all_jumpDest_NONE_get_code[simp]:
  preserves_all_jumpDest_NONE (get_code a)
Proof
  rw[get_code_def]
QED

Theorem preserves_all_jumpDest_NONE_memory_expansion_info[simp]:
  preserves_all_jumpDest_NONE (memory_expansion_info off len)
Proof
  rw[memory_expansion_info_def]
QED

(* Operations that modify rollback/domain but not contexts *)
Theorem preserves_all_jumpDest_NONE_set_rollback[simp]:
  preserves_all_jumpDest_NONE (set_rollback rb)
Proof
  rw[preserves_all_jumpDest_NONE_def, set_rollback_def, return_def,
     all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_update_accounts[simp]:
  preserves_all_jumpDest_NONE (update_accounts f)
Proof
  rw[preserves_all_jumpDest_NONE_def, update_accounts_def, return_def,
     all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_set_domain[simp]:
  preserves_all_jumpDest_NONE (set_domain d)
Proof
  rw[preserves_all_jumpDest_NONE_def, set_domain_def, return_def,
     all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_set_tStorage[simp]:
  preserves_all_jumpDest_NONE (set_tStorage x)
Proof
  rw[preserves_all_jumpDest_NONE_def, set_tStorage_def, return_def,
     all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_add_to_delete[simp]:
  preserves_all_jumpDest_NONE (add_to_delete a)
Proof
  rw[preserves_all_jumpDest_NONE_def, add_to_delete_def, return_def,
     all_jumpDest_NONE_def]
QED

(* Operations that modify current context but keep jumpDest = NONE *)
Theorem preserves_all_jumpDest_NONE_set_current_context_jumpDest_NONE:
  (∀c. (f c).jumpDest = NONE) ⇒
  preserves_all_jumpDest_NONE (bind get_current_context (λc. set_current_context (f c)))
Proof
  rw[preserves_all_jumpDest_NONE_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def, all_jumpDest_NONE_def,
     AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_pop_stack[simp]:
  preserves_all_jumpDest_NONE (pop_stack n)
Proof
  rw[preserves_all_jumpDest_NONE_def, pop_stack_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_push_stack[simp]:
  preserves_all_jumpDest_NONE (push_stack ws)
Proof
  rw[preserves_all_jumpDest_NONE_def, push_stack_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_consume_gas[simp]:
  preserves_all_jumpDest_NONE (consume_gas g)
Proof
  rw[preserves_all_jumpDest_NONE_def, consume_gas_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_unuse_gas[simp]:
  preserves_all_jumpDest_NONE (unuse_gas g)
Proof
  rw[preserves_all_jumpDest_NONE_def, unuse_gas_def, ignore_bind_def, bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_set_return_data[simp]:
  preserves_all_jumpDest_NONE (set_return_data rd)
Proof
  rw[preserves_all_jumpDest_NONE_def, set_return_data_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_push_logs[simp]:
  preserves_all_jumpDest_NONE (push_logs ls)
Proof
  rw[preserves_all_jumpDest_NONE_def, push_logs_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_update_gas_refund[simp]:
  preserves_all_jumpDest_NONE (update_gas_refund (a, sb))
Proof
  rw[preserves_all_jumpDest_NONE_def, update_gas_refund_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_expand_memory[simp]:
  preserves_all_jumpDest_NONE (expand_memory n)
Proof
  rw[preserves_all_jumpDest_NONE_def, expand_memory_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_write_memory[simp]:
  preserves_all_jumpDest_NONE (write_memory off bytes)
Proof
  rw[preserves_all_jumpDest_NONE_def, write_memory_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_read_memory[simp]:
  preserves_all_jumpDest_NONE (read_memory off len)
Proof
  rw[read_memory_def]
QED

Theorem preserves_all_jumpDest_NONE_access_address[simp]:
  preserves_all_jumpDest_NONE (access_address a)
Proof
  rw[preserves_all_jumpDest_NONE_def, access_address_def, domain_check_def,
     ignore_bind_def, bind_def, set_domain_def, set_rollback_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
     >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_access_slot[simp]:
  preserves_all_jumpDest_NONE (access_slot sk)
Proof
  rw[preserves_all_jumpDest_NONE_def, access_slot_def, domain_check_def,
     ignore_bind_def, bind_def, set_domain_def, set_rollback_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
     >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_assert_not_static[simp]:
  preserves_all_jumpDest_NONE assert_not_static
Proof
  rw[preserves_all_jumpDest_NONE_def, assert_not_static_def, bind_def,
     get_static_def, get_current_context_def, assert_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
     >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_ensure_storage_in_domain[simp]:
  preserves_all_jumpDest_NONE (ensure_storage_in_domain a)
Proof
  rw[preserves_all_jumpDest_NONE_def, ensure_storage_in_domain_def, domain_check_def,
     ignore_bind_def, bind_def, set_domain_def, set_rollback_def,
     get_rollback_def, return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
     >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_write_storage[simp]:
  preserves_all_jumpDest_NONE (write_storage a k v)
Proof
  rw[write_storage_def]
QED

Theorem preserves_all_jumpDest_NONE_write_transient_storage[simp]:
  preserves_all_jumpDest_NONE (write_transient_storage a k v)
Proof
  rw[preserves_all_jumpDest_NONE_def, write_transient_storage_def, bind_def,
     get_tStorage_def, set_tStorage_def, return_def, all_jumpDest_NONE_def]
QED

Theorem preserves_all_jumpDest_NONE_set_original[simp]:
  preserves_all_jumpDest_NONE (set_original orig)
Proof
  rw[preserves_all_jumpDest_NONE_def, set_original_def, return_def, fail_def,
     all_jumpDest_NONE_def, AllCaseEqs()]
  >> gvs[set_last_accounts_def]
  >> qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[]
QED

(* inc_pc sets jumpDest := NONE explicitly, preserving all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_inc_pc[simp]:
  preserves_all_jumpDest_NONE inc_pc
Proof
  rw[preserves_all_jumpDest_NONE_def, inc_pc_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

(* push_context: new context has jumpDest = NONE from initial_context *)
Theorem preserves_all_jumpDest_NONE_push_context[simp]:
  (FST ctx).jumpDest = NONE ⇒
  preserves_all_jumpDest_NONE (push_context ctx)
Proof
  rw[preserves_all_jumpDest_NONE_def, push_context_def, return_def,
     all_jumpDest_NONE_def]
QED

(* pop_context: removes head, tail still all NONE *)
Theorem preserves_all_jumpDest_NONE_pop_context[simp]:
  preserves_all_jumpDest_NONE pop_context
Proof
  rw[preserves_all_jumpDest_NONE_def, pop_context_def, return_def, fail_def,
     all_jumpDest_NONE_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

(* Tactic for preserves_all_jumpDest_NONE proofs *)
val pajdn_tac = rpt (
  (irule preserves_all_jumpDest_NONE_bind >> rw[]) ORELSE
  (irule preserves_all_jumpDest_NONE_ignore_bind >> rw[]) ORELSE
  (irule preserves_all_jumpDest_NONE_handle >> rw[])
)

(* Abort functions preserve all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_abort_call_value[simp]:
  preserves_all_jumpDest_NONE (abort_call_value x)
Proof
  rw[abort_call_value_def] >> pajdn_tac
QED

Theorem preserves_all_jumpDest_NONE_abort_unuse[simp]:
  preserves_all_jumpDest_NONE (abort_unuse x)
Proof
  rw[abort_unuse_def] >> pajdn_tac
QED

Theorem preserves_all_jumpDest_NONE_abort_create_exists[simp]:
  preserves_all_jumpDest_NONE (abort_create_exists a)
Proof
  rw[abort_create_exists_def] >> pajdn_tac
QED

(* handle_create preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_handle_create[simp]:
  preserves_all_jumpDest_NONE (handle_create e)
Proof
  rw[handle_create_def] >> pajdn_tac >>
  TOP_CASE_TAC >> pajdn_tac >> gvs[] >>
  TOP_CASE_TAC >> pajdn_tac >> gvs[]
QED

(* pop_and_incorporate_context preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_pop_and_incorporate_context[simp]:
  preserves_all_jumpDest_NONE (pop_and_incorporate_context b)
Proof
  rw[pop_and_incorporate_context_def] >> pajdn_tac >>
  IF_CASES_TAC >> gvs[] >> pajdn_tac
QED

(* handle_exception preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_handle_exception[simp]:
  preserves_all_jumpDest_NONE (handle_exception e)
Proof
  rw[handle_exception_def] >> pajdn_tac >>
  TOP_CASE_TAC >> pajdn_tac >> gvs[]
QED

(* inc_pc_or_jump: either increments pc (preserves) or jumps and sets jumpDest := NONE *)
Theorem preserves_all_jumpDest_NONE_inc_pc_or_jump[simp]:
  preserves_all_jumpDest_NONE (inc_pc_or_jump op)
Proof
  rw[inc_pc_or_jump_def] >>
  rw[preserves_all_jumpDest_NONE_def, bind_def, AllCaseEqs(),
     vfmTypesTheory.option_CASE_rator, get_current_context_def,
     ignore_bind_def, assert_def,
     set_current_context_def, return_def, fail_def] >> gvs[] >>
  gvs[all_jumpDest_NONE_def] >>
  Cases_on`s.contexts` >> gvs[]
QED

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

Theorem preserves_jumpDest_get_value[simp]:
  preserves_jumpDest get_value
Proof
  rw[get_value_def]
QED

Theorem preserves_jumpDest_get_caller[simp]:
  preserves_jumpDest get_caller
Proof
  rw[get_caller_def]
QED

(* ================================================================ *)
(* Precompiles                                                       *)
(* ================================================================ *)

Theorem preserves_jumpDest_precompile_ecrecover[simp]:
  preserves_jumpDest precompile_ecrecover
Proof
  rw[precompile_ecrecover_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_identity[simp]:
  preserves_jumpDest precompile_identity
Proof
  rw[precompile_identity_def] >> pjd_tac
QED

Theorem preserves_jumpDest_precompile_modexp[simp]:
  preserves_jumpDest precompile_modexp
Proof
  rw[precompile_modexp_def] >> pjd_tac
QED

Theorem preserves_jumpDest_precompile_sha2_256[simp]:
  preserves_jumpDest precompile_sha2_256
Proof
  rw[precompile_sha2_256_def] >> pjd_tac
QED

Theorem preserves_jumpDest_precompile_ripemd_160[simp]:
  preserves_jumpDest precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_ecadd[simp]:
  preserves_jumpDest precompile_ecadd
Proof
  rw[precompile_ecadd_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_ecmul[simp]:
  preserves_jumpDest precompile_ecmul
Proof
  rw[precompile_ecmul_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_ecpairing[simp]:
  preserves_jumpDest precompile_ecpairing
Proof
  rw[precompile_ecpairing_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_blake2f[simp]:
  preserves_jumpDest precompile_blake2f
Proof
  rw[precompile_blake2f_def] >> pjd_tac
QED

Theorem preserves_jumpDest_precompile_point_eval[simp]:
  preserves_jumpDest precompile_point_eval
Proof
  rw[precompile_point_eval_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_g1add[simp]:
  preserves_jumpDest precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_g1msm[simp]:
  preserves_jumpDest precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_g2add[simp]:
  preserves_jumpDest precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_g2msm[simp]:
  preserves_jumpDest precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_pairing[simp]:
  preserves_jumpDest precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_map_fp_to_g1[simp]:
  preserves_jumpDest precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_bls_map_fp2_to_g2[simp]:
  preserves_jumpDest precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def] >> pjd_tac
  >> CASE_TAC >> pjd_tac >> rw[]
QED

Theorem preserves_jumpDest_precompile_p256verify[simp]:
  preserves_jumpDest precompile_p256verify
Proof
  rw[precompile_p256verify_def] >> pjd_tac
QED

Theorem preserves_jumpDest_dispatch_precompiles[simp]:
  preserves_jumpDest (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def]
  >> rpt (IF_CASES_TAC >> gvs[])
QED

Theorem bind_preserves_jumpDest_imp:
  bind g f s = (r,s') ∧
  preserves_jumpDest g ∧
  s.contexts ≠ [] ∧
  (∀x s. f x s = (r, s') ∧ s.contexts ≠ [] ⇒
              s'.contexts ≠ [] ∧
              (FST(HD s'.contexts)).jumpDest =
              (FST(HD s.contexts)).jumpDest)
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest =
  (FST(HD s.contexts)).jumpDest
Proof
  simp[bind_def, AllCaseEqs(), preserves_jumpDest_def, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rpt(first_x_assum drule) >> rw[]
QED

Theorem bind_preserves_jumpDest_NONE_imp:
  bind g f s = (r,s') ∧
  preserves_jumpDest g ∧
  (FST(HD s.contexts)).jumpDest = NONE ∧
  s.contexts ≠ [] ∧
  (∀x s. f x s = (r, s') ∧ s.contexts ≠ [] ∧
         (FST(HD s.contexts)).jumpDest = NONE ⇒
              s'.contexts ≠ [] ∧
              (FST(HD s'.contexts)).jumpDest = NONE)
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest = NONE
Proof
  simp[bind_def, AllCaseEqs(), preserves_jumpDest_def, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rpt(first_x_assum drule) >> rw[]
QED

Theorem preserves_jumpDest_NONE_proceed_call:
  proceed_call op a b c d e f g h s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST(HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest = NONE
Proof
  simp[proceed_call_def] >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  reverse conj_tac >- rw[] >> gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, return_def, COND_RATOR, push_context_def] >>
  qpat_x_assum`_ = (_,_)`mp_tac >>
  reverse IF_CASES_TAC >- (
    simp[] >> strip_tac >> gvs[] ) >>
  strip_tac >>
  drule(REWRITE_RULE[preserves_jumpDest_def]
          preserves_jumpDest_dispatch_precompiles) >>
  simp[]
QED

Theorem preserves_jumpDest_NONE_step_call:
  step_call op s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST (HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s'.contexts)).jumpDest = NONE
Proof
  simp[step_call_def] >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> pairarg_tac >> gvs[] >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  reverse conj_tac >- ( CASE_TAC >> rw[] ) >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  reverse conj_tac >- (rw[] ) >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[COND_RATOR] >>
  qpat_x_assum`_ = (_,_)`mp_tac >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  IF_CASES_TAC >> gvs[] >- (
    strip_tac >>
    drule(REWRITE_RULE[preserves_jumpDest_def]
            preserves_jumpDest_abort_call_value) >>
    rw[] ) >>
  strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  gen_tac >> strip_tac >>
  IF_CASES_TAC >> gvs[] >- (
    strip_tac >>
    drule(REWRITE_RULE[preserves_jumpDest_def]
            preserves_jumpDest_abort_unuse) >>
    rw[] ) >>
  strip_tac >> drule preserves_jumpDest_NONE_proceed_call >>
  simp[]
QED

Theorem preserves_jumpDest_abort_create_exists[simp]:
  preserves_jumpDest (abort_create_exists a)
Proof
  rw[abort_create_exists_def] >> pjd_tac
QED

Theorem preserves_jumpDest_NONE_proceed_create:
  proceed_create a b c d e s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST(HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest = NONE
Proof
  simp[proceed_create_def] >> strip_tac >>
  gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, return_def, push_context_def]
QED

Theorem preserves_jumpDest_NONE_step_create:
  step_create two s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST (HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s'.contexts)).jumpDest = NONE
Proof
  simp[step_create_def] >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >> gvs[ignore_bind_def] >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule bind_preserves_jumpDest_NONE_imp >> simp[] >>
  disch_then irule >> qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[COND_RATOR] >>
  qpat_x_assum`_ = (_,_)`mp_tac >>
  IF_CASES_TAC >- (
    strip_tac >>
    drule(REWRITE_RULE[preserves_jumpDest_def]
            preserves_jumpDest_abort_unuse) >>
    rw[] ) >>
  IF_CASES_TAC >- (
    strip_tac >>
    drule(REWRITE_RULE[preserves_jumpDest_def]
            preserves_jumpDest_abort_create_exists) >>
    rw[] ) >>
  strip_tac >> drule preserves_jumpDest_NONE_proceed_create >>
  simp[]
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

Theorem step_inst_Stop_preserves_jumpDest:
  preserves_jumpDest (step_inst Stop)
Proof
  rw[step_inst_def]
QED

Theorem step_inst_Invalid_preserves_jumpDest:
  preserves_jumpDest (step_inst Invalid)
Proof
  rw[step_inst_def]
QED

Theorem preserves_jumpDest_reraise[simp]:
  preserves_jumpDest (reraise e)
Proof
  rw[preserves_jumpDest_def, reraise_def]
QED

Theorem preserves_jumpDest_handle_create[simp]:
  preserves_jumpDest (handle_create e)
Proof
  rw[handle_create_def] >> pjd_tac >>
  TOP_CASE_TAC >> pjd_tac >> gvs[] >>
  TOP_CASE_TAC >> pjd_tac >> gvs[]
QED

Theorem inc_pc_or_jump_INL_jumpDest_NONE:
  inc_pc_or_jump op s = (INL x, s') ∧
  (FST (HD s.contexts)).jumpDest = NONE
  ⇒
  (FST (HD s'.contexts)).jumpDest = NONE
Proof
  rw[inc_pc_or_jump_def, return_def] >> gvs[bind_def] >>
  gvs[AllCaseEqs(), get_current_context_def, set_current_context_def,
      return_def, fail_def, assert_def]
QED

(* handle_step preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_handle_step[simp]:
  preserves_all_jumpDest_NONE (handle_step e)
Proof
  rw[handle_step_def] >>
  IF_CASES_TAC >> gvs[] >> pajdn_tac
QED

(* For step_inst on non-call/create ops, we use the bridge lemma.
   They satisfy preserves_jumpDest and preserves_same_frame. *)

Theorem preserves_all_jumpDest_NONE_dispatch_precompiles[simp]:
  preserves_all_jumpDest_NONE (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def] >>
  rpt (IF_CASES_TAC >> gvs[] >> pajdn_tac) >>
  rw[precompile_ecrecover_def, precompile_sha2_256_def,
     precompile_ripemd_160_def, precompile_identity_def,
     precompile_modexp_def, precompile_ecadd_def,
     precompile_ecmul_def, precompile_ecpairing_def,
     precompile_blake2f_def, precompile_point_eval_def,
     precompile_bls_g1add_def, precompile_bls_g1msm_def,
     precompile_bls_g2add_def, precompile_bls_g2msm_def,
     precompile_bls_pairing_def, precompile_bls_map_fp_to_g1_def,
     precompile_bls_map_fp2_to_g2_def, precompile_p256verify_def] >>
  pajdn_tac >> CASE_TAC >> pajdn_tac >> rw[] >>
  CASE_TAC >> pajdn_tac >> gvs[]
QED

(* step_call and step_create preserve all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_proceed_call[simp]:
  preserves_all_jumpDest_NONE (proceed_call a b c d e f g h s)
Proof
  rw[proceed_call_def] >> pajdn_tac >>
  (* push_context case: initial_context has jumpDest = NONE *)
  irule preserves_all_jumpDest_NONE_push_context >>
  simp[initial_context_simp]
QED

Theorem preserves_all_jumpDest_NONE_step_call[simp]:
  preserves_all_jumpDest_NONE (step_call op)
Proof
  rw[step_call_def] >> pajdn_tac >>
  TRY pairarg_tac >> gvs[] >> pajdn_tac >> gvs[] >>
  TRY pairarg_tac >> gvs[] >> pajdn_tac >> gvs[] >>
  TRY pairarg_tac >> gvs[] >> pajdn_tac >> gvs[] >>
  TOP_CASE_TAC >> pajdn_tac >> gvs[]
QED

Theorem preserves_all_jumpDest_NONE_proceed_create:
  preserves_all_jumpDest_NONE (proceed_create a b c d e)
Proof
  rw[proceed_create_def] >> pajdn_tac >>
  irule preserves_all_jumpDest_NONE_push_context >>
  simp[initial_context_simp]
QED

Theorem preserves_all_jumpDest_NONE_step_create:
  preserves_all_jumpDest_NONE (step_create two)
Proof
  rw[step_create_def] >> pajdn_tac >>
  rpt (IF_CASES_TAC >> gvs[] >> pajdn_tac) >>
  simp[preserves_all_jumpDest_NONE_proceed_create]
QED

(* step_inst preserves all_jumpDest_NONE for all opcodes *)
Theorem preserves_all_jumpDest_NONE_step_inst:
  preserves_all_jumpDest_NONE (step_inst op)
Proof
  Cases_on `op` >> rw[step_inst_def] >> pajdn_tac >>
  (* Call/Create cases use dedicated lemmas *)
  TRY (simp[preserves_all_jumpDest_NONE_step_call] >> NO_TAC) >>
  TRY (simp[preserves_all_jumpDest_NONE_step_create] >> NO_TAC) >>
  (* Other cases: use bridge or direct pajdn_tac *)
  cheat (* TODO: may need bridge lemma or more pajdn_tac unfolding *)
QED

(* Main theorem using all_jumpDest_NONE framework *)
Theorem step_all_jumpDest_NONE:
  step s = (r, s') ∧ all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
Proof
  rw[step_def, handle_def, AllCaseEqs()] >>
  (* INL case: inner block succeeded *)
  TRY (
    gvs[bind_def, AllCaseEqs(), get_current_context_def,
        fail_def, return_def] >>
    `preserves_all_jumpDest_NONE (step_inst Stop)`
       by simp[preserves_all_jumpDest_NONE_step_inst] >>
    `preserves_all_jumpDest_NONE (step_inst Invalid)`
       by simp[preserves_all_jumpDest_NONE_step_inst] >>
    gvs[preserves_all_jumpDest_NONE_def] >>
    NO_TAC) >>
  (* INR case: inner block raised exception, handle_step handles it *)
  `preserves_all_jumpDest_NONE (handle_step e)`
     by simp[preserves_all_jumpDest_NONE_handle_step] >>
  cheat (* TODO: compose inner block + handle_step *)
QED

(* Derived theorem: if all contexts have jumpDest = NONE and contexts ≠ [],
   then HD s'.contexts has jumpDest = NONE *)
Theorem step_jumpDest_NONE:
  step s = (r,s') ∧ all_jumpDest_NONE s ∧ s'.contexts ≠ []
  ⇒ (FST (HD s'.contexts)).jumpDest = NONE
Proof
  rw[all_jumpDest_NONE_def] >>
  drule step_all_jumpDest_NONE >>
  rw[all_jumpDest_NONE_def] >>
  Cases_on `s'.contexts` >> gvs[]
QED
