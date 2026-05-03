(*
 * Head-stack preservation facts.
 *
 * This theory instantiates the generic vfmPreserves framework with the
 * relation saying that an execution preserves the current/head stack.
 * It is intended for CALL/CREATE prefix proofs: after the initial
 * pop_stack creates strict stack room, the remaining prefix operations
 * preserve the head stack until proceed_call/proceed_create pushes the
 * child frame.
 *)
Theory vfmHeadStack
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp vfmPreserves
  vfmSameFrame
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

Definition head_stack_rel_def:
  head_stack_rel s s' ⇔
    s.contexts ≠ [] ⇒
      s'.contexts ≠ [] ∧
      (FST (HD s'.contexts)).stack = (FST (HD s.contexts)).stack
End

Definition preserves_head_stack_def:
  preserves_head_stack m ⇔ preserves head_stack_rel m
End

Theorem head_stack_rel_refl[simp]:
  head_stack_rel s s
Proof
  rw[head_stack_rel_def]
QED

Theorem head_stack_rel_trans:
  head_stack_rel s1 s2 ∧ head_stack_rel s2 s3 ⇒ head_stack_rel s1 s3
Proof
  rw[head_stack_rel_def] >> metis_tac[]
QED

Theorem preserves_head_stack_return[simp]:
  preserves_head_stack (return x)
Proof
  rw[preserves_head_stack_def]
  >> irule preserves_return >> simp[]
QED

Theorem preserves_head_stack_fail[simp]:
  preserves_head_stack (fail e)
Proof
  rw[preserves_head_stack_def]
  >> irule preserves_fail >> simp[]
QED

Theorem preserves_head_stack_reraise[simp]:
  preserves_head_stack (reraise e)
Proof
  rw[preserves_head_stack_def]
  >> irule preserves_reraise >> simp[]
QED

Theorem preserves_head_stack_assert[simp]:
  preserves_head_stack (assert b e)
Proof
  rw[preserves_head_stack_def]
  >> irule preserves_assert >> simp[]
QED

Theorem preserves_head_stack_bind:
  preserves_head_stack g ∧ (∀x. preserves_head_stack (f x)) ⇒
  preserves_head_stack (bind g f)
Proof
  rw[preserves_head_stack_def]
  >> irule preserves_bind
  >> rw[] >> metis_tac[head_stack_rel_trans]
QED

Theorem preserves_head_stack_ignore_bind:
  preserves_head_stack g ∧ preserves_head_stack f ⇒
  preserves_head_stack (ignore_bind g f)
Proof
  rw[preserves_head_stack_def]
  >> irule preserves_ignore_bind
  >> rw[] >> metis_tac[head_stack_rel_trans]
QED

Theorem preserves_head_stack_cond[simp]:
  preserves_head_stack m1 ∧ preserves_head_stack m2 ⇒
  preserves_head_stack (if b then m1 else m2)
Proof
  rw[preserves_head_stack_def]
QED

Theorem preserves_head_stack_case_option[simp]:
  preserves_head_stack m_none ∧ (∀x. preserves_head_stack (m_some x)) ⇒
  preserves_head_stack (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem preserves_head_stack_case_sum[simp]:
  (∀x. preserves_head_stack (f x)) ∧ (∀y. preserves_head_stack (g y)) ⇒
  preserves_head_stack (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` >> rw[]
QED

Theorem preserves_head_stack_case_pair[simp]:
  (∀x y. preserves_head_stack (f x y)) ⇒
  preserves_head_stack (case p of (x,y) => f x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem preserves_head_stack_let[simp]:
  (∀x. preserves_head_stack (f x)) ⇒
  preserves_head_stack (let x = v in f x)
Proof
  rw[]
QED

(* ------------------------------------------------------------------------- *)
(* Primitive operations used in CALL/CREATE prefixes after the initial pop.  *)
(* ------------------------------------------------------------------------- *)

Theorem get_current_context_preserves_head_stack[simp]:
  preserves_head_stack get_current_context
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem set_current_context_preserves_head_stack_when_stack_same:
  (∀s. s.contexts ≠ [] ⇒ c.stack = (FST (HD s.contexts)).stack) ⇒
  preserves_head_stack (set_current_context c)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     set_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem get_gas_left_preserves_head_stack[simp]:
  preserves_head_stack get_gas_left
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_gas_left_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem consume_gas_preserves_head_stack[simp]:
  preserves_head_stack (consume_gas n)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     consume_gas_def, bind_def, get_current_context_def, return_def,
     fail_def, assert_def, set_current_context_def, ignore_bind_def]
  >> gvs[AllCaseEqs()]
QED

Theorem set_return_data_preserves_head_stack[simp]:
  preserves_head_stack (set_return_data bytes)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     set_return_data_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem get_return_data_preserves_head_stack[simp]:
  preserves_head_stack get_return_data
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_return_data_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem get_output_to_preserves_head_stack[simp]:
  preserves_head_stack get_output_to
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_output_to_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem get_num_contexts_preserves_head_stack[simp]:
  preserves_head_stack get_num_contexts
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_num_contexts_def, return_def]
QED

Theorem get_rollback_preserves_head_stack[simp]:
  preserves_head_stack get_rollback
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_rollback_def, return_def]
QED

Theorem get_original_preserves_head_stack[simp]:
  preserves_head_stack get_original
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_original_def, return_def, fail_def] >> gvs[]
QED

Theorem set_original_preserves_head_stack[simp]:
  preserves_head_stack (set_original a)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     set_original_def, return_def, fail_def] >>
  gvs[set_last_accounts_def] >>
  qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES >>
  gvs[] >> Cases_on`l` >> gvs[]
QED

Theorem get_accounts_preserves_head_stack[simp]:
  preserves_head_stack get_accounts
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_accounts_def, return_def]
QED

Theorem update_accounts_preserves_head_stack[simp]:
  preserves_head_stack (update_accounts f)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     update_accounts_def, return_def]
QED

Theorem get_callee_preserves_head_stack[simp]:
  preserves_head_stack get_callee
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_callee_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem get_caller_preserves_head_stack[simp]:
  preserves_head_stack get_caller
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_caller_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem get_value_preserves_head_stack[simp]:
  preserves_head_stack get_value
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_value_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem get_static_preserves_head_stack[simp]:
  preserves_head_stack get_static
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     get_static_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem read_memory_preserves_head_stack[simp]:
  preserves_head_stack (read_memory offset sz)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     read_memory_def, bind_def, get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem write_memory_preserves_head_stack[simp]:
  preserves_head_stack (write_memory offset bytes)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     write_memory_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem memory_expansion_info_preserves_head_stack[simp]:
  preserves_head_stack (memory_expansion_info offset sz)
Proof
  rw[memory_expansion_info_def] >>
  irule preserves_head_stack_bind >> rw[]
QED

Theorem expand_memory_preserves_head_stack[simp]:
  preserves_head_stack (expand_memory by)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     expand_memory_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem access_address_preserves_head_stack[simp]:
  preserves_head_stack (access_address a)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     access_address_def, domain_check_def, set_domain_def,
     ignore_bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs(),bind_def,set_domain_def,return_def]
QED

Theorem access_slot_preserves_head_stack[simp]:
  preserves_head_stack (access_slot k)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     access_slot_def, domain_check_def, set_domain_def,
     ignore_bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs(),bind_def,set_domain_def,return_def]
QED

Theorem ensure_storage_in_domain_preserves_head_stack[simp]:
  preserves_head_stack (ensure_storage_in_domain a)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     ensure_storage_in_domain_def, domain_check_def, set_domain_def,
     ignore_bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs(),bind_def,set_domain_def,return_def]
QED

Theorem get_code_preserves_head_stack[simp]:
  preserves_head_stack (get_code a)
Proof
  rw[get_code_def]
  >> irule preserves_head_stack_bind
  >> rw[]
QED

Theorem get_tx_params_preserves_head_stack[simp]:
  preserves_head_stack get_tx_params
Proof
  rw[preserves_head_stack_def,get_tx_params_def,preserves_def,return_def]
QED

Theorem get_tStorage_preserves_head_stack[simp]:
  preserves_head_stack get_tStorage
Proof
  rw[preserves_head_stack_def,get_tStorage_def,preserves_def,return_def]
QED

Theorem set_tStorage_preserves_head_stack[simp]:
  preserves_head_stack (set_tStorage x)
Proof
  rw[preserves_head_stack_def,set_tStorage_def,preserves_def,return_def] >>
  rw[head_stack_rel_def]
QED

Theorem set_rollback_preserves_head_stack[simp]:
  preserves_head_stack (set_rollback r)
Proof
  rw[preserves_head_stack_def,preserves_def,return_def,set_rollback_def]
  >> rw[head_stack_rel_def]
QED

Theorem get_return_data_check_preserves_head_stack[simp]:
  preserves_head_stack (get_return_data_check offset sz)
Proof
  rw[get_return_data_check_def]
  >> irule preserves_head_stack_bind >> rw[]
  >> irule preserves_head_stack_ignore_bind >> rw[]
QED

Theorem get_current_code_preserves_head_stack[simp]:
  preserves_head_stack get_current_code
Proof
  rw[get_current_code_def]
  >> irule preserves_head_stack_bind
  >> rw[]
QED

Theorem get_call_data_preserves_head_stack[simp]:
  preserves_head_stack get_call_data
Proof
  rw[get_call_data_def]
  >> irule preserves_head_stack_bind
  >> rw[]
QED

Theorem set_jump_dest_preserves_head_stack[simp]:
  preserves_head_stack (set_jump_dest jumpDest)
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def,
     set_jump_dest_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem set_domain_preserves_head_stack[simp]:
  preserves_head_stack (set_domain d)
Proof
  rw[preserves_head_stack_def,preserves_def,return_def,set_domain_def]
  >> rw[head_stack_rel_def]
QED

Theorem assert_not_static_preserves_head_stack[simp]:
  preserves_head_stack assert_not_static
Proof
  rw[assert_not_static_def] >>
  irule preserves_head_stack_bind >> rw[]
QED

Theorem preserves_head_stack_imp:
  preserves_head_stack m ∧ s.contexts ≠ [] ∧ m s = (q, s') ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s'.contexts)).stack = (FST (HD s.contexts)).stack
Proof
  rw[preserves_head_stack_def, preserves_def, head_stack_rel_def] >>
  first_x_assum drule >> rw[]
QED

Theorem bind_psf_phs_grows_extract:
  preserves_same_frame g ∧ preserves_head_stack g ∧
  bind g f s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∃x sm.
    g s = (INL x, sm) ∧ same_frame_rel s sm ∧
    (FST (HD sm.contexts)).stack = (FST (HD s.contexts)).stack ∧
    f x sm = (r, s')
Proof
  strip_tac
  >> drule_all bind_psf_grows_extract
  >> strip_tac >> gvs[]
  >> drule_all preserves_head_stack_imp
  >> strip_tac >> gvs[]
QED
