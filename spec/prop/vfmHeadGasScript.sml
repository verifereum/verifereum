(*
 * Head-gas monotonicity facts.
 *
 * This theory instantiates the generic vfmPreserves framework with the
 * relation saying that an execution does not decrease the current/head
 * context's gasUsed.  It is intended for CALL/CREATE prefix proofs: the
 * prefix before proceed_call/proceed_create only consumes gas or preserves it,
 * and then the pushed frame saves that monotone parent as EL 1.
 *)
Theory vfmHeadGas
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp vfmPreserves
  vfmSameFrame
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

Definition head_gas_mono_rel_def:
  head_gas_mono_rel s s' ⇔
    s.contexts ≠ [] ⇒
      s'.contexts ≠ [] ∧
      (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
End

Definition preserves_head_gas_mono_def:
  preserves_head_gas_mono m ⇔ preserves head_gas_mono_rel m
End

Theorem head_gas_mono_rel_refl[simp]:
  head_gas_mono_rel s s
Proof
  rw[head_gas_mono_rel_def]
QED

Theorem head_gas_mono_rel_trans:
  head_gas_mono_rel s1 s2 ∧ head_gas_mono_rel s2 s3 ⇒
  head_gas_mono_rel s1 s3
Proof
  rw[head_gas_mono_rel_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem preserves_head_gas_mono_return[simp]:
  preserves_head_gas_mono (return x)
Proof
  rw[preserves_head_gas_mono_def]
  >> irule preserves_return >> simp[]
QED

Theorem preserves_head_gas_mono_fail[simp]:
  preserves_head_gas_mono (fail e)
Proof
  rw[preserves_head_gas_mono_def]
  >> irule preserves_fail >> simp[]
QED

Theorem preserves_head_gas_mono_reraise[simp]:
  preserves_head_gas_mono (reraise e)
Proof
  rw[preserves_head_gas_mono_def]
  >> irule preserves_reraise >> simp[]
QED

Theorem preserves_head_gas_mono_assert[simp]:
  preserves_head_gas_mono (assert b e)
Proof
  rw[preserves_head_gas_mono_def]
  >> irule preserves_assert >> simp[]
QED

Theorem preserves_head_gas_mono_bind:
  preserves_head_gas_mono g ∧ (∀x. preserves_head_gas_mono (f x)) ⇒
  preserves_head_gas_mono (bind g f)
Proof
  rw[preserves_head_gas_mono_def]
  >> irule preserves_bind
  >> rw[] >> metis_tac[head_gas_mono_rel_trans]
QED

Theorem preserves_head_gas_mono_ignore_bind:
  preserves_head_gas_mono g ∧ preserves_head_gas_mono f ⇒
  preserves_head_gas_mono (ignore_bind g f)
Proof
  rw[preserves_head_gas_mono_def]
  >> irule preserves_ignore_bind
  >> rw[] >> metis_tac[head_gas_mono_rel_trans]
QED

Theorem preserves_head_gas_mono_cond[simp]:
  preserves_head_gas_mono m1 ∧ preserves_head_gas_mono m2 ⇒
  preserves_head_gas_mono (if b then m1 else m2)
Proof
  rw[preserves_head_gas_mono_def]
QED

Theorem preserves_head_gas_mono_case_option[simp]:
  preserves_head_gas_mono m_none ∧ (∀x. preserves_head_gas_mono (m_some x)) ⇒
  preserves_head_gas_mono (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem preserves_head_gas_mono_case_sum[simp]:
  (∀x. preserves_head_gas_mono (f x)) ∧ (∀y. preserves_head_gas_mono (g y)) ⇒
  preserves_head_gas_mono (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` >> rw[]
QED

Theorem preserves_head_gas_mono_case_pair[simp]:
  (∀x y. preserves_head_gas_mono (f x y)) ⇒
  preserves_head_gas_mono (case p of (x,y) => f x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem preserves_head_gas_mono_let[simp]:
  (∀x. preserves_head_gas_mono (f x)) ⇒
  preserves_head_gas_mono (let x = v in f x)
Proof
  rw[]
QED

(* ------------------------------------------------------------------------- *)
(* Primitive operations used in CALL/CREATE prefixes.                        *)
(* ------------------------------------------------------------------------- *)

Theorem get_current_context_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_current_context
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     get_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem set_current_context_preserves_head_gas_mono_when_gas_mono:
  (∀s. s.contexts ≠ [] ⇒ (FST (HD s.contexts)).gasUsed ≤ c.gasUsed) ⇒
  preserves_head_gas_mono (set_current_context c)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     set_current_context_def, return_def, fail_def]
  >> gvs[]
QED

Theorem pop_stack_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (pop_stack n)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     pop_stack_def, bind_def, ignore_bind_def, get_current_context_def,
     return_def, fail_def, assert_def, set_current_context_def]
  >> gvs[AllCaseEqs()]
QED

Theorem get_gas_left_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_gas_left
Proof
  rw[get_gas_left_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem consume_gas_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (consume_gas n)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     consume_gas_def, bind_def, get_current_context_def, return_def,
     fail_def, assert_def, set_current_context_def, ignore_bind_def]
  >> gvs[AllCaseEqs()]
QED

Theorem set_return_data_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_return_data bytes)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     set_return_data_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem get_return_data_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_return_data
Proof
  rw[get_return_data_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_output_to_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_output_to
Proof
  rw[get_output_to_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_num_contexts_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_num_contexts
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     get_num_contexts_def, return_def]
QED

Theorem get_rollback_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_rollback
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     get_rollback_def, return_def]
QED

Theorem get_original_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_original
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     get_original_def, return_def, fail_def] >> gvs[]
QED

Theorem set_original_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_original a)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     set_original_def, return_def, fail_def]
  >> gvs[set_last_accounts_def]
  >> qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES
  >> gvs[] >> Cases_on`l` >> gvs[]
QED

Theorem get_accounts_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_accounts
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     get_accounts_def, return_def]
QED

Theorem update_accounts_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (update_accounts f)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     update_accounts_def, return_def]
QED

Theorem get_callee_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_callee
Proof
  rw[get_callee_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_caller_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_caller
Proof
  rw[get_caller_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_value_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_value
Proof
  rw[get_value_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_static_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_static
Proof
  rw[get_static_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem read_memory_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (read_memory offset sz)
Proof
  rw[read_memory_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem write_memory_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (write_memory offset bytes)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     write_memory_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem memory_expansion_info_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (memory_expansion_info offset sz)
Proof
  rw[memory_expansion_info_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem expand_memory_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (expand_memory by)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     expand_memory_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem access_address_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (access_address a)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     access_address_def, domain_check_def, set_domain_def,
     ignore_bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs(), bind_def, set_domain_def, return_def]
QED

Theorem access_slot_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (access_slot k)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     access_slot_def, domain_check_def, set_domain_def,
     ignore_bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs(), bind_def, set_domain_def, return_def]
QED

Theorem ensure_storage_in_domain_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (ensure_storage_in_domain a)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     ensure_storage_in_domain_def, domain_check_def, set_domain_def,
     ignore_bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs(), bind_def, set_domain_def, return_def]
QED

Theorem get_code_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (get_code a)
Proof
  rw[get_code_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_tx_params_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_tx_params
Proof
  rw[preserves_head_gas_mono_def, get_tx_params_def, preserves_def,
     head_gas_mono_rel_def, return_def]
QED

Theorem get_tStorage_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_tStorage
Proof
  rw[preserves_head_gas_mono_def, get_tStorage_def, preserves_def,
     head_gas_mono_rel_def, return_def]
QED

Theorem set_tStorage_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_tStorage x)
Proof
  rw[preserves_head_gas_mono_def, set_tStorage_def, preserves_def,
     return_def, head_gas_mono_rel_def]
QED

Theorem set_rollback_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_rollback r)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, return_def,
     set_rollback_def, head_gas_mono_rel_def]
QED

Theorem get_return_data_check_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (get_return_data_check offset sz)
Proof
  rw[get_return_data_check_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
  >> irule preserves_head_gas_mono_ignore_bind >> rw[]
QED

Theorem get_current_code_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_current_code
Proof
  rw[get_current_code_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem get_call_data_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_call_data
Proof
  rw[get_call_data_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem set_jump_dest_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_jump_dest jumpDest)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     set_jump_dest_def, bind_def, get_current_context_def, return_def,
     fail_def, set_current_context_def]
  >> gvs[]
QED

Theorem set_domain_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_domain d)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, return_def,
     set_domain_def, head_gas_mono_rel_def]
QED

Theorem assert_not_static_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono assert_not_static
Proof
  rw[assert_not_static_def]
  >> irule preserves_head_gas_mono_bind >> rw[]
QED

Theorem preserves_head_gas_mono_imp:
  preserves_head_gas_mono m ∧ s.contexts ≠ [] ∧ m s = (q, s') ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def]
  >> first_x_assum drule >> rw[]
QED

Theorem bind_psf_phgm_grows_extract:
  preserves_same_frame g ∧ preserves_head_gas_mono g ∧
  bind g f s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∃x sm.
    g s = (INL x, sm) ∧ same_frame_rel s sm ∧
    (FST (HD s.contexts)).gasUsed ≤ (FST (HD sm.contexts)).gasUsed ∧
    f x sm = (r, s')
Proof
  strip_tac
  >> drule_all bind_psf_grows_extract
  >> strip_tac >> gvs[]
  >> drule_all preserves_head_gas_mono_imp
  >> strip_tac >> gvs[]
QED

Theorem consume_gas_head_gas_ge:
  consume_gas n s = (INL (), s') ∧ s.contexts ≠ [] ⇒
  n ≤ (FST (HD s'.contexts)).gasUsed
Proof
  rw[consume_gas_def, bind_def, get_current_context_def, return_def,
     ignore_bind_def,
     fail_def, assert_def, set_current_context_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem consume_gas_head_gas_add_ge:
  consume_gas n s = (INL (), s') ∧ s.contexts ≠ [] ⇒
    (FST (HD s.contexts)).gasUsed + n ≤
    (FST (HD s'.contexts)).gasUsed
Proof
  rw[consume_gas_def, bind_def, get_current_context_def, return_def,
     ignore_bind_def,
     fail_def, assert_def, set_current_context_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED
