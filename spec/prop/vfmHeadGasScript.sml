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
  cheat  (* SCAFFOLD *)
QED

Theorem head_gas_mono_rel_trans:
  head_gas_mono_rel s1 s2 ∧ head_gas_mono_rel s2 s3 ⇒
  head_gas_mono_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_return[simp]:
  preserves_head_gas_mono (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_fail[simp]:
  preserves_head_gas_mono (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_reraise[simp]:
  preserves_head_gas_mono (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_assert[simp]:
  preserves_head_gas_mono (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_bind:
  preserves_head_gas_mono g ∧ (∀x. preserves_head_gas_mono (f x)) ⇒
  preserves_head_gas_mono (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_ignore_bind:
  preserves_head_gas_mono g ∧ preserves_head_gas_mono f ⇒
  preserves_head_gas_mono (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_cond[simp]:
  preserves_head_gas_mono m1 ∧ preserves_head_gas_mono m2 ⇒
  preserves_head_gas_mono (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_case_option[simp]:
  preserves_head_gas_mono m_none ∧ (∀x. preserves_head_gas_mono (m_some x)) ⇒
  preserves_head_gas_mono (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_case_sum[simp]:
  (∀x. preserves_head_gas_mono (f x)) ∧ (∀y. preserves_head_gas_mono (g y)) ⇒
  preserves_head_gas_mono (case sm of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_case_pair[simp]:
  (∀x y. preserves_head_gas_mono (f x y)) ⇒
  preserves_head_gas_mono (case p of (x,y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_let[simp]:
  (∀x. preserves_head_gas_mono (f x)) ⇒
  preserves_head_gas_mono (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ------------------------------------------------------------------------- *)
(* Primitive operations used in CALL/CREATE prefixes.                        *)
(* ------------------------------------------------------------------------- *)

Theorem get_current_context_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_current_context_preserves_head_gas_mono_when_gas_mono:
  (∀s. s.contexts ≠ [] ⇒ (FST (HD s.contexts)).gasUsed ≤ c.gasUsed) ⇒
  preserves_head_gas_mono (set_current_context c)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_stack_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_gas_left_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem consume_gas_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (consume_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_return_data_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_return_data bytes)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_return_data_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_output_to_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_num_contexts_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_rollback_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_original_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_original
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_original_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_original a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_accounts_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_accounts_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_callee_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_caller_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_value_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_static_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem read_memory_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (read_memory offset sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_memory_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (write_memory offset bytes)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem memory_expansion_info_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (memory_expansion_info offset sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem expand_memory_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (expand_memory by)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_address_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem access_slot_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (access_slot k)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ensure_storage_in_domain_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_code_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (get_code a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_tx_params_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_tStorage_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_tStorage_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_tStorage x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_rollback_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_rollback r)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_return_data_check_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (get_return_data_check offset sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_current_code_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_call_data_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_jump_dest_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_jump_dest jumpDest)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_domain_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono (set_domain d)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_not_static_preserves_head_gas_mono[simp]:
  preserves_head_gas_mono assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_head_gas_mono_imp:
  preserves_head_gas_mono m ∧ s.contexts ≠ [] ∧ m s = (q, s') ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem consume_gas_head_gas_ge:
  consume_gas n s = (INL (), s') ∧ s.contexts ≠ [] ⇒
  n ≤ (FST (HD s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem consume_gas_head_gas_add_ge:
  consume_gas n s = (INL (), s') ∧ s.contexts ≠ [] ⇒
    (FST (HD s.contexts)).gasUsed + n ≤
    (FST (HD s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED
