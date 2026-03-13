Theory vfmStaticCalls
Ancestors
  vfmExecution vfmDecreasesGas vfmExecutionProp


(*
  Proof that static calls do not modify world state.

  Architecture:
  1. static_inv: invariant over full execution state
  2. cp: context-preserving monadic property
  3. Decompose step = handle inner handle_step
  4. Prove inner preserves via cp + special cases
  5. Prove handle_step preserves
  6. run_tr induction lifts to run
  7. Final theorem connects to the frozen statement
*)

Definition static_inv_def:
  static_inv a0 t0 d0 l0 s ⇔
    s.rollback.accounts = a0 ∧
    s.rollback.tStorage = t0 ∧
    s.rollback.toDelete = d0 ∧
    s.contexts ≠ [] ∧
    EVERY (λ(ctxt, rb). ctxt.msgParams.static) s.contexts ∧
    EVERY (λ(ctxt, rb).
      ctxt.logs = [] ∧
      (∀a. ctxt.msgParams.outputTo ≠ Code a) ∧
      rb.accounts = a0 ∧
      rb.tStorage = t0 ∧
      rb.toDelete = d0)
      (FRONT s.contexts) ∧
    (FST (LAST s.contexts)).logs = l0
End

Theorem handle_snd_split:
  (∀r' s'. f s = (r', s') ⇒ P s') ∧
  (∀e s' r'' s''. f s = (INR e, s') ∧ h e s' = (r'', s'') ⇒ P s'')
  ⇒ P (SND (handle f h s))
Proof
  rw[handle_def]
  \\ Cases_on `f s` \\ Cases_on `q` \\ gvs[]
  \\ first_x_assum irule
  \\ Cases_on `h y r` \\ gvs[]
  \\ metis_tac[]
QED

Theorem handle_isl_split:
  (∀x s'. f s = (INL x, s') ⇒ P) ∧
  (∀e s'. f s = (INR e, s') ⇒ ISL (FST (h e s')) ⇒ P)
  ⇒ ISL (FST (handle f h s)) ⇒ P
Proof
  rw[handle_def]
  \\ Cases_on `f s` \\ Cases_on `q` \\ gvs[]
QED

Theorem assert_not_static_static:
  q.msgParams.static ∧ s.contexts = (q,r)::t ⇒
  assert_not_static s = (INR (SOME WriteInStaticContext), s)
Proof
  rw[assert_not_static_def, bind_def, get_static_def,
     get_current_context_def, ok_state_def, return_def,
     assert_def, fail_def]
QED

(* ---- cp: context-preserving monadic property ---- *)

Definition cp_def:
  cp (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      s'.rollback.accounts = s.rollback.accounts ∧
      s'.rollback.tStorage = s.rollback.tStorage ∧
      s'.rollback.toDelete = s.rollback.toDelete ∧
      ∃q'. s'.contexts = (q', SND (HD s.contexts)) :: TL s.contexts ∧
           q'.msgParams = (FST (HD s.contexts)).msgParams ∧
           q'.logs = (FST (HD s.contexts)).logs
End

(* Composition lemmas *)
Theorem cp_bind[simp]:
  cp g ∧ (∀x. cp (f x)) ⇒ cp (bind g f)
Proof
  rw[cp_def, bind_def]
  \\ Cases_on `g s` \\ Cases_on `q` \\ gvs[]
  \\ res_tac \\ gvs[]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ res_tac \\ gvs[] \\ metis_tac[]
QED

Theorem cp_ignore_bind[simp]:
  cp g ∧ cp f ⇒ cp (ignore_bind g f)
Proof
  rw[ignore_bind_def] \\ irule cp_bind \\ simp[]
QED

Theorem cp_handle[simp]:
  cp f ∧ (∀e. cp (h e)) ⇒ cp (handle f h)
Proof
  rw[cp_def, handle_def]
  \\ Cases_on `f s` \\ Cases_on `q` \\ gvs[]
  \\ res_tac \\ gvs[]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h'` \\ gvs[]
  \\ res_tac \\ gvs[] \\ metis_tac[]
QED

Theorem cp_cond[simp]:
  cp m1 ∧ cp m2 ⇒ cp (if b then m1 else m2)
Proof
  rw[]
QED

Theorem cp_case_option[simp]:
  cp m_none ∧ (∀x. cp (m_some x)) ⇒
  cp (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` \\ rw[]
QED

Theorem cp_case_sum[simp]:
  (∀x. cp (f x)) ∧ (∀y. cp (g y)) ⇒
  cp (case s of INL x => f x | INR y => g y)
Proof
  Cases_on `s` \\ rw[]
QED

Theorem cp_case_pair[simp]:
  (∀x y. cp (f x y)) ⇒ cp (case p of (x, y) => f x y)
Proof
  Cases_on `p` \\ rw[]
QED

Theorem cp_let[simp]:
  (∀x. cp (f x)) ⇒ cp (let x = v in f x)
Proof
  rw[]
QED

Theorem cp_preserves_static_inv:
  cp m ∧ static_inv a0 t0 d0 s ⇒
  static_inv a0 t0 d0 (SND (m s))
Proof
  rw[cp_def, static_inv_def]
  \\ Cases_on `m s` \\ first_x_assum (qspecl_then [`s`, `q`, `r`] mp_tac)
  \\ rw[] \\ gvs[]
  \\ Cases_on `s.contexts` \\ gvs[listTheory.FRONT_DEF]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `t` \\ gvs[listTheory.FRONT_DEF]
QED

(* Paired version: when m s = (r, s'), static_inv transfers to s' *)
Theorem cp_preserves_static_inv_pair:
  cp m /\ static_inv a0 t0 d0 s /\ m s = (r, s') ==>
  static_inv a0 t0 d0 s'
Proof
  strip_tac
  \\ `static_inv a0 t0 d0 (SND (m s))` by metis_tac[cp_preserves_static_inv]
  \\ gvs[]
QED

(* General tactic for proving cp of leaf operations *)
val basic_defs = [bind_def, return_def, fail_def, assert_def,
  ignore_bind_def, reraise_def,
  get_current_context_def, set_current_context_def, ok_state_def];

val cp_tac = fn defs =>
  rw[cp_def] \\ rpt strip_tac
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ gvs (defs @ basic_defs)
  \\ rpt (BasicProvers.FULL_CASE_TAC \\ gvs[return_def]);



(* Leaf cp facts *)
Theorem cp_leaves[simp]:
  cp (return x) ∧ cp (fail e) ∧ cp (reraise (eo : exception option)) ∧ cp (assert b e) ∧
  cp (consume_gas n) ∧ cp (push_stack w) ∧ cp (pop_stack n) ∧
  cp (set_return_data rd) ∧ cp inc_pc ∧ cp finish ∧ cp revert ∧
  cp assert_not_static ∧
  cp (access_address a) ∧ cp (access_slot sk) ∧
  cp (set_jump_dest d) ∧ cp (update_gas_refund (a0, s0)) ∧
  cp (ensure_storage_in_domain a')
Proof
  rpt conj_tac
  \\ cp_tac [consume_gas_def, push_stack_def, pop_stack_def,
     set_return_data_def, inc_pc_def, finish_def, revert_def,
     assert_not_static_def, get_static_def,
     access_address_def, access_slot_def, domain_check_def,
     set_domain_def, set_jump_dest_def, update_gas_refund_def,
     ensure_storage_in_domain_def]
QED

(* Getters are cp (they just read state) *)
Theorem cp_getters[simp]:
  cp get_tx_params ∧ cp get_accounts ∧ cp get_rollback ∧
  cp get_current_code ∧ cp get_call_data ∧
  cp get_current_context ∧ cp get_callee ∧ cp get_caller ∧
  cp get_value ∧ cp get_num_contexts ∧ cp get_gas_left ∧
  cp get_static ∧ cp get_output_to ∧ cp get_return_data ∧
  cp get_tStorage
Proof
  rw[cp_def, get_tx_params_def, get_accounts_def, get_rollback_def,
     get_current_code_def, get_call_data_def,
     get_callee_def, get_caller_def, get_value_def,
     get_num_contexts_def, get_gas_left_def, get_static_def,
     get_output_to_def, get_return_data_def, get_tStorage_def,
     get_current_context_def, ok_state_def,
     return_def, bind_def, fail_def]
  \\ rpt strip_tac
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
QED

(* Memory operations are cp *)
Theorem cp_memory[simp]:
  cp (write_memory off ws) ∧ cp (read_memory off sz) ∧
  cp (expand_memory n) ∧ cp (memory_expansion_info off sz)
Proof
  rpt conj_tac
  \\ cp_tac [write_memory_def, read_memory_def, expand_memory_def,
     memory_expansion_info_def, expand_memory_def]
QED

(* get_context >> set_current_context preserving msgParams/logs is cp *)
Theorem cp_get_set_context:
  (∀ctxt. (f ctxt).msgParams = ctxt.msgParams) ∧
  (∀ctxt. (f ctxt).logs = ctxt.logs) ⇒
  cp (bind get_current_context (λctxt. set_current_context (f ctxt)))
Proof
  rw[cp_def, bind_def, get_current_context_def, ok_state_def,
     set_current_context_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem cp_get_cp_set_context:
  (∀ctxt. cp (g ctxt)) ∧
  (∀ctxt x. (f ctxt x).msgParams = ctxt.msgParams) ∧
  (∀ctxt x. (f ctxt x).logs = ctxt.logs) ⇒
  cp (bind get_current_context (λctxt. bind (g ctxt) (λx. set_current_context (f ctxt x))))
Proof
  rw[cp_def, bind_def, get_current_context_def, ok_state_def,
     set_current_context_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ Cases_on `g (FST h) s` \\ Cases_on `q` \\ gvs[]
  \\ (first_x_assum (qspec_then `FST h` mp_tac) \\ rw[cp_def]
      \\ res_tac \\ gvs[])
QED

(* Tactic for compound cp proofs: unfold def then repeatedly apply composition *)
val cp_simp_tac = fn defs =>
  rw defs
  \\ rpt (irule cp_bind \\ rw[]
          ORELSE irule cp_ignore_bind \\ rw[]
          ORELSE irule cp_handle \\ rw[]
          ORELSE irule cp_get_set_context \\ rw[]);

(* inc_pc_or_jump is cp *)
Theorem cp_inc_pc_or_jump[simp]:
  cp (inc_pc_or_jump op)
Proof
  rw[cp_def, inc_pc_or_jump_def, is_call_def] \\ rpt strip_tac
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ gvs[bind_def, get_current_context_def, ok_state_def, return_def,
         set_current_context_def, fail_def, assert_def]
  \\ Cases_on `h0.jumpDest`
  \\ gvs[set_current_context_def, bind_def, assert_def, return_def,
         ignore_bind_def, fail_def]
  \\ BasicProvers.FULL_CASE_TAC \\ gvs[]
QED

Theorem cp_unuse_gas[simp]:
  cp (unuse_gas n)
Proof
  cp_tac [unuse_gas_def]
QED

(* Composition: cp prefix + static_inv-preserving continuation *)
Theorem static_inv_bind_cp:
  cp g /\ (!x s. static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
                  static_inv a0 t0 d0 (SND (f x s))) /\
  static_inv a0 t0 d0 s ==>
  static_inv a0 t0 d0 (SND (bind g f s))
Proof
  strip_tac
  \\ `s.contexts <> []` by fs[static_inv_def]
  \\ simp[bind_def]
  \\ Cases_on `g s` \\ Cases_on `q` \\ gvs[]
  >- (`static_inv a0 t0 d0 r` by metis_tac[cp_preserves_static_inv_pair]
      \\ `r.contexts <> []` by fs[static_inv_def]
      \\ metis_tac[])
  >- metis_tac[cp_preserves_static_inv_pair]
QED

(* Variant for ignore_bind *)
Theorem static_inv_ignore_bind_cp:
  cp g /\ (!s. static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
               static_inv a0 t0 d0 (SND (f s))) /\
  static_inv a0 t0 d0 s ==>
  static_inv a0 t0 d0 (SND (ignore_bind g f s))
Proof
  rw[ignore_bind_def] \\ irule static_inv_bind_cp \\ simp[]
  \\ metis_tac[]
QED

(* LET variant *)
Theorem static_inv_let:
  (!x. static_inv a0 t0 d0 (SND (f x s))) ==>
  static_inv a0 t0 d0 (SND ((let x = v in f x) s))
Proof
  rw[]
QED

(* Cond variant *)
Theorem static_inv_cond:
  static_inv a0 t0 d0 (SND (f1 s)) /\
  static_inv a0 t0 d0 (SND (f2 s)) ==>
  static_inv a0 t0 d0 (SND ((if b then f1 else f2) s))
Proof
  rw[]
QED

(* Under static_inv, bind assert_not_static f preserves inv (fails before f runs) *)
Theorem static_inv_assert_not_static:
  static_inv a0 t0 d0 s ==>
  static_inv a0 t0 d0 (SND (bind assert_not_static f s))
Proof
  strip_tac
  \\ `s.contexts <> []` by fs[static_inv_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h`
  \\ `h0.msgParams.static` by gvs[static_inv_def]
  \\ simp[bind_def, assert_not_static_def, get_static_def,
          get_current_context_def, ok_state_def, return_def,
          assert_def, fail_def]
QED

(* ignore_bind variant *)
Theorem static_inv_ignore_bind_assert:
  static_inv a0 t0 d0 s ==>
  static_inv a0 t0 d0 (SND (ignore_bind assert_not_static f s))
Proof
  rw[ignore_bind_def]
  \\ irule static_inv_assert_not_static \\ simp[]
QED

(* When cp g and static_inv, bind g (.. assert_not_static ..) preserves inv *)
Theorem cp_then_static_fail:
  cp g ∧ static_inv a0 t0 d0 s ⇒
  ¬ISL (FST (bind g (λx. bind assert_not_static (f x)) s)) ∧
  static_inv a0 t0 d0 (SND (bind g (λx. bind assert_not_static (f x)) s))
Proof
  rpt strip_tac
  \\ simp[bind_def]
  \\ Cases_on `g s` \\ Cases_on `q` \\ gvs[]
  \\ `s.contexts ≠ []` by fs[static_inv_def]
  \\ fs[cp_def] \\ first_x_assum drule_all \\ strip_tac \\ gvs[]
  \\ fs[assert_not_static_def, bind_def, get_static_def,
        get_current_context_def, ok_state_def, return_def,
        fail_def, assert_def, ignore_bind_def]
  \\ fs[static_inv_def] \\ gvs[listTheory.FRONT_DEF]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `t` \\ gvs[listTheory.FRONT_DEF]
QED


Theorem cp_precompiles[simp]:
  cp precompile_ecrecover ∧
  cp precompile_sha2_256 ∧
  cp precompile_ripemd_160 ∧
  cp precompile_identity ∧
  cp precompile_modexp ∧
  cp precompile_ecadd ∧
  cp precompile_ecmul ∧
  cp precompile_ecpairing ∧
  cp precompile_blake2f ∧
  cp precompile_point_eval ∧
  cp precompile_bls_g1add ∧
  cp precompile_bls_g1msm ∧
  cp precompile_bls_g2add ∧
  cp precompile_bls_g2msm ∧
  cp precompile_bls_pairing ∧
  cp precompile_bls_map_fp_to_g1 ∧
  cp precompile_bls_map_fp2_to_g2 ∧
  cp precompile_p256verify
Proof
  rpt conj_tac
  \\ rw[precompile_ecrecover_def, precompile_sha2_256_def,
        precompile_ripemd_160_def, precompile_identity_def,
        precompile_modexp_def, precompile_ecadd_def,
        precompile_ecmul_def, precompile_ecpairing_def,
        precompile_blake2f_def, precompile_point_eval_def,
        precompile_bls_g1add_def, precompile_bls_g1msm_def,
        precompile_bls_g2add_def, precompile_bls_g2msm_def,
        precompile_bls_pairing_def, precompile_bls_map_fp_to_g1_def,
        precompile_bls_map_fp2_to_g2_def, precompile_p256verify_def,
        LET_THM]
  \\ rpt (irule cp_bind \\ rw[] \\ rpt (irule cp_ignore_bind \\ rw[]))
QED

Theorem cp_dispatch_precompiles[simp]:
  cp (dispatch_precompiles addr)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem cp_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ cp f) ⇒
  cp (copy_to_memory gas off srcOff sz src)
Proof
  Cases_on `src`
  \\ rw[copy_to_memory_def, LET_THM]
  >- (pairarg_tac \\ rw[])
  \\ cp_simp_tac []
QED

Theorem cp_get_code[simp]:
  cp (get_code addr)
Proof
  cp_simp_tac [get_code_def]
QED

Theorem cp_get_return_data_check[simp]:
  cp (get_return_data_check off sz)
Proof
  cp_simp_tac [get_return_data_check_def]
QED

Theorem cp_get_original[simp]:
  cp get_original
Proof
  rw[cp_def, get_original_def, return_def, fail_def]
  \\ rpt strip_tac \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
QED


Theorem cp_step_sstore_gas[simp]:
  cp (step_sstore_gas_consumption addr key value)
Proof
  cp_simp_tac [step_sstore_gas_consumption_def]
QED

Theorem cp_step_helpers[simp]:
  cp step_mload ∧ cp step_keccak256 ∧
  cp step_ext_code_copy ∧ cp step_return_data_copy ∧
  (∀t. cp (step_sload t)) ∧
  (∀b. cp (step_return b))
Proof
  rpt conj_tac
  \\ cp_simp_tac [step_mload_def, step_keccak256_def,
                  step_ext_code_copy_def, step_return_data_copy_def,
                  step_sload_def, step_return_def]
QED

Theorem cp_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ cp f) ⇒
  cp (step_copy_to_memory op src)
Proof
  rw[step_copy_to_memory_def]
  \\ rpt (irule cp_bind \\ rw[]
          ORELSE irule cp_ignore_bind \\ rw[])
QED

Theorem cp_step_swap[simp]:
  ∀n. cp (step_swap n)
Proof
  cp_tac [step_swap_def, consume_gas_def]
QED

(* All non-guarded, non-call step_inst ops are cp *)
Theorem cp_step_inst_non_call[simp]:
  op ≠ SStore ∧ op ≠ TStore ∧ (∀n. op ≠ Log n) ∧
  op ≠ SelfDestruct ∧ op ≠ Create ∧ op ≠ Create2 ∧
  op ≠ Call ∧ op ≠ CallCode ∧ op ≠ DelegateCall ∧ op ≠ StaticCall
  ⇒ cp (step_inst op)
Proof
  Cases_on `op` \\ rw[step_inst_def]
  \\ TRY (cp_simp_tac [step_binop_def, step_monop_def, step_modop_def,
    step_context_def, step_msgParams_def, step_txParams_def,
    step_exp_def, step_balance_def, step_call_data_load_def,
    step_ext_code_size_def, step_ext_code_hash_def,
    step_block_hash_def, step_blob_hash_def, step_self_balance_def,
    step_mstore_def, step_jump_def, step_jumpi_def,
    step_push_def, step_dup_def, step_pop_def, step_invalid_def])
QED

(* When f returns INR, projections of handle f h s equal projections of h e s' *)
Theorem handle_INR_eq:
  f s = (INR e, s') ==> handle f h s = h e s'
Proof
  rw[handle_def]
QED

Theorem handle_INR_snd:
  f s = (INR e, s') ==> SND (handle f h s) = SND (h e s')
Proof
  rw[handle_def]
QED

Theorem handle_INR_fst:
  f s = (INR e, s') ==> FST (handle f h s) = FST (h e s')
Proof
  rw[handle_def]
QED

(* When outputTo ≠ Code for current context, handle_create just reraises *)
Theorem handle_create_reraises:
  (∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a) ∧
  s.contexts ≠ [] ⇒
  handle_create e s = reraise e s
Proof
  rw[handle_create_def, bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, ok_state_def,
     return_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `h0.msgParams.outputTo` \\ gvs[]
QED

(* push_logs [] is cp — callee had no logs under invariant *)
Theorem cp_push_logs_nil:
  cp (push_logs [])
Proof
  rw[cp_def, push_logs_def, bind_def, get_current_context_def,
     ok_state_def, set_current_context_def, return_def, fail_def]
  \\ rpt strip_tac \\ Cases_on `s.contexts` \\ gvs[]
QED

(* after_pop is cp *)
Theorem cp_after_pop[simp]:
  cp (after_pop a b c)
Proof
  rw[after_pop_def]
  \\ CASE_TAC \\ rpt (irule cp_bind \\ rw[]
    ORELSE irule cp_ignore_bind \\ rw[])
  \\ CASE_TAC \\ rpt (irule cp_bind \\ rw[]
    ORELSE irule cp_ignore_bind \\ rw[])
QED

(* Abbreviation for the 5 conclusions we need *)
val static_conclusions = ``\a0 t0 d0 f s.
  (SND (f s)).rollback.accounts = a0 /\
  (SND (f s)).rollback.tStorage = t0 /\
  (SND (f s)).rollback.toDelete = d0 /\
  EVERY (\(ctxt,rb). ctxt.msgParams.static /\ ctxt.logs = [] /\
    !a. ctxt.msgParams.outputTo <> Code a) (SND (f s)).contexts /\
  (ISL (FST (f s)) ==> static_inv a0 t0 d0 (SND (f s)))``;

(* The cp prefix of handle_exception *)
Theorem cp_handle_exception_prefix:
  cp (if ~success /\ e <> SOME Reverted then
        ignore_bind (bind get_gas_left
          (\gasLeft. ignore_bind (consume_gas gasLeft)
            (set_return_data []))) (return ())
      else return ())
Proof
  rw[]
QED

(* Decompose handle_exception into cp prefix + handle_ex_helper *)
Theorem handle_exception_decomp:
  handle_exception e s =
  (let prefix = (if ~(e = NONE) /\ e <> SOME Reverted then
     do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
   else return ()) in
   bind prefix (\u. handle_ex_helper e) s)
Proof
  simp[handle_exception_def, handle_ex_helper_def, LET_THM,
       bind_def, ignore_bind_def, after_pop_def,
       get_num_contexts_def, get_return_data_def, get_output_to_def,
       get_current_context_def, ok_state_def, return_def, fail_def,
       get_gas_left_def, consume_gas_def, set_return_data_def,
       pop_and_incorporate_context_def, pop_context_def,
       set_rollback_def, push_logs_def, set_current_context_def,
       update_gas_refund_def, inc_pc_def, push_stack_def,
       write_memory_def, expand_memory_def, read_memory_def,
       pop_stack_def, unuse_gas_def, reraise_def, assert_def]
QED

(* pop_and_incorporate_context preserves rollback fields under static_inv *)
Theorem pop_incorporate_static:
  static_inv a0 t0 d0 s /\ 1 < LENGTH s.contexts ==>
  let s1 = SND (pop_and_incorporate_context success s) in
    s1.contexts <> [] /\
    s1.rollback.accounts = a0 /\
    s1.rollback.tStorage = t0 /\
    s1.rollback.toDelete = d0 /\
    EVERY (\(ctxt,rb). ctxt.msgParams.static /\ ctxt.logs = [] /\
      !a. ctxt.msgParams.outputTo <> Code a) s1.contexts /\
    EVERY (\(ctxt,rb).
      rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0)
      (FRONT s1.contexts)
Proof
  strip_tac
  \\ fs[static_inv_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `t` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ simp[pop_and_incorporate_context_def, bind_def,
          get_gas_left_def, get_current_context_def, ok_state_def,
          return_def, pop_context_def, unuse_gas_def, LET_THM,
          set_current_context_def, fail_def, assert_def,
          ignore_bind_def]
  \\ rpt (CASE_TAC \\ gvs[return_def])
  \\ simp[push_logs_def, bind_def, get_current_context_def, ok_state_def,
          set_current_context_def, return_def,
          update_gas_refund_def, set_rollback_def]
  \\ gvs[listTheory.FRONT_DEF]
  \\ rw[] \\ gvs[]
QED

(* handle_ex_helper preserves static_inv properties *)
Theorem handle_ex_helper_static_inv:
  static_inv a0 t0 d0 s ==>
  (SND (handle_ex_helper e s)).rollback.accounts = a0 /\
  (SND (handle_ex_helper e s)).rollback.tStorage = t0 /\
  (SND (handle_ex_helper e s)).rollback.toDelete = d0 /\
  EVERY (\(ctxt, rb).
    ctxt.msgParams.static /\
    ctxt.logs = [] /\
    (!a. ctxt.msgParams.outputTo <> Code a)) (SND (handle_ex_helper e s)).contexts /\
  (ISL (FST (handle_ex_helper e s)) ==>
   static_inv a0 t0 d0 (SND (handle_ex_helper e s)))
Proof
  strip_tac
  \\ `s.contexts <> []` by fs[static_inv_def]
  \\ simp[handle_ex_helper_def, bind_def,
          get_num_contexts_def, get_current_context_def, ok_state_def,
          return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `t`
  >- (
    simp[reraise_def]
    \\ gvs[static_inv_def])
  \\ simp[]
  \\ simp[bind_def, get_return_data_def, get_output_to_def,
          get_current_context_def, ok_state_def, return_def,
          ignore_bind_def]
  \\ `1 < LENGTH s.contexts` by gvs[]
  \\ `static_inv a0 t0 d0 (SND (pop_and_incorporate_context (e = NONE) s))`
     by (drule_all pop_incorporate_static
         \\ simp[LET_THM, static_inv_def])
  \\ Cases_on `pop_and_incorporate_context (e = NONE) s`
  \\ Cases_on `q` \\ simp[]
  >- (
    gvs[]
    \\ `static_inv a0 t0 d0 (SND (after_pop h0.returnData
       h0.msgParams.outputTo (e = NONE) r))` by
      metis_tac[cp_preserves_static_inv, cp_after_pop]
    \\ fs[static_inv_def])
  >- gvs[static_inv_def]
QED

(* handle_exception preserves static_inv *)
Theorem handle_exception_static_inv:
  static_inv a0 t0 d0 s ==>
  (SND (handle_exception e s)).rollback.accounts = a0 /\
  (SND (handle_exception e s)).rollback.tStorage = t0 /\
  (SND (handle_exception e s)).rollback.toDelete = d0 /\
  EVERY (\(ctxt, rb).
    ctxt.msgParams.static /\
    ctxt.logs = [] /\
    (!a. ctxt.msgParams.outputTo <> Code a)) (SND (handle_exception e s)).contexts /\
  (ISL (FST (handle_exception e s)) ==>
   static_inv a0 t0 d0 (SND (handle_exception e s)))
Proof
  strip_tac
  \\ `s.contexts <> []` by fs[static_inv_def]
  \\ qabbrev_tac `prefix = (if e <> NONE /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else return ())`
  \\ `cp prefix` by
    (simp[Abbr `prefix`] \\ rw[]
     \\ irule cp_ignore_bind \\ rw[]
     \\ irule cp_bind \\ rw[]
     \\ irule cp_ignore_bind \\ rw[])
  \\ `handle_exception e s = bind prefix (\u. handle_ex_helper e) s`
     by simp[Abbr `prefix`, handle_exception_decomp]
  \\ pop_assum (fn th => REWRITE_TAC [th])
  \\ simp[bind_def]
  \\ `static_inv a0 t0 d0 (SND (prefix s))` by
    metis_tac[cp_preserves_static_inv]
  \\ Cases_on `prefix s` \\ Cases_on `q` \\ gvs[]
  >- metis_tac[handle_ex_helper_static_inv]
  >- fs[static_inv_def]
QED

(* handle_step preserves static_inv conditions *)
Theorem handle_step_static_inv:
  static_inv a0 t0 d0 s ==>
  (SND (handle_step e s)).rollback.accounts = a0 /\
  (SND (handle_step e s)).rollback.tStorage = t0 /\
  (SND (handle_step e s)).rollback.toDelete = d0 /\
  EVERY (\(ctxt, rb).
    ctxt.msgParams.static /\
    ctxt.logs = [] /\
    (!a. ctxt.msgParams.outputTo <> Code a)) (SND (handle_step e s)).contexts /\
  (ISL (FST (handle_step e s)) ==>
   static_inv a0 t0 d0 (SND (handle_step e s)))
Proof
  strip_tac
  \\ `s.contexts <> []` by fs[static_inv_def]
  \\ `(!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a)` by
    (fs[static_inv_def] \\ Cases_on `s.contexts` \\ gvs[]
     \\ PairCases_on `h` \\ gvs[])
  \\ simp[handle_step_def]
  \\ IF_CASES_TAC
  >- (simp[reraise_def] \\ fs[static_inv_def])
  \\ simp[]
  \\ `(handle_create e : unit execution) s = reraise e s` by
    metis_tac[INST_TYPE [alpha |-> ``:unit``] handle_create_reraises]
  \\ `SND (handle (handle_create e) handle_exception s) =
      SND (handle_exception e s) /\
      FST (handle (handle_create e) handle_exception s) =
      FST (handle_exception e s)` by
    simp[reraise_def, handle_def]
  \\ simp[]
  \\ metis_tac[handle_exception_static_inv]
QED

(* Lifting lemma: if inner preserves static_inv, then handle inner handle_step
   gives all 5 properties needed for step_preserves_static_inv_every *)
Theorem handle_step_lift:
  (!r s'. inner s0 = (r, s') ==> static_inv a0 t0 d0 s') ==>
  static_inv a0 t0 d0 s0 ==>
  (SND (handle (inner:unit execution) handle_step s0)).rollback.accounts = a0 /\
  (SND (handle inner handle_step s0)).rollback.tStorage = t0 /\
  (SND (handle inner handle_step s0)).rollback.toDelete = d0 /\
  EVERY (\(ctxt, rb). ctxt.msgParams.static /\ ctxt.logs = [] /\
    (!a. ctxt.msgParams.outputTo <> Code a))
    (SND (handle inner handle_step s0)).contexts /\
  (ISL (FST (handle inner handle_step s0)) ==>
   static_inv a0 t0 d0 (SND (handle inner handle_step s0)))
Proof
  strip_tac \\ strip_tac
  \\ simp[handle_def]
  \\ Cases_on `inner s0` \\ Cases_on `q` \\ fs[]
  >- fs[static_inv_def]
  >- (imp_res_tac handle_step_static_inv \\ fs[])
QED

(* LET with UNCURRY (for tuple let-bindings like (a,b) <<- expr) *)
Theorem static_inv_let_uncurry:
  (!a b. static_inv a0 t0 d0 (SND (f a b s))) ==>
  static_inv a0 t0 d0 (SND (LET (UNCURRY (\a b. f a b)) v s))
Proof
  Cases_on `v` \\ simp[]
QED

(* Direct UNCURRY application (after LET reduction) *)
Theorem static_inv_uncurry:
  (!a b. static_inv a0 t0 d0 (SND (f a b s))) ==>
  static_inv a0 t0 d0 (SND (UNCURRY f p s))
Proof
  Cases_on `p` \\ simp[]
QED

(* ignore_bind where first op is conditional assert_not_static.
   When b=T, assert_not_static fails under static_inv (state unchanged).
   When b=F, return () is a no-op and we continue with ~b available. *)
Theorem static_inv_ignore_bind_assert_cond:
  static_inv a0 t0 d0 s /\
  (~b ==> static_inv a0 t0 d0 (SND (f s))) ==>
  static_inv a0 t0 d0
    (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  Cases_on `b` \\ strip_tac
  >- (rw[ignore_bind_def]
      \\ irule static_inv_assert_not_static \\ simp[])
  >- gvs[ignore_bind_def, bind_def, return_def]
QED

(* Tactic: step through a monadic chain under static_inv.
   Repeatedly decomposes bind/ignore_bind/let/cond into cp prefix + rest,
   stopping when it hits assert_not_static (which kills the chain). *)
(* Solve trivial subgoals from irule: cp facts + assumptions *)
val solve_side = simp[] ORELSE first_assum ACCEPT_TAC;
val static_inv_step =
  rpt (CHANGED_TAC (
    irule static_inv_assert_not_static
    ORELSE irule static_inv_ignore_bind_assert
    ORELSE (irule static_inv_ignore_bind_assert_cond \\ conj_tac
            >- first_assum ACCEPT_TAC \\ strip_tac)
    ORELSE (irule static_inv_uncurry \\ rpt strip_tac)
    ORELSE (irule static_inv_bind_cp \\ TRY solve_side
            \\ TRY (simp[pairTheory.FORALL_PROD] \\ rpt strip_tac))
    ORELSE (irule static_inv_ignore_bind_cp \\ TRY solve_side
            \\ TRY (rpt strip_tac))
    ORELSE (irule static_inv_let_uncurry \\ TRY (rpt strip_tac))
    ORELSE (irule static_inv_let \\ TRY (rpt strip_tac))
    ORELSE (irule static_inv_cond)
    ORELSE solve_side));

(* Guarded ops all have: cp_prefix >> assert_not_static >> rest *)
Theorem guarded_op_preserves_static_inv:
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 (SND (step_sstore transient s)) /\
  static_inv a0 t0 d0 (SND (step_log n s)) /\
  static_inv a0 t0 d0 (SND (step_self_destruct s)) /\
  static_inv a0 t0 d0 (SND (step_create two s))
Proof
  strip_tac \\ rpt conj_tac
  \\ simp[step_sstore_def, step_log_def,
       step_self_destruct_def, step_create_def]
  \\ static_inv_step
QED

(* proceed_call preserves static_inv when:
   - value = 0 or op = CallCode (so update_accounts is skipped)
   - subStatic = T (so new context is static)
   - outputTo = Memory mr (so outputTo <> Code) *)
Theorem static_inv_push_context:
  static_inv a0 t0 d0 s /\ s.contexts <> [] /\
  ctxt.msgParams.static /\ ctxt.logs = [] /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\
  rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0 ==>
  static_inv a0 t0 d0 (SND (push_context (ctxt, rb) s))
Proof
  rw[static_inv_def, push_context_def, return_def]
  \\ gvs[listTheory.FRONT_DEF]
QED

(* Composition: push_context followed by cp suffix *)
Theorem static_inv_ignore_bind_push_context:
  cp f /\
  ctxt.msgParams.static /\ ctxt.logs = [] /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\
  rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0 /\
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 (SND (ignore_bind (push_context (ctxt, rb)) f s))
Proof
  strip_tac
  \\ simp[ignore_bind_def, bind_def, push_context_def, return_def]
  \\ irule cp_preserves_static_inv \\ simp[]
  \\ rw[static_inv_def, listTheory.FRONT_DEF]
  \\ Cases_on `s.contexts` \\ gvs[static_inv_def]
QED

Theorem proceed_call_preserves_static_inv:
  static_inv a0 t0 d0 s /\ s.contexts <> [] /\
  (value = 0 \/ op = CallCode) ==>
  static_inv a0 t0 d0
    (SND (proceed_call op sender address value
       argsOff argsSize code stipend (Memory mr) s))
Proof
  strip_tac
  \\ `?ctxt rb. HD s.contexts = (ctxt, rb)` by metis_tac[pairTheory.PAIR]
  \\ simp[proceed_call_def, bind_def, ignore_bind_def, return_def,
          get_rollback_def, read_memory_def,
          get_caller_def, get_value_def, get_static_def,
          get_current_context_def, ok_state_def,
          push_context_def,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ irule cp_preserves_static_inv \\ simp[]
  \\ rw[static_inv_def, listTheory.FRONT_DEF]
  \\ gvs[static_inv_def, listTheory.FRONT_DEF]
QED

Theorem cp_abort_call_value[simp]:
  cp (abort_call_value n)
Proof
  cp_simp_tac [abort_call_value_def]
QED

Theorem cp_abort_unuse[simp]:
  cp (abort_unuse n)
Proof
  cp_simp_tac [abort_unuse_def]
QED

(*
  step_call proof strategy:
  - For op=Call: assert_not_static always fails under static_inv,
    so the entire continuation after it is dead code. The cp prefix
    before assert_not_static preserves static_inv.
  - For op<>Call: the guard simplifies to return() (no-op),
    and proceed_call has value=0 or op=CallCode.
*)
Theorem step_call_Call_static:
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 (SND (step_call Call s))
Proof
  strip_tac
  \\ simp[step_call_def, call_has_value_def]
  \\ irule static_inv_bind_cp \\ simp[]
  \\ rpt strip_tac
  \\ Cases_on `w2n (EL 2 x) = 0`
  >- (
    simp[]
    \\ static_inv_step
    \\ rpt conj_tac
    \\ TRY (irule cp_preserves_static_inv \\ simp[] \\ NO_TAC)
    \\ irule proceed_call_preserves_static_inv
    \\ simp[call_has_value_def]
  )
  >- (
    `0 < w2n (EL 2 x)` by simp[]
    \\ simp[]
    \\ static_inv_step
  )
QED

Theorem step_call_nonCall_static:
  op <> Call ==>
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 (SND (step_call op s))
Proof
  strip_tac \\ strip_tac
  \\ simp[step_call_def]
  \\ static_inv_step
  \\ rpt conj_tac
  \\ TRY (irule cp_preserves_static_inv \\ simp[] \\ NO_TAC)
  \\ static_inv_step
  \\ rpt conj_tac
  \\ TRY (irule cp_preserves_static_inv \\ simp[] \\ NO_TAC)
  \\ irule proceed_call_preserves_static_inv
  \\ simp[call_has_value_def]
  \\ Cases_on `op = CallCode` \\ simp[]
QED

Theorem step_call_preserves_static_inv:
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 (SND (step_call op s))
Proof
  strip_tac \\ Cases_on `op = Call`
  >- (gvs[] \\ irule step_call_Call_static \\ gvs[])
  >- (irule step_call_nonCall_static \\ gvs[])
QED

Theorem step_inst_preserves_static_inv:
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 (SND (step_inst op s))
Proof
  strip_tac \\ Cases_on `op`
  (* cp ops: don't expand step_inst_def, use cp_step_inst_non_call[simp] *)
  \\ TRY (irule cp_preserves_static_inv \\ simp[] \\ NO_TAC)
  (* Guarded ops: expand and use static_inv_step *)
  \\ TRY (simp[step_inst_def, step_sstore_def, step_log_def,
               step_self_destruct_def, step_create_def]
          \\ static_inv_step \\ NO_TAC)
  (* Call ops *)
  \\ simp[step_inst_def]
  \\ irule step_call_preserves_static_inv \\ gvs[]
QED

Theorem inner_preserves_static_inv:
  static_inv a0 t0 d0 s /\ s.contexts <> [] ==>
  !r s'. (do
    ctxt <- get_current_context;
    if LENGTH ctxt.msgParams.code <= ctxt.pc then step_inst Stop
    else case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
           NONE => step_inst Invalid
         | SOME op => do step_inst op; inc_pc_or_jump op od
  od) s = (r, s') ==>
  static_inv a0 t0 d0 s'
Proof
  rpt strip_tac
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h`
  \\ gvs[bind_def, get_current_context_def, ok_state_def, return_def]
  \\ Cases_on `LENGTH h0.msgParams.code <= h0.pc` \\ gvs[]
  >- (`cp (step_inst Stop)` by simp[]
      \\ metis_tac[cp_preserves_static_inv_pair])
  \\ Cases_on `FLOOKUP h0.msgParams.parsed h0.pc` \\ gvs[]
  >- (`cp (step_inst Invalid)` by simp[]
      \\ metis_tac[cp_preserves_static_inv_pair])
  \\ gvs[ignore_bind_def, bind_def]
  \\ `static_inv a0 t0 d0 (SND (step_inst x s))`
       by (irule step_inst_preserves_static_inv \\ gvs[])
  \\ Cases_on `step_inst x s` \\ Cases_on `q` \\ gvs[]
  >- metis_tac[cp_preserves_static_inv_pair, cp_inc_pc_or_jump]
QED

Theorem step_preserves_static_inv_every:
  static_inv a0 t0 d0 s0 ==>
  (SND (step s0)).rollback.accounts = a0 /\
  (SND (step s0)).rollback.tStorage = t0 /\
  (SND (step s0)).rollback.toDelete = d0 /\
  EVERY (\(ctxt, rb).
    ctxt.msgParams.static /\
    ctxt.logs = [] /\
    (!a. ctxt.msgParams.outputTo <> Code a)) (SND (step s0)).contexts /\
  (ISL (FST (step s0)) ==> static_inv a0 t0 d0 (SND (step s0)))
Proof
  strip_tac
  \\ `s0.contexts <> []` by fs[static_inv_def]
  \\ `step s0 = handle (do
       ctxt <- get_current_context;
       code <<- ctxt.msgParams.code;
       parsed <<- ctxt.msgParams.parsed;
       if LENGTH code <= ctxt.pc then step_inst Stop
       else case FLOOKUP parsed ctxt.pc of
              NONE => step_inst Invalid
            | SOME op => do step_inst op; inc_pc_or_jump op od od)
       handle_step s0`
     by simp[step_def]
  \\ pop_assum (fn th => REWRITE_TAC[th])
  \\ irule handle_step_lift \\ simp[]
  \\ metis_tac[inner_preserves_static_inv]
QED

Theorem run_tr_preserves_static_inv:
  ∀r s. static_inv a0 t0 d0 s ⇒
  (SND (run_tr (r, s))).rollback.accounts = a0 ∧
  (SND (run_tr (r, s))).rollback.tStorage = t0 ∧
  (SND (run_tr (r, s))).rollback.toDelete = d0 ∧
  EVERY (λ(ctxt, rb).
    ctxt.msgParams.static ∧
    ctxt.logs = [] ∧
    (∀a. ctxt.msgParams.outputTo ≠ Code a)) (SND (run_tr (r, s))).contexts
Proof
  recInduct run_tr_ind
  \\ gen_tac \\ gen_tac \\ strip_tac \\ strip_tac
  \\ once_rewrite_tac[run_tr_def]
  \\ reverse (Cases_on `r`) >- fs[static_inv_def]
  \\ simp[]
  \\ drule step_preserves_static_inv_every
  \\ Cases_on `step s` \\ Cases_on `q`
  \\ gvs[] \\ strip_tac
  \\ once_rewrite_tac[run_tr_def] \\ simp[]
QED

Theorem run_static_preserves:
  ∀es result final_state ctxt rb.
    run es = SOME (INR result, final_state) ∧
    es.contexts = [(ctxt, rb)] ∧
    ctxt.msgParams.static ⇒
    final_state.rollback.accounts = es.rollback.accounts ∧
    final_state.rollback.tStorage = es.rollback.tStorage ∧
    final_state.rollback.toDelete = es.rollback.toDelete ∧
    (case final_state.contexts of
       [(ctxt', _)] => ctxt'.logs = ctxt.logs
     | _ => T)
Proof
  rw[run_eq_tr]
  \\ `static_inv es.rollback.accounts es.rollback.tStorage
        es.rollback.toDelete es` by
    rw[static_inv_def, listTheory.FRONT_DEF]
  \\ first_assum (mp_tac o MATCH_MP
       (Q.SPEC `INL ()` run_tr_preserves_static_inv))
  \\ once_rewrite_tac[run_tr_def] \\ simp[]
  \\ Cases_on `run_tr (step es)` \\ gvs[]
  \\ strip_tac
  \\ Cases_on `final_state.contexts` \\ gvs[]
  \\ Cases_on `h` \\ Cases_on `t` \\ gvs[]
QED
