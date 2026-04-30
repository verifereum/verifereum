Theory vfmStaticCalls
Ancestors
  pair
  vfmExecution vfmDecreasesGas vfmExecutionProp vfmPreserves

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
    EVERY (λ(ctxt, rb). ctxt.msgParams.static ∧
      (∀a. ctxt.msgParams.outputTo ≠ Code a)) s.contexts ∧
    EVERY (λ(ctxt, rb).
      ctxt.logs = [] ∧
      rb.accounts = a0 ∧ rb.tStorage = t0 ∧ rb.toDelete = d0)
      (FRONT s.contexts) ∧
    (FST (LAST s.contexts)).logs = l0
End

Theorem handle_snd_split:
  (∀r' s'. f s = (r', s') ⇒ P s') ∧
  (∀e s' r'' s''. f s = (INR e, s') ∧ h e s' = (r'', s'') ⇒ P s'')
  ⇒ P (SND (handle f h s))
Proof
  rw[handle_def]
  >> Cases_on `f s` >> Cases_on `q` >> gvs[]
  >> first_x_assum irule
  >> Cases_on `h y r` >> gvs[]
  >> metis_tac[]
QED

Theorem handle_isl_split:
  (∀x s'. f s = (INL x, s') ⇒ P) ∧
  (∀e s'. f s = (INR e, s') ⇒ ISL (FST (h e s')) ⇒ P)
  ⇒ ISL (FST (handle f h s)) ⇒ P
Proof
  rw[handle_def]
  >> Cases_on `f s` >> Cases_on `q` >> gvs[]
QED

Theorem assert_not_static_static:
  q.msgParams.static ∧ s.contexts = (q,r)::t ⇒
  assert_not_static s = (INR (SOME WriteInStaticContext), s)
Proof
  rw[assert_not_static_def, bind_def, get_static_def,
     get_current_context_def, return_def,
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

(* ================================================================== *)
(* cp_rel: the state relation underlying cp.                           *)
(*                                                                    *)
(* cp_rel captures exactly what cp says: rollback.accounts, tStorage,  *)
(* and toDelete are preserved, the head context agrees on msgParams  *)
(* and logs, and the tail is unchanged. NOTE: cp_rel does NOT        *)
(* preserve rollback.accesses — operations like access_address and  *)
(* access_slot modify accesses while being cp.                         *)
(* ================================================================== *)

Definition cp_rel_def:
  cp_rel s s' ⇔
    s'.rollback.accounts = s.rollback.accounts ∧
    s'.rollback.tStorage = s.rollback.tStorage ∧
    s'.rollback.toDelete = s.rollback.toDelete ∧
    (s.contexts ≠ [] ⇒
      ∃q'. s'.contexts = (q', SND (HD s.contexts)) :: TL s.contexts ∧
           q'.msgParams = (FST (HD s.contexts)).msgParams ∧
           q'.logs = (FST (HD s.contexts)).logs)
End

Theorem cp_eq_preserves_when:
  cp m ⇔ preserves_when (λs. s.contexts ≠ []) cp_rel m
Proof
  rw[cp_def, preserves_when_def, cp_rel_def]
QED

(* ================================================================== *)
(* Reflexivity and transitivity of cp_rel.                             *)
(* Needed for the generic preserves_when composition lemmas.          *)
(* ================================================================== *)

Theorem cp_rel_refl:
  s.contexts ≠ [] ⇒ cp_rel s s
Proof
  rw[cp_rel_def]
  >> qexists_tac `FST (HD s.contexts)` >> simp[GSYM PAIR]
QED

Theorem cp_rel_trans:
  cp_rel s1 s2 ∧ cp_rel s2 s3 ⇒ cp_rel s1 s3
Proof
  rw[cp_rel_def]
  >> first_x_assum drule >> rw[] >> gvs[]
QED

(* cp_rel preserves non-empty contexts (precondition transfer).       *)
Theorem cp_rel_contexts_ne:
  s.contexts ≠ [] ∧ cp_rel s s' ⇒ s'.contexts ≠ []
Proof
  rw[cp_rel_def] >> gvs[]
QED

(* Composition lemmas (derived from the generic preserves_when     *)
(* framework via cp_eq_preserves_when + cp_rel_trans / cp_rel_refl / *)
(* cp_rel_contexts_ne).                                            *)
Theorem cp_bind[simp]:
  cp g ∧ (∀x. cp (f x)) ⇒ cp (bind g f)
Proof
  rw[cp_eq_preserves_when]
  >> match_mp_tac preserves_when_bind
  >> rw[]
  >> TRY(drule_all cp_rel_contexts_ne >> rw[] >> NO_TAC)
  >> irule cp_rel_trans >> metis_tac[]
QED

Theorem cp_ignore_bind[simp]:
  cp g ∧ cp f ⇒ cp (ignore_bind g f)
Proof
  rw[cp_eq_preserves_when]
  >> match_mp_tac preserves_when_ignore_bind
  >> rw[]
  >> TRY(drule_all cp_rel_contexts_ne >> rw[] >> NO_TAC)
  >> irule cp_rel_trans >> metis_tac[]
QED

Theorem cp_handle[simp]:
  cp f ∧ (∀e. cp (h e)) ⇒ cp (handle f h)
Proof
  rw[cp_eq_preserves_when]
  >> match_mp_tac preserves_when_handle
  >> rw[]
  >> TRY(drule_all cp_rel_contexts_ne >> rw[] >> NO_TAC)
  >> irule cp_rel_trans >> metis_tac[]
QED

Theorem cp_cond[simp]:
  cp m1 ∧ cp m2 ⇒ cp (if b then m1 else m2)
Proof
  rw[cp_eq_preserves_when, preserves_when_cond]
QED

Theorem cp_case_option[simp]:
  cp m_none ∧ (∀x. cp (m_some x)) ⇒
  cp (case opt of NONE => m_none | SOME x => m_some x)
Proof
  rw[cp_eq_preserves_when, preserves_when_case_option]
QED

Theorem cp_case_sum[simp]:
  (∀x. cp (f x)) ∧ (∀y. cp (g y)) ⇒
  cp (case s of INL x => f x | INR y => g y)
Proof
  rw[cp_eq_preserves_when, preserves_when_case_sum]
QED

Theorem cp_case_pair[simp]:
  (∀x y. cp (f x y)) ⇒ cp (case p of (x, y) => f x y)
Proof
  rw[cp_eq_preserves_when, preserves_when_case_pair]
QED

Theorem cp_let[simp]:
  (∀x. cp (f x)) ⇒ cp (let x = v in f x)
Proof
  rw[cp_eq_preserves_when, preserves_when_let]
QED

Theorem cp_preserves_static_inv:
  cp m ∧ static_inv a0 t0 d0 l0 s ⇒
  static_inv a0 t0 d0 l0 (SND (m s))
Proof
  rw[cp_def, static_inv_def]
  >> Cases_on `m s` >> first_x_assum (qspecl_then [`s`, `q`, `r`] mp_tac)
  >> rw[] >> gvs[]
  >> Cases_on `s.contexts` >> gvs[listTheory.FRONT_DEF]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[listTheory.FRONT_DEF]
QED

(* Paired version: when m s = (r, s'), static_inv transfers to s' *)
Theorem cp_preserves_static_inv_pair:
  cp m /\ static_inv a0 t0 d0 l0 s /\ m s = (r, s') ==>
  static_inv a0 t0 d0 l0 s'
Proof
  strip_tac
  >> `static_inv a0 t0 d0 l0 (SND (m s))` by metis_tac[cp_preserves_static_inv]
  >> gvs[]
QED

(* General tactic for proving cp of leaf operations *)
val basic_defs = [bind_def, return_def, fail_def, assert_def,
  ignore_bind_def, reraise_def,
  get_current_context_def, set_current_context_def];

val cp_tac = fn defs =>
  rw[cp_def] >> rpt strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> gvs (defs @ basic_defs)
  >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def]);



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
  >> cp_tac [consume_gas_def, push_stack_def, pop_stack_def,
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
     get_current_context_def,
     return_def, bind_def, fail_def]
  >> rpt strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
QED

(* Memory operations are cp *)
Theorem cp_memory[simp]:
  cp (write_memory off ws) ∧ cp (read_memory off sz) ∧
  cp (expand_memory n) ∧ cp (memory_expansion_info off sz)
Proof
  rpt conj_tac
  >> cp_tac [write_memory_def, read_memory_def, expand_memory_def,
     memory_expansion_info_def, expand_memory_def]
QED

(* get_context >> set_current_context preserving msgParams/logs is cp *)
Theorem cp_get_set_context:
  (∀ctxt. (f ctxt).msgParams = ctxt.msgParams) ∧
  (∀ctxt. (f ctxt).logs = ctxt.logs) ⇒
  cp (bind get_current_context (λctxt. set_current_context (f ctxt)))
Proof
  rw[cp_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem cp_get_cp_set_context:
  (∀ctxt. cp (g ctxt)) ∧
  (∀ctxt x. (f ctxt x).msgParams = ctxt.msgParams) ∧
  (∀ctxt x. (f ctxt x).logs = ctxt.logs) ⇒
  cp (bind get_current_context (λctxt. bind (g ctxt) (λx. set_current_context (f ctxt x))))
Proof
  rw[cp_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `g (FST h) s` >> Cases_on `q` >> gvs[]
  >> (first_x_assum (qspec_then `FST h` mp_tac) >> rw[cp_def]
      >> res_tac >> gvs[])
QED

(* Tactic for compound cp proofs: unfold def then repeatedly apply composition *)
val cp_simp_tac = fn defs =>
  rw defs
  >> rpt (irule cp_bind >> rw[]
          ORELSE irule cp_ignore_bind >> rw[]
          ORELSE irule cp_handle >> rw[]
          ORELSE irule cp_get_set_context >> rw[]);

(* inc_pc_or_jump is cp *)
Theorem cp_inc_pc_or_jump[simp]:
  cp (inc_pc_or_jump op)
Proof
  rw[cp_def, inc_pc_or_jump_def, is_call_def] >> rpt strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> gvs[bind_def, get_current_context_def, return_def,
         set_current_context_def, fail_def, assert_def]
  >> Cases_on `h0.jumpDest`
  >> gvs[set_current_context_def, bind_def, assert_def, return_def,
         ignore_bind_def, fail_def]
  >> BasicProvers.FULL_CASE_TAC >> gvs[]
QED

Theorem cp_unuse_gas[simp]:
  cp (unuse_gas n)
Proof
  cp_tac [unuse_gas_def]
QED

(* Composition: cp prefix + static_inv-preserving continuation *)
Theorem static_inv_bind_cp:
  cp g /\ (!x s. static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
                  static_inv a0 t0 d0 l0 (SND (f x s))) /\
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (bind g f s))
Proof
  strip_tac
  >> `s.contexts <> []` by fs[static_inv_def]
  >> simp[bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >- (`static_inv a0 t0 d0 l0 r` by metis_tac[cp_preserves_static_inv_pair]
      >> `r.contexts <> []` by fs[static_inv_def]
      >> metis_tac[])
  >- metis_tac[cp_preserves_static_inv_pair]
QED

(* Variant for ignore_bind *)
Theorem static_inv_ignore_bind_cp:
  cp g /\ (!s. static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
               static_inv a0 t0 d0 l0 (SND (f s))) /\
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (ignore_bind g f s))
Proof
  rw[ignore_bind_def] >> irule static_inv_bind_cp >> simp[]
  >> metis_tac[]
QED

(* LET variant *)
Theorem static_inv_let:
  (!x. static_inv a0 t0 d0 l0 (SND (f x s))) ==>
  static_inv a0 t0 d0 l0 (SND ((let x = v in f x) s))
Proof
  rw[]
QED

(* Cond variant *)
Theorem static_inv_cond:
  static_inv a0 t0 d0 l0 (SND (f1 s)) /\
  static_inv a0 t0 d0 l0 (SND (f2 s)) ==>
  static_inv a0 t0 d0 l0 (SND ((if b then f1 else f2) s))
Proof
  rw[]
QED

(* Under static_inv, bind assert_not_static f preserves inv (fails before f runs) *)
Theorem static_inv_assert_not_static:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (bind assert_not_static f s))
Proof
  strip_tac
  >> `s.contexts <> []` by fs[static_inv_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> `h0.msgParams.static` by gvs[static_inv_def]
  >> simp[bind_def, assert_not_static_def, get_static_def,
          get_current_context_def, return_def,
          assert_def, fail_def]
QED

(* ignore_bind variant *)
Theorem static_inv_ignore_bind_assert:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (ignore_bind assert_not_static f s))
Proof
  rw[ignore_bind_def]
  >> irule static_inv_assert_not_static >> simp[]
QED

(* When cp g and static_inv, bind g (.. assert_not_static ..) preserves inv *)
Theorem cp_then_static_fail:
  cp g ∧ static_inv a0 t0 d0 l0 s ⇒
  ¬ISL (FST (bind g (λx. bind assert_not_static (f x)) s)) ∧
  static_inv a0 t0 d0 l0 (SND (bind g (λx. bind assert_not_static (f x)) s))
Proof
  rpt strip_tac
  >> simp[bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> `s.contexts ≠ []` by fs[static_inv_def]
  >> fs[cp_def] >> first_x_assum drule_all >> strip_tac >> gvs[]
  >> fs[assert_not_static_def, bind_def, get_static_def,
        get_current_context_def, return_def,
        fail_def, assert_def, ignore_bind_def]
  >> fs[static_inv_def] >> gvs[listTheory.FRONT_DEF]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[listTheory.FRONT_DEF]
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
  >> rw[precompile_ecrecover_def, precompile_sha2_256_def,
        precompile_ripemd_160_def, precompile_identity_def,
        precompile_modexp_def, precompile_ecadd_def,
        precompile_ecmul_def, precompile_ecpairing_def,
        precompile_blake2f_def, precompile_point_eval_def,
        precompile_bls_g1add_def, precompile_bls_g1msm_def,
        precompile_bls_g2add_def, precompile_bls_g2msm_def,
        precompile_bls_pairing_def, precompile_bls_map_fp_to_g1_def,
        precompile_bls_map_fp2_to_g2_def, precompile_p256verify_def,
        LET_THM]
  >> rpt (irule cp_bind >> rw[] >> rpt (irule cp_ignore_bind >> rw[]))
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
  >> rw[copy_to_memory_def, LET_THM]
  >- (pairarg_tac >> rw[])
  >> cp_simp_tac []
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
  >> rpt strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
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
  >> cp_simp_tac [step_mload_def, step_keccak256_def,
                  step_ext_code_copy_def, step_return_data_copy_def,
                  step_sload_def, step_return_def]
QED

Theorem cp_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ cp f) ⇒
  cp (step_copy_to_memory op src)
Proof
  rw[step_copy_to_memory_def]
  >> rpt (irule cp_bind >> rw[]
          ORELSE irule cp_ignore_bind >> rw[])
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
  Cases_on `op` >> rw[step_inst_def]
  >> TRY (cp_simp_tac [step_binop_def, step_monop_def, step_modop_def,
    step_context_def, step_msgParams_def, step_txParams_def,
    step_exp_def, step_balance_def, step_call_data_load_def,
    step_ext_code_size_def, step_ext_code_hash_def,
    step_block_hash_def, step_blob_hash_def, step_self_balance_def,
    step_mstore_def, step_jump_def, step_jumpi_def,
    step_push_def, step_dup_def, step_pop_def])
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
     get_output_to_def, get_current_context_def,
     return_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `h0.msgParams.outputTo` >> gvs[]
QED

(* push_logs [] is cp — callee had no logs under invariant *)
Theorem cp_push_logs_nil:
  cp (push_logs [])
Proof
  rw[cp_def, push_logs_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def]
  >> rpt strip_tac >> Cases_on `s.contexts` >> gvs[]
QED

(* after_pop is cp *)
Theorem cp_after_pop[simp]:
  cp (after_pop a b c)
Proof
  rw[after_pop_def]
  >> CASE_TAC >> rpt (irule cp_bind >> rw[]
    ORELSE irule cp_ignore_bind >> rw[])
  >> CASE_TAC >> rpt (irule cp_bind >> rw[]
    ORELSE irule cp_ignore_bind >> rw[])
QED

(* Abbreviation for the 5 conclusions we need *)
(* static_conclusions val removed — simplified theorems conclude with
   static_inv directly instead of 5 separate conjuncts *)

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
       get_current_context_def, return_def, fail_def,
       get_gas_left_def, consume_gas_def, set_return_data_def,
       pop_and_incorporate_context_def, pop_context_def,
       set_rollback_def, push_logs_def, set_current_context_def,
       update_gas_refund_def, inc_pc_def, push_stack_def,
       write_memory_def, expand_memory_def, read_memory_def,
       pop_stack_def, unuse_gas_def, reraise_def, assert_def]
QED

(* pop_and_incorporate_context preserves static_inv.
   Key: callee (head) has logs=[] from FRONT, so push_logs [] = no-op.
   Caller's logs are preserved. LAST is unchanged or becomes head. *)
Theorem pop_incorporate_static:
  static_inv a0 t0 d0 l0 s /\ 1 < LENGTH s.contexts ==>
  static_inv a0 t0 d0 l0
    (SND (pop_and_incorporate_context success s))
Proof
  strip_tac
  >> fs[static_inv_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> simp[pop_and_incorporate_context_def, bind_def,
          get_gas_left_def, get_current_context_def,
          return_def, pop_context_def, unuse_gas_def, LET_THM,
          set_current_context_def, fail_def, assert_def,
          ignore_bind_def]
  >> rpt (CASE_TAC >> gvs[return_def])
  >> simp[push_logs_def, bind_def, get_current_context_def,
          set_current_context_def, return_def,
          update_gas_refund_def, set_rollback_def]
  >> gvs[listTheory.FRONT_DEF, combinTheory.C_DEF]
  >> rw[] >> gvs[]
  >> Cases_on `t'` >> gvs[listTheory.FRONT_DEF]
QED

(* handle_ex_helper preserves static_inv *)
Theorem handle_ex_helper_static_inv:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (handle_ex_helper e s))
Proof
  strip_tac
  >> `s.contexts <> []` by fs[static_inv_def]
  >> simp[handle_ex_helper_def, bind_def,
          get_num_contexts_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t`
  >- (simp[reraise_def] >> gvs[static_inv_def])
  >> simp[]
  >> simp[bind_def, get_return_data_def, get_output_to_def,
          get_current_context_def, return_def,
          ignore_bind_def]
  >> `1 < LENGTH s.contexts` by gvs[]
  >> `static_inv a0 t0 d0 l0 (SND (pop_and_incorporate_context (e = NONE) s))`
     by metis_tac[pop_incorporate_static]
  >> Cases_on `pop_and_incorporate_context (e = NONE) s`
  >> Cases_on `q` >> gvs[]
  >> metis_tac[cp_preserves_static_inv, cp_after_pop]
QED

(* handle_exception preserves static_inv *)
Theorem handle_exception_static_inv:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (handle_exception e s))
Proof
  strip_tac
  >> `s.contexts <> []` by fs[static_inv_def]
  >> qabbrev_tac `prefix = (if e <> NONE /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else return ())`
  >> `cp prefix` by
    (simp[Abbr `prefix`] >> rw[]
     >> irule cp_ignore_bind >> rw[]
     >> irule cp_bind >> rw[]
     >> irule cp_ignore_bind >> rw[])
  >> `handle_exception e s = bind prefix (\u. handle_ex_helper e) s`
     by simp[Abbr `prefix`, handle_exception_decomp]
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> simp[bind_def]
  >> `static_inv a0 t0 d0 l0 (SND (prefix s))` by
    metis_tac[cp_preserves_static_inv]
  >> Cases_on `prefix s` >> Cases_on `q` >> gvs[]
  >> metis_tac[handle_ex_helper_static_inv]
QED

(* handle_step preserves static_inv *)
Theorem handle_step_static_inv:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (handle_step e s))
Proof
  strip_tac
  >> `s.contexts <> []` by fs[static_inv_def]
  >> `(!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a)` by
    (fs[static_inv_def] >> Cases_on `s.contexts` >> gvs[]
     >> PairCases_on `h` >> gvs[])
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> gvs[static_inv_def])
  >> simp[]
  >> `(handle_create e : unit execution) s = reraise e s` by
    metis_tac[INST_TYPE [alpha |-> ``:unit``] handle_create_reraises]
  >> `SND (handle (handle_create e) handle_exception s) =
      SND (handle_exception e s)` by
    simp[reraise_def, handle_def]
  >> simp[]
  >> metis_tac[handle_exception_static_inv]
QED

(* Lifting lemma: if inner preserves static_inv, then handle inner handle_step
   also preserves static_inv *)
Theorem handle_step_lift:
  (!r s'. inner s0 = (r, s') ==> static_inv a0 t0 d0 l0 s') ==>
  static_inv a0 t0 d0 l0 s0 ==>
  static_inv a0 t0 d0 l0
    (SND (handle (inner:unit execution) handle_step s0))
Proof
  strip_tac >> strip_tac
  >> simp[handle_def]
  >> Cases_on `inner s0` >> Cases_on `q` >> fs[]
  >> metis_tac[handle_step_static_inv]
QED

(* LET with UNCURRY (for tuple let-bindings like (a,b) <<- expr) *)
Theorem static_inv_let_uncurry:
  (!a b. static_inv a0 t0 d0 l0 (SND (f a b s))) ==>
  static_inv a0 t0 d0 l0 (SND (LET (UNCURRY (\a b. f a b)) v s))
Proof
  Cases_on `v` >> simp[]
QED

(* Direct UNCURRY application (after LET reduction) *)
Theorem static_inv_uncurry:
  (!a b. static_inv a0 t0 d0 l0 (SND (f a b s))) ==>
  static_inv a0 t0 d0 l0 (SND (UNCURRY f p s))
Proof
  Cases_on `p` >> simp[]
QED

(* ignore_bind where first op is conditional assert_not_static.
   When b=T, assert_not_static fails under static_inv (state unchanged).
   When b=F, return () is a no-op and we continue with ~b available. *)
Theorem static_inv_ignore_bind_assert_cond:
  static_inv a0 t0 d0 l0 s /\
  (~b ==> static_inv a0 t0 d0 l0 (SND (f s))) ==>
  static_inv a0 t0 d0 l0
    (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  Cases_on `b` >> strip_tac
  >- (rw[ignore_bind_def]
      >> irule static_inv_assert_not_static >> simp[])
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
    ORELSE (irule static_inv_ignore_bind_assert_cond >> conj_tac
            >- first_assum ACCEPT_TAC >> strip_tac)
    ORELSE (irule static_inv_uncurry >> rpt strip_tac)
    ORELSE (irule static_inv_bind_cp >> TRY solve_side
            >> TRY (simp[pairTheory.FORALL_PROD] >> rpt strip_tac))
    ORELSE (irule static_inv_ignore_bind_cp >> TRY solve_side
            >> TRY (rpt strip_tac))
    ORELSE (irule static_inv_let_uncurry >> TRY (rpt strip_tac))
    ORELSE (irule static_inv_let >> TRY (rpt strip_tac))
    ORELSE (irule static_inv_cond)
    ORELSE solve_side));

(* Guarded ops all have: cp_prefix >> assert_not_static >> rest *)
Theorem guarded_op_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_sstore transient s)) /\
  static_inv a0 t0 d0 l0 (SND (step_log n s)) /\
  static_inv a0 t0 d0 l0 (SND (step_self_destruct s)) /\
  static_inv a0 t0 d0 l0 (SND (step_create two s))
Proof
  strip_tac >> rpt conj_tac
  >> simp[step_sstore_def, step_log_def,
       step_self_destruct_def, step_create_def]
  >> static_inv_step
QED

(* proceed_call preserves static_inv when:
   - value = 0 or op = CallCode (so update_accounts is skipped)
   - subStatic = T (so new context is static)
   - outputTo = Memory mr (so outputTo <> Code) *)
Theorem static_inv_push_context:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] /\
  ctxt.msgParams.static /\ ctxt.logs = [] /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\
  rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0 ==>
  static_inv a0 t0 d0 l0 (SND (push_context (ctxt, rb) s))
Proof
  rw[static_inv_def, push_context_def, return_def]
  >> Cases_on `s.contexts`
  >> gvs[listTheory.FRONT_DEF, rich_listTheory.LAST_CONS]
QED

(* Composition: push_context followed by cp suffix *)
Theorem static_inv_ignore_bind_push_context:
  cp f /\
  ctxt.msgParams.static /\ ctxt.logs = [] /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\
  rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0 /\
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (ignore_bind (push_context (ctxt, rb)) f s))
Proof
  strip_tac
  >> simp[ignore_bind_def, bind_def, push_context_def, return_def]
  >> irule cp_preserves_static_inv >> simp[]
  >> rw[static_inv_def, listTheory.FRONT_DEF, rich_listTheory.LAST_CONS]
  >> Cases_on `s.contexts` >> gvs[static_inv_def]
QED

Theorem proceed_call_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] /\
  (value = 0 \/ op = CallCode) ==>
  static_inv a0 t0 d0 l0
    (SND (proceed_call op sender address value
       argsOff argsSize code stipend (Memory mr) s))
Proof
  strip_tac
  >> `?ctxt rb. HD s.contexts = (ctxt, rb)` by metis_tac[pairTheory.PAIR]
  >> simp[proceed_call_def, bind_def, ignore_bind_def, return_def,
          get_rollback_def, read_memory_def,
          get_caller_def, get_value_def, get_static_def,
          get_current_context_def,
          push_context_def,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> irule cp_preserves_static_inv >> simp[]
  >> rw[static_inv_def, listTheory.FRONT_DEF, rich_listTheory.LAST_CONS]
  >> gvs[static_inv_def, listTheory.FRONT_DEF]
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
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_call Call s))
Proof
  strip_tac
  >> simp[step_call_def, call_has_value_def]
  >> irule static_inv_bind_cp >> simp[]
  >> rpt strip_tac
  >> Cases_on `w2n (EL 2 x) = 0`
  >- (
    simp[]
    >> static_inv_step
    >> rpt conj_tac
    >> TRY (irule cp_preserves_static_inv >> simp[] >> NO_TAC)
    >> irule proceed_call_preserves_static_inv
    >> simp[call_has_value_def]
  )
  >- (
    `0 < w2n (EL 2 x)` by simp[]
    >> simp[]
    >> static_inv_step
  )
QED

Theorem step_call_nonCall_static:
  op <> Call ==>
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_call op s))
Proof
  strip_tac >> strip_tac
  >> simp[step_call_def]
  >> static_inv_step
  >> rpt conj_tac
  >> TRY (irule cp_preserves_static_inv >> simp[] >> NO_TAC)
  >> static_inv_step
  >> rpt conj_tac
  >> TRY (irule cp_preserves_static_inv >> simp[] >> NO_TAC)
  >> irule proceed_call_preserves_static_inv
  >> simp[call_has_value_def]
  >> Cases_on `op = CallCode` >> simp[]
QED

Theorem step_call_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_call op s))
Proof
  strip_tac >> Cases_on `op = Call`
  >- (gvs[] >> irule step_call_Call_static >> gvs[])
  >- (irule step_call_nonCall_static >> gvs[])
QED

Theorem step_inst_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_inst op s))
Proof
  strip_tac >> Cases_on `op`
  (* cp ops: don't expand step_inst_def, use cp_step_inst_non_call[simp] *)
  >> TRY (irule cp_preserves_static_inv >> simp[] >> NO_TAC)
  (* Guarded ops: expand and use static_inv_step *)
  >> TRY (simp[step_inst_def, step_sstore_def, step_log_def,
               step_self_destruct_def, step_create_def]
          >> static_inv_step >> NO_TAC)
  (* Call ops *)
  >> simp[step_inst_def]
  >> irule step_call_preserves_static_inv >> gvs[]
QED

Theorem inner_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  !r s'. (do
    ctxt <- get_current_context;
    if LENGTH ctxt.msgParams.code <= ctxt.pc then step_inst Stop
    else case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
           NONE => step_inst Invalid
         | SOME op => do step_inst op; inc_pc_or_jump op od
  od) s = (r, s') ==>
  static_inv a0 t0 d0 l0 s'
Proof
  rpt strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> gvs[bind_def, get_current_context_def, return_def]
  >> Cases_on `LENGTH h0.msgParams.code <= h0.pc` >> gvs[]
  >- (`cp (step_inst Stop)` by simp[]
      >> metis_tac[cp_preserves_static_inv_pair])
  >> Cases_on `FLOOKUP h0.msgParams.parsed h0.pc` >> gvs[]
  >- (`cp (step_inst Invalid)` by simp[]
      >> metis_tac[cp_preserves_static_inv_pair])
  >> gvs[ignore_bind_def, bind_def]
  >> `static_inv a0 t0 d0 l0 (SND (step_inst x s))`
       by (irule step_inst_preserves_static_inv >> gvs[])
  >> Cases_on `step_inst x s` >> Cases_on `q` >> gvs[]
  >- metis_tac[cp_preserves_static_inv_pair, cp_inc_pc_or_jump]
QED

Theorem step_preserves_static_inv:
  static_inv a0 t0 d0 l0 s0 ==>
  static_inv a0 t0 d0 l0 (SND (step s0))
Proof
  strip_tac
  >> `s0.contexts <> []` by fs[static_inv_def]
  >> `step s0 = handle (do
       ctxt <- get_current_context;
       code <<- ctxt.msgParams.code;
       parsed <<- ctxt.msgParams.parsed;
       if LENGTH code <= ctxt.pc then step_inst Stop
       else case FLOOKUP parsed ctxt.pc of
              NONE => step_inst Invalid
            | SOME op => do step_inst op; inc_pc_or_jump op od od)
       handle_step s0`
     by simp[step_def]
  >> pop_assum (fn th => REWRITE_TAC[th])
  >> irule handle_step_lift >> simp[]
  >> metis_tac[inner_preserves_static_inv]
QED

Theorem run_tr_preserves_static_inv:
  ∀r s. static_inv a0 t0 d0 l0 s ⇒
  static_inv a0 t0 d0 l0 (SND (run_tr (r, s)))
Proof
  recInduct run_tr_ind
  >> gen_tac >> gen_tac >> strip_tac >> strip_tac
  >> once_rewrite_tac[run_tr_def]
  >> reverse (Cases_on `r`) >- simp[]
  >> simp[]
  >> `static_inv a0 t0 d0 l0 (SND (step s))` by
    metis_tac[step_preserves_static_inv]
  >> Cases_on `step s` >> Cases_on `q` >> gvs[]
  >> once_rewrite_tac[run_tr_def] >> simp[]
QED

(* TODO: the outputTo ≠ Code precondition should be removable by moving
   outputTo ≠ Code from ALL to FRONT in static_inv (vacuous for singleton) *)
Theorem run_static_preserves:
  ∀es result final_state ctxt rb.
    run es = SOME (INR result, final_state) ∧
    es.contexts = [(ctxt, rb)] ∧
    ctxt.msgParams.static ∧
    (∀a. ctxt.msgParams.outputTo ≠ Code a) ⇒
    final_state.rollback.accounts = es.rollback.accounts ∧
    final_state.rollback.tStorage = es.rollback.tStorage ∧
    final_state.rollback.toDelete = es.rollback.toDelete ∧
    (case final_state.contexts of
       [(ctxt', _)] => ctxt'.logs = ctxt.logs
     | _ => T)
Proof
  rw[run_eq_tr]
  >> `static_inv es.rollback.accounts es.rollback.tStorage
        es.rollback.toDelete ctxt.logs es` by
    rw[static_inv_def, listTheory.FRONT_DEF, rich_listTheory.LAST_CONS]
  >> `static_inv es.rollback.accounts es.rollback.tStorage
        es.rollback.toDelete ctxt.logs (SND (step es))` by
    metis_tac[step_preserves_static_inv]
  >> Cases_on `step es` >> gvs[]
  >> `static_inv es.rollback.accounts es.rollback.tStorage
        es.rollback.toDelete ctxt.logs
        (SND (run_tr (q, r)))` by
    metis_tac[run_tr_preserves_static_inv]
  >> Cases_on `run_tr (q, r)` >> gvs[]
  >> fs[static_inv_def]
  >> Cases_on `final_state.contexts` >> gvs[]
  >> Cases_on `h` >> Cases_on `t` >> gvs[listTheory.FRONT_DEF]
QED

(* ---------- static_not_code (snc) invariant ---------- *)

(* snc: every static context has outputTo ≠ Code *)
Definition snc_def:
  snc s ⇔ EVERY (λ(c,r). c.msgParams.static ⇒
    ∀a. c.msgParams.outputTo ≠ Code a) s.contexts
End

(* cp preserves snc *)
Theorem cp_preserves_snc:
  cp m ∧ snc s ∧ s.contexts ≠ [] ⇒ snc (SND (m s))
Proof
  rw[cp_def, snc_def]
  >> Cases_on `m s`
  >> first_x_assum (qspecl_then [`s`, `q`, `r`] mp_tac)
  >> rw[] >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
QED

Theorem cp_preserves_snc_pair:
  cp m ∧ snc s ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒ snc s'
Proof
  strip_tac
  >> `snc (SND (m s))` by metis_tac[cp_preserves_snc]
  >> gvs[]
QED

(* pop_and_incorporate_context preserves snc:
   pops head context, then does cp operations on new head *)
Theorem pop_incorporate_snc:
  snc s ∧ s.contexts ≠ [] ∧ 1 < LENGTH s.contexts ⇒
  snc (SND (pop_and_incorporate_context success s))
Proof
  strip_tac
  >> fs[snc_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> simp[pop_and_incorporate_context_def, bind_def,
          get_gas_left_def, get_current_context_def,
          return_def, pop_context_def, unuse_gas_def, LET_THM,
          set_current_context_def, fail_def, assert_def,
          ignore_bind_def]
  >> rpt (CASE_TAC >> gvs[return_def])
  >> simp[push_logs_def, bind_def, get_current_context_def,
          set_current_context_def, return_def,
          update_gas_refund_def, set_rollback_def]
QED

(* General: cp preserves contexts ≠ [] *)
Theorem cp_contexts_ne:
  cp m ∧ s.contexts ≠ [] ⇒ (SND (m s)).contexts ≠ []
Proof
  rw[cp_def] >> Cases_on `m s`
  >> first_x_assum (qspecl_then [`s`, `q`, `r`] mp_tac) >> rw[] >> gvs[]
QED

Theorem cp_contexts_ne_pair:
  cp m ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒ s'.contexts ≠ []
Proof
  strip_tac >> `(SND (m s)).contexts ≠ []` by metis_tac[cp_contexts_ne]
  >> gvs[]
QED

(* context-preserving: a weaker property than cp —
   only requires contexts structure preservation (not rollback) *)
Definition ctx_pres_def:
  ctx_pres (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      ∃q'. s'.contexts = (q', SND (HD s.contexts)) :: TL s.contexts ∧
           q'.msgParams = (FST (HD s.contexts)).msgParams
End

Theorem cp_is_ctx_pres:
  cp m ⇒ ctx_pres m
Proof
  rw[cp_def, ctx_pres_def] >> res_tac >> metis_tac[]
QED

Theorem ctx_pres_preserves_snc:
  ctx_pres m ∧ snc s ∧ s.contexts ≠ [] ⇒ snc (SND (m s))
Proof
  rw[ctx_pres_def, snc_def]
  >> Cases_on `m s`
  >> first_x_assum (qspecl_then [`s`, `q`, `r`] mp_tac)
  >> rw[] >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
QED

Theorem ctx_pres_bind[simp]:
  ctx_pres g ∧ (∀x. ctx_pres (f x)) ⇒ ctx_pres (bind g f)
Proof
  rw[ctx_pres_def, bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem ctx_pres_ignore_bind[simp]:
  ctx_pres g ∧ ctx_pres f ⇒ ctx_pres (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule ctx_pres_bind >> simp[]
QED

Theorem ctx_pres_update_accounts[simp]:
  ctx_pres (update_accounts f)
Proof
  rw[ctx_pres_def, vfmExecutionTheory.update_accounts_def, return_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> qexists_tac `FST h` >> Cases_on `h` >> gvs[]
QED

(* ctx_pres composition lemmas *)
Theorem ctx_pres_leaves[simp]:
  ctx_pres (return x) ∧ ctx_pres (fail e) ∧
  ctx_pres (reraise eo) ∧ ctx_pres (assert b e) ∧
  ctx_pres (consume_gas n) ∧ ctx_pres (update_accounts f)
Proof
  rpt conj_tac
  >> TRY (irule cp_is_ctx_pres >> simp[] >> NO_TAC)
  >> rw[ctx_pres_def, return_def, fail_def, reraise_def, assert_def,
        vfmExecutionTheory.update_accounts_def]
QED

Theorem ctx_pres_cond[simp]:
  ctx_pres m1 ∧ ctx_pres m2 ⇒ ctx_pres (if b then m1 else m2)
Proof
  rw[]
QED

Theorem ctx_pres_case_option[simp]:
  ctx_pres m_none ∧ (∀x. ctx_pres (m_some x)) ⇒
  ctx_pres (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem ctx_pres_case_sum[simp]:
  (∀x. ctx_pres (f x)) ∧ (∀y. ctx_pres (g y)) ⇒
  ctx_pres (case s of INL x => f x | INR y => g y)
Proof
  Cases_on `s` >> rw[]
QED

Theorem ctx_pres_case_pair[simp]:
  (∀x y. ctx_pres (f x y)) ⇒ ctx_pres (case p of (x, y) => f x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem ctx_pres_let[simp]:
  (∀x. ctx_pres (f x)) ⇒ ctx_pres (let x = v in f x)
Proof
  rw[]
QED

Theorem ctx_pres_handle[simp]:
  ctx_pres f ∧ (∀e. ctx_pres (h e)) ⇒ ctx_pres (handle f h)
Proof
  rw[ctx_pres_def, handle_def]
  >> Cases_on `f s` >> Cases_on `q` >> gvs[]
  >> res_tac >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h'` >> gvs[]
  >> res_tac >> gvs[] >> metis_tac[]
QED

(* handle_create preserves snc: it either reraises (no state change)
   or does consume_gas (cp) + update_accounts (contexts unchanged) + reraise *)
Theorem handle_create_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_create e s)) ∧
  (SND (handle_create e s)).contexts ≠ []
Proof
  strip_tac
  >> `∃e' s'. handle_create e s = (INR e', s')` by metis_tac[handle_create_INR]
  >> `SND (handle_create e s) = s'` by gvs[]
  >> simp[]
  >> pop_assum kall_tac
  >> gvs[handle_create_def, bind_def,
         get_return_data_def, get_output_to_def,
         get_current_context_def, return_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `h0.msgParams.outputTo` >> gvs[reraise_def, snc_def]
  >> Cases_on `e` >> gvs[reraise_def, snc_def]
  >> gvs[ignore_bind_def, bind_def, CaseEq"prod", CaseEq"sum",
         reraise_def, assert_def, consume_gas_def, return_def, fail_def,
         set_current_context_def, CaseEq"bool",
         update_accounts_def, get_current_context_def]
QED

(* Pair-aware version: avoids polymorphic type mismatch on SND *)
Theorem handle_create_snc_pair[local]:
  handle_create e s = (r, s') ∧ snc s ∧ s.contexts ≠ [] ⇒
  snc s' ∧ s'.contexts ≠ []
Proof
  strip_tac
  >> gvs[handle_create_def, bind_def,
         get_return_data_def, get_output_to_def,
         get_current_context_def, return_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `e` >> gvs[reraise_def, snc_def]
  >> Cases_on `h0.msgParams.outputTo` >> gvs[reraise_def, snc_def]
  >> gvs[ignore_bind_def, bind_def, assert_def, return_def, fail_def,
         consume_gas_def, get_current_context_def,
         set_current_context_def, vfmExecutionTheory.update_accounts_def]
  >> rpt (IF_CASES_TAC >> gvs[return_def, reraise_def, snc_def, fail_def])
  >> rpt (BasicProvers.FULL_CASE_TAC
          >> gvs[return_def, reraise_def, snc_def, fail_def])
QED

(* pop_and_incorporate_context: result has non-empty contexts when starting ≥ 2 *)
Theorem pop_incorporate_contexts_ne:
  s.contexts ≠ [] ∧ 1 < LENGTH s.contexts ∧
  pop_and_incorporate_context success s = (INL (), s') ⇒
  s'.contexts ≠ []
Proof
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> gvs[pop_and_incorporate_context_def, bind_def,
         get_gas_left_def, get_current_context_def,
         return_def, pop_context_def, unuse_gas_def, LET_THM,
         set_current_context_def, fail_def, assert_def,
         ignore_bind_def]
  >> BasicProvers.FULL_CASE_TAC >> gvs[return_def]
  >> Cases_on `success` >> gvs[return_def]
  >> gvs[push_logs_def, bind_def, get_current_context_def,
         set_current_context_def, return_def,
         update_gas_refund_def, set_rollback_def]
QED

(* handle_ex_helper preserves snc *)
Theorem handle_ex_helper_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_ex_helper e s))
Proof
  strip_tac
  >> simp[handle_ex_helper_def, bind_def,
          get_num_contexts_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t`
  >- (simp[reraise_def] >> gvs[snc_def])
  >> simp[]
  >> simp[bind_def, get_return_data_def, get_output_to_def,
          get_current_context_def, return_def,
          ignore_bind_def]
  >> `1 < LENGTH s.contexts` by gvs[]
  >> `snc (SND (pop_and_incorporate_context (e = NONE) s))`
     by (irule pop_incorporate_snc >> gvs[])
  >> Cases_on `pop_and_incorporate_context (e = NONE) s`
  >> Cases_on `q` >> gvs[]
  >> `s.contexts ≠ [] ∧ 1 < LENGTH s.contexts` by gvs[]
  >> `r.contexts ≠ []` by metis_tac[pop_incorporate_contexts_ne]
  >> metis_tac[cp_preserves_snc, cp_after_pop]
QED

(* handle_exception preserves snc *)
Theorem handle_exception_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_exception e s))
Proof
  strip_tac
  >> qabbrev_tac `prefix = (if e <> NONE /\ e <> SOME Reverted then
       do gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else return ())`
  >> `cp prefix` by
    (simp[Abbr `prefix`] >> rw[]
     >> irule cp_ignore_bind >> rw[]
     >> irule cp_bind >> rw[]
     >> irule cp_ignore_bind >> rw[])
  >> `handle_exception e s = bind prefix (\u. handle_ex_helper e) s`
     by simp[Abbr `prefix`, handle_exception_decomp]
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> simp[bind_def]
  >> `snc (SND (prefix s))` by metis_tac[cp_preserves_snc]
  >> `(SND (prefix s)).contexts ≠ []` by metis_tac[cp_contexts_ne]
  >> Cases_on `prefix s` >> Cases_on `q` >> gvs[]
  >> metis_tac[handle_ex_helper_snc]
QED

(* Additional ctx_pres building blocks for non-cp primitives *)
Theorem ctx_pres_more_leaves[simp]:
  ctx_pres (push_logs ls) ∧
  ctx_pres (add_to_delete a) ∧
  ctx_pres (set_tStorage x)
Proof
  rpt conj_tac
  >> rw[ctx_pres_def, push_logs_def, add_to_delete_def, set_tStorage_def,
        bind_def, get_current_context_def,
        set_current_context_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
QED

(* Guarded step_inst ops are ctx_pres *)
Theorem ctx_pres_step_inst_guarded[simp]:
  ctx_pres (step_sstore transient) ∧
  ctx_pres (step_log n) ∧
  ctx_pres step_self_destruct
Proof
  rpt conj_tac
  >> rw[step_sstore_def, step_log_def, step_self_destruct_def,
        write_storage_def, write_transient_storage_def]
  >> rpt (irule ctx_pres_bind >> simp[] >> rpt strip_tac
          ORELSE irule ctx_pres_ignore_bind >> simp[] >> rpt strip_tac
          ORELSE irule cp_is_ctx_pres >> simp[])
QED

(* push_context preserves snc when pushed context satisfies snc predicate *)
Theorem push_context_snc[local]:
  snc s ∧ (c.msgParams.static ⇒ ∀a. c.msgParams.outputTo ≠ Code a) ⇒
  snc (SND (push_context (c, rb) s))
Proof
  rw[snc_def, push_context_def, return_def]
QED

(* ctx_pres preserves contexts≠[] *)
Theorem ctx_pres_contexts_ne:
  ctx_pres m ∧ m s = (q, r) ∧ s.contexts ≠ [] ⇒ r.contexts ≠ []
Proof
  rw[ctx_pres_def] >> res_tac >> gvs[]
QED

(* step_inst preserves contexts ≠ [] — proved by expansion for create/call *)
Theorem proceed_create_contexts_ne[local]:
  s.contexts ≠ [] ⇒
  (SND (proceed_create sAddr addr v code gas s)).contexts ≠ []
Proof
  strip_tac
  >> simp[proceed_create_def, bind_def, ignore_bind_def, return_def,
       get_rollback_def, get_original_def,
       get_current_context_def,
       set_original_def, vfmExecutionTheory.update_accounts_def,
       push_context_def, set_last_accounts_def, listTheory.SNOC_APPEND]
QED

Theorem proceed_call_contexts_ne[local]:
  s.contexts ≠ [] ⇒
  (SND (proceed_call op sender addr v aOff aSz code stip outTo s)).contexts ≠ []
Proof
  strip_tac
  >> simp[proceed_call_def, bind_def, ignore_bind_def, return_def,
       get_rollback_def, read_memory_def,
       get_caller_def, get_value_def, get_static_def,
       get_current_context_def, get_callee_def,
       push_context_def, vfmExecutionTheory.update_accounts_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> rpt (CASE_TAC >> gvs[return_def, fail_def])
  >> TRY (imp_res_tac update_accounts_contexts_pair)
  >> TRY (gvs[] >> NO_TAC)
  >> irule cp_contexts_ne >> simp[]
QED

(* === Combined snc + contexts≠[] composition (sne = snc ∧ ne) === *)
(* These thread BOTH properties through bind chains simultaneously.
   The conjunction avoids the negation issue that plagued separate ne_step. *)

Theorem sne_bind_cp[local]:
  cp g ∧
  (∀x s. snc s ∧ s.contexts ≠ [] ⇒
    snc (SND (f x s)) ∧ (SND (f x s)).contexts ≠ []) ∧
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (bind g f s)) ∧ (SND (bind g f s)).contexts ≠ []
Proof
  strip_tac >> simp[bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >- (`snc r ∧ r.contexts ≠ []`
        by metis_tac[cp_preserves_snc_pair, cp_contexts_ne_pair]
      >> metis_tac[])
  >> metis_tac[cp_preserves_snc_pair, cp_contexts_ne_pair]
QED

Theorem sne_ignore_bind_cp[local]:
  cp g ∧
  (∀s. snc s ∧ s.contexts ≠ [] ⇒
    snc (SND (f s)) ∧ (SND (f s)).contexts ≠ []) ∧
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (ignore_bind g f s)) ∧ (SND (ignore_bind g f s)).contexts ≠ []
Proof
  rw[ignore_bind_def]
  >> `snc (SND (bind g (λx. f) s)) ∧ (SND (bind g (λx. f) s)).contexts ≠ []`
     suffices_by simp[]
  >> irule sne_bind_cp >> simp[]
QED

Theorem sne_let[local]:
  (∀x. snc (SND (f x s)) ∧ (SND (f x s)).contexts ≠ []) ⇒
  snc (SND ((let x = v in f x) s)) ∧
  (SND ((let x = v in f x) s)).contexts ≠ []
Proof
  rw[]
QED

Theorem sne_cond[local]:
  (snc (SND (f1 s)) ∧ (SND (f1 s)).contexts ≠ []) ∧
  (snc (SND (f2 s)) ∧ (SND (f2 s)).contexts ≠ []) ⇒
  snc (SND ((if b then f1 else f2) s)) ∧
  (SND ((if b then f1 else f2) s)).contexts ≠ []
Proof
  rw[]
QED

Theorem sne_uncurry[local]:
  (∀a b. snc (SND (f a b s)) ∧ (SND (f a b s)).contexts ≠ []) ⇒
  snc (SND (UNCURRY f p s)) ∧ (SND (UNCURRY f p s)).contexts ≠ []
Proof
  Cases_on `p` >> simp[]
QED

Theorem sne_let_uncurry[local]:
  (∀a b. snc (SND (f a b s)) ∧ (SND (f a b s)).contexts ≠ []) ⇒
  snc (SND (LET (UNCURRY (λa b. f a b)) v s)) ∧
  (SND (LET (UNCURRY (λa b. f a b)) v s)).contexts ≠ []
Proof
  Cases_on `v` >> simp[]
QED

Theorem sne_case_option[local]:
  (snc (SND (f_none s)) ∧ (SND (f_none s)).contexts ≠ []) ∧
  (∀x. snc (SND (f_some x s)) ∧ (SND (f_some x s)).contexts ≠ []) ⇒
  snc (SND ((case opt of NONE => f_none | SOME x => f_some x) s)) ∧
  (SND ((case opt of NONE => f_none | SOME x => f_some x) s)).contexts ≠ []
Proof
  Cases_on `opt` >> simp[]
QED

Theorem ctx_pres_contexts_ne_snd[local]:
  ctx_pres m ∧ s.contexts ≠ [] ⇒ (SND (m s)).contexts ≠ []
Proof
  strip_tac >> `∃q r. m s = (q, r)` by metis_tac[pairTheory.PAIR]
  >> `r.contexts ≠ []` by metis_tac[ctx_pres_contexts_ne]
  >> gvs[]
QED

(* sne step tactic: decompose monadic chain preserving snc ∧ contexts≠[] *)
val sne_solve = simp[] ORELSE first_assum ACCEPT_TAC;

(* strip_pos: strip ∀ and ⇒ without touching ∧ or ¬ *)
val strip_pos = rpt gen_tac >> rpt disch_tac;

val sne_one =
  (irule sne_uncurry >> strip_pos)
  ORELSE (irule sne_bind_cp >> TRY sne_solve
          >> TRY (simp[pairTheory.FORALL_PROD] >> strip_pos))
  ORELSE (irule sne_ignore_bind_cp >> TRY sne_solve
          >> TRY strip_pos)
  ORELSE (irule sne_let_uncurry >> TRY strip_pos)
  ORELSE (irule sne_let >> TRY strip_pos)
  ORELSE (irule sne_case_option >> TRY strip_pos)
  ORELSE (irule sne_cond >> conj_tac)
  ORELSE sne_solve;

(* Apply sne_one to current goal repeatedly *)
val sne_step = rpt (CHANGED_TAC sne_one);

(* Threading snc through a ctx_pres bind *)
Theorem snc_bind_ctx_pres:
  ctx_pres m ∧ snc s ∧ s.contexts ≠ [] ∧
  (∀x s'. m s = (INL x, s') ∧ snc s' ∧ s'.contexts ≠ [] ⇒
    snc (SND (f x s'))) ⇒
  snc (SND (bind m f s))
Proof
  strip_tac >> simp[bind_def]
  >> Cases_on `m s` >> Cases_on `q` >> gvs[]
  >- (first_x_assum irule >> simp[]
      >> conj_tac
      >- (`snc (SND (m s))` by metis_tac[ctx_pres_preserves_snc] >> gvs[])
      >> metis_tac[ctx_pres_contexts_ne])
  >> `snc (SND (m s))` by metis_tac[ctx_pres_preserves_snc] >> gvs[]
QED

(* proceed_call with Memory outputTo preserves snc *)
Theorem proceed_call_snc[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (proceed_call op sender address value
    argsOff argsSize code stipend (Memory mr) s))
Proof
  strip_tac
  >> simp[proceed_call_def, bind_def, ignore_bind_def, return_def,
          get_rollback_def, read_memory_def,
          get_caller_def, get_value_def, get_static_def,
          get_current_context_def, get_callee_def,
          push_context_def,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> rpt (CASE_TAC >> gvs[return_def, fail_def])
  >> TRY (imp_res_tac update_accounts_contexts_pair)
  >> TRY (gvs[snc_def, vfmContextTheory.return_destination_distinct] >> NO_TAC)
  >> irule cp_preserves_snc
  >> gvs[snc_def, vfmContextTheory.return_destination_distinct]
QED

(* proceed_create preserves snc: pushed context has static=F *)
Theorem set_last_accounts_every_fst:
  ∀P a ls. ls ≠ [] ⇒
    (EVERY (λ(c,r). P c) (set_last_accounts a ls) ⇔
     EVERY (λ(c,r). P c) ls)
Proof
  rpt strip_tac
  >> `SNOC (LAST ls) (FRONT ls) = ls`
      by simp[listTheory.SNOC_LAST_FRONT]
  >> Cases_on `LAST ls` >> gvs[]
  >> ONCE_REWRITE_TAC[set_last_accounts_def]
  >> PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >> gvs[]
  >> `EVERY (λ(c,r). P c) ls ⇔
      EVERY (λ(c,r). P c) (FRONT ls) ∧ P q`
      by (qpat_x_assum `SNOC _ _ = _` (SUBST1_TAC o GSYM)
          >> simp[listTheory.EVERY_SNOC])
  >> simp[]
QED

Theorem proceed_create_snc[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (proceed_create senderAddr address value code cappedGas s))
Proof
  strip_tac
  >> simp[proceed_create_def, bind_def, ignore_bind_def, return_def,
          get_rollback_def, get_original_def,
          get_current_context_def,
          set_original_def, vfmExecutionTheory.update_accounts_def,
          push_context_def,
          vfmContextTheory.initial_context_def,
          vfmContextTheory.initial_msg_params_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> gvs[snc_def, set_last_accounts_every_fst]
QED


Theorem ctx_pres_abort_create_exists[local]:
  ctx_pres (abort_create_exists sAddr)
Proof
  simp[abort_create_exists_def]
  >> irule ctx_pres_ignore_bind >> simp[ctx_pres_update_accounts]
  >> irule ctx_pres_ignore_bind >> simp[ctx_pres_leaves, cp_is_ctx_pres, cp_leaves]
QED

(* snc/ne terminal for individual conjuncts *)
val snc_ne_hints =
  [cp_abort_unuse, cp_abort_call_value,
   cp_is_ctx_pres, ctx_pres_abort_create_exists];

val snc_term =
  (irule proceed_create_snc
   ORELSE irule proceed_call_snc
   ORELSE irule ctx_pres_preserves_snc)
  >> simp snc_ne_hints;

val ne_term =
  FIRST [irule proceed_create_contexts_ne >> simp snc_ne_hints,
         irule proceed_call_contexts_ne >> simp snc_ne_hints,
         irule ctx_pres_contexts_ne_snd >> simp snc_ne_hints];

(* solve_term: close snc or ne terminal goals *)
val solve_term =
  TRY (snc_term >> NO_TAC)
  >> TRY (ne_term >> NO_TAC)
  >> TRY (IF_CASES_TAC >> rpt conj_tac
          >> TRY (snc_term >> NO_TAC)
          >> TRY (ne_term >> NO_TAC));

(* Combined cp/ctx_pres sne: both snc and ne in one irule target *)
Theorem cp_sne[local]:
  cp m ∧ snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (m s)) ∧ (SND (m s)).contexts ≠ []
Proof
  metis_tac[cp_preserves_snc, cp_contexts_ne]
QED

Theorem cp_sne_pair[local]:
  cp m ∧ snc s ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒
  snc s' ∧ s'.contexts ≠ []
Proof
  metis_tac[cp_preserves_snc_pair, cp_contexts_ne_pair]
QED

Theorem ctx_pres_sne[local]:
  ctx_pres m ∧ snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (m s)) ∧ (SND (m s)).contexts ≠ []
Proof
  metis_tac[ctx_pres_preserves_snc, ctx_pres_contexts_ne_snd]
QED

(* Combined step_create: snc ∧ contexts≠[] *)
Theorem step_create_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (step_create two s)) ∧
  (SND (step_create two s)).contexts ≠ []
Proof
  strip_tac >> rewrite_tac[step_create_def]
  >> CHANGED_TAC sne_step
  >> rpt conj_tac >> solve_term
QED

(* Inner block of step_call after the first conditional *)
Theorem step_call_inner_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (do
    set_return_data [];
    sucDepth <- get_num_contexts;
    if sucDepth > 1024 then abort_unuse b
    else proceed_call op sender addr value_arg args_off args_size code stipend
           (Memory mr)
  od s)) ∧
  (SND (do
    set_return_data [];
    sucDepth <- get_num_contexts;
    if sucDepth > 1024 then abort_unuse b
    else proceed_call op sender addr value_arg args_off args_size code stipend
           (Memory mr)
  od s)).contexts ≠ []
Proof
  strip_tac
  >> sne_step
  >> rpt conj_tac >> solve_term
QED

(* Combined step_call: snc ∧ contexts≠[] *)
Theorem step_call_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (step_call op s)) ∧
  (SND (step_call op s)).contexts ≠ []
Proof
  strip_tac >> rewrite_tac[step_call_def]
  \\ sne_step
  \\ rpt conj_tac >> TRY solve_term
  \\ (irule (cj 1 step_call_inner_sne) ORELSE irule (cj 2 step_call_inner_sne))
  \\ simp[]
QED

(* Combined step_inst: snc AND contexts≠[] — SND version *)
Theorem step_inst_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (step_inst op s)) ∧ (SND (step_inst op s)).contexts ≠ []
Proof
  strip_tac >> Cases_on `op`
  (* cp ops *)
  >> TRY (irule cp_sne >> simp[cp_step_inst_non_call] >> NO_TAC)
  (* ctx_pres guarded ops *)
  >> TRY (rewrite_tac[step_inst_def] >> irule ctx_pres_sne
          >> simp[ctx_pres_step_inst_guarded] >> NO_TAC)
  (* Create/Create2 *)
  >> TRY (rewrite_tac[step_inst_def] >> irule step_create_sne >>
          simp[] >> NO_TAC)
  (* Call ops *)
  >> rewrite_tac[step_inst_def] >> irule step_call_sne >> simp[]
QED

(* handle_step preserves snc *)
Theorem handle_step_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_step e s))
Proof
  strip_tac
  >> simp[handle_step_def]
  >> Cases_on `vfm_abort e` >- (simp[] >> irule cp_preserves_snc >> simp[])
  >> simp[handle_def]
  >> `∃r s1. (handle_create:(exception option -> execution_state ->
       (unit + exception option) # execution_state)) e s = (r, s1)`
     by metis_tac[pairTheory.PAIR]
  >> Cases_on `r` >> gvs[]
  >- (drule_all handle_create_snc_pair >> simp[])
  >> `snc s1 ∧ s1.contexts ≠ []` by (drule_all handle_create_snc_pair >> simp[])
  >> irule handle_exception_snc >> simp[]
QED

(* Inner step of step preserves snc AND contexts ≠ [] *)
Theorem inner_preserves_snc_pair[local]:
  snc s ∧ s.contexts = h::t ∧
  (do context <- get_current_context;
      if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
      else case FLOOKUP context.msgParams.parsed context.pc of
             NONE => step_inst Invalid
           | SOME op => do step_inst op; inc_pc_or_jump op od
  od) s = (r, s1) ⇒
  snc s1 ∧ s1.contexts ≠ []
Proof
  strip_tac
  \\ gvs[bind_def, get_current_context_def, return_def]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `LENGTH h0.msgParams.code ≤ h0.pc` \\ gvs[]
  >- (`cp (step_inst Stop)` by simp[]
      \\ `s.contexts ≠ []` by simp[]
      \\ drule_all cp_sne_pair \\ simp[])
  \\ Cases_on `FLOOKUP h0.msgParams.parsed h0.pc` \\ gvs[]
  >- (`cp (step_inst Invalid)` by simp[]
      \\ `s.contexts ≠ []` by simp[]
      \\ drule_all cp_sne_pair \\ simp[])
  \\ gvs[ignore_bind_def, bind_def]
  \\ `snc (SND (step_inst x s)) ∧ (SND (step_inst x s)).contexts ≠ []`
     by (irule step_inst_sne \\ simp[])
  \\ Cases_on `step_inst x s` \\ Cases_on `q` \\ gvs[]
  \\ `cp (inc_pc_or_jump x)` by simp[cp_inc_pc_or_jump]
  \\ metis_tac[cp_sne_pair]
QED

(* step preserves snc *)
Theorem step_preserves_snc:
  snc s ⇒ snc (SND (step s))
Proof
  strip_tac
  \\ Cases_on `s.contexts`
  >- (simp[step_def, handle_def, bind_def, get_current_context_def,
           fail_def, handle_step_def, reraise_def, snc_def])
  \\ simp[step_def, handle_def]
  \\ `∃r s1. (do
        context <- get_current_context;
        if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
        else case FLOOKUP context.msgParams.parsed context.pc of
               NONE => step_inst Invalid
             | SOME op => do step_inst op; inc_pc_or_jump op od
      od : unit execution) s = (r, s1)` by metis_tac[pairTheory.PAIR]
  \\ gvs[]
  \\ Cases_on `r` \\ gvs[]
  >- (drule_all inner_preserves_snc_pair \\ simp[])
  \\ `snc s1 ∧ s1.contexts ≠ []`
     by (drule_all inner_preserves_snc_pair \\ simp[])
  \\ irule handle_step_snc \\ simp[]
QED

Theorem run_tr_preserves_snc:
  ∀r s. snc s ⇒ snc (SND (run_tr (r, s)))
Proof
  recInduct run_tr_ind
  >> gen_tac >> gen_tac >> strip_tac >> strip_tac
  >> once_rewrite_tac[run_tr_def]
  >> reverse (Cases_on `r`) >- simp[]
  >> simp[]
  >> `snc (SND (step s))` by metis_tac[step_preserves_snc]
  >> Cases_on `step s` >> Cases_on `q` >> gvs[]
QED

Theorem static_not_code_preserved:
  ∀es result fs.
    run es = SOME (INR result, fs) ∧
    EVERY (λ(c,r). c.msgParams.static ⇒
      ∀a. c.msgParams.outputTo ≠ Code a) es.contexts ⇒
    EVERY (λ(c,r). c.msgParams.static ⇒
      ∀a. c.msgParams.outputTo ≠ Code a) fs.contexts
Proof
  rw[run_eq_tr, snc_def |> REWRITE_RULE [GSYM snc_def] |> GSYM]
  >> `snc es` by rw[snc_def]
  >> `snc (SND (step es))` by metis_tac[step_preserves_snc]
  >> Cases_on `step es` >> gvs[]
  >> `snc (SND (run_tr (q, r)))` by metis_tac[run_tr_preserves_snc]
  >> Cases_on `run_tr (q, r)` >> gvs[snc_def]
QED
