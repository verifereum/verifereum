(* ==========================================================================
 * Per-account frame for run_call.
 *
 * A step whose current context's callee is not `a` changes account `a` only
 * by a foreign_account_change: its code and storage stay, and its nonce
 * stays unless `a` is not yet created (a CREATE at `a`).  So during run_call
 * `a`'s code and storage change only inside frames executing as `a`.
 *
 * run_call_account_frame is the rely form: if every frame entered as `a`
 * preserves a predicate P of `a`'s account, then run_call preserves P.
 * run_call_empty_code_account instantiates it for an account with no code.
 * ========================================================================== *)
Theory vfmAccountFrame
Ancestors
  combin pair option list rich_list relation arithmetic While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStaticCalls vfmDecreasesGas
  vfmStoragePredicates vfmPreserves vfmHandleStep vfmStepLength
Libs
  BasicProvers

(* -------------------------------------------------------------------------
 * What a frame not executing as an account can do to it.
 * ------------------------------------------------------------------------- *)

(* Balance is free (value transfers); the nonce may change only for an
 * account a CREATE may target (EIP-7610: no nonce, code or storage). *)
Definition foreign_account_change_def:
  foreign_account_change acc acc' ⇔
    acc'.code = acc.code ∧ acc'.storage = acc.storage ∧
    (acc'.nonce = acc.nonce ∨ ¬account_already_created acc)
End

Theorem foreign_account_change_refl[simp]:
  foreign_account_change acc acc
Proof
  rw[foreign_account_change_def]
QED

Theorem foreign_account_change_trans:
  foreign_account_change acc1 acc2 ∧ foreign_account_change acc2 acc3 ⇒
  foreign_account_change acc1 acc3
Proof
  rw[foreign_account_change_def] >> gvs[account_already_created_def]
QED

(* -------------------------------------------------------------------------
 * States run_call es takes a step from or reaches with a continuing result.
 * ------------------------------------------------------------------------- *)

Definition run_call_reaches_def:
  run_call_reaches es s ⇔
    RTC (λs1 s2. LENGTH es.contexts ≤ LENGTH s1.contexts ∧
                 ∃u. step s1 = (INL u, s2)) es s
End

Theorem run_call_reaches_refl[simp]:
  run_call_reaches es es
Proof
  rw[run_call_reaches_def]
QED

Theorem run_call_reaches_step:
  run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
  step s = (INL u, s') ⇒
  run_call_reaches es s'
Proof
  rw[run_call_reaches_def]
  >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1))
  >> metis_tac[]
QED

(* An invariant of every step holds at every reached state. *)
Theorem run_call_reaches_inv:
  Q es ∧
  (∀s u s'. Q s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
            step s = (INL u, s') ⇒ Q s') ∧
  run_call_reaches es s ⇒
  Q s
Proof
  rw[run_call_reaches_def]
  >> qmatch_asmsub_abbrev_tac `RTC R es s`
  >> `∀x y. RTC R x y ⇒ x = es ⇒ Q y` suffices_by metis_tac[]
  >> ho_match_mp_tac RTC_INDUCT_RIGHT1
  >> rw[Abbr`R`] >> metis_tac[]
QED

Theorem run_call_reaches_wf_state:
  wf_state es ∧ run_call_reaches es s ⇒ wf_state s
Proof
  strip_tac
  >> irule run_call_reaches_inv
  >> qexists_tac `es` >> simp[]
  >> metis_tac[step_preserves_wf_state, SND]
QED

(* OWHILE from any state on its own trajectory gives the same result. *)
Theorem OWHILE_RTC:
  ∀x y. RTC (λx y. G x ∧ f x = y) x y ⇒ OWHILE G f x = OWHILE G f y
Proof
  ho_match_mp_tac RTC_INDUCT
  >> rw[]
  >> simp[Once OWHILE_THM]
QED

Theorem OWHILE_finite_trace:
  OWHILE G f x = SOME y ⇒
  ∃n. FUNPOW f n x = y ∧ ¬G y ∧
      ∀k. k < n ⇒ G (FUNPOW f k x)
Proof
  rw[OWHILE_def]
  >> qexists_tac `LEAST n. ¬G (FUNPOW f n x)`
  >> numLib.LEAST_ELIM_TAC >> metis_tac[]
QED

Theorem OWHILE_from_finite_trace:
  ∀n x. ¬G (FUNPOW f n x) ∧
    (∀k. k < n ⇒ G (FUNPOW f k x)) ⇒
    OWHILE G f x = SOME (FUNPOW f n x)
Proof
  Induct >> rw[]
  >- simp[Once OWHILE_THM]
  >> `G x` by (first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >> simp[Once OWHILE_THM]
  >> fs[FUNPOW]
  >> first_x_assum irule >> simp[]
  >> rpt strip_tac
  >> first_x_assum (qspec_then `SUC k` mp_tac)
  >> simp[FUNPOW]
QED

Theorem OWHILE_nested_trace:
  (∀z. H z ⇒ G z) ∧ ¬G (FUNPOW f n x) ⇒
  ∃m. m ≤ n ∧
      OWHILE H f x = SOME (FUNPOW f m x) ∧
      ¬H (FUNPOW f m x) ∧
      (∀k. k < m ⇒ H (FUNPOW f k x))
Proof
  strip_tac
  >> qexists_tac `LEAST m. ¬H (FUNPOW f m x)`
  >> numLib.LEAST_ELIM_TAC
  >> conj_tac >- metis_tac[]
  >> rpt strip_tac
  >- (spose_not_then assume_tac >>
      rename1 `¬(j ≤ n)` >>
      `n < j` by decide_tac >> metis_tac[])
  >- (irule OWHILE_from_finite_trace >> metis_tac[])
  >> metis_tac[]
QED

Theorem run_call_finite_trace:
  run_call es = SOME (r, es') ⇒
  ∃n. FUNPOW (step o SND) n (INL (), es) = (r, es') ∧
      ¬(ISL r ∧ LENGTH es.contexts ≤ LENGTH es'.contexts) ∧
      ∀k. k < n ⇒
        ISL (FST (FUNPOW (step o SND) k (INL (), es))) ∧
        LENGTH es.contexts ≤
          LENGTH (SND (FUNPOW (step o SND) k (INL (), es))).contexts
Proof
  rw[run_call_def]
  >> drule OWHILE_finite_trace
  >> strip_tac >> qexists_tac `n` >> gvs[GREATER_EQ]
  >> rpt strip_tac
  >> first_x_assum drule
  >> pairarg_tac >> simp[GREATER_EQ]
QED

Theorem run_call_trace_reaches:
  ∀n. (∀k. k < n ⇒
          ISL (FST (FUNPOW (step o SND) k (INL (), es))) ∧
          LENGTH es.contexts ≤
            LENGTH (SND (FUNPOW (step o SND) k (INL (), es))).contexts) ∧
      ISL (FST (FUNPOW (step o SND) n (INL (), es))) ⇒
      run_call_reaches es (SND (FUNPOW (step o SND) n (INL (), es)))
Proof
  Induct >- simp[]
  >> strip_tac
  >> `ISL (FST (FUNPOW (step o SND) n (INL (), es))) ∧
      LENGTH es.contexts ≤
        LENGTH (SND (FUNPOW (step o SND) n (INL (), es))).contexts`
       by (first_x_assum (qspec_then `n` mp_tac) >> simp[])
  >> `run_call_reaches es (SND (FUNPOW (step o SND) n (INL (), es)))`
       by (first_x_assum irule >> simp[] >> rpt strip_tac >>
           first_x_assum irule >> decide_tac)
  >> gvs[FUNPOW_SUC]
  >> qmatch_goalsub_abbrev_tac `step s`
  >> `LENGTH es.contexts ≤ LENGTH s.contexts`
       by (first_x_assum (qspec_then `n` mp_tac) >> simp[Abbr`s`])
  >> Cases_on `step s` >> gvs[]
  >> Cases_on `q` >> gvs[]
  >> irule run_call_reaches_step >> metis_tac[]
QED

Theorem run_call_nested_trace:
  d ≤ LENGTH e.contexts ∧
  ¬(λ(r,s). ISL r ∧ d ≤ LENGTH s.contexts)
      (FUNPOW (step o SND) n (INL (), e)) ⇒
  ∃m. m ≤ n ∧
      run_call e = SOME (FUNPOW (step o SND) m (INL (), e)) ∧
      ¬(λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
        (FUNPOW (step o SND) m (INL (), e)) ∧
      (∀k. k < m ⇒
        (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
          (FUNPOW (step o SND) k (INL (), e)))
Proof
  strip_tac >> simp[run_call_def, GREATER_EQ]
  >> irule OWHILE_nested_trace
  >> qexists_tac `λ(r,s). ISL r ∧ d ≤ LENGTH s.contexts`
  >> simp[FORALL_PROD] >> rpt strip_tac >> decide_tac
QED

Theorem OWHILE_trace_continuation:
  (∀k. k < n ⇒ G (FUNPOW f k x)) ∧ m ≤ n ⇒
  OWHILE G f x = OWHILE G f (FUNPOW f m x)
Proof
  strip_tac >> irule OWHILE_RTC
  >> `∀j. j ≤ n ⇒ RTC (λx y. G x ∧ f x = y) x (FUNPOW f j x)`
       suffices_by metis_tac[]
  >> Induct >- simp[]
  >> strip_tac >> simp[FUNPOW_SUC]
  >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1))
  >> qexists_tac `FUNPOW f j x`
  >> simp[]
QED

(* -------------------------------------------------------------------------
 * Per-step effect on accounts other than the current callee.
 * ------------------------------------------------------------------------- *)

(* Equality of the storage-key projection composes independently of all
 * other rollback fields. *)
Theorem rollback_preserves_storage_keys[local]:
  preserves_rollback m ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) m
Proof
  rw[preserves_rollback_def, preserves_def] >> metis_tac[]
QED

Theorem storage_keys_bind[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves (λs t. t.rollback.accesses.storageKeys =
                          s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (bind g f)
Proof
  strip_tac >> irule preserves_bind >> simp[]
QED

Theorem storage_keys_ignore_bind[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) f ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (ignore_bind g f)
Proof
  strip_tac >> irule preserves_ignore_bind >> simp[]
QED

Theorem access_address_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (access_address a)
Proof
  rw[preserves_def, access_address_def, domain_check_def,
     set_domain_def, ignore_bind_def, bind_def, return_def, fail_def,
     AllCaseEqs()] >> gvs[]
QED

Theorem access_slot_foreign_storage_key[local]:
  x ≠ SK y k ⇒
  preserves (λs t. fIN (SK y k) t.rollback.accesses.storageKeys ⇒
                   fIN (SK y k) s.rollback.accesses.storageKeys)
            (access_slot x)
Proof
  rw[preserves_def, access_slot_def, domain_check_def,
     set_domain_def, ignore_bind_def, bind_def, return_def, fail_def,
     AllCaseEqs()] >> gvs[finite_setTheory.fIN_IN,
                            finite_setTheory.toSet_fINSERT]
QED

Theorem update_accounts_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (update_accounts f)
Proof
  rw[preserves_def, update_accounts_def, return_def]
QED

Theorem storage_keys_copy_to_memory[local]:
  (∀f. src = SOME f ⇒ preserves_rollback f) ⇒
  preserves_rollback (copy_to_memory gas off srcOff sz src)
Proof
  Cases_on `src`
  >- (rw[copy_to_memory_def] >> pairarg_tac >> simp[write_memory_def])
  >> rw[copy_to_memory_def, write_memory_def]
  >> irule preserves_rollback_bind >> rw[]
  >> irule preserves_rollback_ignore_bind >> rw[]
  >> irule preserves_rollback_bind >> rw[]
QED

Theorem storage_keys_readers_rollback[local]:
  preserves_rollback get_tx_params ∧
  preserves_rollback get_current_code ∧
  preserves_rollback (get_code a) ∧
  preserves_rollback (get_return_data_check off sz) ∧
  preserves_rollback (write_memory off bytes)
Proof
  rpt conj_tac
  >- rw[preserves_rollback_def, get_tx_params_def, return_def]
  >> rw[get_current_code_def, get_code_def,
        get_return_data_check_def, write_memory_def]
  >> irule preserves_rollback_bind >> rw[]
QED

Theorem step_inst_plain_storage_keys[local]:
  op ≠ SLoad ∧ op ≠ SStore ∧ op ≠ TLoad ∧ op ≠ TStore ∧
  op ≠ SelfDestruct ∧ ¬is_call op ⇒
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (step_inst op)
Proof
  Cases_on `op` >> simp[is_call_def, step_inst_def]
  >> rpt strip_tac
  >> simp[step_binop_def, step_monop_def, step_modop_def,
          step_exp_def, step_keccak256_def, step_msgParams_def,
          step_txParams_def, step_context_def, step_balance_def,
          step_call_data_load_def, step_copy_to_memory_def,
          step_ext_code_size_def, step_ext_code_copy_def,
          step_ext_code_hash_def, step_return_data_copy_def,
          step_block_hash_def, step_self_balance_def, step_blob_hash_def,
          step_pop_def, step_mload_def, step_mstore_def,
          step_push_def, step_dup_def, step_swap_def,
          step_dupn_def, step_swapn_def, step_exchange_def,
          code_byte_def, exchange_stack_def,
          storage_keys_bind, storage_keys_ignore_bind,
          access_address_storage_keys, rollback_preserves_storage_keys,
          storage_keys_copy_to_memory]
  >> rpt (FIRST [irule storage_keys_bind,
                 irule storage_keys_ignore_bind] >>
          rw[access_address_storage_keys, rollback_preserves_storage_keys,
             storage_keys_copy_to_memory])
  >> irule rollback_preserves_storage_keys
  >> simp[storage_keys_copy_to_memory, storage_keys_readers_rollback,
          GSYM step_inst_def, step_inst_Log_preserves_rollback]
QED

Theorem proceed_call_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys)
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  simp[proceed_call_def]
  >> rpt (FIRST [irule storage_keys_bind,
                 irule storage_keys_ignore_bind, irule preserves_cond] >>
          rw[rollback_preserves_storage_keys, update_accounts_storage_keys])
QED

Theorem proceed_create_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys)
    (proceed_create sender address value code cappedGas)
Proof
  simp[proceed_create_def]
  >> rpt (FIRST [irule storage_keys_bind,
                 irule storage_keys_ignore_bind] >>
          rw[rollback_preserves_storage_keys, update_accounts_storage_keys])
QED

Theorem step_create_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (step_create two)
Proof
  simp[step_create_def, abort_create_exists_def]
  >> rpt (FIRST [irule storage_keys_bind,
                 irule storage_keys_ignore_bind, irule preserves_cond] >>
          rw[rollback_preserves_storage_keys, update_accounts_storage_keys,
             access_address_storage_keys, proceed_create_storage_keys])
QED

Theorem step_call_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (step_call op)
Proof
  simp[step_call_def]
  >> irule storage_keys_bind >> simp[rollback_preserves_storage_keys]
  >> qx_gen_tac `args` >> pairarg_tac >> simp[]
  >> irule storage_keys_bind >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> irule storage_keys_bind >> simp[access_address_storage_keys] >> gen_tac
  >> irule storage_keys_bind >> simp[rollback_preserves_storage_keys]
  >> qx_gen_tac `accounts`
  >> irule storage_keys_bind
  >> reverse conj_tac
  >- (Cases_on `get_delegate (lookup_account (w2w (EL 1 args)) accounts).code`
      >> simp[rollback_preserves_storage_keys]
      >> irule storage_keys_bind
      >> rw[access_address_storage_keys, rollback_preserves_storage_keys])
  >> Cases >> simp[]
  >> irule storage_keys_bind >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> pairarg_tac >> simp[]
  >> rpt (FIRST [irule storage_keys_bind,
                 irule storage_keys_ignore_bind, irule preserves_cond] >>
          rw[rollback_preserves_storage_keys, proceed_call_storage_keys])
QED

Theorem add_to_delete_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (add_to_delete a)
Proof
  rw[preserves_def, add_to_delete_def, return_def]
QED

Theorem step_self_destruct_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) step_self_destruct
Proof
  simp[step_self_destruct_def]
  >> rpt (FIRST [irule storage_keys_bind,
                 irule storage_keys_ignore_bind, irule preserves_cond] >>
          rw[rollback_preserves_storage_keys, update_accounts_storage_keys,
             access_address_storage_keys, add_to_delete_storage_keys])
QED

Theorem storage_key_backward_from_eq[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) m ⇒
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) m
Proof
  rw[preserves_def] >> metis_tac[]
QED

Theorem storage_key_backward_bind[local]:
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                          fIN z s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) (bind g f)
Proof
  strip_tac >> irule preserves_bind >> simp[] >> metis_tac[]
QED

Theorem storage_key_backward_ignore_bind[local]:
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) g ∧
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) f ⇒
  preserves (λs t. fIN z t.rollback.accesses.storageKeys ⇒
                   fIN z s.rollback.accesses.storageKeys) (ignore_bind g f)
Proof
  strip_tac >> irule preserves_ignore_bind >> simp[] >> metis_tac[]
QED

Theorem sstore_gas_foreign_storage_key[local]:
  address ≠ y ⇒
  preserves (λs t. fIN (SK y k) t.rollback.accesses.storageKeys ⇒
                   fIN (SK y k) s.rollback.accesses.storageKeys)
    (step_sstore_gas_consumption address key value)
Proof
  strip_tac >> simp[step_sstore_gas_consumption_def]
  >> rpt (FIRST [irule storage_key_backward_bind,
                 irule storage_key_backward_ignore_bind] >>
          rw[storage_key_backward_from_eq, rollback_preserves_storage_keys,
             access_slot_foreign_storage_key])
QED

Theorem step_sload_foreign_storage_key[local]:
  s.contexts ≠ [] ∧ step_sload transient s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  Cases_on `transient` >>
  rw[step_sload_def, bind_def, ignore_bind_def,
     pop_stack_def, get_callee_def, get_current_context_def,
     set_current_context_def, return_def, fail_def, assert_def,
     consume_gas_def, get_tStorage_def, get_accounts_def,
     push_stack_def, AllCaseEqs()]
  >> gvs[AllCaseEqs()]
  >> drule_at (Pat `access_slot _ _ = _`)
       (SRULE[preserves_def] access_slot_foreign_storage_key)
  >> simp[]
QED

Theorem step_sstore_foreign_storage_key[local]:
  s.contexts ≠ [] ∧ step_sstore transient s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  Cases_on `transient` >>
  rw[step_sstore_def, bind_def, ignore_bind_def,
     pop_stack_def, get_callee_def, get_current_context_def,
     set_current_context_def, return_def, fail_def, assert_def,
     consume_gas_def, assert_not_static_def, get_static_def,
     write_storage_def, write_transient_storage_def,
     get_tStorage_def, set_tStorage_def, update_accounts_def, AllCaseEqs()]
  >> gvs[AllCaseEqs()]
  >> drule_at (Pat `step_sstore_gas_consumption _ _ _ _ = _`)
       (SRULE[preserves_def] sstore_gas_foreign_storage_key)
  >> simp[]
QED

Theorem step_inst_foreign_storage_key[local]:
  s.contexts ≠ [] ∧ step_inst op s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  Cases_on `op = SLoad ∨ op = TLoad`
  >- (strip_tac >> gvs[step_inst_def] >>
      metis_tac[step_sload_foreign_storage_key])
  >> Cases_on `op = SStore ∨ op = TStore`
  >- (strip_tac >> gvs[step_inst_def] >>
      metis_tac[step_sstore_foreign_storage_key])
  >> strip_tac
  >> `preserves (λs t. t.rollback.accesses.storageKeys =
                       s.rollback.accesses.storageKeys) (step_inst op)` by
    (Cases_on `op = SelfDestruct`
     >- simp[step_inst_def, step_self_destruct_storage_keys]
     >> Cases_on `is_call op`
     >- (Cases_on `op` >> gvs[is_call_def, step_inst_def,
                             step_call_storage_keys, step_create_storage_keys])
     >> irule step_inst_plain_storage_keys >> gvs[])
  >> gvs[preserves_def] >> metis_tac[]
QED

Theorem step_inner_foreign_storage_key[local]:
  wf_state s ∧ step_inner s = (r,t) ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) t.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys
Proof
  rw[step_inner_def, bind_def, ignore_bind_def, get_current_context_def,
     return_def, fail_def, AllCaseEqs()]
  >> gvs[AllCaseEqs()]
  >> Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                       (FST (HD s.contexts)).pc`
  >- (gvs[COND_RATOR, AllCaseEqs()] >>
      metis_tac[step_inst_foreign_storage_key])
  >> gvs[bind_def, AllCaseEqs()]
  >> metis_tac[step_inst_foreign_storage_key,
       REWRITE_RULE[preserves_rollback_def]
         preserves_rollback_inc_pc_or_jump]
QED

Theorem proceed_call_saved_storage_keys[local]:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r,t) ∧ s.contexts ≠ [] ⇒
  (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  >> `s1.contexts = s.contexts` by
    (gvs[Abbr `g`, COND_RATOR, AllCaseEqs(), update_accounts_def, return_def])
  >> `ISL q` by
    (gvs[Abbr `g`, AllCaseEqs(), COND_RATOR, return_def, update_accounts_def])
  >> TOP_CASE_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> TOP_CASE_TAC
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC >> simp[return_def]
  >- (strip_tac >> gvs[])
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, t)`
  >> `ss.contexts ≠ []` by simp[Abbr `ss`]
  >> qmatch_asmsub_abbrev_tac `dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr `dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> `ss.contexts = (ctx, s.rollback) :: s.contexts` by simp[Abbr `ss`]
  >> simp[same_frame_rel_def]
QED

Theorem proceed_create_saved_storage_keys[local]:
  proceed_create sender address value code cappedGas s = (r,t) ∧
  s.contexts ≠ [] ⇒
  (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
QED

Theorem saved_storage_keys_bind[local]:
  preserves_same_frame g ∧
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  (∀x s r t. f x s = (r,t) ∧ s.contexts ≠ [] ∧
              LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ⇒
  ∀s r t. bind g f s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  rpt strip_tac
  >> drule_at (Pat `bind _ _ _ = _`) bind_psf_grows_extract
  >> simp[arithmeticTheory.GREATER_DEF] >> strip_tac
  >> `sm.contexts ≠ [] ∧ LENGTH sm.contexts = LENGTH s.contexts`
       by (gvs[same_frame_rel_def] >> Cases_on `sm.contexts` >> gvs[])
  >> gvs[preserves_def]
  >> metis_tac[]
QED

Theorem saved_storage_keys_same_frame[local]:
  preserves_same_frame m ⇒
  ∀s r t. m s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  rw[preserves_same_frame_def]
  >> first_x_assum drule >> simp[same_frame_rel_def]
QED

Theorem saved_storage_keys_ignore_bind[local]:
  preserves_same_frame g ∧
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) g ∧
  (∀s r t. f s = (r,t) ∧ s.contexts ≠ [] ∧
            LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ⇒
  ∀s r t. ignore_bind g f s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  simp[ignore_bind_def] >> strip_tac
  >> ho_match_mp_tac saved_storage_keys_bind >> simp[]
QED

Theorem saved_storage_keys_cond[local]:
  (∀s r t. m1 s = (r,t) ∧ s.contexts ≠ [] ∧
            LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ∧
  (∀s r t. m2 s = (r,t) ∧ s.contexts ≠ [] ∧
            LENGTH s.contexts < LENGTH t.contexts ⇒
     (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys) ⇒
  ∀s r t. (if b then m1 else m2) s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  Cases_on `b` >> simp[]
QED

Theorem step_call_saved_storage_keys[local]:
  ∀s r t. step_call op s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  simp[step_call_def]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> qx_gen_tac `args`
  >> pairarg_tac >> simp[]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[access_address_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> qx_gen_tac `accounts`
  >> ho_match_mp_tac saved_storage_keys_bind
  >> conj_tac >- (Cases_on `get_delegate (lookup_account (w2w (EL 1 args)) accounts).code` >> simp[])
  >> conj_tac
  >- (Cases_on `get_delegate (lookup_account (w2w (EL 1 args)) accounts).code`
      >> simp[rollback_preserves_storage_keys]
      >> irule storage_keys_bind
      >> rw[access_address_storage_keys, rollback_preserves_storage_keys])
  >> Cases >> simp[]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> pairarg_tac >> simp[]
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_cond >> conj_tac
  >- (ho_match_mp_tac saved_storage_keys_same_frame >> simp[SF ETA_ss])
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_cond >> conj_tac
  >- (ho_match_mp_tac saved_storage_keys_same_frame >> simp[SF ETA_ss])
  >> rpt strip_tac >> drule_all proceed_call_saved_storage_keys >> simp[]
QED

Theorem step_create_saved_storage_keys[local]:
  ∀s r t. step_create two s = (r,t) ∧ s.contexts ≠ [] ∧
           LENGTH s.contexts < LENGTH t.contexts ⇒
    (SND (HD t.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  simp[step_create_def]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[access_address_storage_keys, rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> rpt (ho_match_mp_tac saved_storage_keys_ignore_bind
          >> simp[rollback_preserves_storage_keys])
  >> ho_match_mp_tac saved_storage_keys_bind
  >> simp[rollback_preserves_storage_keys] >> gen_tac
  >> ho_match_mp_tac saved_storage_keys_cond >> conj_tac
  >- (ho_match_mp_tac saved_storage_keys_same_frame >> simp[SF ETA_ss])
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys, access_address_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_ignore_bind
  >> simp[rollback_preserves_storage_keys]
  >> ho_match_mp_tac saved_storage_keys_cond >> conj_tac
  >- (rpt strip_tac >> drule_all abort_create_exists_length
      >> simp[arithmeticTheory.GREATER_DEF])
  >> rpt strip_tac >> drule_all proceed_create_saved_storage_keys >> simp[]
QED

Theorem same_frame_saved_storage_keys[local]:
  s.contexts ≠ [] ∧ same_frame_rel s t ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
  MAP (λp. (SND p).accesses.storageKeys) s.contexts
Proof
  Cases_on `s.contexts` >> Cases_on `t.contexts`
  >> simp[same_frame_rel_def]
  >> rpt strip_tac >> gvs[]
QED

Theorem step_call_saved_storage_keys_shape[local]:
  step_call op s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    s.rollback.accesses.storageKeys ::
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts + 1
Proof
  strip_tac
  >> drule step_call_push_structure >> simp[arithmeticTheory.GREATER_DEF]
  >> strip_tac
  >> drule_all step_call_saved_storage_keys >> strip_tac
  >> drule_at (Pat `step_call _ _ = _`) step_call_grows_by_exactly_one
  >> simp[arithmeticTheory.GREATER_DEF]
  >> strip_tac
  >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
  >> qmatch_goalsub_rename_tac `MAP _ tail`
  >> Cases_on `tail` >> gvs[]
QED

Theorem step_create_saved_storage_keys_shape[local]:
  step_create two s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    s.rollback.accesses.storageKeys ::
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts + 1
Proof
  strip_tac
  >> drule step_create_push_structure >> simp[arithmeticTheory.GREATER_DEF]
  >> strip_tac
  >> drule_all step_create_saved_storage_keys >> strip_tac
  >> drule_at (Pat `step_create _ _ = _`) step_create_grows_by_exactly_one
  >> simp[arithmeticTheory.GREATER_DEF]
  >> strip_tac
  >> Cases_on `t.contexts` >> gvs[]
  >> irule LIST_EQ >> simp[EL_MAP]
  >> rpt strip_tac
  >> first_x_assum drule >> simp[]
QED

Theorem step_inst_saved_storage_keys_grow[local]:
  step_inst op s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    s.rollback.accesses.storageKeys ::
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts + 1
Proof
  strip_tac
  >> `is_call op` by
    (Cases_on `r`
     >- (Cases_on `x` >>
         drule step_inst_inl_grew_is_call >> simp[arithmeticTheory.GREATER_DEF])
     >> drule step_inst_inr_grew_is_call_family
     >> simp[arithmeticTheory.GREATER_DEF] >> strip_tac
     >> gvs[is_call_def])
  >> Cases_on `op` >> gvs[is_call_def, step_inst_def]
  >> metis_tac[step_call_saved_storage_keys_shape,
               step_create_saved_storage_keys_shape]
QED

Theorem psf_saved_storage_keys[local]:
  m s = (r,t) ∧ s.contexts ≠ [] ∧ preserves_same_frame m ⇒
  MAP (λp. (SND p).accesses.storageKeys) t.contexts =
    MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
  LENGTH t.contexts = LENGTH s.contexts ∧ t.contexts ≠ []
Proof
  rw[preserves_same_frame_def]
  >> first_x_assum drule >> simp[] >> strip_tac
  >> drule_all same_frame_saved_storage_keys >> strip_tac
  >> gvs[same_frame_rel_def]
  >> Cases_on `t.contexts` >> gvs[]
QED

Theorem step_inner_saved_storage_keys[local]:
  wf_state s ∧ step_inner s = (r,t) ⇒
  (MAP (λp. (SND p).accesses.storageKeys) t.contexts =
     MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
   LENGTH t.contexts = LENGTH s.contexts) ∨
  (MAP (λp. (SND p).accesses.storageKeys) t.contexts =
     s.rollback.accesses.storageKeys ::
     MAP (λp. (SND p).accesses.storageKeys) s.contexts ∧
   LENGTH t.contexts = LENGTH s.contexts + 1)
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >> mp_tac (REWRITE_RULE[same_frame_or_grow_def]
               same_frame_or_grow_step_inner_named)
  >> disch_then drule >> simp[] >> strip_tac
  >- (disj1_tac >> drule_all same_frame_saved_storage_keys
      >> gvs[same_frame_rel_def])
  >> disj2_tac
  >> gvs[step_inner_def, bind_def, ignore_bind_def, get_current_context_def,
         return_def, fail_def, COND_RATOR, AllCaseEqs()]
  >> gvs[vfmTypesTheory.option_CASE_rator, COND_RATOR, AllCaseEqs()]
  >~ [`step_inst Stop s = _`]
  >- (drule psf_saved_storage_keys >> simp[])
  >~ [`step_inst Invalid s = _`]
  >- (drule psf_saved_storage_keys >> simp[])
  >> gvs[bind_def, AllCaseEqs()]
  >~ [`inc_pc_or_jump op mid = _`]
  >- (`LENGTH mid.contexts ≥ LENGTH s.contexts` by
        (irule (INST_TYPE [``:'a`` |-> ``:unit``] same_frame_or_grow_length) >> simp[]
         >> qexistsl [`step_inst op`, `INL ()`] >> simp[])
      >> `mid.contexts ≠ []` by (Cases_on `mid.contexts` >> gvs[arithmeticTheory.GREATER_EQ])
      >> `preserves_same_frame (inc_pc_or_jump op)` by simp[]
      >> drule_at (Pat `preserves_same_frame _`) psf_saved_storage_keys
      >> disch_then drule >> simp[] >> strip_tac
      >> drule step_inst_saved_storage_keys_grow >> simp[])
  >> drule step_inst_saved_storage_keys_grow >> simp[]
QED

Theorem handle_exception_storage_keys[local]:
  s.contexts ≠ [] ∧ handle_exception e s = (r,t) ⇒
  t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∨
  (LENGTH t.contexts < LENGTH s.contexts ∧
   t.rollback.accesses.storageKeys =
     (SND (HD s.contexts)).accesses.storageKeys)
Proof
  Cases_on `s.contexts` >> simp[]
  >> PairCases_on `h`
  >> Cases_on `t'` >> gvs[]
  >> Cases_on `h0.msgParams.outputTo`
  >> Cases_on `e = NONE`
  >> Cases_on `e = SOME Reverted` >> gvs[]
  >> rw[handle_exception_def, bind_def, ignore_bind_def,
        get_gas_left_def, get_current_context_def, return_def,
        consume_gas_def, set_return_data_def, set_current_context_def,
        get_num_contexts_def, get_return_data_def, get_output_to_def,
        reraise_def, assert_def, fail_def,
        inc_pc_def, push_stack_def, write_memory_def,
        pop_and_incorporate_context_def, pop_context_def,
        set_rollback_def, unuse_gas_def,
        update_gas_refund_def, push_logs_def, AllCaseEqs()]
  >> gvs[AllCaseEqs()]
QED

Theorem handle_step_storage_keys[local]:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ⇒
  t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∨
  (LENGTH t.contexts < LENGTH s.contexts ∧
   t.rollback.accesses.storageKeys =
     (SND (HD s.contexts)).accesses.storageKeys)
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[handle_def]
  >> strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> simp[] >> strip_tac
  >> drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac
  >> drule_all handle_create_preserves_length >> strip_tac
  >> drule handle_create_preserves_accesses >> strip_tac
  >> drule_all handle_exception_storage_keys >> strip_tac >> gvs[]
QED

Theorem step_same_frame_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts = LENGTH s.contexts ⇒
  TL s'.contexts = TL s.contexts ∧
  SND (HD s'.contexts) = SND (HD s.contexts) ∧
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts)
Proof
  strip_tac
  >> `outputTo_consistent s`
       by metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def]
  >> drule_all step_same_frame
  >> rw[same_frame_rel_def, callee_local_changes_def,
        foreign_account_change_def]
QED

Theorem call_prefix_refl:
  s.contexts ≠ [] ⇒
  cp_rel s s ∧ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  simp[cp_rel_refl]
QED

Theorem call_prefix_trans:
  (cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) ∧
  (cp_rel t u ∧ u.rollback.accesses.storageKeys = t.rollback.accesses.storageKeys) ⇒
  cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  metis_tac[cp_rel_trans]
QED

Theorem call_prefix_contexts:
  cp_rel s t ∧ s.contexts ≠ [] ⇒
  t.contexts ≠ [] ∧ LENGTH t.contexts = LENGTH s.contexts
Proof
  rw[cp_rel_def] >> Cases_on `s.contexts` >> gvs[]
QED

Theorem bind_call_prefix_grows_extract:
  (cp_rel s0 s ∧ s.rollback.accesses.storageKeys = s0.rollback.accesses.storageKeys) ∧
  s0.contexts ≠ [] ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) g ∧
  bind g f s = (r,t) ∧ LENGTH s0.contexts < LENGTH t.contexts ⇒
  ∃x u. g s = (INL x,u) ∧
    (cp_rel s0 u ∧ u.rollback.accesses.storageKeys = s0.rollback.accesses.storageKeys) ∧
    f x u = (r,t)
Proof
  rw[preserves_when_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> drule_all call_prefix_contexts >> strip_tac
  >> first_x_assum drule >> simp[] >> strip_tac
  >> imp_res_tac call_prefix_contexts
  >> gvs[]
  >- (irule cp_rel_trans >> qexists_tac `s` >> simp[])
  >> strip_tac >> gvs[]
QED

Theorem call_prefix_of_cp_keys:
  cp m ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) m ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) m
Proof
  rw[cp_eq_preserves_when, preserves_when_def] >> metis_tac[]
QED

Theorem call_prefix_keys_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (pop_stack n) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (memory_expansion_info off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (consume_gas gas) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) assert_not_static ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (expand_memory ext) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (set_return_data data)
Proof
  rw[preserves_when_def, pop_stack_def, memory_expansion_info_def,
     consume_gas_def, assert_not_static_def, expand_memory_def,
     set_return_data_def, get_static_def, get_current_context_def,
     set_current_context_def, bind_def, ignore_bind_def, return_def,
     assert_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem call_prefix_keys_access_address:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (access_address a)
Proof
  rw[preserves_when_def, access_address_def, domain_check_def,
     set_domain_def, ignore_bind_def, bind_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem call_prefix_keys_getters:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_accounts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_gas_left ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_callee ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_num_contexts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (return x)
Proof
  rw[preserves_when_def, get_accounts_def, get_gas_left_def,
     get_callee_def, get_num_contexts_def, get_current_context_def,
     bind_def, return_def, fail_def] >> gvs[AllCaseEqs()]
QED

Theorem call_prefix_bind:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (bind g f)
Proof
  strip_tac >> irule preserves_when_bind >> simp[]
  >> metis_tac[call_prefix_trans, call_prefix_contexts]
QED

Theorem call_prefix_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (pop_stack n) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (memory_expansion_info off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (consume_gas gas) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) assert_not_static ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (expand_memory ext) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (set_return_data data) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (access_address a) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_accounts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_gas_left ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_callee ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) get_num_contexts ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (return x)
Proof
  rpt conj_tac >> irule call_prefix_of_cp_keys
  >> simp[call_prefix_keys_leaves, call_prefix_keys_access_address,
          call_prefix_keys_getters]
QED

Theorem call_prefix_delegate_code_selection:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys)
    (case get_delegate bytecode of
       NONE => return (bytecode, 0)
     | SOME d => do
         cost <- access_address d;
         return ((lookup_account d accounts).code, cost)
       od)
Proof
  Cases_on `get_delegate bytecode` >> simp[call_prefix_leaves]
  >> irule call_prefix_bind >> simp[call_prefix_leaves]
QED

Theorem step_call_reaches_proceed_call:
  step_call op s = (r,s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∃u sender address value ao az code gas mr.
    cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
    proceed_call op sender address value ao az code gas (Memory mr) u = (r,s') ∧
    sender = (FST (HD s.contexts)).msgParams.callee ∧
    value ≤ (lookup_account sender s.rollback.accounts).balance ∧
    code = (case get_delegate (lookup_account address s.rollback.accounts).code of
      NONE => (lookup_account address s.rollback.accounts).code
    | SOME d => (lookup_account d s.rollback.accounts).code) ∧
    (¬call_has_value op ⇒ value = 0) ∧
    (op = Call ∧ 0 < value ⇒ ¬(FST (HD s.contexts)).msgParams.static)
Proof
  let
    val peel =
      drule_at (Pat `bind`) bind_call_prefix_grows_extract
      >> simp[call_prefix_leaves]
      >> disch_then (qspec_then `s` mp_tac) >> simp[]
      >> qpat_x_assum `bind _ _ _ = _` kall_tac
      >> strip_tac >> gvs[]
  in
  simp[step_call_def] >> strip_tac
  >> `cp_rel s s ∧ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys`
    by simp[call_prefix_refl]
  >> peel >> pairarg_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `proceed_call op _ address value ao az _ _ rd`
  >> peel
  >> peel
  >> `u''.rollback.accounts = s.rollback.accounts` by gvs[cp_rel_def]
  >> gvs[get_accounts_def, Once bind_def, return_def]
  >> drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> (impl_tac >- irule call_prefix_delegate_code_selection)
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[] >> pairarg_tac >> gvs[]
  >> `code = (case get_delegate (lookup_account address s.rollback.accounts).code of
       NONE => (lookup_account address s.rollback.accounts).code
     | SOME d => (lookup_account d s.rollback.accounts).code)`
    by (Cases_on `get_delegate (lookup_account address s.rollback.accounts).code`
        >> gvs[bind_def, return_def, AllCaseEqs()])
  >> peel >> pairarg_tac >> gvs[ignore_bind_def]
  >> qpat_x_assum `pop_stack _ _ = _` kall_tac
  >> qpat_x_assum `memory_expansion_info _ _ _ = _` kall_tac
  >> qpat_x_assum `access_address _ _ = _` kall_tac
  >> qpat_x_assum `(case _ of NONE => _ | SOME _ => _) _ = _` kall_tac
  >> qpat_x_assum `get_gas_left _ = _` kall_tac
  >> qpat_x_assum `call_gas _ _ _ _ _ = _` kall_tac
  >> peel
  >> drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[] >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> (impl_tac >- (Cases_on `op = Call ∧ 0 < value` >> simp[call_prefix_leaves]))
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[]
  >> `op = Call ∧ 0 < value ⇒ ¬(FST (HD s.contexts)).msgParams.static`
    by (strip_tac
        >> gvs[assert_not_static_def, get_static_def, get_current_context_def,
               bind_def, assert_def, return_def, fail_def, cp_rel_def, AllCaseEqs()])
  >> peel
  >> peel
  >> rename1 `get_callee beforeSender = (INL sender,afterSender)`
  >> `sender = (FST (HD s.contexts)).msgParams.callee`
    by gvs[get_callee_def, get_current_context_def, bind_def, return_def,
           fail_def, cp_rel_def, AllCaseEqs()]
  >> gvs[COND_RATOR]
  >> Cases_on `(lookup_account (FST (HD s.contexts)).msgParams.callee
                 s.rollback.accounts).balance < value` >> gvs[]
  >- (drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> peel
  >> peel >> gvs[COND_RATOR]
  >> rename1 `get_num_contexts depthState = (INL depth,entry)`
  >> Cases_on `depth > 1024` >> gvs[]
  >- (drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> qexistsl_tac [`entry`, `address`, `value`, `ao`, `az`, `stipend`]
  >> simp[] >> gvs[Abbr `rd`]
  >> qexists_tac `<|offset := w2n (EL ((if call_has_value op then 1 else 0) + 4) x);
                   size := w2n (EL ((if call_has_value op then 1 else 0) + 5) x)|>`
  >> simp[] >> simp[Abbr `value`]
  end
QED


Theorem proceed_call_saved_rollback:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  SND (HD s'.contexts) = s.rollback ∧
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
QED

Theorem proceed_call_nonprecompile_frame:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  ∃static t.
    FST (HD s'.contexts) =
      initial_context (if op = CallCode ∨ op = DelegateCall then sender else address)
        code static rd t ∧
    s'.rollback.accounts =
      (if op ≠ CallCode ∧ 0 < value then
         transfer_value sender address value s.rollback.accounts
       else s.rollback.accounts)
Proof
  strip_tac >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
  >> metis_tac[]
QED

Theorem proceed_call_nonprecompile_message:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  r = INL () ∧ s'.rollback.tStorage = s.rollback.tStorage ∧
  ∃tx.
    FST (HD s'.contexts) =
      initial_context (if op = CallCode ∨ op = DelegateCall then sender else address)
        code (op = StaticCall ∨ (FST (HD s.contexts)).msgParams.static) rd tx ∧
    tx.from = (if op = DelegateCall then (FST (HD s.contexts)).msgParams.caller else sender) ∧
    tx.value = (if op = DelegateCall then (FST (HD s.contexts)).msgParams.value else value)
Proof
  strip_tac >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
  >> qmatch_goalsub_abbrev_tac `initial_context _ _ _ _ calltx`
  >> qexists_tac `calltx` >> simp[Abbr `calltx`]
  >> Cases_on `op = DelegateCall` >> simp[]
QED

Theorem terminal_bind:
  (∀x s. ISR (FST (f x s))) ⇒ ISR (FST (bind g f s))
Proof
  rw[bind_def] >> Cases_on `g s` >> Cases_on `q` >> gvs[]
QED

Theorem terminal_ignore_bind:
  (∀s. ISR (FST (f s))) ⇒ ISR (FST (ignore_bind g f s))
Proof
  simp[ignore_bind_def] >> strip_tac >> irule terminal_bind >> simp[]
QED

Theorem dispatch_precompiles_terminal:
  ISR (FST (dispatch_precompiles a s))
Proof
  rw[dispatch_precompiles_def]
  >> simp[precompile_ecrecover_def, precompile_sha2_256_def,
          precompile_ripemd_160_def, precompile_identity_def,
          precompile_modexp_def, precompile_ecadd_def,
          precompile_ecmul_def, precompile_ecpairing_def,
          precompile_blake2f_def, precompile_point_eval_def,
          precompile_bls_g1add_def, precompile_bls_g1msm_def,
          precompile_bls_g2add_def, precompile_bls_g2msm_def,
          precompile_bls_pairing_def, precompile_bls_map_fp_to_g1_def,
          precompile_bls_map_fp2_to_g2_def, precompile_p256verify_def,
          fail_def]
  >> rpt (FIRST [irule terminal_bind >> rpt gen_tac,
                 irule terminal_ignore_bind >> gen_tac,
                 CHANGED_TAC (simp[finish_def, fail_def]),
                 BasicProvers.PURE_CASE_TAC])
QED

Theorem proceed_call_inl_nonprecompile:
  proceed_call op sender address value ao az code gas rd s = (INL (), s') ∧
  s.contexts ≠ [] ⇒ ¬fIN address precompile_addresses
Proof
  strip_tac >> strip_tac
  >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed`
  >> `ISR (FST ((dispatch_precompiles address : unit execution) pushed))`
       by simp[dispatch_precompiles_terminal]
  >> qpat_x_assum `ISR _` mp_tac
  >> qpat_x_assum `dispatch_precompiles _ _ = _` (fn th => simp[th, sumTheory.ISR])
QED

Theorem step_call_push_storage_keys:
  step_call op s = (INL (),s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_call_inl_nonprecompile >> strip_tac
  >> drule_all proceed_call_saved_rollback >> simp[]
QED

Theorem step_call_push_foreign_accounts:
  step_call op s = (INL (),s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∀y. foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts) ∧
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y (SND (HD s'.contexts)).accounts)
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_call_inl_nonprecompile >> strip_tac
  >> drule_all proceed_call_saved_rollback >> strip_tac
  >> drule_all proceed_call_nonprecompile_frame >> strip_tac
  >> gvs[cp_rel_def]
  >> rw[foreign_account_change_def, transfer_value_preserves_code,
        transfer_value_preserves_storage, transfer_value_preserves_nonce]
QED

Theorem transfer_value_zero[local,simp]:
  transfer_value sender address 0 accounts = accounts
Proof
  simp[transfer_value_def]
QED

Theorem step_call_push_new_frame:
  step_call op s = (INL (),s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ∧
  (FST (HD s'.contexts)).msgParams.callee ≠
    (FST (HD s.contexts)).msgParams.callee ⇒
  ∃code static mr t.
    FST (HD s'.contexts) =
      initial_context (FST (HD s'.contexts)).msgParams.callee
        code static (Memory mr) t ∧
    code = (case get_delegate
               (lookup_account (FST (HD s'.contexts)).msgParams.callee
                  s.rollback.accounts).code of
          NONE => (lookup_account (FST (HD s'.contexts)).msgParams.callee
                     s.rollback.accounts).code
        | SOME d => (lookup_account d s.rollback.accounts).code) ∧
    (FST (HD s'.contexts)).msgParams.caller =
      (FST (HD s.contexts)).msgParams.callee ∧
    (FST (HD s'.contexts)).msgParams.value ≤
      (lookup_account (FST (HD s.contexts)).msgParams.callee
         s.rollback.accounts).balance ∧
    s'.rollback.accounts =
      transfer_value (FST (HD s.contexts)).msgParams.callee
        (FST (HD s'.contexts)).msgParams.callee
        (FST (HD s'.contexts)).msgParams.value s.rollback.accounts ∧
    s'.rollback.tStorage = s.rollback.tStorage ∧
    (static ⇒ (SND (HD s'.contexts)).accounts = s'.rollback.accounts)
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_call_inl_nonprecompile >> strip_tac
  >> drule_all proceed_call_saved_rollback >> strip_tac
  >> drule_all proceed_call_nonprecompile_frame >> strip_tac
  >> qpat_x_assum `FST (HD s'.contexts) = _` kall_tac
  >> drule_all proceed_call_nonprecompile_message >> strip_tac
  >> qpat_x_assum `step_call _ _ = _` kall_tac
  >> qpat_x_assum `proceed_call _ _ _ _ _ _ _ _ _ _ = _` kall_tac
  >> gvs[cp_rel_def]
  >> Cases_on `op = CallCode ∨ op = DelegateCall`
  >- gvs[initial_msg_params_def]
  >> gvs[initial_msg_params_def]
  >> qexistsl_tac [`op = StaticCall ∨ (FST (HD s.contexts)).msgParams.static`, `mr`, `tx`]
  >> Cases_on `tx.value = 0` >> gvs[]
  >> `op = Call` by gvs[call_has_value_def]
  >> gvs[]
QED

Theorem create_prefix_keys_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (read_memory off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (assert b e) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (ensure_storage_in_domain a)
Proof
  rw[preserves_when_def, read_memory_def, get_current_context_def,
     ensure_storage_in_domain_def, domain_check_def, set_domain_def,
     bind_def, ignore_bind_def, assert_def, return_def, fail_def]
  >> gvs[AllCaseEqs()]
QED

Theorem create_prefix_leaves:
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (read_memory off sz) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (assert b e) ∧
  preserves_when (λs. s.contexts ≠ [])
    (λs t. cp_rel s t ∧ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys) (ensure_storage_in_domain a)
Proof
  rpt conj_tac >> irule call_prefix_of_cp_keys
  >> simp[create_prefix_keys_leaves]
QED

val create_peel =
  drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[call_prefix_leaves, create_prefix_leaves]
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[];

Theorem step_create_reaches_proceed_create:
  step_create two s = (r,s') ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∃u sender address value code gas.
    cp_rel s u ∧ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
    proceed_create sender address value code gas u = (r,s') ∧
    sender = (FST (HD s.contexts)).msgParams.callee ∧
    ¬account_already_created (lookup_account address s.rollback.accounts)
Proof
  simp[step_create_def, ignore_bind_def] >> strip_tac
  >> `cp_rel s s ∧ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys`
    by simp[call_prefix_refl]
  >> create_peel >> create_peel >> create_peel
  >> create_peel >> create_peel >> create_peel
  >> rename1 `get_callee beforeSender = (INL sender,afterSender)`
  >> `sender = (FST (HD s.contexts)).msgParams.callee`
    by gvs[get_callee_def, get_current_context_def, bind_def, return_def,
           fail_def, cp_rel_def, AllCaseEqs()]
  >> `afterSender.rollback.accounts = s.rollback.accounts` by gvs[cp_rel_def]
  >> gvs[get_accounts_def, Once bind_def, return_def]
  >> create_peel >> create_peel >> create_peel
  >> create_peel >> create_peel >> create_peel
  >> qpat_x_assum `pop_stack _ _ = _` kall_tac
  >> qpat_x_assum `memory_expansion_info _ _ _ = _` kall_tac
  >> qpat_x_assum `consume_gas _ _ = _` kall_tac
  >> qpat_x_assum `expand_memory _ _ = _` kall_tac
  >> qpat_x_assum `read_memory _ _ _ = _` kall_tac
  >> qmatch_asmsub_abbrev_tac `proceed_create _ address value code gas`
  >> qmatch_asmsub_abbrev_tac `if (_ ∨ _ ∨ _) then _ else _`
  >> qmatch_asmsub_abbrev_tac `(if guard then abort_unuse _ else _) _ = _`
  >> Cases_on `guard`
  >- (fs[COND_RATOR, IgnAsm `Abbrev _`]
      >> drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> gvs[COND_RATOR, ignore_bind_def]
  >> create_peel >> create_peel
  >> Cases_on `account_already_created (lookup_account address s.rollback.accounts)`
  >> gvs[COND_RATOR]
  >- (imp_res_tac call_prefix_contexts
      >> drule_all abort_create_exists_length >> simp[])
  >> rename1 `proceed_create _ address value code gas entry = (r,s')`
  >> qexistsl_tac [`entry`, `address`, `value`, `code`, `gas`] >> simp[]
QED

Theorem proceed_create_frame_effects:
  proceed_create sender address value code gas s = (r,s') ∧ s.contexts ≠ [] ⇒
  r = INL () ∧
  s'.rollback.accounts =
    transfer_value sender address value (increment_nonce address (increment_nonce sender s.rollback.accounts)) ∧
  (SND (HD s'.contexts)).accounts = increment_nonce sender s.rollback.accounts ∧
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  ∃t. FST (HD s'.contexts) = initial_context address code F (Code address) t
Proof
  strip_tac
  >> gvs[proceed_create_def, update_accounts_def, get_rollback_def,
         get_original_def, set_original_def, push_context_def,
         ignore_bind_def, bind_def, return_def, fail_def, AllCaseEqs()]
  >> metis_tac[]
QED

Theorem create_foreign_account_updates:
  y ≠ sender ∧ ¬account_already_created (lookup_account address accounts) ⇒
  foreign_account_change (lookup_account y accounts)
    (lookup_account y (transfer_value sender address value
      (increment_nonce address (increment_nonce sender accounts)))) ∧
  foreign_account_change (lookup_account y accounts)
    (lookup_account y (increment_nonce sender accounts))
Proof
  rw[foreign_account_change_def, transfer_value_preserves_code,
     transfer_value_preserves_storage, transfer_value_preserves_nonce,
     increment_nonce_def, lookup_account_def, update_account_def]
  >> Cases_on `y = address` >> gvs[combinTheory.APPLY_UPDATE_THM]
QED

Theorem step_create_push_foreign_accounts:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
  foreign_account_change (lookup_account y s.rollback.accounts)
    (lookup_account y s'.rollback.accounts) ∧
  foreign_account_change (lookup_account y s.rollback.accounts)
    (lookup_account y (SND (HD s'.contexts)).accounts)
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_create_frame_effects >> strip_tac
  >> `u.rollback.accounts = s.rollback.accounts` by gvs[cp_rel_def]
  >> gvs[] >> irule create_foreign_account_updates >> simp[]
QED

Theorem proceed_create_stack_effects:
  proceed_create sender address value code gas s = (r,s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts))
Proof
  strip_tac
  >> gvs[proceed_create_def, update_accounts_def, get_rollback_def,
         get_original_def, set_original_def, push_context_def,
         ignore_bind_def, bind_def, return_def, fail_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[set_last_accounts_def]
  >> Cases_on `t` >> gvs[]
  >> simp[MAP_SNOC, MAP_FRONT]
  >> qspec_then `MAP FST (h'::t')` mp_tac SNOC_LAST_FRONT
  >> simp[]
QED

Theorem step_create_push_stack:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ISL r ∧ LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts))
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_create_frame_effects >> strip_tac
  >> drule_all proceed_create_stack_effects >> strip_tac
  >> gvs[cp_rel_def]
QED

Theorem step_create_push_storage_keys:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_create_frame_effects >> simp[]
QED

Theorem step_create_push_new_frame:
  s.contexts ≠ [] ∧ step_create two s = (r,s') ∧
  LENGTH s.contexts < LENGTH s'.contexts ⇒
  ∃code t.
    FST (HD s'.contexts) =
      initial_context (FST (HD s'.contexts)).msgParams.callee code F
        (Code (FST (HD s'.contexts)).msgParams.callee) t ∧
    ¬account_already_created
      (lookup_account (FST (HD s'.contexts)).msgParams.callee s.rollback.accounts)
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac
  >> drule_all call_prefix_contexts >> strip_tac
  >> drule_all proceed_create_frame_effects >> strip_tac
  >> ` (FST (HD s'.contexts)).msgParams.callee = address`
    by simp[initial_context_def, initial_msg_params_def]
  >> qexistsl_tac [`code`, `t`] >> simp[]
QED

Theorem step_grow_dispatch:
  wf_state s ∧ step s = (r,s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  r = INL () ∧
  ((∃op. step_call op s = (INL (),s')) ∨
   (∃two. step_create two s = (INL (),s')))
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  >- (simp[] >> strip_tac >> gvs[]
      >> gvs[Abbr `inner`, bind_def, AllCaseEqs()]
      >> gvs[get_current_context_def, return_def, fail_def, bind_def]
      >> gvs[option_CASE_rator, CaseEq "option", COND_RATOR, CaseEq "bool"]
      >~ [`step_inst Stop`]
      >- (drule_at Any psf_imp_length_contexts_preserved >> simp[])
      >~ [`step_inst Invalid`]
      >- (drule_at Any psf_imp_length_contexts_preserved >> simp[])
      >> gvs[ignore_bind_def, bind_def, AllCaseEqs()]
      >> rename1 `step_inst op s = (INL (),mid)`
      >> drule_at Any psf_imp_length_contexts_preserved >> simp[]
      >> (impl_keep_tac >- (strip_tac >>
          gvs[inc_pc_or_jump_def, COND_RATOR, AllCaseEqs(), return_def,
              bind_def, get_current_context_def, fail_def]))
      >> strip_tac
      >> `LENGTH s.contexts < LENGTH mid.contexts` by simp[]
      >> `is_call op` by (irule step_inst_inl_grew_is_call
          >> qexistsl_tac [`s`, `mid`] >> simp[])
      >> gvs[inc_pc_or_jump_def, return_def, COND_RATOR, CaseEq "bool"]
      >> Cases_on `op` >> gvs[is_call_def, step_inst_def]
      >> metis_tac[])
  >> simp[] >> strip_tac
  >> `same_frame_or_grow inner` by simp[Abbr `inner`]
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts` by
      (drule_all same_frame_or_grow_length >> simp[])
  >> `r'.contexts ≠ []` by (strip_tac >> gvs[] >> Cases_on `s.contexts` >> gvs[])
  >> `LENGTH s'.contexts ≤ LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts`
  >- (drule handle_step_shrinks_by_one >> simp[])
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
      (irule outputTo_consistent_stack_imp_consistent >> gvs[wf_state_def])
  >> `¬vfm_abort y` by (irule step_inner_inr_grow_not_abort
      >> qexistsl_tac [`s`, `r'`] >> simp[Abbr `inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[])
  >> `LENGTH r'.contexts ≥ 2` by simp[]
  >> `LENGTH r'.contexts = LENGTH s.contexts + 1` by
      (qunabbrev_tac `inner` >> drule_then drule step_inner_grows_by_exactly_one >> gvs[])
  >> drule_at (Pat `handle_step`) handle_step_not_abort_pops >> gvs[]
  >> `decreases_gas_cred T 0 0 inner` suffices_by
      (gvs[decreases_gas_cred_def]
       >> disch_then (qspec_then `s` mp_tac) >> rw[]
       >> gvs[wf_state_def, EVERY_MEM])
  >> simp[Abbr `inner`]
  >> irule decreases_gas_cred_bind_mono
  >> qexistsl_tac [`T`, `F`] >> simp[] >> gen_tac
  >> rw[] >> CASE_TAC >> rw[]
  >> irule decreases_gas_cred_ignore_bind_mono >> rw[]
  >> qexistsl_tac [`F`, `T`] >> simp[]
QED

(* A push copies the stack below, except that CREATE's set_original may
 * change the last saved rollback.  Only the callee's nonce and the created
 * account's nonce change, and the latter only when it is not yet created. *)
Theorem step_push_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  ISL r ∧
  LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts)) ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts) ∧
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y (SND (HD s'.contexts)).accounts)
Proof
  strip_tac
  >> `s.contexts ≠ [] ∧ outputTo_consistent_stack s` by gvs[wf_state_def]
  >> `1 ≤ LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[])
  >> drule step_push_structure >> simp[] >> strip_tac
  >> drule_all step_grow_dispatch >> strip_tac
  >- (drule step_call_push_structure >> simp[] >> strip_tac
      >> `SND (EL 1 s'.contexts) = SND (HD s.contexts)` by
           (Cases_on `s'.contexts` >> gvs[] >> Cases_on `t` >> gvs[])
      >> drule_all step_call_push_foreign_accounts >> simp[])
  >> drule_all step_create_push_stack >> strip_tac
  >> simp[] >> gen_tac >> disch_tac
  >> drule_all step_create_push_foreign_accounts >> simp[]
QED

(* The frame a push enters as a new callee: a CALL or STATICCALL running the
 * target's code (or its EIP-7702 delegate's), or a CREATE at an address
 * that is not yet created. *)
Theorem step_push_new_frame:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ∧
  (FST (HD s'.contexts)).msgParams.callee ≠
    (FST (HD s.contexts)).msgParams.callee ⇒
  ∃code static rd t.
    FST (HD s'.contexts) =
      initial_context (FST (HD s'.contexts)).msgParams.callee
        code static rd t ∧
    ((∃mr. rd = Memory mr) ∧
     code =
       (case get_delegate
               (lookup_account (FST (HD s'.contexts)).msgParams.callee
                  s.rollback.accounts).code of
          NONE => (lookup_account (FST (HD s'.contexts)).msgParams.callee
                     s.rollback.accounts).code
        | SOME d => (lookup_account d s.rollback.accounts).code) ∧
     (FST (HD s'.contexts)).msgParams.caller =
       (FST (HD s.contexts)).msgParams.callee ∧
     (FST (HD s'.contexts)).msgParams.value ≤
       (lookup_account (FST (HD s.contexts)).msgParams.callee
          s.rollback.accounts).balance ∧
     s'.rollback.accounts =
       transfer_value (FST (HD s.contexts)).msgParams.callee
         (FST (HD s'.contexts)).msgParams.callee
         (FST (HD s'.contexts)).msgParams.value s.rollback.accounts ∧
     s'.rollback.tStorage = s.rollback.tStorage ∨
     rd = Code (FST (HD s'.contexts)).msgParams.callee ∧
     ¬account_already_created
        (lookup_account (FST (HD s'.contexts)).msgParams.callee
           s.rollback.accounts)) ∧
    (static ⇒ (∃mr. rd = Memory mr) ∧
              (SND (HD s'.contexts)).accounts = s'.rollback.accounts)
Proof
  strip_tac >> drule_all step_grow_dispatch >> strip_tac
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >- (drule_all step_call_push_new_frame >> strip_tac
      >> qexistsl_tac [`code`, `static`, `Memory mr`, `t`] >> simp[])
  >> drule_all step_create_push_new_frame >> strip_tac
  >> qexistsl_tac [`code`, `F`, `Code (FST (HD s'.contexts)).msgParams.callee`, `t`]
  >> simp[]
QED

Theorem handle_create_foreign_accounts:
  handle_create e s = (q,s') ∧ s.contexts ≠ [] ∧ outputTo_consistent s ⇒
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
    foreign_account_change (lookup_account y s.rollback.accounts)
      (lookup_account y s'.rollback.accounts)
Proof
  strip_tac
  >> mp_tac psf_handle_create >> rw[psf_def]
  >> first_x_assum drule >> simp[]
  >> rw[same_frame_rel_def, callee_local_changes_def, foreign_account_change_def]
QED

Theorem handle_step_pop_foreign_boundary:
  s.contexts = (callee,callee_rb)::parent::rest ∧
  outputTo_consistent_ctx callee ∧ handle_step e s = (q,s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
  ∃new_parent.
    s'.contexts = (new_parent,SND parent)::rest ∧
    new_parent.msgParams = (FST parent).msgParams ∧
    (s'.rollback.accounts = callee_rb.accounts ∨
     ∀y. y ≠ callee.msgParams.callee ⇒
       foreign_account_change (lookup_account y s.rollback.accounts)
         (lookup_account y s'.rollback.accounts))
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[handle_def]
  >> `s.contexts ≠ []` by simp[]
  >> strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e',s1)`
  >> drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac
  >> `s1.contexts = (FST (HD s1.contexts),callee_rb)::parent::rest` by
      (Cases_on `s1.contexts` >> fs[] >> PairCases_on `h` >> fs[])
  >> drule_all handle_create_preserves_length >> strip_tac
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s1.contexts` by decide_tac
  >> drule_all handle_exception_pop_generic_gen >> strip_tac >> gvs[]
  >> disj2_tac
  >> `s.contexts ≠ [] ∧ outputTo_consistent s`
    by gvs[outputTo_consistent_def, outputTo_consistent_ctx_def]
  >> drule handle_create_foreign_accounts >> simp[]
QED

(* A pop restores the popped frame's saved rollback (failure) or keeps the
 * current one, where only the popped frame's callee changed (success). *)
Theorem step_pop_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  ∃new_head parent rest.
    s.contexts = HD s.contexts :: parent :: rest ∧
    s'.contexts = (new_head, SND parent) :: rest ∧
    new_head.msgParams = (FST parent).msgParams ∧
    (s'.rollback.accounts = (SND (HD s.contexts)).accounts ∨
     ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
         foreign_account_change (lookup_account y s.rollback.accounts)
                                (lookup_account y s'.rollback.accounts))
Proof
  strip_tac
  >> `s.contexts ≠ [] ∧ outputTo_consistent_stack s` by gvs[wf_state_def]
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  >- (simp[] >> strip_tac >> gvs[]
      >> `same_frame_or_grow inner` by simp[Abbr `inner`]
      >> drule_all same_frame_or_grow_length >> simp[])
  >> simp[] >> strip_tac
  >> `same_frame_or_grow inner` by simp[Abbr `inner`]
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts` by
      (drule_all same_frame_or_grow_length >> simp[])
  >> `r'.contexts ≠ []` by (Cases_on `r'.contexts` >> fs[])
  >> `LENGTH s'.contexts + 1 ≥ LENGTH r'.contexts ∧
      LENGTH s'.contexts ≤ LENGTH r'.contexts`
      by (drule handle_step_shrinks_by_one >> fs[])
  >> `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac
  >> `same_frame_rel s r'` by (drule_all same_frame_or_grow_eq_length >> fs[])
  >> `LENGTH s.contexts ≥ 2` by
      (CCONTR_TAC >> fs[]
       >> `LENGTH s.contexts = 1` by decide_tac
       >> drule handle_step_preserves_length_1 >> fs[])
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> PairCases_on `h`
  >> `r'.contexts = (FST (HD r'.contexts),h1)::h'::t'` by
      (gvs[same_frame_rel_def] >> Cases_on `r'.contexts` >> gvs[]
       >> PairCases_on `h` >> gvs[])
  >> `outputTo_consistent_ctx (FST (HD r'.contexts))` by
      gvs[same_frame_rel_def, outputTo_consistent_stack_def,
          outputTo_consistent_ctx_def]
  >> drule handle_step_pop_foreign_boundary >> simp[]
  >> disch_then (qspecl_then [`s'`,`r`,`y`] mp_tac) >> simp[]
  >> strip_tac >> qexists_tac `new_parent` >> simp[]
  >> gvs[same_frame_rel_def, callee_local_changes_def,
         foreign_account_change_def, account_already_created_def]
QED

Theorem account_prefix_bind[local]:
  (∀s. Q s ⇒ Q (SND (g s))) ∧
  (∀x s. Q s ⇒ Q (SND (f x s))) ⇒
  ∀s. Q s ⇒ Q (SND (bind g f s))
Proof
  rpt strip_tac
  >> simp[bind_def]
  >> Cases_on `g s` >> Cases_on `q` >> gvs[]
  >> metis_tac[SND]
QED

Theorem account_prefix_ignore_bind[local]:
  (∀s. Q s ⇒ Q (SND (g s))) ∧
  (∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind g f s))
Proof
  strip_tac >> rewrite_tac[ignore_bind_def]
  >> ho_match_mp_tac account_prefix_bind >> simp[]
QED

Theorem account_prefix_static_guard[local]:
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind assert_not_static f s))
Proof
  rpt strip_tac
  >> `s.contexts ≠ [] ∧ (FST (HD s.contexts)).msgParams.static`
    by metis_tac[]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> drule_all assert_not_static_static
  >> simp[ignore_bind_def, bind_def]
QED

Theorem account_prefix_conditional_guard[local]:
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (¬b ⇒ ∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒
    Q (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  Cases_on `b`
  >- (simp[] >> MATCH_ACCEPT_TAC account_prefix_static_guard)
  >> simp[ignore_bind_def, bind_def, return_def]
QED

Theorem cp_preserves_static_prefix[local]:
  cp m ⇒ ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧ n ≤ LENGTH (SND (m s)).contexts ∧
   (SND (m s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (m s)).contexts - n + 1) (SND (m s)).contexts))
Proof
  rw[cp_def]
  >> `s.contexts ≠ []` by (strip_tac >> gvs[])
  >> Cases_on `m s` >> gvs[]
  >> first_x_assum drule >> disch_then drule >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `LENGTH t + 2 - n` >> gvs[]
QED

Theorem proceed_call_preserves_static_prefix[local]:
  value = 0 ∨ op = CallCode ⇒ ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧
   n ≤ LENGTH (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).contexts ∧
   (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).contexts - n + 1)
       (SND (proceed_call op sender address value argsOff argsSize code stipend (Memory mr) s)).contexts))
Proof
  strip_tac >> gen_tac >> disch_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> `LENGTH t + 2 - n = SUC (LENGTH t + 1 - n)` by decide_tac
  >> gvs[]
  >> simp[proceed_call_def, bind_def, ignore_bind_def, return_def,
          get_rollback_def, read_memory_def,
          get_caller_def, get_value_def, get_static_def,
          get_current_context_def, push_context_def,
          initial_context_def, initial_msg_params_def]
  >> qmatch_goalsub_abbrev_tac `SND (f pushed)`
  >> `cp f` by simp[Abbr `f`]
  >> `pushed.contexts ≠ []` by simp[Abbr `pushed`]
  >> Cases_on `f pushed` >> gvs[]
  >> qpat_x_assum `cp f` mp_tac >> rewrite_tac[cp_def]
  >> disch_then drule >> disch_then drule >> strip_tac
  >> gvs[Abbr `pushed`]
  >> qpat_x_assum `EVERY _ _` mp_tac
  >> `SUC (SUC (LENGTH t)) - (n + 1) = SUC (LENGTH t) - n` by decide_tac
  >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem account_prefix_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp m ⇒
  ∀s. Q s ⇒ Q (SND (m s))
Proof
  rw[cp_def]
  >> `s.contexts ≠ []` by metis_tac[]
  >> Cases_on `m s` >> gvs[]
  >> first_x_assum drule >> simp[] >> strip_tac
  >> first_x_assum irule
  >> qexists_tac `s` >> simp[cp_rel_def]
QED

Theorem account_prefix_bind_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp g ∧
  (∀x s. Q s ⇒ Q (SND (f x s))) ⇒
  ∀s. Q s ⇒ Q (SND (bind g f s))
Proof
  strip_tac >> ho_match_mp_tac account_prefix_bind
  >> simp[] >> ho_match_mp_tac account_prefix_cp
  >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_ignore_bind_cp[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧ cp g ∧
  (∀s. Q s ⇒ Q (SND (f s))) ⇒
  ∀s. Q s ⇒ Q (SND (ignore_bind g f s))
Proof
  strip_tac >> ho_match_mp_tac account_prefix_ignore_bind
  >> simp[] >> ho_match_mp_tac account_prefix_cp
  >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_step_call[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (∀op sender address value ao az code stipend mr.
    value = 0 ∨ op = CallCode ⇒
    ∀s. Q s ⇒ Q (SND (proceed_call op sender address value ao az code stipend (Memory mr) s))) ⇒
  ∀s. Q s ⇒ Q (SND (step_call op s))
Proof
  strip_tac >> simp[step_call_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac >> pairarg_tac >> simp[]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac >> PairCases_on `x` >> simp[]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> gen_tac >> pairarg_tac >> simp[]
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_conditional_guard
  >> conj_tac >- (first_assum ACCEPT_TAC)
  >> strip_tac
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> IF_CASES_TAC
  >- (ho_match_mp_tac account_prefix_cp >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> IF_CASES_TAC
  >- (ho_match_mp_tac account_prefix_cp >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC)
  >> first_x_assum ho_match_mp_tac
  >> Cases_on `op` >> gvs[call_has_value_def]
QED

Theorem static_prefix_cp_rel[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ∧ cp_rel s s' ⇒
  (0 < n ∧ n ≤ LENGTH s'.contexts ∧ s'.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  rw[cp_rel_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `LENGTH t + 2 - n` >> gvs[]
QED

Theorem static_prefix_head[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  s.contexts ≠ [] ∧ (FST (HD s.contexts)).msgParams.static
Proof
  Cases_on `s.contexts` >- (strip_tac >> gvs[])
  >> PairCases_on `h` >> simp[] >> strip_tac
  >> `LENGTH t + 2 - n = SUC (LENGTH t + 1 - n)` by decide_tac
  >> gvs[]
QED

Theorem step_call_preserves_static_prefix[local]:
  ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧ n ≤ LENGTH (SND (step_call op s)).contexts ∧
   (SND (step_call op s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (step_call op s)).contexts - n + 1)
       (SND (step_call op s)).contexts))
Proof
  match_mp_tac (BETA_RULE (Q.INST [`Q` |->
    `λs. 0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
      EVERY (λ(c,rb). c.msgParams.static ∧
        (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
        (TAKE (LENGTH s.contexts - n + 1) s.contexts)`]
    account_prefix_step_call))
  >> rpt conj_tac
  >- (rpt strip_tac >> drule_all static_prefix_cp_rel >> simp[])
  >- (rpt strip_tac >> drule_all static_prefix_head >> simp[])
  >> rpt gen_tac >> disch_tac
  >> match_mp_tac proceed_call_preserves_static_prefix >> simp[]
QED

Theorem account_prefix_sstore[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_sstore transient s))
Proof
  strip_tac >> simp[step_sstore_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_log[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_log num s))
Proof
  strip_tac >> simp[step_log_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_self_destruct[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_self_destruct s))
Proof
  strip_tac >> simp[step_self_destruct_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_create[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ⇒
  ∀s. Q s ⇒ Q (SND (step_create two s))
Proof
  strip_tac >> simp[step_create_def, LET_THM]
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> gen_tac >> ho_match_mp_tac account_prefix_ignore_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_static_guard
  >> first_assum ACCEPT_TAC
QED

Theorem account_prefix_step_inst[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ [] ∧
    (FST (HD s.contexts)).msgParams.static) ∧
  (∀op s. Q s ⇒ Q (SND (step_call op s))) ⇒
  ∀s. Q s ⇒ Q (SND (step_inst op s))
Proof
  strip_tac >> Cases_on `op`
  >~ [`step_inst SStore`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_sstore >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst TStore`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_sstore >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst (Log _)`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_log >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst SelfDestruct`] >- (
    rewrite_tac[step_inst_def]
    >> match_mp_tac account_prefix_self_destruct >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst Create`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_create >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst Create2`] >- (
    rewrite_tac[step_inst_def]
    >> ho_match_mp_tac account_prefix_create >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`step_inst Call`] >- simp[step_inst_def]
  >~ [`step_inst CallCode`] >- simp[step_inst_def]
  >~ [`step_inst DelegateCall`] >- simp[step_inst_def]
  >~ [`step_inst StaticCall`] >- simp[step_inst_def]
  >> ho_match_mp_tac account_prefix_cp
  >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC
QED

Theorem step_inst_preserves_static_prefix[local]:
  ∀s.
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ⇒
  (0 < n ∧ n ≤ LENGTH (SND (step_inst op s)).contexts ∧
   (SND (step_inst op s)).rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (step_inst op s)).contexts - n + 1)
       (SND (step_inst op s)).contexts))
Proof
  match_mp_tac (BETA_RULE (Q.INST [`Q` |->
    `λs. 0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
      EVERY (λ(c,rb). c.msgParams.static ∧
        (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
        (TAKE (LENGTH s.contexts - n + 1) s.contexts)`]
    account_prefix_step_inst))
  >> rpt conj_tac
  >- (rpt strip_tac >> drule_all static_prefix_cp_rel >> simp[])
  >- (rpt strip_tac >> drule_all static_prefix_head >> simp[])
  >> gen_tac >> MATCH_ACCEPT_TAC step_call_preserves_static_prefix
QED

Theorem account_prefix_inner[local]:
  (∀s s'. Q s ∧ cp_rel s s' ⇒ Q s') ∧
  (∀s. Q s ⇒ s.contexts ≠ []) ∧
  (∀op s. Q s ⇒ Q (SND (step_inst op s))) ⇒
  ∀s. Q s ⇒ Q (SND ((do
    ctxt <- get_current_context;
    case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE => if LENGTH ctxt.msgParams.code ≤ ctxt.pc then step_inst Stop
              else step_inst Invalid
  od) s))
Proof
  strip_tac >> ho_match_mp_tac account_prefix_bind_cp
  >> simp[] >> conj_tac >- (first_assum ACCEPT_TAC)
  >> qx_gen_tac `ctxt` >> Cases_on `FLOOKUP ctxt.msgParams.parsed ctxt.pc`
  >- (simp[] >> IF_CASES_TAC >> first_assum MATCH_ACCEPT_TAC)
  >> simp[] >> ho_match_mp_tac account_prefix_ignore_bind
  >> conj_tac >- (first_assum MATCH_ACCEPT_TAC)
  >> ho_match_mp_tac account_prefix_cp
  >> simp[SF ETA_ss] >> first_assum ACCEPT_TAC
QED

Theorem inner_preserves_static_prefix[local]:
  (0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ∧
  (do
    ctxt <- get_current_context;
    case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE => if LENGTH ctxt.msgParams.code ≤ ctxt.pc then step_inst Stop
              else step_inst Invalid
  od) s = (r,s') ⇒
  (0 < n ∧ n ≤ LENGTH s'.contexts ∧ s'.rollback.accounts = A ∧
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  strip_tac
  >> mp_tac (BETA_RULE (Q.INST [`Q` |->
    `λs. 0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
      EVERY (λ(c,rb). c.msgParams.static ∧
        (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
        (TAKE (LENGTH s.contexts - n + 1) s.contexts)`]
    account_prefix_inner))
  >> impl_tac
  >- (rpt conj_tac
      >- (rpt strip_tac >> drule_all static_prefix_cp_rel >> simp[])
      >- (rpt strip_tac >> drule_all static_prefix_head >> simp[])
      >> gen_tac >> MATCH_ACCEPT_TAC step_inst_preserves_static_prefix)
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
QED

Theorem pop_incorporate_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ 1 < LENGTH s.contexts ∧
  s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (pop_and_incorporate_context success s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (pop_and_incorporate_context success s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (pop_and_incorporate_context success s)).contexts - n + 1)
       (SND (pop_and_incorporate_context success s)).contexts))
Proof
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> `LENGTH t' + 3 - n = SUC (LENGTH t' + 2 - n)` by decide_tac
  >> gvs[]
  >> simp[pop_and_incorporate_context_def, bind_def,
    get_gas_left_def, get_current_context_def, return_def,
    pop_context_def, unuse_gas_def, LET_THM,
    set_current_context_def, fail_def, assert_def, ignore_bind_def]
  >> Cases_on `success`
  >> simp[push_logs_def, bind_def, get_current_context_def,
    set_current_context_def, return_def, update_gas_refund_def, set_rollback_def]
  >> IF_CASES_TAC >> gvs[]
  >> strip_tac
  >> `LENGTH t' + 2 - n = SUC (LENGTH t' + 1 - n)` by decide_tac
  >> gvs[]
  >> `SUC (SUC (LENGTH t')) - (n + 1) = SUC (LENGTH t') - n` by decide_tac
  >> pop_assum SUBST_ALL_TAC >> simp[]
QED

Theorem cp_preserves_account_prefix_exit[local]:
  cp m ∧ s.contexts ≠ [] ∧ s.rollback.accounts = A ∧
  (n ≤ LENGTH s.contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s.contexts - n + 1) s.contexts)) ∧
  m s = (r,s') ⇒
  s'.rollback.accounts = A ∧
  (n ≤ LENGTH s'.contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  rw[cp_def]
  >> first_x_assum drule >> disch_then drule >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> Cases_on `LENGTH t + 2 - n` >> gvs[]
QED

Theorem handle_ex_helper_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (handle_ex_helper e s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (handle_ex_helper e s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (handle_ex_helper e s)).contexts - n + 1)
       (SND (handle_ex_helper e s)).contexts))
Proof
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> simp[handle_ex_helper_def, bind_def, get_num_contexts_def,
    get_current_context_def, return_def, fail_def]
  >> Cases_on `t`
  >- simp[reraise_def]
  >> simp[bind_def, get_return_data_def, get_output_to_def,
    get_current_context_def, return_def, ignore_bind_def]
  >> `1 < LENGTH s.contexts` by simp[]
  >> mp_tac (Q.INST [`A` |-> `s.rollback.accounts`,
      `success` |-> `(e : exception option) = NONE`] pop_incorporate_account_prefix)
  >> impl_tac >- gvs[]
  >> strip_tac
  >> Cases_on `pop_and_incorporate_context (e = NONE) s`
  >> Cases_on `q` >> gvs[]
  >> `r.contexts ≠ []`
    by (irule pop_incorporate_contexts_ne
        >> goal_assum (drule_at Any) >> simp[])
  >> Cases_on `after_pop h0.returnData h0.msgParams.outputTo (e = NONE) r`
  >> gvs[]
  >> drule_at (Pos (el 5)) cp_preserves_account_prefix_exit
  >> disch_then (qspecl_then [`n`, `s.rollback.accounts`] mp_tac)
  >> simp[]
QED

Theorem handle_exception_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (handle_exception e s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (handle_exception e s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (handle_exception e s)).contexts - n + 1)
       (SND (handle_exception e s)).contexts))
Proof
  strip_tac >> simp[handle_exception_decomp, LET_THM]
  >> qmatch_goalsub_abbrev_tac `bind prefix _ s`
  >> `cp prefix` by simp[Abbr `prefix`]
  >> drule cp_preserves_static_prefix
  >> disch_then (qspecl_then [`n`, `A`, `s`] mp_tac)
  >> simp[] >> strip_tac
  >> simp[bind_def]
  >> Cases_on `prefix s` >> Cases_on `q` >> gvs[]
  >> mp_tac (Q.INST [`s` |-> `r`, `A` |-> `s.rollback.accounts`]
      handle_ex_helper_account_prefix)
  >> simp[]
QED

Theorem handle_step_account_prefix[local]:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ⇒
  (SND (handle_step e s)).rollback.accounts = A ∧
  (n ≤ LENGTH (SND (handle_step e s)).contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH (SND (handle_step e s)).contexts - n + 1)
       (SND (handle_step e s)).contexts))
Proof
  strip_tac
  >> `s.contexts ≠ []` by (strip_tac >> gvs[])
  >> `(∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a)` by
    (Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
     >> `LENGTH t + 2 - n = SUC (LENGTH t + 1 - n)` by decide_tac
     >> gvs[])
  >> simp[handle_step_def]
  >> IF_CASES_TAC >- gvs[reraise_def]
  >> drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises)
  >> simp[handle_def, reraise_def]
  >> strip_tac >> mp_tac handle_exception_account_prefix >> gvs[]
QED

Theorem step_preserves_static_account_prefix[local]:
  wf_state s ∧ 0 < n ∧ n ≤ LENGTH s.contexts ∧
  s.rollback.accounts = A ∧
  EVERY (λ(c,rb). c.msgParams.static ∧
    (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
    (TAKE (LENGTH s.contexts - n + 1) s.contexts) ∧
  step s = (r,s') ⇒
  wf_state s' ∧ s'.rollback.accounts = A ∧
  (n ≤ LENGTH s'.contexts ⇒
   EVERY (λ(c,rb). c.msgParams.static ∧
     (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
     (TAKE (LENGTH s'.contexts - n + 1) s'.contexts))
Proof
  strip_tac
  >> `wf_state s'` by (drule step_preserves_wf_state >> simp[])
  >> simp[]
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, LET_THM]
  >> qmatch_goalsub_abbrev_tac `handle inner handle_step s`
  >> `∀r s'. inner s = (r,s') ⇒
       0 < n ∧ n ≤ LENGTH s'.contexts ∧ s'.rollback.accounts = A ∧
       EVERY (λ(c,rb). c.msgParams.static ∧
         (∀a. c.msgParams.outputTo ≠ Code a) ∧ rb.accounts = A)
         (TAKE (LENGTH s'.contexts - n + 1) s'.contexts)` by
    (map_every qx_gen_tac [`res`, `st`] >> disch_tac
     >> irule inner_preserves_static_prefix >> conj_tac >- simp[]
     >> map_every qexists_tac [`res`, `s`] >> gvs[Abbr `inner`])
  >> simp[handle_def]
  >> Cases_on `inner s` >> Cases_on `q` >> gvs[]
  >- (strip_tac >> gvs[])
  >> rename1 `inner s = (INR ex, mid)`
  >> mp_tac (Q.INST [`s` |-> `mid`, `e` |-> `ex`,
       `A` |-> `s.rollback.accounts`] handle_step_account_prefix)
  >> simp[] >> strip_tac >> Cases_on `handle_step ex mid` >> gvs[]
  >> strip_tac >> gvs[]
QED

(* A static frame changes no account: SSTORE, CREATE, SELFDESTRUCT and
 * value-carrying CALL fail in it, and the frames it calls are static too.
 * Its saved rollback must agree on accounts, since a failure restores it. *)
Theorem run_call_static_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.static ∧
  (∀x. (FST (HD e.contexts)).msgParams.outputTo ≠ Code x) ∧
  (SND (HD e.contexts)).accounts = e.rollback.accounts ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  strip_tac
  >> `0 < LENGTH e.contexts` by (gvs[wf_state_def] >> Cases_on `e.contexts` >> gvs[])
  >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧
       (SND p).rollback.accounts = e.rollback.accounts ∧
       (LENGTH e.contexts ≤ LENGTH (SND p).contexts ⇒
        EVERY (λ(c,rb). c.msgParams.static ∧
          (∀a. c.msgParams.outputTo ≠ Code a) ∧
          rb.accounts = e.rollback.accounts)
          (TAKE (LENGTH (SND p).contexts - LENGTH e.contexts + 1)
                (SND p).contexts))) (r,e')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum $ drule_at Any
  >> simp[]
  >> conj_tac
  >- (Cases_on `e.contexts` >> gvs[] >> PairCases_on `h` >> gvs[])
  >> qx_gen_tac `p` >> PairCases_on `p` >> simp[]
  >> strip_tac >> Cases_on `step p1` >> simp[]
  >> mp_tac (Q.INST [`s` |-> `p1`, `s'` |-> `r'`, `r` |-> `q`,
       `n` |-> `LENGTH e.contexts`, `A` |-> `e.rollback.accounts`]
       step_preserves_static_account_prefix)
  >> simp[]
QED

(* -------------------------------------------------------------------------
 * The rely form.
 *
 * The frame hypothesis covers each frame entered as `a` from outside any
 * frame of `a`: es itself if its callee is `a`, and each push by a reached
 * state whose callee is not `a` (a CALL/STATICCALL to `a` or a CREATE at
 * `a`; see step_push_new_frame).  run_call e runs that frame until it pops
 * (or the run stops), nested calls included.  Static pushed frames are
 * discharged by run_call_static_frame.
 * ------------------------------------------------------------------------- *)

Theorem active_rollbacks_initial:
  Q es.rollback ∧
  (2 ≤ LENGTH es.contexts ⇒ Q (SND (HD es.contexts))) ⇒
  EVERY Q (active_rollbacks (LENGTH es.contexts) es)
Proof
  rw[active_rollbacks_saved]
  >> Cases_on `es.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[MIN_DEF]
  >> rw[] >> gvs[]
  >> `LENGTH t' = 0` by decide_tac >> gvs[]
QED

Theorem active_rollbacks_same_stack:
  LENGTH t.contexts = LENGTH s.contexts ∧
  TL t.contexts = TL s.contexts ∧
  SND (HD t.contexts) = SND (HD s.contexts) ⇒
  TL (active_rollbacks d t) = TL (active_rollbacks d s)
Proof
  strip_tac >> simp[active_rollbacks_def]
  >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
  >> qmatch_goalsub_abbrev_tac `TAKE k (h::t')`
  >> Cases_on `k` >> simp[]
QED

Theorem step_same_frame_account_invariant:
  wf_state s ∧ step s = (r,t) ∧
  LENGTH t.contexts = LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  strip_tac
  >> drule_all step_same_frame_foreign >> strip_tac
  >> `TL (active_rollbacks d t) = TL (active_rollbacks d s)`
       by (irule active_rollbacks_same_stack >> simp[])
  >> `P (lookup_account a s.rollback.accounts)`
       by gvs[active_rollbacks_def]
  >> `P (lookup_account a t.rollback.accounts)` by metis_tac[]
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
            (TL (active_rollbacks d s))` by gvs[active_rollbacks_def]
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
            (TL (active_rollbacks d t))` by metis_tac[]
  >> gvs[active_rollbacks_def]
QED

Theorem active_rollbacks_push_tail:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  FRONT (TL (TL t.contexts)) = FRONT (TL s.contexts) ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 t.contexts) = SND (HD s.contexts)) ⇒
  TL (active_rollbacks d t) =
    SND (HD t.contexts) :: TL (active_rollbacks d s)
Proof
  strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t.contexts` >> gvs[]
  >> Cases_on `t'` >> gvs[]
  >> Cases_on `t` >> gvs[active_rollbacks_saved, MIN_DEF]
  >> rw[] >> gvs[]
  >> rename1 `FRONT (TL ys) = FRONT (z::zs)`
  >> Cases_on `ys` >> gvs[]
  >> simp[ADD1]
  >> AP_TERM_TAC
  >> qmatch_goalsub_abbrev_tac `TAKE k _`
  >> `k < LENGTH t ∧ k < LENGTH (z::zs)` by (simp[Abbr `k`] >> decide_tac)
  >> metis_tac[TAKE_FRONT, NOT_CONS_NIL, LENGTH_NIL, prim_recTheory.NOT_LESS_0]
QED

Theorem step_push_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  LENGTH s.contexts < LENGTH t.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  strip_tac >> drule_all step_push_foreign >> strip_tac
  >> `TL (active_rollbacks d t) =
       SND (HD t.contexts) :: TL (active_rollbacks d s)`
       by (irule active_rollbacks_push_tail >> simp[])
  >> `P (lookup_account a s.rollback.accounts) ∧
      EVERY (λrb. P (lookup_account a rb.accounts))
        (TL (active_rollbacks d s))` by gvs[active_rollbacks_def]
  >> `P (lookup_account a t.rollback.accounts) ∧
      P (lookup_account a (SND (HD t.contexts)).accounts)` by metis_tac[]
  >> Cases_on `active_rollbacks d t` >> gvs[active_rollbacks_def]
QED

Theorem active_rollbacks_pop:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  s.contexts = h::parent::rest ∧
  t.contexts = (new_head,SND parent)::rest ∧
  EVERY Q (active_rollbacks d s) ⇒
  Q s.rollback ∧ Q (SND h) ∧ EVERY Q (TL (active_rollbacks d t))
Proof
  simp[active_rollbacks_saved] >> strip_tac
  >> gvs[MIN_DEF] >> rw[] >> gvs[]
  >> gvs[ADD1]
  >> Cases_on `rest` >> gvs[]
QED

Theorem active_rollbacks_pop_tail:
  0 < d ∧ d ≤ LENGTH t.contexts ∧
  s.contexts = h::parent::rest ∧
  t.contexts = (new_head,SND parent)::rest ⇒
  TL (active_rollbacks d t) = TL (TL (active_rollbacks d s))
Proof
  strip_tac >> simp[active_rollbacks_saved]
  >> gvs[MIN_DEF] >> rw[] >> gvs[ADD1]
  >> Cases_on `rest` >> gvs[]
QED

Theorem step_pop_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  LENGTH t.contexts < LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  strip_tac >> drule_all step_pop_foreign >> strip_tac
  >> drule_all active_rollbacks_pop >> strip_tac
  >> `P (lookup_account a t.rollback.accounts)` by metis_tac[]
  >> gvs[active_rollbacks_def]
QED

Theorem step_foreign_account_invariant:
  0 < d ∧ d ≤ LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ∧
  (FST (HD s.contexts)).msgParams.callee ≠ a ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d s) ⇒
  EVERY (λrb. P (lookup_account a rb.accounts)) (active_rollbacks d t)
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (irule step_same_frame_account_invariant >> metis_tac[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule step_push_account_invariant >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> irule step_pop_account_invariant >> metis_tac[]
QED

Theorem step_outer_saved_rollbacks:
  0 < d ∧ d ≤ k ∧ k < LENGTH s.contexts ∧
  wf_state s ∧ step s = (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (TL (active_rollbacks d t)) =
  DROP (LENGTH s.contexts - k) (TL (active_rollbacks d s))
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`outputTo_consistent s`
        by metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def]
      >> drule_all step_same_frame >> strip_tac
      >> `TL (active_rollbacks d t) = TL (active_rollbacks d s)`
          by (irule active_rollbacks_same_stack >> gvs[same_frame_rel_def])
      >> simp[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_all step_push_foreign >> strip_tac
      >> `TL (active_rollbacks d t) =
           SND (HD t.contexts) :: TL (active_rollbacks d s)`
           by (irule active_rollbacks_push_tail >> simp[])
      >> `LENGTH t.contexts - k = SUC (LENGTH s.contexts - k)` by decide_tac
      >> simp[])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> drule_all step_pop_foreign >> strip_tac
  >> `LENGTH s.contexts = SUC (SUC (LENGTH rest))`
       by (qpat_assum `s.contexts = _` (once_rewrite_tac o single) >> simp[])
  >> `k ≤ LENGTH t.contexts` by (gvs[] >> decide_tac)
  >> `TL (active_rollbacks d t) = TL (TL (active_rollbacks d s))`
       by (irule active_rollbacks_pop_tail >> metis_tac[LESS_EQ_TRANS])
  >> `LENGTH s.contexts - k = SUC (LENGTH t.contexts - k)`
       by (gvs[] >> decide_tac)
  >> simp[DROP_SUC]
  >> once_rewrite_tac[GSYM DROP_SUC]
  >> Cases_on `TL (active_rollbacks d s)` >> simp[]
QED

Theorem run_call_outer_saved_rollbacks:
  0 < d ∧ d ≤ k ∧ k < LENGTH e.contexts ∧
  wf_state e ∧ run_call e = SOME (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (TL (active_rollbacks d t)) =
  DROP (LENGTH e.contexts - k) (TL (active_rollbacks d e))
Proof
  strip_tac >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧ k ≤ LENGTH (SND p).contexts ∧
       DROP (LENGTH (SND p).contexts - k) (TL (active_rollbacks d (SND p))) =
       DROP (LENGTH e.contexts - k) (TL (active_rollbacks d e))) (r,t)`
       suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt gen_tac >> strip_tac
  >> pairarg_tac >> gvs[]
  >> rename1 `LENGTH s.contexts ≥ LENGTH e.contexts`
  >> Cases_on `step s` >> gvs[]
  >> `k < LENGTH s.contexts` by decide_tac
  >> drule_all step_outer_saved_rollbacks >> strip_tac
  >> metis_tac[step_preserves_wf_state, SND]
QED

Theorem run_call_popped_saved_rollbacks:
  0 < d ∧ d < LENGTH e.contexts ∧
  wf_state e ∧ run_call e = SOME (INL (),t) ⇒
  TL (active_rollbacks d t) = TL (TL (active_rollbacks d e))
Proof
  strip_tac
  >> `d ≤ LENGTH e.contexts - 1 ∧ LENGTH e.contexts - 1 < LENGTH e.contexts`
       by decide_tac
  >> `LENGTH e.contexts - 1 ≤ LENGTH t.contexts ∧
       DROP (LENGTH t.contexts - (LENGTH e.contexts - 1)) (TL (active_rollbacks d t)) =
       DROP (LENGTH e.contexts - (LENGTH e.contexts - 1)) (TL (active_rollbacks d e))`
       by (irule run_call_outer_saved_rollbacks >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH e.contexts`
       by (drule run_call_finite_trace >> simp[] >> strip_tac >> decide_tac)
  >> `LENGTH t.contexts = LENGTH e.contexts - 1 ∧
      LENGTH e.contexts - (LENGTH e.contexts - 1) = 1` by decide_tac
  >> gvs[]
  >> Cases_on `TL (active_rollbacks d e)` >> gvs[]
QED

Theorem run_call_saved_account_invariant:
  0 < d ∧ d < LENGTH e.contexts ∧ wf_state e ∧
  EVERY Q (TL (active_rollbacks d e)) ∧
  Q t.rollback ∧ run_call e = SOME (INL (),t) ⇒
  EVERY Q (active_rollbacks d t)
Proof
  strip_tac >> drule_all run_call_popped_saved_rollbacks >> strip_tac
  >> `EVERY Q (TL (TL (active_rollbacks d e)))`
       by (Cases_on `TL (active_rollbacks d e)` >> gvs[])
  >> Cases_on `active_rollbacks d t` >> gvs[active_rollbacks_def]
QED

Theorem step_outer_msgParams:
  0 < k ∧ k < LENGTH s.contexts ∧ wf_state s ∧ step s = (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (MAP (λp. (FST p).msgParams) t.contexts) =
  DROP (LENGTH s.contexts - k) (MAP (λp. (FST p).msgParams) s.contexts)
Proof
  strip_tac
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`outputTo_consistent s`
        by metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def]
      >> drule_all step_same_frame >> simp[same_frame_rel_def]
      >> strip_tac
      >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_all step_push_foreign >> strip_tac
      >> `MAP (λp. (FST p).msgParams) (TL (TL t.contexts)) =
          MAP (λp. (FST p).msgParams) (TL s.contexts)`
          by metis_tac[MAP_MAP_o, combinTheory.o_DEF]
      >> `LENGTH t.contexts - k = SUC (LENGTH s.contexts - k)` by decide_tac
      >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
      >> rename1 `MAP FST (TL cs) = _`
      >> Cases_on `cs` >> gvs[ADD1])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> drule_all step_pop_foreign >> strip_tac
  >> `LENGTH s.contexts = SUC (SUC (LENGTH rest))`
       by (qpat_assum `s.contexts = _` (once_rewrite_tac o single) >> simp[])
  >> `k ≤ LENGTH t.contexts ∧
      LENGTH s.contexts - k = SUC (LENGTH t.contexts - k)` by (gvs[] >> decide_tac)
  >> qpat_assum `s.contexts = _` (once_rewrite_tac o single)
  >> simp[ADD1]
QED

Theorem run_call_outer_msgParams:
  0 < k ∧ k < LENGTH e.contexts ∧ wf_state e ∧ run_call e = SOME (r,t) ⇒
  k ≤ LENGTH t.contexts ∧
  DROP (LENGTH t.contexts - k) (MAP (λp. (FST p).msgParams) t.contexts) =
  DROP (LENGTH e.contexts - k) (MAP (λp. (FST p).msgParams) e.contexts)
Proof
  strip_tac >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧ k ≤ LENGTH (SND p).contexts ∧
       DROP (LENGTH (SND p).contexts - k)
         (MAP (λp. (FST p).msgParams) (SND p).contexts) =
       DROP (LENGTH e.contexts - k) (MAP (λp. (FST p).msgParams) e.contexts)) (r,t)`
       suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt gen_tac >> strip_tac
  >> pairarg_tac >> gvs[]
  >> rename1 `LENGTH s.contexts ≥ LENGTH e.contexts`
  >> Cases_on `step s` >> gvs[]
  >> `k < LENGTH s.contexts` by decide_tac
  >> drule_all step_outer_msgParams >> strip_tac
  >> metis_tac[step_preserves_wf_state, SND]
QED

Theorem run_call_parent_msgParams:
  2 ≤ LENGTH e.contexts ∧ wf_state e ∧ run_call e = SOME (INL (),t) ⇒
  (FST (HD t.contexts)).msgParams = (FST (EL 1 e.contexts)).msgParams
Proof
  strip_tac
  >> `0 < LENGTH e.contexts - 1 ∧ LENGTH e.contexts - 1 < LENGTH e.contexts`
       by decide_tac
  >> `LENGTH e.contexts - 1 ≤ LENGTH t.contexts ∧
       DROP (LENGTH t.contexts - (LENGTH e.contexts - 1))
         (MAP (λp. (FST p).msgParams) t.contexts) =
       DROP (LENGTH e.contexts - (LENGTH e.contexts - 1))
         (MAP (λp. (FST p).msgParams) e.contexts)`
       by (irule run_call_outer_msgParams >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH e.contexts`
       by (drule run_call_finite_trace >> simp[] >> strip_tac >> decide_tac)
  >> `LENGTH t.contexts = LENGTH e.contexts - 1 ∧
      LENGTH e.contexts - (LENGTH e.contexts - 1) = 1` by decide_tac
  >> gvs[]
  >> Cases_on `t.contexts` >> Cases_on `e.contexts` >> gvs[]
  >> rename1 `e.contexts = _::cs`
  >> Cases_on `cs` >> gvs[]
QED

Theorem run_call_reaches_trans:
  run_call_reaches es e ∧ LENGTH es.contexts ≤ LENGTH e.contexts ∧
  run_call_reaches e t ⇒ run_call_reaches es t
Proof
  simp[run_call_reaches_def] >> strip_tac
  >> irule RTC_TRANS >> qexists_tac `e` >> simp[]
  >> irule RTC_MONOTONE >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt strip_tac >> metis_tac[LESS_EQ_TRANS]
QED

Theorem run_call_step_equation:
  step e = (q,t) ⇒
  run_call e =
    OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
      (step o SND) (q,t)
Proof
  strip_tac >> simp[run_call_def, GREATER_EQ, Once OWHILE_THM]
QED

Theorem run_call_child_continuation:
  LENGTH e.contexts ≤ LENGTH c.contexts ∧
  run_call c = SOME (q,t) ⇒
  OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
    (step o SND) (INL (),c) =
  OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
    (step o SND) (q,t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac
  >> qmatch_goalsub_abbrev_tac `OWHILE G f _`
  >> `∀k. k < n ⇒ G (FUNPOW f k (INL (),c))`
       by (simp[Abbr `G`, Abbr `f`] >> rpt strip_tac >>
           first_x_assum drule >> pairarg_tac >> simp[] >>
           strip_tac >> decide_tac)
  >> `OWHILE G f (INL (),c) = OWHILE G f (FUNPOW f n (INL (),c))`
       by (irule OWHILE_trace_continuation >> qexists_tac `n` >> simp[])
  >> metis_tac[]
QED

Theorem run_call_foreign_trace:
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  (∀s c q t.
     run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
     wf_state s ∧ (FST (HD s.contexts)).msgParams.callee ≠ a ∧
     P (lookup_account a s.rollback.accounts) ∧
     step s = (INL (),c) ∧ LENGTH s.contexts < LENGTH c.contexts ∧
     (FST (HD c.contexts)).msgParams.callee = a ∧
     run_call c = SOME (q,t) ⇒ P (lookup_account a t.rollback.accounts)) ⇒
  ∀n e r t.
    ¬(λ(q,s). ISL q ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
       (FUNPOW (step o SND) n (INL (),e)) ∧
    run_call_reaches es e ∧ LENGTH es.contexts ≤ LENGTH e.contexts ∧
    wf_state e ∧ (FST (HD e.contexts)).msgParams.callee ≠ a ∧
    EVERY (λrb. P (lookup_account a rb.accounts))
      (active_rollbacks (LENGTH e.contexts) e) ∧
    run_call e = SOME (r,t) ⇒ P (lookup_account a t.rollback.accounts)
Proof
  strip_tac >> completeInduct_on `n` >> rpt gen_tac >> strip_tac
  >> Cases_on `n` >- gvs[]
  >> rename1 `FUNPOW (step o SND) (SUC j) _`
  >> `0 < LENGTH e.contexts` by (gvs[wf_state_def] >> Cases_on `e.contexts` >> gvs[])
  >> Cases_on `step e` >> rename1 `step e = (q,c)`
  >> `wf_state c` by metis_tac[step_preserves_wf_state, SND]
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
        (active_rollbacks (LENGTH e.contexts) c)`
       by (irule step_foreign_account_invariant >> metis_tac[LESS_EQ_REFL])
  >> `P (lookup_account a e.rollback.accounts) ∧
      P (lookup_account a c.rollback.accounts)` by gvs[active_rollbacks_def]
  >> drule run_call_step_equation >> strip_tac
  >> Cases_on `q`
  >- suspend "continuing"
  >> gvs[Once OWHILE_THM]
QED

Resume run_call_foreign_trace[continuing]:
  Cases_on `x` >> gvs[]
  >> Cases_on `LENGTH c.contexts < LENGTH e.contexts`
  >- gvs[Once OWHILE_THM]
  >> Cases_on `LENGTH c.contexts = LENGTH e.contexts`
  >- suspend "same_depth"
  >> suspend "push"
QED

Resume run_call_foreign_trace[same_depth]:
  `run_call_reaches es c` by (irule run_call_reaches_step >> metis_tac[])
  >> `(FST (HD c.contexts)).msgParams.callee ≠ a`
       by (drule_all step_same_frame_foreign >> metis_tac[])
  >> `run_call c = SOME (r,t)` by gvs[run_call_def, GREATER_EQ]
  >> qpat_x_assum `∀m. m < SUC j ⇒ _` (qspec_then `j` mp_tac)
  >> simp[] >> disch_then irule
  >> qexists_tac `c` >> qexists_tac `r`
  >> gvs[FUNPOW, combinTheory.o_DEF]
QED

Resume run_call_foreign_trace[push]:
  `LENGTH e.contexts < LENGTH c.contexts` by decide_tac
  >> `run_call_reaches es c` by (irule run_call_reaches_step >> metis_tac[])
  >> qpat_x_assum `¬(λ(q,s). _) _` mp_tac
  >> simp[Once FUNPOW] >> strip_tac
  >> drule_at (Pat `¬ _`) run_call_nested_trace
  >> simp[] >> strip_tac
  >> rename1 `m ≤ j`
  >> Cases_on `FUNPOW (step o SND) m (INL (),c)`
  >> rename1 `run_call c = SOME (q,v)`
  >> `P (lookup_account a v.rollback.accounts)` by
       (Cases_on `(FST (HD c.contexts)).msgParams.callee = a`
        >- (qpat_x_assum `∀s c q t. _` irule >>
            qexistsl_tac [`c`,`q`,`e`] >> simp[])
        >> qpat_x_assum `∀m. m < SUC j ⇒ _` (qspec_then `m` mp_tac)
        >> simp[] >> disch_then irule
        >> qexists_tac `c` >> qexists_tac `q` >> simp[]
        >> irule active_rollbacks_initial
        >> drule_all step_push_foreign >> strip_tac
        >> gvs[active_rollbacks_def] >> metis_tac[])
  >> `OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
        (step o SND) (INL (),c) =
      OWHILE (λ(r,s). ISL r ∧ LENGTH e.contexts ≤ LENGTH s.contexts)
        (step o SND) (q,v)`
       by (irule run_call_child_continuation >> simp[])
  >> Cases_on `q`
  >- suspend "child_return"
  >> gvs[Once OWHILE_THM]
QED

Resume run_call_foreign_trace[child_return]:
  Cases_on `x` >> gvs[]
  >> drule_all step_push_foreign >> strip_tac
  >> `LENGTH e.contexts ≤ LENGTH v.contexts`
       by (qpat_assum `run_call c = _`
             (mp_then Any mp_tac (Q.INST
               [`d` |-> `LENGTH e.contexts`, `k` |-> `LENGTH e.contexts`]
               (Q.INST [`e` |-> `c`] run_call_outer_saved_rollbacks))) >> simp[])
  >> `LENGTH v.contexts = LENGTH e.contexts` by decide_tac
  >> `wf_state v` by metis_tac[run_call_preserves_wf_state]
  >> `2 ≤ LENGTH c.contexts` by decide_tac
  >> `(FST (HD v.contexts)).msgParams = (FST (HD e.contexts)).msgParams`
       by (drule_all run_call_parent_msgParams >> simp[])
  >> `EVERY (λrb. P (lookup_account a rb.accounts))
        (active_rollbacks (LENGTH e.contexts) v)`
       by (irule run_call_saved_account_invariant >> simp[] >>
           qexists_tac `c` >> simp[] >> gvs[active_rollbacks_def])
  >> `run_call_reaches c v`
       by (`run_call_reaches c (SND (FUNPOW (step o SND) m (INL (),c)))`
             suffices_by gvs[] >>
           irule run_call_trace_reaches >> simp[] >> rpt strip_tac >>
           first_x_assum drule >> pairarg_tac >> simp[])
  >> `run_call_reaches es v` by (irule run_call_reaches_trans >> metis_tac[LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ])
  >> `run_call v = SOME (r,t)` by gvs[run_call_def, GREATER_EQ]
  >> `FUNPOW (step o SND) j (INL (),c) =
      FUNPOW (step o SND) (j-m) (INL (),v)`
       by (`j = (j-m)+m` by decide_tac >>
           qpat_assum `j = _` (once_rewrite_tac o single) >> simp[FUNPOW_ADD])
  >> qpat_x_assum `∀m. m < SUC j ⇒ _` (qspec_then `j-m` mp_tac)
  >> simp[] >> disch_then irule
  >> qexistsl_tac [`v`,`r`] >> simp[] >> metis_tac[]
QED

Finalise run_call_foreign_trace

Theorem run_call_account_frame:
  wf_state es ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  P (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     P (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  (∀e r e'.
     (FST (HD e.contexts)).msgParams.callee = a ∧
     wf_state e ∧ P (lookup_account a e.rollback.accounts) ∧
     (2 ≤ LENGTH e.contexts ⇒
        P (lookup_account a (SND (HD e.contexts)).accounts)) ∧
     (e = es ∨
      ∃s u. run_call_reaches es s ∧
            LENGTH es.contexts ≤ LENGTH s.contexts ∧
            wf_state s ∧
            (FST (HD s.contexts)).msgParams.callee ≠ a ∧
            P (lookup_account a s.rollback.accounts) ∧
            step s = (INL u, e) ∧
            LENGTH s.contexts < LENGTH e.contexts ∧
            ¬(FST (HD e.contexts)).msgParams.static) ∧
     run_call e = SOME (r, e') ⇒
     P (lookup_account a e'.rollback.accounts)) ∧
  run_call es = SOME (r, es') ⇒
  P (lookup_account a es'.rollback.accounts)
Proof
  strip_tac
  >> Cases_on `(FST (HD es.contexts)).msgParams.callee = a`
  >- (qpat_x_assum `∀e r e'. _` irule >> qexistsl_tac [`es`,`r`] >> simp[])
  >> drule run_call_finite_trace >> strip_tac
  >> irule run_call_foreign_trace
  >> conj_tac >- metis_tac[]
  >> qexistsl_tac [`es`,`es`,`n`,`r`]
  >> simp[]
  >> conj_tac >- suspend "rely_push"
  >> irule active_rollbacks_initial >> simp[]
QED

Resume run_call_account_frame[rely_push]:
  rpt gen_tac >> strip_tac
  >> `wf_state c` by metis_tac[step_preserves_wf_state, SND]
  >> drule_all step_push_foreign >> strip_tac
  >> `P (lookup_account a c.rollback.accounts) ∧
      P (lookup_account a (SND (HD c.contexts)).accounts)` by metis_tac[]
  >> Cases_on `(FST (HD c.contexts)).msgParams.static`
  >- suspend "static_push"
  >> qpat_x_assum `∀e r e'. _` irule
  >> qexistsl_tac [`c`,`q`] >> simp[]
  >> disj2_tac >> qexists_tac `s` >> simp[]
QED

Resume run_call_account_frame[static_push]:
  `(FST (HD c.contexts)).msgParams.callee ≠ (FST (HD s.contexts)).msgParams.callee`
    by simp[]
  >> `t.rollback.accounts = c.rollback.accounts` suffices_by metis_tac[]
  >> qpat_x_assum `∀e r e'. _` kall_tac
  >> qpat_x_assum `∀k. k < n ⇒ _` kall_tac
  >> drule_all step_push_new_frame >> strip_tac
  >> `(FST (HD c.contexts)).msgParams.static = static ∧
      (FST (HD c.contexts)).msgParams.outputTo = rd`
       by (qpat_assum `FST (HD c.contexts) = initial_context _ _ _ _ _`
             (once_rewrite_tac o single) >>
           simp[initial_context_def, initial_msg_params_def])
  >> qpat_x_assum `FST (HD c.contexts) = initial_context _ _ _ _ _` kall_tac
  >> irule run_call_static_frame >> gvs[] >> metis_tac[]
QED

Finalise run_call_account_frame

(* -------------------------------------------------------------------------
 * Accounts with no code.
 * ------------------------------------------------------------------------- *)

Theorem step_empty_code[local]:
  wf_state e ∧ (FST (HD e.contexts)).msgParams.code = [] ⇒
  step e = handle (step_inst Stop) handle_step e
Proof
  strip_tac
  >> `e.contexts ≠ [] ∧ EVERY (wf_context o FST) e.contexts` by
       gvs[wf_state_def]
  >> Cases_on `e.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
  >> `h0.msgParams.parsed = FEMPTY` by
       (qpat_x_assum `wf_context h0` mp_tac
        >> simp[wf_context_def, Once parse_code_def])
  >> simp[step_def, get_current_context_def, bind_def, return_def,
          LET_THM, handle_def]
QED

Theorem handle_exception_success_accounts[local]:
  handle_exception NONE s = (r,s') ⇒
  s'.rollback.accounts = s.rollback.accounts
Proof
  Cases_on `s.contexts` >- simp[handle_exception_def, get_num_contexts_def,
    bind_def, ignore_bind_def, return_def, reraise_def]
  >> Cases_on `t`
  >- simp[handle_exception_def, get_num_contexts_def,
    bind_def, ignore_bind_def, return_def, reraise_def]
  >> PairCases_on `h` >> PairCases_on `h'`
  >> Cases_on `h0.msgParams.outputTo`
  >> simp[handle_exception_def, bind_def, ignore_bind_def,
     get_num_contexts_def, get_current_context_def, return_def,
     get_return_data_def, get_output_to_def, reraise_def,
     pop_and_incorporate_context_def, get_gas_left_def, pop_context_def,
     unuse_gas_def, assert_def, fail_def, set_current_context_def,
     push_logs_def, update_gas_refund_def, inc_pc_def,
     set_return_data_def, push_stack_def, write_memory_def,
     AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
QED

(* A frame running empty code stops at once; if the callee has no code, a
 * code deposit leaves it so. *)
Theorem handle_create_empty_identity[local]:
  s.contexts ≠ [] ∧
  wf_context (FST (HD s.contexts)) ∧
  outputTo_consistent_ctx (FST (HD s.contexts)) ∧
  (FST (HD s.contexts)).returnData = [] ∧
  (lookup_account (FST (HD s.contexts)).msgParams.callee
    s.rollback.accounts).code = [] ⇒
  handle_create NONE s = (INR NONE,s)
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h`
  >> simp[wf_context_def, outputTo_consistent_ctx_def]
  >> strip_tac
  >> Cases_on `h0.msgParams.outputTo`
  >> simp[handle_create_def, get_return_data_def, get_output_to_def,
      get_current_context_def, bind_def, ignore_bind_def, return_def,
      reraise_def, assert_def, consume_gas_def, set_current_context_def,
      update_accounts_def, LET_THM]
  >> `h0.msgParams.callee = c` by metis_tac[]
  >> `update_account c (lookup_account c s.rollback.accounts with code := [])
         s.rollback.accounts = s.rollback.accounts` by
       (gvs[lookup_account_def, update_account_def, FUN_EQ_THM,
            combinTheory.APPLY_UPDATE_THM]
        >> gen_tac >> IF_CASES_TAC >> gvs[]
        >> simp[account_state_component_equality])
  >> simp[execution_state_component_equality, rollback_state_component_equality]
QED

Theorem step_empty_code_exit[local]:
  wf_state e ∧ (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
    e.rollback.accounts).code = [] ∧ step e = (r,s) ⇒
  s.rollback.accounts = e.rollback.accounts ∧
  (¬ISL r ∨ LENGTH s.contexts < LENGTH e.contexts)
Proof
  strip_tac
  >> `step e = handle (step_inst Stop) handle_step e` by
       (irule step_empty_code >> simp[])
  >> `e.contexts ≠ [] ∧ EVERY (wf_context o FST) e.contexts ∧
       outputTo_consistent_stack e` by gvs[wf_state_def]
  >> Cases_on `e.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
  >> qpat_x_assum `handle _ _ _ = _` mp_tac
  >> simp[step_inst_def, set_return_data_def, finish_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `handle_step NONE mid`
  >> `(handle_create NONE mid : (unit + exception option) # execution_state) = (INR NONE,mid)` by
       (irule handle_create_empty_identity
        >> gvs[Abbr `mid`, outputTo_consistent_stack_def,
               outputTo_consistent_ctx_def, wf_context_def])
  >> simp[handle_step_def, vfm_abort_def, handle_def]
  >> strip_tac >> gvs[]
  >> conj_tac
  >- (drule handle_exception_success_accounts >> simp[Abbr `mid`])
  >> Cases_on `t`
  >- (qpat_x_assum `handle_exception _ _ = _` mp_tac
      >> simp[Abbr `mid`, handle_exception_def, get_num_contexts_def,
              bind_def, ignore_bind_def, return_def, reraise_def]
      >> strip_tac >> gvs[])
  >> disj2_tac
  >> `EVERY (wf_context o FST) mid.contexts ∧ LENGTH mid.contexts ≥ 2` by
       gvs[Abbr `mid`, wf_context_def]
  >> drule_all vfmHandleStepTheory.handle_exception_ge_2_pops
  >> simp[Abbr `mid`]
QED

Theorem run_call_empty_code_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
     e.rollback.accounts).code = [] ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  strip_tac
  >> Cases_on `step e`
  >> drule_all step_empty_code_exit >> strip_tac
  >> qpat_x_assum `run_call _ = _` mp_tac
  >> simp[run_call_def, Once OWHILE_THM]
  >> simp[Once OWHILE_THM]
  >> strip_tac >> gvs[]
QED

(* If `a` has no code and a CREATE at `a` would collide (nonzero nonce or
 * nonempty storage), run_call changes neither its code nor its storage. *)
Theorem run_call_empty_code_account:
  wf_state es ∧
  (lookup_account a es.rollback.accounts).code = [] ∧
  account_already_created (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     (lookup_account a (SND (HD es.contexts)).accounts).code = [] ∧
     (lookup_account a (SND (HD es.contexts)).accounts).storage =
       (lookup_account a es.rollback.accounts).storage ∧
     account_already_created
       (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  ((FST (HD es.contexts)).msgParams.callee = a ⇒
     (FST (HD es.contexts)).msgParams.code = []) ∧
  run_call es = SOME (r, es') ⇒
  (lookup_account a es'.rollback.accounts).code = [] ∧
  (lookup_account a es'.rollback.accounts).storage =
    (lookup_account a es.rollback.accounts).storage
Proof
  strip_tac
  >> `((λacc. acc.code = [] ∧
          acc.storage = (lookup_account a es.rollback.accounts).storage ∧
          account_already_created acc)
        (lookup_account a es'.rollback.accounts))` suffices_by simp[]
  >> irule run_call_account_frame
  >> conj_tac
  >- (rpt strip_tac >> gvs[foreign_account_change_def, account_already_created_def])
  >> qexistsl_tac [`es`,`r`] >> simp[]
  >> rpt gen_tac >> strip_tac
  >> `e'.rollback.accounts = e.rollback.accounts` suffices_by simp[]
  >> irule run_call_empty_code_frame >> simp[] >> gvs[]
  >> suspend "empty_entry"
QED

Resume run_call_empty_code_account[empty_entry]:
  `(FST (HD e.contexts)).msgParams.callee ≠ (FST (HD s.contexts)).msgParams.callee`
    by metis_tac[]
  >> drule_all step_push_new_frame >> strip_tac >> gvs[]
  >> qpat_assum `FST (HD e.contexts) = initial_context _ _ _ _ _`
       (once_rewrite_tac o single)
  >> simp[initial_context_def, initial_msg_params_def,
          get_delegate_def, is_delegation_def]
QED

Finalise run_call_empty_code_account

(* -------------------------------------------------------------------------
 * Provenance of storage keys: SK y k enters the access list only in a step
 * executing as y (SLOAD/SSTORE access the callee's slots).
 * ------------------------------------------------------------------------- *)

Theorem step_storage_keys_foreign:
  wf_state s ∧ step s = (r, s') ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) s'.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys ∨
  LENGTH s'.contexts < LENGTH s.contexts ∧
  fIN (SK y k) (SND (HD s.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> Cases_on `step_inner s`
  >> rename1 `step_inner s = (u,t)`
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >> Cases_on `u`
  >- (gvs[step_eq_handle_step_inner, handle_def]
      >> metis_tac[step_inner_foreign_storage_key])
  >> gvs[step_eq_handle_step_inner, handle_def]
  >> `t.contexts ≠ []` by
    (drule_all step_inner_saved_storage_keys >> strip_tac
     >> Cases_on `t.contexts` >> gvs[])
  >> drule_all handle_step_storage_keys >> strip_tac
  >- (gvs[] >> metis_tac[step_inner_foreign_storage_key])
  >> drule_all step_inner_saved_storage_keys >> strip_tac
  >- (Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[])
  >> Cases_on `t.contexts` >> gvs[]
QED

Theorem step_push_storage_keys:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys =
    s.rollback.accesses.storageKeys
Proof
  strip_tac >> drule_all step_grow_dispatch >> strip_tac
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >- (drule_all step_call_push_storage_keys >> simp[])
  >> drule_all step_create_push_storage_keys >> simp[]
QED

Theorem active_storage_key_absent_iff[local]:
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ⇔
  ¬fIN z s.rollback.accesses.storageKeys ∧
  (d ≤ LENGTH s.contexts ⇒
   ∀i. i < LENGTH s.contexts - d + 1 ∧ i + 1 < LENGTH s.contexts ⇒
     ¬fIN z (SND (EL i s.contexts)).accesses.storageKeys)
Proof
  simp[active_rollbacks_saved]
  >> IF_CASES_TAC >> simp[]
  >> simp[EVERY_EL, EL_MAP, EL_TAKE, arithmeticTheory.MIN_DEF]
  >> IF_CASES_TAC >> simp[]
  >> eq_tac >> rpt strip_tac >> gvs[]
  >> first_x_assum drule >> simp[] >> decide_tac
QED

Theorem active_storage_key_absent_current[local]:
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ⇒
  ¬fIN z s.rollback.accesses.storageKeys
Proof
  simp[active_rollbacks_def]
QED

Theorem active_storage_key_absent_head[local]:
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ∧
  d ≤ LENGTH s.contexts ∧ 2 ≤ LENGTH s.contexts ⇒
  ¬fIN z (SND (HD s.contexts)).accesses.storageKeys
Proof
  rw[active_storage_key_absent_iff] >> gvs[]
  >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem active_storage_key_absent_initial[local]:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     ¬fIN z (SND (HD es.contexts)).accesses.storageKeys) ∧
  ¬fIN z es.rollback.accesses.storageKeys ⇒
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys)
        (active_rollbacks (LENGTH es.contexts) es)
Proof
  rw[active_storage_key_absent_iff]
  >> gvs[finite_setTheory.fIN_IN, pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem front_eq_el[local]:
  FRONT xs = FRONT ys ∧ i + 1 < LENGTH xs ∧ i + 1 < LENGTH ys ⇒
  EL i xs = EL i ys
Proof
  strip_tac
  >> `xs ≠ [] ∧ ys ≠ []` by (Cases_on `xs` >> Cases_on `ys` >> gvs[])
  >> `EL i (FRONT xs) = EL i (FRONT ys)` by simp[]
  >> qpat_x_assum `FRONT _ = _` kall_tac
  >> gvs[rich_listTheory.EL_FRONT, rich_listTheory.LENGTH_FRONT, NULL_EQ]
QED

Theorem step_push_saved_key_index[local]:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ⇒
  ∀i. i + 1 < LENGTH t.contexts ⇒
    (SND (EL i t.contexts)).accesses.storageKeys =
    (if i = 0 then s.rollback.accesses.storageKeys
     else (SND (EL (i-1) s.contexts)).accesses.storageKeys)
Proof
  strip_tac
  >> drule_all step_push_storage_keys >> strip_tac
  >> drule_all step_push_foreign >> strip_tac
  >> qpat_x_assum `∀y. _` kall_tac
  >> Cases_on `i`
  >- simp[]
  >> Cases_on `n`
  >- (rpt strip_tac >> gvs[])
  >> rpt strip_tac
  >> rename1 `SUC (SUC j) + 1 < LENGTH t.contexts`
  >> `EL j (TL (TL t.contexts)) = EL j (TL s.contexts)` by
    (irule front_eq_el >> simp[]
     >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
     >> Cases_on `t'` >> gvs[])
  >> namedCases_on `t.contexts` ["", "tc tcs"] >> gvs[]
  >> Cases_on `tcs` >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem active_storage_key_absent_step[local]:
  wf_state s ∧ 0 < d ∧ d ≤ LENGTH s.contexts ∧ step s = (r,t) ∧
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d s) ∧
  ¬fIN z t.rollback.accesses.storageKeys ⇒
  EVERY (λrb. ¬fIN z rb.accesses.storageKeys) (active_rollbacks d t)
Proof
  simp[active_storage_key_absent_iff] >> strip_tac >> gvs[]
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac
      >> qpat_x_assum `∀y. _` kall_tac
      >> simp[] >> rpt strip_tac
      >> first_x_assum (qspec_then `i` mp_tac)
      >> Cases_on `i`
      >- gvs[]
      >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[])
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_at (Pat `step _ = _`) step_push_saved_key_index
      >> simp[] >> strip_tac
      >> drule_all step_push_foreign >> strip_tac
      >> qpat_x_assum `∀y. _` kall_tac
      >> simp[] >> rpt strip_tac
      >> first_x_assum (qspec_then `i` mp_tac)
      >> impl_tac >- decide_tac
      >> strip_tac >> simp[]
      >> Cases_on `i` >> gvs[]
      >> first_x_assum irule >> decide_tac)
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> drule_all step_pop_foreign >> strip_tac
  >> simp[] >> rpt strip_tac
  >> first_x_assum (qspec_then `SUC i` mp_tac)
  >> (impl_tac >- (Cases_on `s.contexts` >> gvs[] >> decide_tac))
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `i` >> gvs[]
QED

(* Every storage key run_call adds for `a` was added by a step executing as
 * `a`, from a reached state. *)
Theorem run_call_storage_key_added:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     ¬fIN (SK a k) (SND (HD es.contexts)).accesses.storageKeys) ∧
  run_call es = SOME (r, es') ∧
  fIN (SK a k) es'.rollback.accesses.storageKeys ∧
  ¬fIN (SK a k) es.rollback.accesses.storageKeys ⇒
  ∃s u s'.
    run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
    (FST (HD s.contexts)).msgParams.callee = a ∧
    step s = (u, s') ∧
    ¬fIN (SK a k) s.rollback.accesses.storageKeys ∧
    fIN (SK a k) s'.rollback.accesses.storageKeys
Proof
  strip_tac >> spose_not_then assume_tac
  >> `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[wf_state_def])
  >> `EVERY (λrb. ¬fIN (SK a k) rb.accesses.storageKeys)
         (active_rollbacks (LENGTH es.contexts) es)` by
    (irule active_storage_key_absent_initial >> simp[])
  >> `¬fIN (SK a k) es'.rollback.accesses.storageKeys` suffices_by simp[]
  >> gvs[run_call_def]
  >> `((λp. wf_state (SND p) ∧
          EVERY (λrb. ¬fIN (SK a k) rb.accesses.storageKeys)
            (active_rollbacks (LENGTH es.contexts) (SND p)) ∧
          (ISL (FST p) ⇒ run_call_reaches es (SND p))) (r,es'))`
       suffices_by (BETA_TAC >> pure_rewrite_tac[FST, SND] >> strip_tac
                    >> drule active_storage_key_absent_current >> simp[])
  >> irule (MP_CANON WhileTheory.OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[] >> rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac
  >> Cases_on `step s''` >> rename1 `step s'' = (v,t)` >> gvs[]
  >> `LENGTH es.contexts ≤ LENGTH s''.contexts` by decide_tac
  >> `¬fIN (SK a k) s''.rollback.accesses.storageKeys` by
    (drule active_storage_key_absent_current >> simp[])
  >> `¬fIN (SK a k) t.rollback.accesses.storageKeys` by
    (Cases_on `(FST (HD s''.contexts)).msgParams.callee = a`
     >- (qpat_x_assum `∀s u s'. _` (qspecl_then [`s''`,`v`,`t`] mp_tac)
         >> simp[] >> decide_tac)
     >> `a ≠ (FST (HD s''.contexts)).msgParams.callee` by simp[]
     >> strip_tac
     >> drule_all step_storage_keys_foreign >> strip_tac >> gvs[]
     >> `s''.contexts ≠ []` by gvs[wf_state_def]
     >> `t.contexts ≠ []` by
       (drule step_preserves_nonempty_contexts >> simp[])
     >> `2 ≤ LENGTH s''.contexts` by
       (Cases_on `t.contexts` >> gvs[])
     >> drule_all active_storage_key_absent_head >> simp[])
  >> conj_tac >- (qspec_then `s''` mp_tac (GEN_ALL step_preserves_wf_state) >> simp[])
  >> conj_tac
  >- (irule active_storage_key_absent_step >> simp[] >> goal_assum drule >> simp[])
  >> Cases_on `v` >> simp[]
  >> irule run_call_reaches_step >> goal_assum drule >> simp[]
QED
