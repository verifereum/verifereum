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
  combin pair option list rich_list relation While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStoragePredicates vfmPreserves vfmHandleStep
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

Theorem set_tStorage_storage_keys[local]:
  preserves (λs t. t.rollback.accesses.storageKeys =
                   s.rollback.accesses.storageKeys) (set_tStorage x)
Proof
  rw[preserves_def, set_tStorage_def, return_def]
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
  cheat
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
  cheat
QED

(* Domain collection mode is never left. *)
Theorem step_preserves_collect:
  (∃d. s.msdomain = Collect d) ∧ step s = (r, s') ⇒
  ∃d. s'.msdomain = Collect d
Proof
  cheat
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
  cheat
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
  cheat
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

Theorem run_call_account_frame:
  wf_state es ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
  P (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     P (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  (∀e r e'.
     (FST (HD e.contexts)).msgParams.callee = a ∧
     wf_state e ∧ P (lookup_account a e.rollback.accounts) ∧
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
  cheat
QED

(* -------------------------------------------------------------------------
 * Accounts with no code.
 * ------------------------------------------------------------------------- *)

(* A frame running empty code stops at once; if the callee has no code, a
 * code deposit leaves it so. *)
Theorem run_call_empty_code_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
     e.rollback.accounts).code = [] ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts
Proof
  cheat
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
  cheat
QED

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
  cheat
QED

Theorem step_push_storage_keys:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys =
    s.rollback.accesses.storageKeys
Proof
  cheat
QED

(* Every storage key run_call adds for `a` was added by a step executing as
 * `a`, from a reached state. *)
Theorem run_call_storage_key_added:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     toSet (SND (HD es.contexts)).accesses.storageKeys ⊆
     toSet es.rollback.accesses.storageKeys) ∧
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
  cheat
QED
