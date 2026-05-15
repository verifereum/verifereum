(* ==========================================================================
 * run_call storage preservation: slots not in final storageKeys are unchanged.
 * The invariant tracks txParams and rollback states reachable by revert.
 * ========================================================================== *)
Theory vfmRunCall
Ancestors
  combin pair option pred_set list rich_list sum
  arithmetic finite_map While vfmTypes vfmConstants
  vfmContext vfmState vfmExecution vfmExecutionProp
  vfmStoragePredicates vfmSameFrame vfmStaticCalls
  vfmDecreasesGas vfmStepLength vfmHandleStep vfmRunWithinFrame
  vfmHeadStack vfmHeadGas vfmJumpDest
Libs
  dep_rewrite BasicProvers

(* Rollbacks that can become current by reverting during run_call.
 * Exclude the final saved rollback: it is never restored, and CREATE may
 * modify it via set_original. *)

Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback ::
    (if LENGTH s.contexts < es_depth then []
     else MAP SND (TAKE (MIN (LENGTH s.contexts - es_depth + 1)
                              (LENGTH s.contexts - 1)) s.contexts))
End

(* Per-context outputTo consistency, needed across pops. *)

Theorem outputTo_consistent_stack_imp_consistent:
  outputTo_consistent_stack s ⇒ outputTo_consistent s
Proof
  rw[outputTo_consistent_stack_def, outputTo_consistent_def]
  >> Cases_on `s.contexts` >> gvs[outputTo_consistent_ctx_def]
QED

(* Per-slot storage preservation outside access-listed storage keys. *)

Definition storage_slot_preserved_def:
  storage_slot_preserved rb rb0 ⇔
    ∀a k. ¬fIN (SK a k) rb.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a rb.accounts).storage =
        lookup_storage k (lookup_account a rb0.accounts).storage
End

(* -------------------------------------------------------------------------
 * The 2-state run_call invariant.
 * ------------------------------------------------------------------------- *)

Definition run_call_inv_def:
  run_call_inv es s ⇔
    s.txParams = es.txParams ∧
    outputTo_consistent_stack s ∧
    wf_state s ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  wf_state es ∧
  (FST (HD es.contexts)).jumpDest = NONE ∧
  EVERY (λrb. storage_slot_preserved rb es.rollback)
        (MAP SND (TAKE 2 es.contexts)) ⇒
  run_call_inv es es
Proof
  rw[run_call_inv_def, active_rollbacks_def, storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def,wf_state_def]
  >> Cases_on `es.contexts` >> gvs[]
  >> rw[MIN_DEF]
  >> Cases_on`t` >> gvs[ADD1]
QED

(* Single-step preservation of run_call_inv: split on same-frame/push/pop. *)


(* Same-frame step storage preservation outside final storageKeys. *)

(* Same-frame case: non-callee storage is unchanged by callee_local_changes;
 * callee storage can change only via SSTORE, which first access-lists the slot. *)



(* Pushed rollback storage: when CALL/CREATE pushes, the new head's saved
 * rollback has the old rollback's storage. *)

(* proceed_call captures s.rollback as the pushed rollback. *)
Theorem proceed_call_pushed_rb_storage:
  proceed_call op sender address value argsOffset argsSize code stipend
                outputTo s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  (* get_rollback captures s.rollback. *)
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  (* g is either update_accounts (transfer_value ...) or return () — both
     preserve storage of s.rollback.accounts at every address. *)
  >> `∀a. (lookup_account a s1.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage`
      by (`preserves_storage g`
            by (simp[Abbr`g`] >> IF_CASES_TAC >> simp[])
          >> fs[preserves_storage_def] >> first_x_assum drule >>
          rw[lookup_storage_def] >> gvs[FUN_EQ_THM])
  >> `ISL q` by (gvs[Abbr`g`,AllCaseEqs(),COND_RATOR,return_def,
                     update_accounts_def])
  >> TOP_CASE_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> IF_CASES_TAC >> gvs[fail_def] >- (rw[] >> gvs[])
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
  (* After push_context: HD = (context, s1.rollback-like). Specifically,
     push_context (c, rollback) where `rollback` was captured by get_rollback
     after g ran. So HD s_after_push.contexts = (c, s1.rollback). *)
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC >> simp[return_def]
  >- ((* No precompile: result state has HD = (ctx, s1.rollback). *)
      strip_tac >> gvs[])
  (* Precompile: dispatch_precompiles runs after push. It is
     preserves_same_frame at the new depth, so SND (HD ·) is invariant. *)
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac`dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> `ss.contexts = (ctx, s.rollback) :: s1.contexts` by simp[Abbr`ss`]
  >> simp[same_frame_rel_def]
QED

(* Intermediate: proceed_create captures s.rollback (post increment_nonce)
   as the pushed rollback. increment_nonce and set_original do not touch
   s.rollback.accounts.storage. transfer_value happens AFTER get_rollback,
   so it doesn't affect the captured rollback. *)
Theorem proceed_create_pushed_rb_storage:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback: captures increment_nonce'd rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original / set_original: don't modify s.rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce): modifies s.rollback,
     but the captured `rollback` variable already holds the pre-transfer one. *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context. *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* After push: HD s'.contexts = (ctx, rollback-with-incremented-nonce).
     increment_nonce preserves storage at every address. *)
  >> rw[lookup_account_def, increment_nonce_def,
        combinTheory.APPLY_UPDATE_THM, finite_mapTheory.FLOOKUP_UPDATE]
  >> gvs[update_account_def, APPLY_UPDATE_THM]
  >> rw[]
QED

(* proceed_call push structure. *)
Theorem proceed_call_push_structure:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  TL s'.contexts = s.contexts ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  (FST (HD s'.contexts)).msgParams.outputTo = outputTo ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  (* g preserves contexts and accesses. *)
  >> `s1.contexts = s.contexts ∧
      toSet s.rollback.accesses.storageKeys ⊆ toSet s1.rollback.accesses.storageKeys`
      by (simp[Abbr`g`] >> gvs[COND_RATOR,AllCaseEqs(),update_accounts_def, return_def])
  >> `ISL q` by (gvs[Abbr`g`,AllCaseEqs(),COND_RATOR,return_def,
                     update_accounts_def])
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
  (* After push_context, TL is the old contexts. *)
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC >> simp[return_def]
  >- ((* No precompile *)
      strip_tac >> gvs[Abbr`ctx`, initial_msg_params_def] >>
      gvs[SUBSET_DEF] )
  (* Precompile dispatch is same-frame. *)
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac`dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> `ss.contexts = (ctx, s.rollback) :: s.contexts` by simp[Abbr`ss`]
  >> simp[same_frame_rel_def]
  >> strip_tac >> gvs[SUBSET_DEF]
  >> gvs[Abbr`ctx`,initial_context_def, initial_msg_params_def]
  >> gvs[Abbr`ss`]
QED

(* proceed_create push structure. *)
Theorem proceed_create_push_structure:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  MAP FST (TL s'.contexts) = MAP FST s.contexts ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original / set_original: don't modify contexts or accesses *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce) *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* outputTo_consistent: outputTo = Code address, callee = address *)
  >> simp[outputTo_consistent_ctx_def, initial_context_def,
          initial_msg_params_def]
  >> simp[set_last_accounts_def, MAP_SNOC, MAP_FRONT]
  >> qspec_then`MAP FST s.contexts`mp_tac SNOC_LAST_FRONT
  >> simp[]
  (* SND HD is the captured rollback; nonce changes preserve accesses. *)
  >> gvs[SUBSET_DEF]
QED

(* CALL/CREATE wrappers: same-frame storage-preserving prefixes, then proceed_*. *)

(* Composable predicate: if m grows, the pushed rollback preserves storage. *)
Definition preserves_pushed_rb_storage_def:
  preserves_pushed_rb_storage (m : α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ∧
             LENGTH s'.contexts > LENGTH s.contexts ⇒
      ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
          (lookup_account a s.rollback.accounts).storage
End

(* Same-frame prefixes cannot grow, so the pushed-rb property is vacuous. *)
Theorem preserves_pushed_rb_storage_of_same_frame[simp]:
  preserves_same_frame m ⇒ preserves_pushed_rb_storage m
Proof
  rw[preserves_same_frame_def, preserves_pushed_rb_storage_def]
  >> first_x_assum drule >> simp[same_frame_rel_def]
QED

(* bind composition for pushed-rb storage. *)
Theorem preserves_pushed_rb_storage_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  (∀x. preserves_pushed_rb_storage (f x)) ⇒
  preserves_pushed_rb_storage (bind g f)
Proof
  rw[preserves_pushed_rb_storage_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> fs[preserves_storage_def, preserves_same_frame_def]
  >> rpt (first_x_assum drule) >> simp[same_frame_rel_def] >> strip_tac
  >> rpt strip_tac
  (* s_mid has same contexts and storage as s. *)
  >> qmatch_asmsub_rename_tac `g s = (_, s_mid)`
  >> `s_mid.contexts ≠ []` by (Cases_on `s.contexts` >> Cases_on `s_mid.contexts` >> fs[])
  >> `LENGTH s'.contexts > LENGTH s_mid.contexts` by fs[]
  >> first_x_assum drule >> simp[]
  >> disch_then (qspec_then `a` mp_tac) >> simp[]
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

Theorem preserves_pushed_rb_storage_ignore_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  preserves_pushed_rb_storage f ⇒
  preserves_pushed_rb_storage (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule preserves_pushed_rb_storage_bind >> rw[]
QED

Theorem preserves_pushed_rb_storage_cond[simp]:
  preserves_pushed_rb_storage m1 ∧ preserves_pushed_rb_storage m2 ⇒
  preserves_pushed_rb_storage (if b then m1 else m2)
Proof
  rw[]
QED

(* Base case: proceed_call preserves pushed rb storage. *)
Theorem preserves_pushed_rb_storage_proceed_call[simp]:
  preserves_pushed_rb_storage
    (proceed_call op sender address value argsOffset argsSize
                  code stipend outputTo)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_call_pushed_rb_storage
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_proceed_create[simp]:
  preserves_pushed_rb_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_create_pushed_rb_storage
  >> simp[]
QED

(* Now step_call = a bunch of preserves_storage+preserves_same_frame
   primitives followed by either abort_call_value (which is
   preserves_same_frame, vacuously preserves_pushed_rb_storage),
   abort_unuse (likewise), or proceed_call. *)
Theorem preserves_pushed_rb_storage_step_call[simp]:
  preserves_pushed_rb_storage (step_call op)
Proof
  simp[step_call_def]
  (* Shape mirrors preserves_storage_step_call's proof. Every bind
     prefix is preserves_storage + preserves_same_frame; use the
     bind rule with those two side conditions. *)
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[]
  >> reverse conj_tac >- (CASE_TAC >> simp[])
  >> Cases >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* abort_create_exists doesn't grow contexts, so vacuously preserves
   pushed-rb storage. Unlike abort_call_value/abort_unuse, it is NOT
   unconditionally preserves_same_frame (it requires the sender address
   to match the current callee), so we prove it from the length lemma. *)
Theorem preserves_pushed_rb_storage_abort_create_exists[simp]:
  preserves_pushed_rb_storage (abort_create_exists a)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all abort_create_exists_length
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_step_create[simp]:
  preserves_pushed_rb_storage (step_create two)
Proof
  simp[step_create_def]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> rpt (irule preserves_pushed_rb_storage_ignore_bind >> simp[])
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> rpt (irule preserves_pushed_rb_storage_ignore_bind >> simp[])
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* Final user-facing lemmas. *)
Theorem step_call_pushed_rb_storage:
  ∀op s r s'. step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_call,
            preserves_pushed_rb_storage_def]
QED

Theorem step_create_pushed_rb_storage:
  ∀two s r s'. step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_create,
            preserves_pushed_rb_storage_def]
QED

(* step_call growth structure: peel same-frame prefixes, then proceed_call. *)
Theorem step_call_push_structure:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  TL (TL s'.contexts) = TL s.contexts ∧
  SND (HD (TL s'.contexts)) = SND (HD s.contexts) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  simp[step_call_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> pairarg_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 s9`
  >> `same_frame_rel s s9` by metis_tac[same_frame_rel_trans]
  >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s9 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> gvs[Ntimes COND_RATOR 2]
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Peel set_return_data via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the conditional: if value check then abort else continue *)
  (* Second conditional: if depth/code check then abort else proceed_call *)
  >> gvs[COND_RATOR]
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Now we have proceed_call sm = (_, s') with growth, and same_frame_rel s sm *)
  >> drule_all proceed_call_push_structure
  >> strip_tac
  (* From same_frame_rel s sm: sm.contexts = s.contexts *)
  >> `TL sb.contexts = TL s.contexts` by ( fs[same_frame_rel_def] )
  >> gvs[]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_tac >- metis_tac[SUBSET_TRANS, same_frame_rel_def]
  (* outputTo_consistent: outputTo = Memory from step_call, so Code a is vacuous *)
  >> conj_tac >- simp[outputTo_consistent_ctx_def]
  >> metis_tac[SUBSET_TRANS, same_frame_rel_def]
QED

(* TODO: move *)
Theorem LAST_CONS_SNOC:
  LAST (x::(SNOC y z)) = y
Proof
  map_every qid_spec_tac[`x`,`y`,`z`] >> Induct >> rw[]
QED

(* TODO: move *)
Theorem FRONT_CONS_SNOC:
  FRONT (x::(SNOC y z)) = x::z
Proof
  map_every qid_spec_tac[`x`,`y`,`z`] >> Induct >> rw[] >>
  rewrite_tac[GSYM SNOC_APPEND] >> rw[]
QED

(* step_create growth structure.  set_original may alter the last saved
 * rollback, so storage equality is limited to the needed non-callee case. *)
Theorem step_create_push_structure:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  (∀i. i < LENGTH s.contexts ⇒
       (SND (EL i (TL s'.contexts))).accesses = (SND (EL i s.contexts)).accesses) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
     (lookup_account a (SND (HD (TL s'.contexts))).accounts).storage =
     (lookup_account a (SND (HD s.contexts)).accounts).storage) ∧
  (∀i. i < LENGTH s.contexts - 1 ⇒
     (SND (EL i (TL s'.contexts))).accounts =
     (SND (EL i s.contexts)).accounts) ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
    (lookup_account a (SND (EL (LENGTH s.contexts) s'.contexts)).accounts).storage =
    (lookup_account a (SND (LAST s.contexts)).accounts).storage)
Proof
  simp[step_create_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel read_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_accounts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert (code length) via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel access_address *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 s9`
  >> `same_frame_rel s s9` by metis_tac[same_frame_rel_trans]
  >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_gas_left *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s9 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas (cappedGas) *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert_not_static *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel set_return_data *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sb sc`
  >> `same_frame_rel s sc` by metis_tac[same_frame_rel_trans]
  >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sc sd`
  >> `same_frame_rel s sd` by metis_tac[same_frame_rel_trans]
  >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel ensure_storage_in_domain *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sd se`
  >> `same_frame_rel s se` by metis_tac[same_frame_rel_trans]
  >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the conditional *)
  >> gvs[Ntimes COND_RATOR 2]
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
  >> qpat_x_assum`COND bbb _ _ = _`mp_tac
  >> IF_CASES_TAC
  >- ((* abort_unuse: preserves_same_frame, can't grow *)
      strip_tac >>
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
  >> IF_CASES_TAC
  >- ((* abort_create_exists: length_preserves, can't grow *)
      strip_tac >>
      drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists)
      >> simp[])
  (* Now we have proceed_create sf = (_, s') with growth, and same_frame_rel s sf *)
  >> strip_tac
  >> drule_all proceed_create_push_structure
  >> strip_tac
  (* From same_frame_rel s sf: TL sf.contexts = TL s.contexts *)
  >> `TL se.contexts = TL s.contexts` by gvs[same_frame_rel_def]
  >> gvs[]
  >> conj_asm1_tac >- (
    qpat_x_assum`same_frame_rel s se`mp_tac >>
    simp[same_frame_rel_def] >> strip_tac >>
    Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`t` >> gvs[] >>
    Cases_on`se.contexts` >> gvs[] )
  (* Remaining: per-pos accesses, msgParams, rollback, outputTo, SND(HD),
     a≠callee storage *)
  >> rewrite_tac[Ntimes CONJ_ASSOC 3]
  >> reverse conj_tac >- (
    (* Position-1 storage equality for non-callee addresses. *)
    qpat_x_assum `proceed_create _ _ _ _ _ se = _` mp_tac >>
    rewrite_tac[proceed_create_def] >>
    simp[ignore_bind_def, bind_def, update_accounts_def, return_def,
          get_rollback_def, get_original_def, set_original_def, fail_def] >>
    strip_tac >> gvs[] >>
    drule push_context_effect >> strip_tac >> gvs[] >>
    simp[lookup_storage_def, lookup_account_def] >>
    qmatch_goalsub_abbrev_tac`SND (EL _ (slc uc _))` >>
    qmatch_goalsub_abbrev_tac`(SND (EL _ icc)).accounts _` >>
    gvs[push_context_def,return_def,execution_state_component_equality] >>
    gvs[account_already_created_def,lookup_account_def] >>
    Cases_on`s.contexts` >- gvs[] >> simp[] >>
    Cases_on`se.contexts` >- gvs[] >> simp[Abbr`slc`] >>
    gvs[set_last_accounts_def] >>
    simp[EL_SNOC] >>
    simp[Abbr`icc`] >>
    qmatch_goalsub_abbrev_tac`EL (LENGTH t) (SNOC sn fr)` >>
    `LENGTH fr = LENGTH t` by simp[Abbr`fr`] >>
    pop_assum(SUBST1_TAC o SYM) >> simp[EL_LENGTH_SNOC,Abbr`sn`] >>
    gvs[Abbr`fr`] >>
    `SND h = SND h'` by (
      qpat_x_assum`same_frame_rel s se`mp_tac >>
      simp[same_frame_rel_def] ) >>
    simp[initial_msg_params_def] >>
    reverse(qspec_then`t`FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[]) >- (
      simp[LAST_CONS_SNOC, FRONT_CONS_SNOC] >>
      conj_tac >- ( Cases >> simp[EL_SNOC] ) >>
      simp[Abbr`uc`, update_account_def, APPLY_UPDATE_THM] >>
      gen_tac >> simp[LAST_CONS_SNOC] ) >>
    simp[Abbr`uc`, lookup_account_def, update_account_def, APPLY_UPDATE_THM] )
  >> simp[GSYM CONJ_ASSOC]
  >> reverse conj_tac >- (
    (* SND (HD s'.contexts) accesses subset *)
    reverse conj_tac
    >- metis_tac[SUBSET_TRANS, same_frame_rel_def] >>
    (* msgParams *)
    qpat_x_assum`same_frame_rel s se`mp_tac >>
    simp[same_frame_rel_def] >> strip_tac >>
    Cases_on`s.contexts` >- gvs[] >> simp[] >>
    Cases_on`s'.contexts` >- gvs[] >> simp[] >>
    Cases_on`t'` >- gvs[] >> simp[] >>
    Cases_on`se.contexts` >- gvs[] >>
    fs[]  )
  (* set_original only touches .accounts. *)
  >> qpat_x_assum `proceed_create _ _ _ _ _ se = _` mp_tac
  >> simp[proceed_create_def]
  >> simp[ignore_bind_def, bind_def, update_accounts_def, return_def,
          get_rollback_def, get_original_def, set_original_def, fail_def]
  >> strip_tac >> gvs[]
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* TL s'.contexts = set_last_accounts ... sf.contexts *)
  >> rpt strip_tac
  >> `i < LENGTH se.contexts` by gvs[same_frame_rel_def]
  >> simp[set_last_accounts_def]
  >> qmatch_goalsub_abbrev_tac`SNOC new`
  >> qhdtm_x_assum`push_context` kall_tac
  >> qpat_x_assum`_ = TL s.contexts`mp_tac
  >> simp[LIST_EQ_REWRITE] >> rewrite_tac[GSYM EL]
  >> Cases_on`i=0` >- (
    Cases_on`FRONT se.contexts = []`
    >- (
      gvs[] >>
      gvs[Abbr`new`] >>
      Cases_on`se.contexts` >> gvs[] >>
      Cases_on`s.contexts` >> gvs[] >>
      qpat_x_assum`same_frame_rel s se`mp_tac >>
      simp[same_frame_rel_def] ) >>
    rewrite_tac[GSYM EL] >>
    DEP_REWRITE_TAC[EL_SNOC] >>
    simp[LENGTH_FRONT] >>
    simp[PRE_SUB1] >>
    Cases_on`se.contexts` >> gvs[] >>
    Cases_on`s.contexts` >> gvs[] >>
    Cases_on`t` >> gvs[] >>
    qpat_x_assum`same_frame_rel s se`mp_tac >>
    simp[same_frame_rel_def] )
  >> Cases_on`i = LENGTH s.contexts - 1`
  >- (
    `i = LENGTH (FRONT se.contexts)` by simp[LENGTH_FRONT] >>
    pop_assum SUBST1_TAC >>
    simp[EL_LENGTH_SNOC] >>
    simp[Abbr`new`, LENGTH_FRONT, GSYM LAST_EL] >>
    simp[LAST_EL] >> strip_tac >>
    AP_TERM_TAC >> AP_TERM_TAC >>
    first_x_assum(qspec_then`PRE i`mp_tac) >>
    simp[PRE_SUB1,ADD1] )
  >> strip_tac
  >> simp[EL_SNOC, LENGTH_FRONT, EL_FRONT, NULL_EQ]
  >> first_x_assum(qspec_then`PRE i`mp_tac)
  >> simp[ADD1, PRE_SUB1]
QED

(* Full step storage preservation in the same-frame case. *)
Theorem step_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent s ∧
    same_frame_rel s s' ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >> reverse (Cases_on `a = (FST (HD s.contexts)).msgParams.callee`)
  >- (
    (* Non-callee address: callee_local_changes gives equality directly. *)
    `(lookup_account a s'.rollback.accounts).storage =
     (lookup_account a s.rollback.accounts).storage`
       by fs[same_frame_rel_def, callee_local_changes_def]
    >> simp[])
  (* Callee address. Unfold step = handle inner handle_step and
     analyse the cases. *)
  >> `¬fIN (SK a k) s.rollback.accesses.storageKeys` by (
       `toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys`
          by fs[same_frame_rel_def]
       >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
       >> metis_tac[])
  (* Unfold step = handle inner handle_step. *)
  >> qhdtm_x_assum `step` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `pair_CASE (inner s)`
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> Cases_on `inner s` >> Cases_on `q` >> simp[]
  >- (
    (* inner INL: step returns inner result. *)
    strip_tac >> gvs[]
    (* Unfold inner to get the actual primitives that ran. *)
    >> qhdtm_x_assum `Abbrev` mp_tac
    >> simp[markerTheory.Abbrev_def]
    >> disch_then SUBST_ALL_TAC
    >> qpat_x_assum `_ s = (INL (), r')` mp_tac
    >> simp[bind_def, ignore_bind_def]
    >> simp[get_current_context_def, return_def, fail_def]
    >> Cases_on `s.contexts` >> gvs[]
    >> Cases_on `LENGTH (FST h).msgParams.code ≤ (FST h).pc` >> gvs[]
    >- (
      (* Stop case. *)
      strip_tac
      >> drule step_inst_preserves_non_accessed_storage
      >> simp[is_call_def]
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    >> Cases_on `FLOOKUP (FST h).msgParams.parsed (FST h).pc` >> gvs[]
    >- (
      (* Invalid case. *)
      strip_tac
      >> drule step_inst_preserves_non_accessed_storage
      >> simp[is_call_def]
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op. *)
    >> strip_tac
    >> gvs[bind_def, ignore_bind_def, AllCaseEqs()]
    >> rename1 `step_inst op s = (INL _, r_mid)`
    >> `r_mid.rollback = r'.rollback`
         by (mp_tac preserves_rollback_inc_pc_or_jump
             >> rewrite_tac[preserves_rollback_def]
             >> disch_then drule
             >> simp[])
    >> `s.contexts ≠ []` by (strip_tac >> fs[])
    >> Cases_on `is_call op`
    >- (
      (* Call/Create family: step_inst returned INL with same frame length
         (since inc_pc_or_jump is same_frame and r' has same length as s).
         This means an abort path ran — no storage written. *)
      `r_mid.contexts ≠ []` by (
         `(SND (step_inst op s)).contexts ≠ []`
            by metis_tac[step_inst_preserves_nonempty_contexts]
         >> rev_full_simp_tac std_ss [])
      >> `LENGTH r_mid.contexts = LENGTH s.contexts` by (
         `LENGTH r'.contexts = LENGTH r_mid.contexts` by (
            `preserves_same_frame (inc_pc_or_jump op)` by simp[]
            >> metis_tac[psf_imp_length_contexts_preserved])
         >> fs[same_frame_rel_def])
      >> drule_all is_call_same_frame_preserves_storage
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    >> drule step_inst_preserves_non_accessed_storage
    >> simp[]
    >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
    >> simp[])
  >> strip_tac >>
  qhdtm_x_assum`same_frame_or_grow`mp_tac >>
  simp[same_frame_or_grow_def] >> disch_then drule >> simp[] >>
  strip_tac >- (
    qpat_x_assum`inner _ = _`mp_tac >>
    simp[Abbr`inner`, bind_def,AllCaseEqs()] >>
    simp[get_current_context_def, return_def, COND_RATOR, AllCaseEqs()] >>
    strip_tac >- (
      drule step_inst_preserves_non_accessed_storage >>
      simp[is_call_def] >>
      disch_then(qspecl_then[`a`,`k`]mp_tac) >>
      impl_keep_tac >- (
        gvs[step_inst_def, bind_def, ignore_bind_def,
            set_return_data_def, finish_def, AllCaseEqs(),
            get_current_context_def,set_current_context_def,
            return_def,fail_def] ) >>
      disch_then $ assume_tac o SYM >> gvs[] >>
      irule handle_step_preserves_storage_same_length >>
      drule same_frame_rel_contexts_ne >> simp[] >> strip_tac >>
      conj_asm1_tac >- (
        gvs[same_frame_rel_def] >>
        gvs[outputTo_consistent_def] ) >>
      reverse conj_tac >- goal_assum drule >>
      fs[same_frame_rel_def] ) >>
    gvs[AllCaseEqs(),option_CASE_rator] >- (
      drule step_inst_preserves_non_accessed_storage >>
      simp[is_call_def] >>
      qmatch_goalsub_abbrev_tac`lookup_account a` >>
      disch_then(qspecl_then[`a`,`k`]mp_tac) >>
      impl_keep_tac >- (
        gvs[step_inst_def, bind_def, ignore_bind_def,
            set_return_data_def, finish_def, AllCaseEqs(),
            get_current_context_def,set_current_context_def,
            return_def,fail_def] ) >>
      disch_then $ assume_tac o SYM >> gvs[] >>
      irule handle_step_preserves_storage_same_length >>
      drule same_frame_rel_contexts_ne >> simp[] >> strip_tac >>
      conj_asm1_tac >- (
        gvs[same_frame_rel_def] >>
        gvs[outputTo_consistent_def] ) >>
      reverse conj_tac >- goal_assum drule >>
      fs[same_frame_rel_def] ) >>
    pop_assum mp_tac >>
    simp[ignore_bind_def,bind_def] >>
    TOP_CASE_TAC >> strip_tac >>
    reverse (Cases_on `q`) >> gvs[] >- (
      (* step_inst op s = (INR y, r' = r'') *)
      Cases_on `is_call op` >- (
        (* call op INR same-length: use preserves_storage_step_call/create *)
        `lookup_storage k
            (lookup_account (FST (HD s.contexts)).msgParams.callee
               r'.rollback.accounts).storage =
         lookup_storage k
            (lookup_account (FST (HD s.contexts)).msgParams.callee
               s.rollback.accounts).storage` by (
          Cases_on `op` >> fs[is_call_def, step_inst_def]
          >> metis_tac[preserves_storage_step_call, preserves_storage_step_create,
                       preserves_storage_def])
        >> irule EQ_TRANS
        >> qexists `lookup_storage k
                      (lookup_account (FST (HD s.contexts)).msgParams.callee
                         r'.rollback.accounts).storage`
        >> reverse conj_tac >- metis_tac[]
        >> irule handle_step_preserves_storage_same_length
        >> drule same_frame_rel_contexts_ne >> simp[] >> strip_tac
        >> conj_asm1_tac >- (gvs[same_frame_rel_def] >> gvs[outputTo_consistent_def])
        >> reverse conj_tac >- goal_assum drule
        >> fs[same_frame_rel_def])
      >> (* non-call op *)
         `outputTo_consistent r'` by (
           fs[outputTo_consistent_def]
           >> `r'.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
           >> `(FST (HD r'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
                by fs[same_frame_rel_def]
           >> simp[])
         >> `LENGTH s'.contexts = LENGTH r'.contexts` by fs[same_frame_rel_def]
         >> `same_frame_rel r' s'` by metis_tac[handle_step_same_frame]
         >> drule step_inst_preserves_non_accessed_storage >> simp[]
         >> disch_then (qspecl_then [`(FST (HD s.contexts)).msgParams.callee`, `k`] mp_tac)
         >> impl_keep_tac
         >- (`toSet r'.rollback.accesses.storageKeys ⊆
              toSet s'.rollback.accesses.storageKeys`
               by fs[same_frame_rel_def]
             >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
             >> metis_tac[])
         >> strip_tac
         >> pop_assum $ assume_tac o SYM >> gvs[]
         >> irule handle_step_preserves_storage_same_length
         >> drule same_frame_rel_contexts_ne >> simp[] >> strip_tac
         >> reverse conj_tac >- goal_assum drule
         >> imp_res_tac same_frame_rel_contexts_ne)
    >> (* INR from inc_pc_or_jump: use step_inst storage preservation, then
          rollback preservation of inc_pc_or_jump. *)
       Cases_on `is_call op`
       >- ((* is_call op + step_inst INL + inc_pc_or_jump INR: impossible.
              For is_call op, inc_pc_or_jump op = return () which always
              returns (INL (), r). So INR is impossible. *)
           fs[inc_pc_or_jump_def, return_def])
       >> (* non-call op case *)
          `outputTo_consistent r'` by (
            fs[outputTo_consistent_def]
            >> `r'.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
            >> `(FST (HD r'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
                 by fs[same_frame_rel_def]
            >> simp[])
          >> `LENGTH s'.contexts = LENGTH r'.contexts` by fs[same_frame_rel_def]
          >> `same_frame_rel r' s'` by metis_tac[handle_step_same_frame]
          >> `lookup_storage k
                (lookup_account (FST (HD s.contexts)).msgParams.callee
                   r'.rollback.accounts).storage =
              lookup_storage k
                (lookup_account (FST (HD s.contexts)).msgParams.callee
                   s.rollback.accounts).storage` by (
             (* Chain: s → r'' (step_inst) → r' (inc_pc_or_jump).
                inc_pc_or_jump preserves_rollback, so r'.rollback = r''.rollback.
                step_inst_preserves_non_accessed_storage gives storage r'' = storage s
                at non-accessed slots. *)
             qhdtm_x_assum `step_inst` assume_tac
             >> drule step_inst_preserves_non_accessed_storage
             >> simp[]
             >> disch_then (qspecl_then
                 [`(FST (HD s.contexts)).msgParams.callee`, `k`] mp_tac)
             >> `r'.rollback = r''.rollback` by (
                mp_tac preserves_rollback_inc_pc_or_jump
                >> rewrite_tac[preserves_rollback_def]
                >> disch_then drule >> simp[])
             >> fs[]
             >> impl_tac
             >- (`toSet r''.rollback.accesses.storageKeys ⊆
                  toSet s'.rollback.accesses.storageKeys`
                    by (`r''.rollback = r'.rollback` by simp[]
                        >> fs[same_frame_rel_def])
                 >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
             >> strip_tac >> fs[])
          >> pop_assum $ assume_tac o SYM >> gvs[]
          >> irule handle_step_preserves_storage_same_length
          >> simp[]
          >> reverse conj_tac >- goal_assum drule
          >> imp_res_tac same_frame_rel_contexts_ne) >>
  `LENGTH s'.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def] >>
  gvs[Abbr`inner`,bind_def,AllCaseEqs(),get_current_context_def,return_def] >>
  gvs[COND_RATOR,AllCaseEqs()] >- (
    `¬is_call Stop` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] ) >>
  gvs[option_CASE_rator,AllCaseEqs()] >- (
    `¬is_call Invalid` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] ) >>
  qpat_x_assum`_ = (INR _, _)`mp_tac >>
  simp[ignore_bind_def,bind_def] >> TOP_CASE_TAC >>
  reverse $ Cases_on`is_call op` >- (
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] >> strip_tac >>
    CASE_TAC >> rw[] >> gvs[] >>
    mp_tac preserves_same_frame_inc_pc_or_jump >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    rw[same_frame_rel_def] >> gvs[] ) >>
  simp[inc_pc_or_jump_def, return_def] >>
  TOP_CASE_TAC >> rw[] >>
  drule_at Any handle_step_pop_generic_gen >>
  Cases_on`r'.contexts` >> gvs[] >>
  Cases_on`h` >> gvs[] >>
  Cases_on`t` >> gvs[] >- ( Cases_on`s.contexts` >> gvs[] ) >>
  disch_then assume_tac >>
  irule EQ_TRANS >>
  qmatch_goalsub_abbrev_tac`lookup_storage k (lookup_account a _).storage` >>
  qexists_tac`lookup_storage k (lookup_account a r'.rollback.accounts).storage` >>
  reverse conj_tac >- (
    qpat_x_assum`_ ∧ _`kall_tac >>
    mp_tac (INST_TYPE[alpha |-> ``:unit``](GEN_ALL preserves_storage_step_call)) >>
    mp_tac (INST_TYPE[alpha |-> ``:unit``](GEN_ALL preserves_storage_step_create)) >>
    rewrite_tac[preserves_storage_def] >>
    Cases_on`op` >> gvs[is_call_def, step_inst_def] >>
    rpt strip_tac >> first_x_assum drule >> rw[] ) >>
  (* Relate s'.rollback storage to r'.rollback storage after handle_step. *)
  qpat_x_assum `_ ∧ _` strip_assume_tac
  (* Split the handle_step_pop_generic_gen disjunction. *)
  >- ((* Disjunct A: ∀a. storage s'.rollback @ a = storage r'.rollback @ a. *)
      simp[] >> metis_tac[])
  (* Disjunct B: chain through the pushed rollback storage. *)
  >> `(lookup_account a r''.accounts).storage =
      (lookup_account a s.rollback.accounts).storage` by (
       `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
       >> `SND (HD r'.contexts) = r''` by simp[]
       >> Cases_on `op` >> fs[is_call_def, step_inst_def]
       >> metis_tac[step_call_pushed_rb_storage,
                    step_create_pushed_rb_storage])
  >> `lookup_storage k (lookup_account a s.rollback.accounts).storage =
      lookup_storage k (lookup_account a r'.rollback.accounts).storage` by (
       Cases_on `op` >> fs[is_call_def, step_inst_def]
       >> metis_tac[preserves_storage_step_call, preserves_storage_step_create,
                    preserves_storage_def])
  >> `lookup_storage k (lookup_account a s'.rollback.accounts).storage =
      lookup_storage k (lookup_account a r''.accounts).storage` by simp[]
  >> simp[]

QED

(* -------------------------------------------------------------------------
 * Stack room for CALL/CREATE growth.
 * ------------------------------------------------------------------------- *)

Theorem step_call_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_call op s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> `0 < n` by (simp[Abbr`n`] >> Cases_on `call_has_value op` >> simp[])
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `LENGTH (FST (HD sp.contexts)).stack < stack_limit ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              wf_context_def, ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    (* Peel memory_expansion_info *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s2.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s3.contexts)).stack < stack_limit` by gvs[]
    (* Peel expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s4.contexts)).stack < stack_limit` by gvs[]
    (* Peel access/read prefix pieces, following step_call_push_structure. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac >- (CASE_TAC >> simp[] >> irule preserves_head_stack_bind
                         >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s5.contexts)).stack < stack_limit` by gvs[]
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s6.contexts)).stack < stack_limit` by gvs[]
    >> pairarg_tac >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s7.contexts)).stack < stack_limit` by gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s8.contexts)).stack < stack_limit` by gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s9.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s0.contexts)).stack < stack_limit` by gvs[]
    >> gvs[Ntimes COND_RATOR 2]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> Cases_on`bbb` >> gs[]
    >- (
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
    (* Peel set_return_data via ignore_bind *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sa.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sb.contexts)).stack < stack_limit` by gvs[]
    >> gvs[COND_RATOR]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> Cases_on`bbb` >> gs[]
    >- (
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
    >> drule_all proceed_call_push_structure
    >> strip_tac
    >> `TL s'.contexts = sb.contexts` by simp[]
    >> Cases_on`sb.contexts` >> gvs[])
  >> (
    (* If pop_stack failed, the state did not grow. *)
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def,bind_def,assert_def,set_current_context_def,
            return_def,fail_def,AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> `0 < n` by (simp[Abbr`n`] >> Cases_on `two` >> simp[])
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `LENGTH (FST (HD sp.contexts)).stack < stack_limit ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              wf_context_def, ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    (* Peel memory_expansion_info *)
    >> strip_tac
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s2.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas *)
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s3.contexts)).stack < stack_limit` by gvs[]
    (* Peel expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s4.contexts)).stack < stack_limit` by gvs[]
    (* Peel read_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s5.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s6.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_accounts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s7.contexts)).stack < stack_limit` by gvs[]
    (* Peel assert (code length) via ignore_bind *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s8.contexts)).stack < stack_limit` by gvs[]
    (* Peel access_address *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s9.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_gas_left *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s0.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas (cappedGas) *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sa.contexts)).stack < stack_limit` by gvs[]
    (* Peel assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sb.contexts)).stack < stack_limit` by gvs[]
    (* Peel set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sc.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sd.contexts)).stack < stack_limit` by gvs[]
    (* Peel ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD se.contexts)).stack < stack_limit` by gvs[]
    >> gvs[Ntimes COND_RATOR 2]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> drule_all proceed_create_push_structure
    >> strip_tac
    >> `FST (HD (TL s'.contexts)) = FST (HD se.contexts)` by (
         Cases_on`s'.contexts` >> gvs[] >> Cases_on`t` >> gvs[] >>
         Cases_on`se.contexts` >> gvs[] )
    >> gvs[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_call_grow_parent_gas_monotone:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s2.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s3.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s4.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac >- (CASE_TAC >> simp[] >> irule preserves_head_gas_mono_bind >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s5.contexts)).gasUsed` by decide_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> pairarg_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s6.contexts)).gasUsed` by decide_tac
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s7.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s8.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s9.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s0.contexts)).gasUsed` by decide_tac
    >> gvs[Ntimes COND_RATOR 2]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sa.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sb.contexts)).gasUsed` by decide_tac
    >> gvs[COND_RATOR]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_all proceed_call_push_structure
    >> strip_tac
    >> `TL s'.contexts = sb.contexts` by simp[]
    >> Cases_on`sb.contexts` >> gvs[EL_CONS]
    >> Cases_on`s.contexts` >> gvs[]
    >> Cases_on`s'.contexts` >> gvs[] )
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_gas_monotone:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    (* memory_expansion_info *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s2.contexts)).gasUsed` by decide_tac
    (* consume_gas *)
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s3.contexts)).gasUsed` by decide_tac
    (* expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s4.contexts)).gasUsed` by decide_tac
    (* read_memory *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s5.contexts)).gasUsed` by decide_tac
    (* get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s6.contexts)).gasUsed` by decide_tac
    (* get_accounts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s7.contexts)).gasUsed` by decide_tac
    (* assert code length *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s8.contexts)).gasUsed` by decide_tac
    (* access_address *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s9.contexts)).gasUsed` by decide_tac
    (* get_gas_left *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s0.contexts)).gasUsed` by decide_tac
    (* consume_gas cappedGas *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sa.contexts)).gasUsed` by decide_tac
    (* assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sb.contexts)).gasUsed` by decide_tac
    (* set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sc.contexts)).gasUsed` by decide_tac
    (* get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sd.contexts)).gasUsed` by decide_tac
    (* ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD se.contexts)).gasUsed` by decide_tac
    >> gvs[Ntimes COND_RATOR 2]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> drule_all proceed_create_push_structure
    >> strip_tac
    >> `FST (EL 1 s'.contexts) = FST (HD se.contexts)` by (
         Cases_on`s'.contexts` >> gvs[EL_CONS] >> Cases_on`t` >> gvs[EL_CONS] >>
         Cases_on`se.contexts` >> gvs[] )
    >> gvs[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem call_gas_stipend_le_consumed:
  (if 0 < value then call_stipend else 0) ≤ otherCost + memoryCost ∧
  call_gas value gas gasLeft memoryCost otherCost = (dynamicGas, stipend) ⇒
  stipend ≤ dynamicGas + memoryCost
Proof
  rw[call_gas_def]
QED

Theorem proceed_call_parent_gas_ok:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r, s') ∧
  s.contexts ≠ [] ∧
  oldGas + stipend ≤ (FST (HD s.contexts)).gasUsed ⇒
    oldGas +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `ignore_bind g`
  >> simp[ignore_bind_def, Once bind_def]
  >> TOP_CASE_TAC
  >> qmatch_asmsub_rename_tac `g s = (q, s1)`
  >> `s1.contexts = s.contexts`
      by (simp[Abbr`g`] >> gvs[COND_RATOR, AllCaseEqs(),
                                 update_accounts_def, return_def])
  >> `ISL q`
      by (gvs[Abbr`g`, AllCaseEqs(), COND_RATOR, return_def,
              update_accounts_def])
  >> TOP_CASE_TAC >> gvs[]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
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
  >> reverse IF_CASES_TAC
  >- (
    rw[return_def]
    >> gvs[Abbr`ctx`, initial_context_def, initial_msg_params_def])
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac `dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> simp[same_frame_rel_def]
  >> strip_tac
  >> gvs[Abbr`ctx`, Abbr`ss`, initial_context_def, initial_msg_params_def]
  >> Cases_on`s'.contexts` >> gvs[]
QED

Theorem proceed_create_parent_gas_ok:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧
  oldGas + cappedGas ≤ (FST (HD s.contexts)).gasUsed ⇒
    oldGas +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
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
  >> drule push_context_effect >> strip_tac
  >> gvs[initial_context_def, initial_msg_params_def]
  >> qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[]
  >> gvs[set_last_accounts_def,update_account_def]
  >> Cases_on`l` >> gvs[]
QED

Theorem step_call_grow_parent_gas_ok:
  wf_state s ∧ step_call op s = (r, s') ∧
  is_call op ∧ (op ≠ Create ∧ op ≠ Create2) ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed = (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> simp[] >> strip_tac
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac
    >- (CASE_TAC >> simp[] >> irule preserves_head_gas_mono_bind >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> pairarg_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> qpat_x_assum`_ _ = (_,stipend)`(markerLib.ASSUME_NAMED_TAC"cg")
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac `consume_gas callCost s6 = _`
    >> `((FST (HD s.contexts)).gasUsed + callCost ≤
          (FST (HD s7.contexts)).gasUsed)` by (
       qhdtm_x_assum`consume_gas`mp_tac >>
       simp[consume_gas_def, bind_def,get_current_context_def,return_def] >>
       simp[assert_def,ignore_bind_def,bind_def,CaseEq"bool",CaseEq"sum"] >>
       simp[set_current_context_def,return_def] >> strip_tac >>
       gvs[] )
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[Ntimes COND_RATOR 2]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[COND_RATOR]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule proceed_call_parent_gas_ok
    >> disch_then irule
    >> simp[]
    >> qmatch_goalsub_abbrev_tac`stipend + spg <= sbg`
    >> qpat_x_assum`_ + spg <= _`mp_tac
    >> qmatch_goalsub_abbrev_tac`_ <= s7g`
    >> `s7g <= sbg` by simp[]
    >> `stipend <= callCost` suffices_by simp[]
    >> qunabbrev_tac`callCost`
    >> qmatch_asmsub_abbrev_tac`call_gas value gas gasLeft memoryCost`
    >> `static_gas op = 0` by (
      qhdtm_x_assum`is_call`mp_tac >>
      Cases_on`op` >> EVAL_TAC >> gs[] )
    >> irule call_gas_stipend_le_consumed
    >> markerLib.LABEL_ASSUM"cg"assume_tac
    >> gvs[]
    >> goal_assum $ drule_at Any
    >> Cases_on`0 < value` >> simp[]
    >> EVAL_TAC >> rw[] )
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_gas_ok:
  wf_state s ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    (* Same peel as gas monotonicity, with additive cappedGas reservation. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* assert code length *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* access_address *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* get_gas_left *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* consume_gas cappedGas: this is the key additive-reservation point. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> qmatch_asmsub_abbrev_tac `consume_gas cappedGas s2 = _`
    >> `((FST (HD s2.contexts)).gasUsed + cappedGas ≤
          (FST (HD s3.contexts)).gasUsed)` by (
        irule consume_gas_head_gas_add_ge >> gvs[] )
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[Ntimes COND_RATOR 2]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ = (_, _)`
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> irule proceed_create_parent_gas_ok
    >> goal_assum $ drule_at Any
    >> simp[]
    >> irule LESS_EQ_TRANS >> goal_assum $ drule_at Any
    >> irule LESS_EQ_TRANS >> goal_assum $ drule_at Any
    >> irule LESS_EQ_TRANS >> goal_assum $ drule_at Any
    >> irule LESS_EQ_TRANS >> goal_assum $ drule_at Any
    >> drule consume_gas_head_gas_add_ge
    >> simp[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

(* Named facts about the pre-handler inner step. *)

(* Full-step push structure: storage/access shape plus parent stack/gas facts. *)
Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧ wf_state s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    (* Storage preservation for s'.rollback *)
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage) ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    (* saved rollback storage; CREATE's old-LAST exception is excluded *)
    (∀i. i < LENGTH s.contexts ⇒
         (∀a. (lookup_account a (SND (EL i s'.contexts)).accounts).storage =
              (lookup_account a (if i = 0 then s.rollback
                                 else SND (EL (i-1) s.contexts)).accounts).storage)) ∧
    (∀i. i < LENGTH s'.contexts ⇒
         toSet (if i = 0 then s.rollback
                else SND (EL (i-1) s.contexts)).accesses.storageKeys ⊆
           toSet (SND (EL i s'.contexts)).accesses.storageKeys) ∧
    (* saved parent / shifted tail *)
    MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
    LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit ∧
    (FST (EL 1 s'.contexts)).gasUsed ≥ (FST (HD s.contexts)).gasUsed ∧
    (FST (HD s.contexts)).gasUsed +
      ((FST (HD s'.contexts)).msgParams.gasLimit -
       (FST (HD s'.contexts)).gasUsed) ≤
      (FST (EL 1 s'.contexts)).gasUsed ∧
    (* parent msgParams *)
    (LENGTH s.contexts ≥ 1 ⇒
       (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams) ∧
    (* new child outputTo consistency *)
    outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
    (* shifted outputTo consistency *)
    (∀i. i < LENGTH s.contexts ⇒
         outputTo_consistent_ctx (FST (EL i s.contexts)) ⇒
         outputTo_consistent_ctx (FST (EL (i+1) s'.contexts)))
Proof
  rpt gen_tac >> strip_tac
  (* Unfold step = handle inner handle_step *)
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  (* Case: inner returned INL - step returns inner's result *)
  >- (
    simp[] >> strip_tac >> gvs[]
    (* inner = get_ctx; step_inst; inc_pc_or_jump *)
    >> gvs[Abbr`inner`, bind_def,AllCaseEqs()]
    >> gvs[get_current_context_def, return_def, fail_def, bind_def]
    >> gvs[COND_RATOR, CaseEq"bool"]
    (* Case: code ≤ pc, step_inst Stop *)
    >- (
      `preserves_same_frame (step_inst Stop)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* Case: FLOOKUP *)
    >> gvs[option_CASE_rator,CaseEq"option"]
    (* NONE: step_inst Invalid *)
    >- (
      `preserves_same_frame (step_inst Invalid)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op *)
    >> gvs[ignore_bind_def, bind_def]
    >> gvs[AllCaseEqs()]
    >> rename1 `step_inst op s0 = (INL (), s1)`
    >> drule_at Any psf_imp_length_contexts_preserved
    >> simp[]
    >> impl_keep_tac >- (strip_tac >>
         gvs[inc_pc_or_jump_def,COND_RATOR,AllCaseEqs(),return_def] >>
         gvs[bind_def,get_current_context_def,fail_def,AllCaseEqs()] )
    >> strip_tac
    >> `LENGTH s1.contexts > LENGTH s0.contexts` by simp[]
    (* By step_inst_inl_grew_is_call, is_call op *)
    >> `is_call op` by metis_tac[step_inst_inl_grew_is_call]
    (* For is_call, inc_pc_or_jump = return (), so s' = s1 *)
    >> `r' = s1` by (
         gvs[inc_pc_or_jump_def, return_def, COND_RATOR, CaseEq"bool"])
    >> gvs[]
    >> `outputTo_consistent s0` by (
         gvs[outputTo_consistent_def, outputTo_consistent_stack_def]
         >> Cases_on`s0.contexts`
         >> gvs[outputTo_consistent_ctx_def])
    (* Case split on which call/create op *)
    >> Cases_on `∃two. step_inst op s0 = step_create two s0`
    >- (
      (* CREATE/CREATE2 case *)
      gvs[] >> pop_assum(assume_tac o SYM) >>
      (* Use step_create lemmas *)
      drule_then drule step_create_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* s1.rollback storage preserved *)
      >> `preserves_storage (step_create two)` by simp[preserves_storage_step_create]
      >> gvs[preserves_storage_def]
      >> pop_assum drule >> strip_tac
      >> gvs[lookup_storage_def, FUN_EQ_THM]
      (* Use step_create_push_structure *)
      >> drule step_create_push_structure
      >> simp[]
      >> strip_tac
      >> drule_then drule step_create_pushed_rb_storage
      >> simp[] >> strip_tac
      >> conj_tac
      >- ( Cases >> simp[] >> Cases_on`r'.contexts` >> gvs[] )
      >> conj_tac >- ( Cases >> gvs[] >> Cases_on`r'.contexts` >> gvs[] )
      >> drule_at Any step_create_grow_parent_stack_room
      >> impl_tac >- ( gvs[wf_state_def] >> Cases_on`s0.contexts` >> gvs[] )
      >> strip_tac
      >> conj_tac >- (
        qmatch_goalsub_rename_tac`EL 1 rr.contexts` >>
        Cases_on`rr.contexts` >> gvs[] )
      >> Cases_on`s0.contexts` >> gvs[]
      >> Cases_on`r'.contexts` >> gvs[]
      >> Cases_on`t'` >> gvs[]
      >> drule step_create_grow_parent_gas_monotone
      >> simp[] >> strip_tac
      >> drule_at(Pat`step_create`) step_create_grow_parent_gas_ok
      >> simp[] >> strip_tac
      >> Cases >> gvs[EL_CONS]
      >- ( simp[outputTo_consistent_ctx_def] )
      >> gvs[PRE_SUB1,ADD1]
      >> simp[outputTo_consistent_ctx_def]
      >> gvs[LIST_EQ_REWRITE,EL_MAP])
    >> (
      (* CALL family case *)
      `step_inst op s0 = step_call op s0`
      by (Cases_on`op` >> gvs[step_inst_def, is_call_def])
      (* Use step_call lemmas *)
      >> gvs[]
      >> drule_then drule step_call_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* s1.rollback storage preserved *)
      >> drule(REWRITE_RULE[preserves_storage_def]preserves_storage_step_call)
      >> simp[lookup_storage_def, FUN_EQ_THM]
      >> strip_tac
      >> drule_all step_call_pushed_rb_storage
      >> strip_tac
      (* Use step_call_push_structure *)
      >> drule_all step_call_push_structure
      >> strip_tac
      >> simp[]
      >> conj_tac
      >- (
        Cases >> gvs[ADD1] >>
        Cases_on`r'.contexts` >> gvs[EL_CONS,PRE_SUB1] >>
        Cases_on`s0.contexts` >> gvs[ADD1] >>
        Cases_on`t` >> gvs[ADD1] >>
        Cases_on`n` >> gvs[ADD1] )
      >> drule_at(Pat`step_call`)step_call_grow_parent_stack_room
      >> impl_tac >- ( gvs[wf_state_def] >> Cases_on`s0.contexts` >- gvs[] >>
                       simp[] >> fs[])
      >> strip_tac
      >> Cases_on`r'.contexts` >> gvs[EL_CONS, PRE_SUB1]
      >> Cases_on`t` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> Cases_on`s0.contexts` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> drule step_call_grow_parent_gas_monotone
      >> simp[] >> strip_tac
      >> drule_at(Pat`step_call`)step_call_grow_parent_gas_ok
      >> simp[]
      >> impl_tac >- (rpt strip_tac >> gs[step_inst_def])
      >> strip_tac >> gvs[]
      >> conj_tac >> Cases >> gvs[ADD1]
      >- ( Cases_on`n` >> gvs[] )
      >> gvs[outputTo_consistent_ctx_def]))
  (* Case: inner returned INR - handle_step runs *)
  >> simp[]
  >> rename1 `handle_step e r' = (_, s')`
  (* inner is same_frame_or_grow *)
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts` by (
       drule_all same_frame_or_grow_length >> simp[])
  >> strip_tac
  >> `r'.contexts ≠ []` by (strip_tac >> gvs[] >> Cases_on`s.contexts` >> gvs[])
  (* Inner INR-grow cannot lead to full-step growth: non-abort handlers pop;
     aborts reraise and preserve the inner length. *)
  >> `LENGTH s'.contexts ≤ LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts` >- (
       drule handle_step_shrinks_by_one >> simp[])
  (* inner grew *)
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
       metis_tac[outputTo_consistent_stack_imp_consistent]
  >> `¬vfm_abort e` by (
       irule step_inner_inr_grow_not_abort
       >> qexistsl_tac [`s`, `r'`] >> simp[Abbr`inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on`s.contexts` >> gvs[])
  >> `LENGTH r'.contexts ≥ 2` by simp[]
  (* Inner grew by exactly 1 *)
  >> `LENGTH r'.contexts = LENGTH s.contexts + 1` by (
       qunabbrev_tac`inner` >>
       drule_then drule step_inner_grows_by_exactly_one >> gvs[])
  (* Need EVERY (wf_context o FST) r'.contexts to apply handle_step_not_abort_pops *)
  >> drule_at(Pat`handle_step`) handle_step_not_abort_pops
  >> gvs[]
  >> `decreases_gas_cred T 0 0 inner` suffices_by (
    gvs[decreases_gas_cred_def] >>
    disch_then(qspec_then`s`mp_tac) >> rw[] >>
    gvs[wf_state_def] >>
    gvs[EVERY_MEM] ) >>
  simp[Abbr`inner`] >>
  irule decreases_gas_cred_bind_mono >>
  qexistsl_tac[`T`,`F`] >> simp[] >> gen_tac >>
  rw[] >> CASE_TAC >> rw[] >>
  irule decreases_gas_cred_ignore_bind_mono >> rw[] >>
  qexistsl_tac[`F`,`T`] >> simp[]
QED

(* Reusable pre-handler push structure for step_inner. *)

Theorem step_inner_push_structure:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
    LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit ∧
    (FST (EL 1 s'.contexts)).gasUsed ≥
      (FST (HD s.contexts)).gasUsed ∧
    (FST (HD s.contexts)).gasUsed +
      ((FST (HD s'.contexts)).msgParams.gasLimit -
       (FST (HD s'.contexts)).gasUsed) ≤
      (FST (EL 1 s'.contexts)).gasUsed ∧
    (FST (EL 1 s'.contexts)).msgParams =
      (FST (HD s.contexts)).msgParams
Proof
  strip_tac
  >> Cases_on `r`
  >- (
    `step s = (INL x, s')` by simp[step_eq_handle_step_inner, handle_def]
    >> drule step_push_structure
    >> gvs[wf_state_def]
    >> strip_tac
    >> Cases_on`s.contexts` >> gvs[] )
  (* Inner INR-growth can only be CALL-family. *)
  >> gvs[step_inner_def, bind_def, get_current_context_def, COND_RATOR,
         fail_def,return_def,CaseEq"bool",CaseEq"prod",
         option_CASE_rator,CaseEq"option",ignore_bind_def]
  >> TRY (drule step_inst_inr_grew_is_call_family >> simp[] >> NO_TAC)
  >> mp_tac step_inst_preserves_nonempty_contexts
  >> impl_keep_tac >- (strip_tac >> gvs[wf_state_def])
  >> simp[Excl"step_inst_preserves_nonempty_contexts"] >> strip_tac
  >> gvs[CaseEq"sum",CaseEq"prod"]
  >- (
    drule step_inst_inl_grew_is_call >> simp[] >>
    mp_tac preserves_same_frame_inc_pc_or_jump >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    ntac 2 strip_tac >> gvs[same_frame_rel_def] >>
    gvs[inc_pc_or_jump_def,return_def] )
  >> drule step_inst_inr_grew_is_call_family
  >> simp[] >> disch_then(markerLib.ASSUME_NAMED_TAC"call")
  >> `step_inst op s = step_call op s`
       by (markerLib.LABEL_ASSUM"call"strip_assume_tac >> gvs[step_inst_def])
  >> gvs[]
  >> drule_then drule step_call_grows_by_exactly_one
  >> simp[] >> strip_tac
  >> drule_all step_call_push_structure
  >> strip_tac
  >> drule_at(Pat`step_call`) step_call_grow_parent_stack_room
  >> Cases_on`s.contexts` >> fs[]
  >> impl_keep_tac >- (gvs[wf_state_def])
  >> strip_tac
  >> drule step_call_grow_parent_gas_monotone
  >> simp[] >> strip_tac
  >> drule_at(Pat`step_call`) step_call_grow_parent_gas_ok
  >> simp[]
  >> impl_tac >- (markerLib.LABEL_ASSUM"call"strip_assume_tac >> simp[is_call_def])
  >> strip_tac
  >> Cases_on `s'.contexts` >> gvs[]
QED

(* Full-step pop structure.  Rollback equality is weakened to storage equality
 * plus the matching accesses subset, because handle_create may change code. *)
Theorem step_inst_same_frame_gas_monotone:
   step_inst op s = (q, s') ∧
   same_frame_rel s s' ∧
   EVERY (wf_context o FST) s.contexts
   ⇒
     (FST (HD s.contexts)).gasUsed ≤
     (FST (HD s'.contexts)).gasUsed
Proof
  strip_tac
  >> qspec_then`op`mp_tac(GEN_ALL decreases_gas_cred_step_inst)
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then`s`mp_tac)
  >> simp[]
  >> gvs[same_frame_rel_def]
  >> Cases_on`s.contexts` >> gvs[]
  >> Cases_on`s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def]
  >> gvs[unused_gas_def]
  >> gvs[LEX_DEF]
  >> strip_tac
  >> gvs[wf_context_def]
  >> pop_assum mp_tac >> rw[]
QED

Theorem step_pop_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    EVERY (wf_context o FST) s.contexts ∧
    LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_head parent rest.
      s.contexts = HD s.contexts :: parent :: rest ∧
      s'.contexts = (new_head, SND parent) :: rest ∧
      new_head.msgParams = (FST parent).msgParams ∧
      new_head.gasUsed ≥
        (FST parent).gasUsed -
        ((FST (HD s.contexts)).msgParams.gasLimit -
         (FST (HD s.contexts)).gasUsed) ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet (SND (HD s.contexts)).accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a (SND (HD s.contexts)).accounts).storage)))
Proof
  rpt strip_tac
  >> qpat_x_assum `step s = (r,s')` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q` >> gvs[Abbr `inner`]
  >- (rpt strip_tac >> assume_tac same_frame_or_grow_step_inner
      >> drule_all same_frame_or_grow_length >> fs[])
  >> rpt strip_tac
  >> ASSUME_TAC same_frame_or_grow_step_inner
  >> `LENGTH r'.contexts >= LENGTH s.contexts`
       by (drule_all same_frame_or_grow_length >> fs[])
  >> `r'.contexts <> []` by (Cases_on `r'.contexts` >> fs[])
  >> `LENGTH s'.contexts + 1 >= LENGTH r'.contexts /\
      LENGTH s'.contexts <= LENGTH r'.contexts`
       by (drule handle_step_shrinks_by_one >> fs[])
  >> `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac
  >> `same_frame_rel s r'` by (drule_all same_frame_or_grow_eq_length >> fs[])
  >> `LENGTH s.contexts >= 2` by (
       CCONTR_TAC >> fs[]
       >> `LENGTH s.contexts <= 1` by decide_tac
       >> `LENGTH s.contexts = 1` by decide_tac
       >> drule handle_step_preserves_length_1 >> fs[])
  >> `s.contexts = HD s.contexts :: TL s.contexts`
       by (Cases_on `s.contexts` >> fs[])
  >> `LENGTH (TL s.contexts) >= 1`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `?parent rest. TL s.contexts = parent :: rest`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `r'.contexts <> []` by fs[same_frame_rel_def]
  >> `TL r'.contexts = TL s.contexts /\ SND (HD r'.contexts) = SND (HD s.contexts)`
       by fs[same_frame_rel_def]
  >> `r'.contexts = (FST (HD r'.contexts), SND (HD s.contexts)) :: parent :: rest`
       by (Cases_on `r'.contexts` >> fs[] >> Cases_on `h` >> fs[])
  >> `LENGTH s'.contexts < LENGTH r'.contexts` by decide_tac
  (* Use paired lemma. Split its disjunction into two separate subgoals
     via strip_assume_tac, avoiding gvs contamination.
     DISJ1(r'): storage s'.rollback = storage r'.rollback
     DISJ2(r'): storage s'.rollback = storage (SND (HD r'.contexts)) *)
  >> Cases_on`y`
  >- (
    gvs[bind_def,get_current_context_def,return_def,fail_def]
    >> Cases_on`∃op. step_inst op s = (INR NONE, r')`
    >- (
      gvs[] >>
      drule_all step_inst_inr_preserves_storage >> rw[] >>
      drule_at_then(Pat`handle_step`)drule
        handle_step_pop_generic_gen_paired >>
      simp[] >>
      Cases_on`s.contexts` >> gvs[] >>
      drule step_inst_same_frame_gas_monotone >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on`r'.contexts` >> gvs[wf_context_def] >>
      Cases_on`s'.contexts` >> gvs[] >>
      disch_then (qx_choosel_then [`new_head`] strip_assume_tac) >>
      gvs[lookup_storage_def, FUN_EQ_THM] >>
      gvs[SUBSET_DEF,same_frame_rel_def] )
    >> gvs[COND_RATOR,AllCaseEqs()]
    >> gvs[option_CASE_rator, AllCaseEqs()]
    >> gvs[ignore_bind_def,bind_def,AllCaseEqs()]
    >> drule inc_pc_or_jump_inr_eq >> rw[] )
  >> gvs[handle_step_def]
  >> gvs[COND_RATOR,CaseEq"bool",reraise_def]
  >> gvs[handle_def,CaseEq"prod"]
  >> gvs[handle_create_reraises_when_some]
  >> gvs[reraise_def]
  >> gvs[bind_def, get_current_context_def, return_def]
  >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD r'.contexts)).gasUsed`
  by (
    gvs[COND_RATOR,CaseEq"bool"]
    >- metis_tac[step_inst_same_frame_gas_monotone] >>
    gvs[CaseEq"option",option_CASE_rator,ignore_bind_def]
    >- metis_tac[step_inst_same_frame_gas_monotone] >>
    reverse(gvs[bind_def,AllCaseEqs()])
    >- metis_tac[step_inst_same_frame_gas_monotone] >>
    drule inc_pc_or_jump_inr_eq >> simp[] >> strip_tac >> gvs[] >>
    qspec_then`step_inst op`(drule_at(Pat`_ = (_,_)`))
      same_frame_or_grow_eq_length >>
    simp[] >>
    mp_tac(UNDISCH step_inst_preserves_nonempty_contexts) >>
    qhdtm_assum`step_inst`SUBST1_TAC >> simp[] >> strip_tac >>
    impl_keep_tac >- (
      mp_tac preserves_same_frame_inc_pc_or_jump >>
      rewrite_tac[preserves_same_frame_def] >>
      disch_then drule >> gvs[] >>
      strip_tac >> gvs[same_frame_rel_def] ) >>
    strip_tac >>
    drule step_inst_same_frame_gas_monotone >>
    simp[] >> strip_tac >>
    mp_tac decreases_gas_inc_pc_or_jump >>
    rewrite_tac[decreases_gas_def] >>
    disch_then(qspec_then`s''`mp_tac) >>
    strip_tac >> Cases_on`s''.contexts` >> fs[] >>
    Cases_on`h` >> fs[] >> gvs[] )
  >> reverse(Cases_on`x = Reverted`)
  >- (
    drule_at(Pat`handle_exception`)handle_exception_pop_failure_rollback_gen >>
    simp[] >> Cases_on`r'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> strip_tac >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen >>
    simp[] >> strip_tac >> gvs[]
  )
  >> drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen
  >> simp[]
  >> Cases_on`r'.contexts` >> gvs[]
  >> Cases_on`h` >> gvs[]
  >> rpt strip_tac >> gvs[]
  >- (
    qexists_tac`parent` >> gvs[] >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    disj1_tac >> qx_gen_tac`a` >>
    qmatch_asmsub_abbrev_tac`callee_local_changes callee` >>
    reverse(Cases_on`a = callee`) >- (
      gvs[callee_local_changes_def] ) >>
    gvs[bind_def,get_current_context_def,return_def,AllCaseEqs()] >>
    Cases_on`∃op. step_inst op s = (INR (SOME Reverted),r')`
    >- (
      gvs[] >>
      drule step_inst_inr_preserves_storage >>
      simp[lookup_storage_def, FUN_EQ_THM] ) >>
    gvs[COND_RATOR,AllCaseEqs()] >>
    gvs[option_CASE_rator,AllCaseEqs()] >>
    gvs[ignore_bind_def,bind_def,AllCaseEqs()] >>
    drule inc_pc_or_jump_inr_eq >> rw[]) >>
  Cases_on`s.contexts` >> fs[] >>
  gvs[wf_context_def] >>  gvs[same_frame_rel_def]
QED

(* -------------------------------------------------------------------------
 * Full wf_state preservation. Placed here because the strong wf_state
 * invariants use whole-step push/pop structure proved above.
 * ------------------------------------------------------------------------- *)

Theorem step_push_parent_stack_room:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts
  ⇒ LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit
Proof
  rpt strip_tac
  >> drule step_push_structure
  >> gvs[]
  >> impl_tac >- gvs[wf_state_def]
  >> strip_tac
  >> simp[]
QED

Theorem step_preserves_stack_room_ok:
  wf_state s ⇒ stack_room_ok (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1 `step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
      by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel s s'` by metis_tac[step_same_frame] >>
    metis_tac[same_frame_rel_preserves_stack_room_ok, wf_state_def])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    `LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit`
      by metis_tac[step_push_parent_stack_room] >>
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >>
    gvs[stack_room_ok_def, wf_state_def] >>
    Cases_on `s'.contexts` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    rw[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    gvs[])
  >> (
    `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
    `outputTo_consistent_stack s` by gvs[wf_state_def] >>
    drule step_pop_structure >> simp[] >>
    impl_tac >- (rpt strip_tac >> gvs[wf_state_def]) >>
    strip_tac >>
    gvs[stack_room_ok_def, wf_state_def] >>
    Cases_on`s.contexts` >> gvs[]
  )
QED

Theorem same_frame_rel_preserves_outputTo_consistent_stack:
  same_frame_rel s s' ∧ outputTo_consistent_stack s ⇒
  outputTo_consistent_stack s'
Proof
  rw[outputTo_consistent_stack_def, same_frame_rel_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[outputTo_consistent_ctx_def]
QED

Theorem step_preserves_outputTo_consistent_stack:
  wf_state s ⇒ outputTo_consistent_stack (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1 `step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
    by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel s s'` by metis_tac[step_same_frame] >>
    irule same_frame_rel_preserves_outputTo_consistent_stack >>
    simp[] >> gvs[wf_state_def] >> metis_tac[])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >>
    gvs[outputTo_consistent_stack_def, EVERY_MEM, MEM_EL] >>
    conj_tac >- (strip_tac >> gvs[]) >>
    rw[] >>
    Cases_on `n` >> gvs[] >- (
      Cases_on`s'.contexts` >> gvs[] ) >>
    simp[ADD1, EL_MAP] >> gvs[ADD1] >>
    first_x_assum irule >>
    gvs[wf_state_def,outputTo_consistent_stack_def] >>
    gvs[EVERY_EL, EL_MAP] ) >>
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  `outputTo_consistent_stack s` by gvs[wf_state_def] >>
  gvs[wf_state_def] >>
  drule_all step_pop_structure >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on`s'.contexts` >> gvs[] >>
  strip_tac >> gvs[outputTo_consistent_stack_def] >>
  gvs[outputTo_consistent_ctx_def]
QED

Theorem step_push_parent_gas_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  rpt strip_tac
  >> drule step_push_structure
  >> simp[]
  >> impl_tac >- gvs[wf_state_def]
  >> strip_tac >> simp[]
QED

Theorem step_inner_same_frame_gas_monotone:
  step_inner s = (r, s') ∧ same_frame_rel s s' ∧
  EVERY (wf_context o FST) s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤
    (FST (HD s'.contexts)).gasUsed
Proof
  rpt strip_tac
  >> mp_tac decreases_gas_cred_step_inner
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then `s` mp_tac)
  >> IF_CASES_TAC >> gvs[same_frame_rel_def]
  >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def, unused_gas_def, LEX_DEF, wf_context_def]
  >> ntac 3 (pop_assum mp_tac) >> rw[]
QED

Theorem inner_push_preserves_stack_room_ok:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    stack_room_ok s'
Proof
  rpt strip_tac
  >> drule step_inner_push_structure
  >> simp[] >> strip_tac
  >> gvs[stack_room_ok_def, wf_state_def]
  >> Cases_on `s'.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> rw[EVERY_MEM, MEM_MAP, PULL_EXISTS]
  >> gvs[]
QED

Theorem inner_push_preserves_gas_stack_ok:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    gas_stack_ok s'
Proof
  rpt strip_tac
  >> `gas_stack_ok s` by gvs[wf_state_def]
  >> drule step_inner_push_structure >> simp[] >> strip_tac
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[gas_stack_ok_def]
  >> Cases_on `i` >> gvs[unused_gas_def] >> gvs[ADD1]
  >> Cases_on `s.contexts` >> gvs[] >> Cases_on `t` >> gvs[]
  >> gvs[LIST_EQ_REWRITE, EL_MAP] >> strip_tac
  >> simp[EL_CONS, PRE_SUB1]
  >> gvs[ADD1, MAP_TAKE, MAP_MAP_o, o_DEF]
  >> last_x_assum(qspec_then `n` mp_tac) >> simp[EL_CONS, PRE_SUB1]
  >> qmatch_goalsub_abbrev_tac `_ (_ + stl) ⇒ (_ ≥ (_ + (_ + stl1)))`
  >> `stl1 = stl` by (
       unabbrev_all_tac >> AP_TERM_TAC
       >> simp[LIST_EQ_REWRITE, EL_TAKE, EL_MAP])
  >> gvs[GREATER_EQ]
  >> mp_tac decreases_gas_cred_step_inner
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then `s` mp_tac) >> simp[]
  >> IF_CASES_TAC >> gvs[wf_state_def]
  >> strip_tac
  >> Cases_on `s'.contexts` >> gvs[]
  >> Cases_on `s.contexts` >> gvs[]
  >> gvs[wf_context_def]
  >> first_assum(qspec_then `0` mp_tac)
  >> impl_tac >- simp[] >> simp_tac(srw_ss())[EL_CONS]
  >> strip_tac >> gvs[]
  >> qpat_x_assum `$! _` mp_tac
  >> first_assum(qspec_then `0` mp_tac)
  >> simp_tac (srw_ss()++ARITH_ss) []
  >> rpt strip_tac >> gvs[]
  >> Cases_on `t` >> gvs[wf_context_def]
  >> first_assum(qspec_then `1` mp_tac)
  >> impl_tac >- simp[] >> simp_tac(srw_ss())[EL_CONS]
  >> strip_tac >> gvs[]
  >> qpat_x_assum `$! _` mp_tac
  >> first_assum(qspec_then `1` mp_tac)
  >> simp_tac (srw_ss()++ARITH_ss) []
  >> rpt strip_tac >> gvs[]
QED

Theorem step_inner_preserves_stack_room_gas_ok:
  wf_state s ∧ step_inner s = (r, s') ⇒
    stack_room_ok s' ∧ gas_stack_ok s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >> `LENGTH s'.contexts ≥ LENGTH s.contexts` by (
       mp_tac same_frame_or_grow_step_inner_named
       >> metis_tac[same_frame_or_grow_length])
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `same_frame_rel s s'` by (
       mp_tac same_frame_or_grow_step_inner_named
       >> metis_tac[same_frame_or_grow_eq_length])
    >> conj_tac
    >- metis_tac[same_frame_rel_preserves_stack_room_ok, wf_state_def]
    >> irule same_frame_rel_preserves_gas_stack_ok
    >> goal_assum $ drule_at Any
    >> gvs[wf_state_def]
    >> simp[GREATER_EQ]
    >> irule step_inner_same_frame_gas_monotone
    >> simp[])
  >> `LENGTH s'.contexts > LENGTH s.contexts` by decide_tac
  >> metis_tac[inner_push_preserves_stack_room_ok
              ,inner_push_preserves_gas_stack_ok]
QED

Theorem step_pop_preserves_gas_stack_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  gas_stack_ok s'
Proof
  rpt strip_tac
  >> drule step_pop_structure
  >> impl_tac >- gvs[wf_state_def]
  >> disch_then $ qx_choosel_then [`new_head`, `parent`, `rest`] assume_tac
  >> gvs[gas_stack_ok_def, wf_state_def]
  >> rw[]
  >> Cases_on `i` >> gvs[]
  >> TRY (
    first_x_assum (qspec_then `SUC 0` mp_tac)
    >> Cases_on `s.contexts` >> gvs[]
    >> gvs[wf_context_def, unused_gas_def] >> NO_TAC)
  >> first_x_assum (qspec_then `SUC (SUC n)` mp_tac)
  >> Cases_on `s.contexts` >> gvs[unused_gas_def]
QED

Theorem step_preserves_gas_stack_ok:
  wf_state s ⇒ gas_stack_ok (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1` step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
    by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel s s'` by metis_tac[step_same_frame] >>
    `s.contexts ≠ []` by gvs[wf_state_def] >>
    `EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
    `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed` by (
       irule step_same_frame_gas_monotone >> simp[]) >>
    irule same_frame_rel_preserves_gas_stack_ok >>
    goal_assum $ drule_at Any >> gvs[wf_state_def])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    `gas_stack_ok s` by gvs[wf_state_def] >>
    `(FST (HD s.contexts)).gasUsed +
      ((FST (HD s'.contexts)).msgParams.gasLimit -
       (FST (HD s'.contexts)).gasUsed) ≤
      (FST (EL 1 s'.contexts)).gasUsed` by metis_tac[step_push_parent_gas_ok] >>
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >> Cases_on`s'.contexts` >> gvs[] >>
    gvs[gas_stack_ok_def] >>
    Cases_on `i` >> gvs[unused_gas_def] >> gvs[ADD1] >>
    Cases_on`s.contexts` >> gvs[] >> Cases_on`t` >> gvs[] >>
    gvs[LIST_EQ_REWRITE, EL_MAP] >> strip_tac >>
    simp[EL_CONS,PRE_SUB1] >>
    gvs[ADD1,MAP_TAKE,MAP_MAP_o,o_DEF] >>
    last_x_assum(qspec_then `n` mp_tac) >> simp[EL_CONS,PRE_SUB1] >>
    qmatch_goalsub_abbrev_tac`_ (_ + stl) ⇒ (_ ≥ (_ + (_ + stl1)))` >>
    `stl1 = stl` by (
      unabbrev_all_tac >> AP_TERM_TAC >>
      simp[LIST_EQ_REWRITE,EL_TAKE,EL_MAP] ) >>
    gvs[GREATER_EQ] >>
    mp_tac decreases_gas_cred_step >>
    rewrite_tac[decreases_gas_cred_def] >>
    disch_then(qspec_then`s`mp_tac) >> simp[] >>
    IF_CASES_TAC >> gvs[wf_state_def] >>
    strip_tac >>
    Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`s.contexts` >> gvs[] >>
    gvs[wf_context_def] >>
    first_assum(qspec_then`0`mp_tac) >>
    impl_tac >- simp[] >> simp_tac(srw_ss())[EL_CONS] >>
    strip_tac >> gvs[] >>
    qpat_x_assum`$! _`mp_tac >>
    first_assum(qspec_then`0`mp_tac) >>
    simp_tac (srw_ss()++ARITH_ss) [] >>
    rpt strip_tac >> gvs[] >>
    Cases_on`t` >> gvs[wf_context_def] >>
    first_assum(qspec_then`1`mp_tac) >>
    impl_tac >- simp[] >> simp_tac(srw_ss())[EL_CONS] >>
    strip_tac >> gvs[] >>
    qpat_x_assum`$! _`mp_tac >>
    first_assum(qspec_then`1`mp_tac) >>
    simp_tac (srw_ss()++ARITH_ss) [] >>
    rpt strip_tac >> gvs[]  )
  >> (
    `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
    metis_tac[step_pop_preserves_gas_stack_ok])
QED

Theorem step_preserves_wf_state:
  wf_state s ⇒ wf_state (SND (step s))
Proof
  mp_tac decreases_gas_cred_step
  \\ mp_tac preserves_wf_accounts_step
  \\ mp_tac (GEN_ALL limits_num_contexts_step)
  \\ rewrite_tac[decreases_gas_cred_def, preserves_wf_accounts_def,
                 limits_num_contexts_def]
  \\ rw[wf_state_def]
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[] )
  >- ( `1026 = SUC 1025` by simp[] \\ metis_tac[LESS_EQ_IFF_LESS_SUC])
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[])
  >- ( irule step_preserves_stack_room_ok \\ simp[] \\ gvs[wf_state_def])
  >- ( irule step_preserves_gas_stack_ok \\ simp[] \\ gvs[wf_state_def])
  >- ( irule step_preserves_outputTo_consistent_stack \\ simp[] \\ gvs[wf_state_def])
QED

Theorem run_preserves_wf_state:
  wf_state s ∧ run s = SOME (r, s') ⇒ wf_state s'
Proof
  rpt strip_tac
  >> gvs[run_def]
  >> `(λp. wf_state (SND p)) (r, s')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum $ drule_at Any
  >> simp[]
  >> qx_gen_tac`s''`
  >> PairCases_on `s''`
  >> simp[]
  >> strip_tac
  >> Cases_on `step s''1`
  >> simp[]
  >> drule step_preserves_wf_state
  >> simp[]
QED

Theorem run_call_preserves_wf_state:
  wf_state es ∧ run_call es = SOME (r, es') ⇒ wf_state es'
Proof
  rpt strip_tac
  >> gvs[run_call_def]
  >> `(λp. wf_state (SND p)) (r, es')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum $ drule_at Any
  >> simp[]
  >> qx_gen_tac`s`
  >> PairCases_on `s`
  >> simp[]
  >> strip_tac
  >> Cases_on `step s1`
  >> simp[]
  >> drule step_preserves_wf_state
  >> simp[]
QED

(* Single-step preservation of run_call_inv, by length-change cases. *)

Theorem run_call_inv_step:
  ∀es s s' r.
    es.contexts ≠ [] ∧
    run_call_inv es s ∧
    LENGTH s.contexts ≥ LENGTH es.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es s'
Proof
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `step s0 = (rr, s1)`
  >> `outputTo_consistent_stack s0` by fs[run_call_inv_def]
  >> `outputTo_consistent s0` by
       metis_tac[outputTo_consistent_stack_imp_consistent]
  >> `s0.contexts ≠ []` by fs[outputTo_consistent_def]
  >> `s1.txParams = s0.txParams`
       by metis_tac[vfmTxParamsTheory.step_preserves_txParams, SND]
  >> `s1.txParams = es.txParams` by fs[run_call_inv_def]
  >> `wf_state s0` by fs[run_call_inv_def]
  >> `wf_state s1` by metis_tac[step_preserves_wf_state, SND]
  >> simp[run_call_inv_def]
  (* Trichotomy on the length change. *)
  >> Cases_on `LENGTH s1.contexts = LENGTH s0.contexts` >> gvs[]
  >- (
    (* CASE 0: same-frame. *)
    `same_frame_rel s0 s1` by metis_tac[step_same_frame]
    >> `LENGTH s1.contexts = LENGTH s0.contexts ∧
        TL s1.contexts = TL s0.contexts ∧
        SND (HD s1.contexts) = SND (HD s0.contexts) ∧
        (FST (HD s1.contexts)).msgParams = (FST (HD s0.contexts)).msgParams ∧
        toSet s0.rollback.accesses.storageKeys ⊆
          toSet s1.rollback.accesses.storageKeys`
      by fs[same_frame_rel_def]
    >> `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
    (* outputTo_consistent_stack s1. *)
    >> `outputTo_consistent_stack s1` by (
         fs[outputTo_consistent_stack_def]
         >> Cases_on `s0.contexts` >> Cases_on `s1.contexts` >> gvs[]
         >> gvs[outputTo_consistent_ctx_def])
    >> simp[]
    (* active_rollbacks: tail unchanged. Using same_frame_rel's
       TL s1 = TL s0 and SND HD s1 = SND HD s0, so MAP SND of any
       TAKE prefix is the same. *)
    >> `∀n. MAP SND (TAKE n s1.contexts) = MAP SND (TAKE n s0.contexts)`
        by (
          `∃hd0 hd1 t. s0.contexts = hd0 :: t ∧ s1.contexts = hd1 :: t ∧
                       SND hd0 = SND hd1`
            by (Cases_on `s0.contexts` >> Cases_on `s1.contexts`
                >> gvs[] >> metis_tac[])
          >> simp[]
          >> Cases >> simp[])
    >> `active_rollbacks (LENGTH es.contexts) s1 =
          s1.rollback :: TL (active_rollbacks (LENGTH es.contexts) s0)`
        by (simp[active_rollbacks_def]
            >> `¬(LENGTH s0.contexts < LENGTH es.contexts)` by simp[]
            >> simp[])
    >> simp[]
    (* Tail invariant transfers. *)
    >> `EVERY (λrb. storage_slot_preserved rb es.rollback)
              (TL (active_rollbacks (LENGTH es.contexts) s0))`
        by (`EVERY (λrb. storage_slot_preserved rb es.rollback)
                   (active_rollbacks (LENGTH es.contexts) s0)`
              by fs[run_call_inv_def]
            >> Cases_on `active_rollbacks (LENGTH es.contexts) s0` >> gvs[])
    >> simp[]
    (* Head: storage_slot_preserved s1.rollback es.rollback. *)
    >> `storage_slot_preserved s0.rollback es.rollback`
        by (fs[run_call_inv_def, active_rollbacks_def])
    >> simp[storage_slot_preserved_def]
    >> rpt strip_tac
    >> `¬fIN (SK a k) s0.rollback.accesses.storageKeys`
        by (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
            >> metis_tac[])
    >> `lookup_storage k (lookup_account a s0.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage`
        by fs[storage_slot_preserved_def]
    >> drule_all step_preserves_non_accessed_storage
    >> simp[]
    >> metis_tac[])
  >> Cases_on `LENGTH s1.contexts > LENGTH s0.contexts` >> gvs[]
  >- (
    (* CASE +1: push. *)
    drule_all step_push_structure
    >> strip_tac
    >> `s1.contexts ≠ []` by (strip_tac >> gvs[])
    >> `outputTo_consistent_stack s1` by (
         simp[outputTo_consistent_stack_def]
         >> Cases_on`s1.contexts` >> gvs[]
         >> simp[EVERY_MEM, MEM_EL, PULL_EXISTS]
         >> qx_gen_tac`i` >> strip_tac
         >> first_x_assum(qspec_then`i`mp_tac)
         >> simp[EL_CONS,PRE_SUB1,EL_MAP]
         >> gvs[outputTo_consistent_stack_def,EVERY_MEM,MEM_EL,
                PULL_EXISTS,EL_MAP])
    >> simp[]
    >> qabbrev_tac`ed = LENGTH es.contexts`
    >> qabbrev_tac`m = LENGTH s1.contexts  - ed + 2`
    >> `storage_slot_preserved s1.rollback es.rollback` by (
      rw[storage_slot_preserved_def] >>
      gvs[SUBSET_DEF, finite_setTheory.fIN_IN] >>
      gvs[run_call_inv_def, active_rollbacks_def] >>
      gvs[storage_slot_preserved_def] >>
      first_x_assum irule >>
      simp[finite_setTheory.fIN_IN] >>
      metis_tac[] )
    (* Now prove EVERY storage_slot_preserved for active_rollbacks *)
    >> simp[active_rollbacks_def]
    >> `¬(LENGTH s1.contexts < ed)` by simp[Abbr`ed`]
    >> simp[EVERY_EL, EL_MAP]
    >> rpt strip_tac
    >> Cases_on `n = 0`
    >- (
      (* n = 0: SND (EL 0 s1.contexts) has storage = s0.rollback storage *)
      gvs[]
      >> `storage_slot_preserved s0.rollback es.rollback`
           by (fs[run_call_inv_def, active_rollbacks_def])
      >> last_x_assum (qspec_then `0` mp_tac) >> simp[]
      >> strip_tac
      >> gvs[storage_slot_preserved_def]
      >> `0 < m` by (Cases_on`m` >> gvs[])
      >> simp[HD_TAKE]
      >> rpt strip_tac
      >> first_x_assum irule
      >> gvs[SUBSET_DEF, finite_setTheory.fIN_IN]
      >> Cases_on`s1.contexts` >> gvs[]
      >> strip_tac
      >> first_x_assum(qspec_then`0`(fn th => mp_tac th >> impl_tac >- gvs[]
            >> IF_CASES_TAC)) >> rw[]
      >> metis_tac[])
    >> (
      (* n > 0: SND (EL n s1.contexts) has storage = SND (EL (n-1) s0.contexts) storage *)
      last_x_assum (qspec_then `n` mp_tac) >> simp[]
      >> gvs[LENGTH_TAKE_EQ]
      >> strip_tac
      >> simp[EL_TAKE]
      >> gvs[run_call_inv_def, active_rollbacks_def]
      >> gvs[EVERY_EL, EL_MAP, LENGTH_TAKE_EQ]
      >> last_x_assum(qspec_then`n-1`mp_tac)
      >> simp[EL_TAKE]
      >> strip_tac
      >> gvs[storage_slot_preserved_def]
      >> rpt strip_tac
      >> gvs[EL_TAKE]
      >> gvs[MIN_DEF]
      >> Cases_on`s0.contexts` >> gvs[ADD1]
      >> Cases_on`es.contexts` >> gvs[Abbr`ed`,ADD1]
      >> Cases_on`n` >> gvs[ADD1]
      >> qmatch_asmsub_rename_tac`n < LENGTH t`
      >> last_x_assum(qspec_then`n + 1`mp_tac)
      >> simp[SUBSET_DEF] >> gvs[finite_setTheory.fIN_IN]
      >> disch_then(qspec_then`SK a k`mp_tac) >> simp[] >> strip_tac
      >> first_x_assum(qspecl_then[`a`,`k`]mp_tac)
      >> Cases_on`n` >> gvs[]
      >> simp[EL_TAKE,EL_CONS]))
  >> (
    (* CASE −1: pop. *)
    drule step_pop_structure
    >> impl_keep_tac >- gvs[wf_state_def]
    >> disch_then $ qx_choosel_then[`new_head`,`parent`,`rest`]assume_tac
    >> qmatch_asmsub_abbrev_tac `s0.contexts = callee_ctx :: parent :: rest`
    (* outputTo_consistent_stack s1: new_head has parent's msgParams. *)
    >> `outputTo_consistent_stack s1` by (
         `EVERY outputTo_consistent_ctx (MAP FST s0.contexts) ∧
          s0.contexts ≠ []`
           by fs[outputTo_consistent_stack_def]
         >> gvs[]
         >> simp[outputTo_consistent_stack_def,
                 outputTo_consistent_ctx_def]
         >> gvs[outputTo_consistent_ctx_def])
    >> simp[]
    (* active_rollbacks ed s1 vs active_rollbacks ed s0.
       LENGTH s1 = LENGTH s0 - 1. s1.contexts = (new_head, SND parent) :: rest.
       s0.contexts = HD :: parent :: rest. *)
    >> qabbrev_tac `ed = LENGTH es.contexts`
    >> `EVERY (λrb. storage_slot_preserved rb es.rollback)
              (active_rollbacks ed s0)`
         by fs[run_call_inv_def]
    >> `LENGTH s0.contexts = 2 + LENGTH rest ∧
        LENGTH s1.contexts = 1 + LENGTH rest`
        by (gvs[])
    >> `¬(LENGTH s0.contexts < ed)` by simp[]
    (* Key: show storage_slot_preserved s1.rollback es.rollback from the
       storage-pointwise disjunction + access monotonicity + the relevant
       s0-side slot-preserved facts. *)
    >> `storage_slot_preserved s0.rollback es.rollback ∧
        storage_slot_preserved (SND callee_ctx) es.rollback`
         by (qpat_x_assum `EVERY _ (active_rollbacks ed s0)` mp_tac
             >> simp[active_rollbacks_def]
             >> qpat_x_assum `s0.contexts = _` SUBST1_TAC
             >> `LENGTH s0.contexts + 2 - ed ≥ 2` by simp[]
             >> `∃n. LENGTH s0.contexts + 2 - ed = SUC (SUC n)` by
                  (Cases_on `LENGTH s0.contexts + 2 - ed` >> fs[]
                   >> Cases_on `n` >> fs[])
             >> simp[] >> strip_tac >> fs[])
    >> `storage_slot_preserved s1.rollback es.rollback` by (
         (* step_pop_structure's conclusion is a disjunction of
            (accesses-subset ∧ storage-eq) pairs. Case-split and discharge
            each via the matching subset and the corresponding
            storage_slot_preserved hypothesis. *)
         simp[storage_slot_preserved_def]
         >> rpt strip_tac
         >> gvs[]
         >- (
           (* Disjunct A: s.accesses ⊆ s'.accesses ∧ storage s' = storage s. *)
           `¬fIN (SK a k) s0.rollback.accesses.storageKeys`
             by (fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
           >> `lookup_storage k (lookup_account a s0.rollback.accounts).storage =
               lookup_storage k (lookup_account a es.rollback.accounts).storage`
                by fs[storage_slot_preserved_def]
           >> fs[lookup_storage_def]
           >> metis_tac[])
         >>
           (* Disjunct B: callee_rb.accesses ⊆ s'.accesses ∧
              storage s' = storage callee_rb. *)
           `¬fIN (SK a k) (SND callee_ctx).accesses.storageKeys`
             by (gvs[]
                 >> gvs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
           >> `lookup_storage k (lookup_account a (SND callee_ctx).accounts).storage =
               lookup_storage k (lookup_account a es.rollback.accounts).storage`
                by fs[storage_slot_preserved_def])
    (* Split on whether s1.contexts is below ed or not. *)
    >> Cases_on `LENGTH s1.contexts < ed`
    >- ((* LENGTH s1 < ed: active_rollbacks s1 = [s1.rollback]. *)
        simp[active_rollbacks_def])
    (* LENGTH s1 ≥ ed. Both active_rollbacks have a non-trivial tail.
       s0's TAKE takes one more element than s1's. *)
    >> qpat_x_assum `EVERY _ (active_rollbacks ed s0)` mp_tac
    >> simp[active_rollbacks_def]
    >> gvs[MIN_DEF] >> rw[] >> gvs[ADD1,Abbr`ed`]
    >> Cases_on`es.contexts` >> gvs[ADD1]
    >> Cases_on`rest` >> Cases_on`t` >> gvs[ADD1]
  )
QED

(* -------------------------------------------------------------------------
 * Main run_call preservation theorem.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_inv:
  ∀es res es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (res, es') ⇒
    run_call_inv es es'
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by fs[wf_state_def]
  >> gvs[run_call_def]
  >> `(λ p. run_call_inv es (SND p)) (res, es')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[run_call_inv_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `s''.contexts ≠ []` by (
       Cases_on `s''.contexts` >> gvs[]
       >> Cases_on `es.contexts` >> gvs[outputTo_consistent_stack_def])
  >> irule run_call_inv_step
  >> simp[]
  >> qexistsl_tac [`q`, `s''`]
  >> simp[]
QED

(* Headline corollary: untouched storageKeys imply unchanged storage slot. *)

Theorem run_call_preserves_storage_outside_accessed_slots:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def, active_rollbacks_def, storage_slot_preserved_def]
QED

Theorem run_call_preserves_txParams:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def]
QED

(* Single-context entry corollary for the standard top-level transaction. *)

Theorem run_call_preserves_storage_outside_accessed_slots_single:
    outputTo_consistent_ctx ctx ∧
    wf_context ctx ∧
    wf_accounts es.rollback.accounts ∧
    ctx.jumpDest = NONE ∧
    es.contexts = [(ctx, es.rollback)] ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> irule run_call_preserves_storage_outside_accessed_slots
  >> gvs[outputTo_consistent_stack_def]
  >> simp[storage_slot_preserved_def]
  >> gvs[wf_state_def, all_accounts_def]
  >> gs[stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def]
QED

Theorem run_call_preserves_storage_outside_accessed_slots_initial:
    es.contexts = [(initial_context callee code static rd t, es.rollback)] ∧
    wf_accounts es.rollback.accounts ∧
    (∀a. rd = Code a ⇒ callee = a) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  >> irule run_call_preserves_storage_outside_accessed_slots_single
  >> gvs[]
  >> simp[outputTo_consistent_ctx_def, initial_msg_params_def]
QED

Theorem run_call_preserves_txParams_single:
  ∀es r es'.
    outputTo_consistent_ctx ctx ∧ wf_context ctx ∧
    wf_accounts es.rollback.accounts ∧
    ctx.jumpDest = NONE ∧
    es.contexts = [(ctx,es.rollback)] ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> irule run_call_preserves_txParams
  >> gvs[storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def, wf_state_def, all_accounts_def]
  >> gs[gas_stack_ok_def, stack_room_ok_def]
QED

Theorem run_call_eq_run_single_context:
  LENGTH es.contexts = 1 ⇒
  run_call es = run es
Proof
  rw[run_call_def,run_def] >>
  simp[OWHILE_def] >>
  qho_match_abbrev_tac`COND (∃n. P1 n es) _ _ = COND (∃n. P2 n es) _ _` >>
  simp[] >>
  `∀n es. LENGTH es.contexts ≥ 1 ⇒ P1 n es = P2 n es` by (
    Induct >> simp[Abbr`P1`,Abbr`P2`] >>
    simp[FUNPOW_SUC] >> rpt strip_tac >> gvs[] >>
    first_x_assum drule >> pairarg_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qmatch_asmsub_rename_tac`step s1 = (_,s2)` >>
    qmatch_asmsub_rename_tac`_ (_,s0) = (_,s1)` >>
    `s0.contexts <> []` by (strip_tac >> gvs[]) >>
    `s1.contexts <> []` by (
      qmatch_asmsub_abbrev_tac`FUNPOW f m x` >>
      `(λp. (SND p).contexts ≠ []) (FUNPOW f m x)` suffices_by rw[] >>
      irule FUNPOW_invariant >> rw[Abbr`f`,Abbr`x`] >>
      irule step_preserves_nonempty_contexts >> rw[] ) >>
    `s2.contexts <> []` by (
      drule step_preserves_nonempty_contexts >> rw[] ) >>
    Cases_on`LENGTH s1.contexts` >> gvs[] >>
    Cases_on`LENGTH s2.contexts` >> gvs[] ) >>
  gvs[]
QED
