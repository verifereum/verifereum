(* ==========================================================================
 * run_call storage preservation: slots not in final storageKeys are unchanged,
 * unless a CREATE cleared the storage of an account that was not yet created.
 * The invariant tracks txParams and rollback states reachable by revert.
 * ========================================================================== *)
Theory vfmRunCall
Ancestors
  combin pair option pred_set list rich_list sum
  arithmetic finite_map While vfmTypes vfmConstants
  vfmContext vfmState vfmExecution vfmExecutionProp
  vfmStoragePredicates vfmSameFrame vfmStaticCalls
  vfmDecreasesGas vfmStepLength vfmHandleStep vfmRunWithinFrame
  vfmHeadStack vfmHeadGas vfmJumpDest vfmPreserves vfmWfState
Libs
  dep_rewrite BasicProvers

(* Saved frames can revert down to the entry frame, but never the root. *)
Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback ::
    MAP SND (TAKE (SUC (LENGTH s.contexts) - MAX 2 es_depth) s.contexts)
End

Theorem active_rollbacks_saved:
  active_rollbacks es_depth s =
    s.rollback ::
    (if LENGTH s.contexts < es_depth then []
     else MAP SND (TAKE (MIN (LENGTH s.contexts - es_depth + 1)
                              (LENGTH s.contexts - 1)) s.contexts))
Proof
  Cases_on `LENGTH s.contexts < es_depth`
  >- (`SUC (LENGTH s.contexts) - MAX 2 es_depth = 0`
      by (rw[MAX_DEF] >> decide_tac)
      >> simp[active_rollbacks_def])
  >> `SUC (LENGTH s.contexts) - MAX 2 es_depth =
        MIN (LENGTH s.contexts - es_depth + 1) (LENGTH s.contexts - 1)`
     by (rw[MAX_DEF, MIN_DEF] >> decide_tac)
  >> simp[active_rollbacks_def]
QED

Theorem active_rollbacks_set_original[simp]:
  active_rollbacks n (SND (set_original a s)) = active_rollbacks n s
Proof
  rw[set_original_def, return_def, fail_def, active_rollbacks_def]
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

(* Note: CREATE now clears the storage of the address it creates (as EELS
   process_create_message does) without adding its slots to storageKeys, so
   storage_slot_preserved no longer holds for the active rollbacks. One
   invariant that does hold: for each active rollback rb, a slot outside
   rb's storageKeys either equals its value in es.rollback, or is 0w and the
   account had nonce 0 and no code in es.rollback. Creation sets the nonce
   to 1, and the invariant also tracks that an account created in es.rollback
   stays created in the current rollback and in every saved rollback above
   es. *)
Definition run_call_inv_def:
  run_call_inv es (q:unit + exception option) s ⇔
    s.txParams = es.txParams ∧
    outputTo_consistent_stack s ∧
    wf_state s ∧
    EVERY (λrb. ∀a k. ¬fIN (SK a k) rb.accesses.storageKeys ⇒
      lookup_storage k (lookup_account a rb.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
      lookup_storage k (lookup_account a rb.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts))
      (active_rollbacks (LENGTH es.contexts) s) ∧
    (ISL q ∧ LENGTH es.contexts ≤ LENGTH s.contexts ⇒
      EVERY (λrb. ∀a.
        account_already_created (lookup_account a es.rollback.accounts) ⇒
        account_already_created (lookup_account a rb.accounts))
        (s.rollback :: MAP SND
          (TAKE (LENGTH s.contexts - LENGTH es.contexts) s.contexts)) ∧
      EVERY (λmp. ∀a. mp.outputTo = Code a ⇒
        ¬account_already_created (lookup_account a es.rollback.accounts))
        (MAP (λp. (FST p).msgParams)
          (TAKE (LENGTH s.contexts - LENGTH es.contexts) s.contexts)))
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  wf_state es ∧
  (FST (HD es.contexts)).jumpDest = NONE ∧
  EVERY (λrb. storage_slot_preserved rb es.rollback)
        (MAP SND (TAKE 2 es.contexts)) ⇒
  run_call_inv es (INL ()) es
Proof
  rw[run_call_inv_def, active_rollbacks_saved, storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def,wf_state_def]
  >> Cases_on `es.contexts` >> gvs[]
  >> rw[MIN_DEF]
  >> Cases_on`t` >> gvs[ADD1]
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
    >> Cases_on `FLOOKUP (FST h).msgParams.parsed (FST h).pc` >> gvs[]
    >- (
      (* Stop and Invalid cases. *)
      Cases_on `LENGTH (FST h).msgParams.code ≤ (FST h).pc` >> gvs[]
      >> strip_tac
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
    simp[get_current_context_def, return_def, option_CASE_rator, COND_RATOR,
         AllCaseEqs()] >>
    rpt strip_tac
    >~ [`step_inst Stop`] >- (
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
      fs[same_frame_rel_def] )
    >~ [`step_inst Invalid`] >- (
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
          >~ [`step_create F s = _`]
          >- (drule step_create_storage >> simp[] >> metis_tac[])
          >~ [`step_create T s = _`]
          >- (drule step_create_storage >> simp[] >> metis_tac[])
          >> metis_tac[preserves_storage_step_call, preserves_storage_def])
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
  gvs[option_CASE_rator,COND_RATOR,AllCaseEqs()]
  >~ [`step_inst Stop`] >- (
    `¬is_call Stop` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] )
  >~ [`step_inst Invalid`] >- (
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
    Cases_on `op` >> gvs[is_call_def, step_inst_def]
    >~ [`step_create F s = _`]
    >- (drule_all step_create_inr_no_grow >> simp[])
    >~ [`step_create T s = _`]
    >- (drule_all step_create_inr_no_grow >> simp[])
    >> metis_tac[preserves_storage_step_call, preserves_storage_def] ) >>
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
       >~ [`step_create F s = _`]
       >- (drule_all step_create_inr_no_grow >> simp[])
       >~ [`step_create T s = _`]
       >- (drule_all step_create_inr_no_grow >> simp[])
       >> metis_tac[preserves_storage_step_call, preserves_storage_def])
  >> `lookup_storage k (lookup_account a s'.rollback.accounts).storage =
      lookup_storage k (lookup_account a r''.accounts).storage` by simp[]
  >> simp[]
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

(* The rollback projections of a same-frame prefix are literally equal. *)
Theorem same_frame_saved_prefix:
  same_frame_rel s t ==>
  !n. MAP SND (TAKE n t.contexts) = MAP SND (TAKE n s.contexts) /\
      MAP (\p. (FST p).msgParams) (TAKE n t.contexts) =
      MAP (\p. (FST p).msgParams) (TAKE n s.contexts)
Proof
  rw[same_frame_rel_def]
  >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
  >> Cases_on `n` >> simp[]
QED

Theorem active_rollbacks_same_frame_transport:
  same_frame_rel s t /\ EVERY P (active_rollbacks d s) /\ P t.rollback ==>
  EVERY P (active_rollbacks d t)
Proof
  strip_tac >> drule same_frame_saved_prefix >> strip_tac
  >> gvs[active_rollbacks_def, same_frame_rel_def]
QED

(* A pop consumes the first saved rollback. The surviving saved prefix is
   unchanged, even when the pop exits below the entry depth. *)
Theorem saved_prefix_pop_transport:
  EVERY P (MAP SND (TAKE (SUC n) (child :: parent :: rest))) ==>
  EVERY P (MAP SND (TAKE n ((new_head,SND parent) :: rest)))
Proof
  Cases_on `n` >> simp[]
QED

Theorem active_rollbacks_pop_transport:
  s.contexts = child :: parent :: rest /\
  t.contexts = (new_head,SND parent) :: rest /\
  EVERY P (active_rollbacks d s) /\ P t.rollback ==>
  EVERY P (active_rollbacks d t)
Proof
  strip_tac >> gvs[active_rollbacks_def]
  >> Cases_on `LENGTH rest + 2 < MAX 2 d`
  >- (`SUC (SUC (LENGTH rest)) - MAX 2 d = 0` by decide_tac >> simp[])
  >> `SUC (SUC (SUC (LENGTH rest))) - MAX 2 d =
        SUC (SUC (SUC (LENGTH rest)) - MAX 2 d)` by decide_tac
  >> gvs[] >> irule saved_prefix_pop_transport >> qexists_tac `child` >> simp[]
QED

Theorem protected_rollbacks_pop_transport:
  s.contexts = child :: parent :: rest /\
  t.contexts = (new_head,SND parent) :: rest /\
  d <= LENGTH t.contexts /\
  EVERY P (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) /\
  P t.rollback ==>
  EVERY P (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> gvs[]
  >> `SUC (SUC (LENGTH rest)) - d = SUC (SUC (LENGTH rest) - d)` by decide_tac
  >> gvs[] >> irule saved_prefix_pop_transport >> qexists_tac `child` >> simp[]
  >> `SUC (SUC (LENGTH rest)) - (d + 1) = SUC (LENGTH rest) - d` by decide_tac
  >> gvs[]
QED

(* Relational transport from the old active rollback followed by its saved
   prefix to the newly saved prefix. Consumers use EVERY, not EL arithmetic. *)
Theorem saved_prefix_push_transport:
  n < LENGTH (cs:(context # rollback_state) list) /\ SUC n <= LENGTH cs' /\
  EVERY P ((rb:rollback_state) :: MAP SND (TAKE n cs)) /\
  (!i. i < SUC n ==>
       R (if i = 0 then rb else SND (EL (i-1) cs)) (SND (EL i cs'))) /\
  (!x y. P x /\ R x y ==> Q y) ==>
  EVERY Q (MAP SND (TAKE (SUC n) cs'))
Proof
  strip_tac
  >> fs[EVERY_EL, EL_MAP, LENGTH_TAKE_EQ]
  >> qx_gen_tac `i` >> strip_tac
  >> simp[EL_TAKE]
  >> first_x_assum irule
  >> qexists_tac `if i = 0 then rb else SND (EL (i-1) cs)`
  >> conj_tac
  >- (Cases_on `i` >> gvs[EL_TAKE, ADD1])
  >> first_x_assum irule >> simp[]
QED

Theorem active_rollbacks_push_transport:
  0 < d /\ d <= LENGTH s.contexts /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  EVERY P (active_rollbacks d s) /\ Q t.rollback /\
  (!i. i < LENGTH s.contexts ==>
       R (if i = 0 then s.rollback else SND (EL (i-1) s.contexts))
         (SND (EL i t.contexts))) /\
  (!x y. P x /\ R x y ==> Q y) ==>
  EVERY Q (active_rollbacks d t)
Proof
  strip_tac
  >> `SUC (LENGTH t.contexts) - MAX 2 d =
        SUC (SUC (LENGTH s.contexts) - MAX 2 d)` by
       (rw[MAX_DEF] >> decide_tac)
  >> `SUC (LENGTH s.contexts) - MAX 2 d < LENGTH s.contexts` by
       (rw[MAX_DEF] >> decide_tac)
  >> gvs[active_rollbacks_def]
  >> irule saved_prefix_push_transport
  >> conj_tac >- simp[]
  >> qexistsl_tac [`P`, `R`, `s.contexts`, `s.rollback`] >> simp[]
  >> metis_tac[]
QED

Theorem protected_rollbacks_same_frame_transport:
  same_frame_rel s t /\
  EVERY P (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) /\
  P t.rollback ==>
  EVERY P (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> drule same_frame_saved_prefix >> strip_tac
  >> gvs[same_frame_rel_def]
QED

Theorem protected_rollbacks_push_transport:
  0 < d /\ d <= LENGTH s.contexts /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  EVERY P (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) /\
  Q t.rollback /\
  (!i. i < LENGTH s.contexts ==>
       R (if i = 0 then s.rollback else SND (EL (i-1) s.contexts))
         (SND (EL i t.contexts))) /\
  (!x y. P x /\ R x y ==> Q y) ==>
  EVERY Q (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac
  >> `LENGTH t.contexts - d = SUC (LENGTH s.contexts - d)` by decide_tac
  >> `LENGTH s.contexts - d < LENGTH s.contexts` by decide_tac
  >> simp[] >> irule saved_prefix_push_transport
  >> conj_tac >- simp[]
  >> qexistsl_tac [`P`, `R`, `s.contexts`, `s.rollback`] >> simp[]
  >> metis_tac[]
QED

Theorem protected_frames_same_frame_transport:
  same_frame_rel s t /\
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> drule same_frame_saved_prefix >> strip_tac
  >> gvs[same_frame_rel_def]
QED

Theorem protected_frames_pop_transport:
  s.contexts = child :: parent :: rest /\
  t.contexts = (new_head,SND parent) :: rest /\
  new_head.msgParams = (FST parent).msgParams /\
  d <= LENGTH t.contexts /\
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> gvs[]
  >> `SUC (SUC (LENGTH rest)) - d = SUC (SUC (LENGTH rest) - d)` by decide_tac
  >> `SUC (SUC (LENGTH rest)) - (d+1) = SUC (LENGTH rest) - d` by decide_tac
  >> gvs[] >> Cases_on `SUC (LENGTH rest) - d` >> gvs[]
QED

Theorem protected_frames_push_transport:
  0 < d /\ d <= LENGTH s.contexts /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  MAP FST (TL (TL t.contexts)) = MAP FST (TL s.contexts) /\
  (FST (EL 1 t.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
  P (FST (HD t.contexts)).msgParams /\
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac
  >> `LENGTH t.contexts - d = SUC (LENGTH s.contexts - d)` by decide_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t.contexts` >> gvs[]
  >> rename1 `t.contexts = child :: cs`
  >> Cases_on `cs` >> gvs[]
  >> rename1 `t.contexts = child :: parent :: rest`
  >> `MAP (\c:context. c.msgParams) (MAP FST rest) =
      MAP (\c:context. c.msgParams) (MAP FST t')` by simp[]
  >> gvs[MAP_MAP_o, combinTheory.o_DEF]
  >> `!n. MAP (\p. (FST p).msgParams) (TAKE n rest) =
            MAP (\p. (FST p).msgParams) (TAKE n t')`
      by simp[MAP_TAKE]
  >> Cases_on `SUC (LENGTH t') - d` >> gvs[]
  >- (`SUC (SUC (LENGTH t')) - (d+1) = 0` by decide_tac >> simp[])
  >> `SUC (SUC (LENGTH t')) - (d+2) = n` by decide_tac >> simp[]
QED

(* Both rollback choices in step_pop_structure come from the old active
   list. In particular this remains true at d=1 and at an exit below d. *)
Theorem active_rollbacks_pop_sources:
  d <= LENGTH s.contexts /\ 2 <= LENGTH s.contexts ==>
  MEM s.rollback (active_rollbacks d s) /\
  MEM (SND (HD s.contexts)) (active_rollbacks d s)
Proof
  strip_tac
  >> `0 < SUC (LENGTH s.contexts) - MAX 2 d` by
       (rw[MAX_DEF] >> decide_tac)
  >> Cases_on `SUC (LENGTH s.contexts) - MAX 2 d` >> gvs[]
  >> Cases_on `s.contexts` >> gvs[active_rollbacks_def]
QED

(* No collision protection is required for an unchanged-storage transition:
   this is the interface used for either rollback choice of a pop. *)
Theorem storage_slots_access_transport:
  (!a k. ~fIN (SK a k) rb.accesses.storageKeys ==>
     lookup_storage k (lookup_account a rb.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a rb.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)) /\
  toSet rb.accesses.storageKeys SUBSET toSet next.accesses.storageKeys /\
  (!a. (lookup_account a next.accounts).storage =
       (lookup_account a rb.accounts).storage) ==>
  !a k. ~fIN (SK a k) next.accesses.storageKeys ==>
     lookup_storage k (lookup_account a next.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a next.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)
Proof
  rpt strip_tac
  >> `~fIN (SK a k) rb.accesses.storageKeys` by
       (gvs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[])
  >> metis_tac[]
QED

(* Slot safety composes across access inclusion and a possible CREATE clear.
   Collision protection is needed only for the clearing alternative. *)
Theorem storage_slots_compose:
  (!a k. ~fIN (SK a k) rb.accesses.storageKeys ==>
     lookup_storage k (lookup_account a rb.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a rb.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)) /\
  toSet rb.accesses.storageKeys SUBSET toSet next.accesses.storageKeys /\
  (!a k. ~fIN (SK a k) next.accesses.storageKeys ==>
     lookup_storage k (lookup_account a next.accounts).storage =
       lookup_storage k (lookup_account a rb.accounts).storage \/
     lookup_storage k (lookup_account a next.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb.accounts)) /\
  (!a. account_already_created (lookup_account a rb0.accounts) ==>
       account_already_created (lookup_account a rb.accounts)) ==>
  !a k. ~fIN (SK a k) next.accesses.storageKeys ==>
     lookup_storage k (lookup_account a next.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a next.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)
Proof
  rpt strip_tac
  >> `~fIN (SK a k) rb.accesses.storageKeys` by
       (gvs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[])
  >> first_x_assum (qspecl_then [`a`, `k`] strip_assume_tac)
  >> metis_tac[]
QED

(* Nonce/code transport before the return-code deposit boundary. *)
val nonce_code_rel = ``\a (s:execution_state) (t:execution_state).
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a t.rollback.accounts).nonce /\
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code``;

Theorem nonce_code_rel_trans:
  ^nonce_code_rel a s u /\ ^nonce_code_rel a u t ==> ^nonce_code_rel a s t
Proof
  simp[] >> strip_tac >> simp[] >> decide_tac
QED

Theorem preserves_nonce_code_of_rollback:
  preserves_rollback m ==> preserves (^nonce_code_rel a) m
Proof
  rw[preserves_rollback_def, preserves_def] >>
  first_x_assum drule >> simp[]
QED

Theorem preserves_nonce_code_bind:
  preserves (^nonce_code_rel a) g /\
  (!x. preserves (^nonce_code_rel a) (f x)) ==>
  preserves (^nonce_code_rel a) (bind g f)
Proof
  strip_tac >> irule preserves_bind >> simp[] >>
  metis_tac[nonce_code_rel_trans]
QED

Theorem preserves_nonce_code_ignore_bind:
  preserves (^nonce_code_rel a) g /\
  preserves (^nonce_code_rel a) f ==>
  preserves (^nonce_code_rel a) (ignore_bind g f)
Proof
  strip_tac >> irule preserves_ignore_bind >> simp[] >>
  metis_tac[nonce_code_rel_trans]
QED

Theorem preserves_nonce_code_increment:
  preserves (^nonce_code_rel a) (update_accounts (increment_nonce b))
Proof
  rw[preserves_def, update_accounts_def, return_def,
     increment_nonce_lookup, increment_nonce_code] >>
  Cases_on `a = b` >> gvs[]
QED

Theorem preserves_nonce_code_transfer:
  preserves (^nonce_code_rel a)
    (update_accounts (transfer_value sender recipient value))
Proof
  rw[preserves_def, update_accounts_def, return_def,
     transfer_value_preserves_code, transfer_value_preserves_nonce]
QED

Theorem preserves_nonce_code_proceed_create:
  preserves (^nonce_code_rel a)
    (proceed_create sender address value code gas)
Proof
  rw[preserves_def, proceed_create_def, bind_def, ignore_bind_def,
       update_accounts_def, get_rollback_def, get_original_def,
       set_original_def, push_context_def, return_def, fail_def,
       COND_RATOR, AllCaseEqs(),
       increment_nonce_lookup, increment_nonce_code,
       transfer_value_preserves_code, transfer_value_preserves_nonce] >>
  Cases_on `a = address` >> Cases_on `a = sender` >>
  gvs[increment_nonce_lookup, increment_nonce_code,
      transfer_value_preserves_code, transfer_value_preserves_nonce]
QED

Theorem preserves_nonce_code_access_address:
  preserves (^nonce_code_rel a) (access_address b)
Proof
  rw[preserves_def, access_address_def, domain_check_def,
     set_domain_def, return_def, fail_def, AllCaseEqs()] >>
  gvs[ignore_bind_def, bind_def, set_domain_def, return_def]
QED

Theorem preserves_nonce_code_step_create:
  preserves (^nonce_code_rel a) (step_create two)
Proof
  simp[step_create_def, ignore_bind_def] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >>
  simp[] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  simp[] >> IF_CASES_TAC
  >- (simp[abort_create_exists_def, ignore_bind_def] >>
      ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
      (conj_tac >- simp[SRULE [] preserves_nonce_code_increment]) >>
      simp[] >> irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  simp[SRULE [] preserves_nonce_code_proceed_create]
QED

Theorem preserves_nonce_code_proceed_call:
  preserves (^nonce_code_rel a)
    (proceed_call op sender address value off sz code gas output)
Proof
  simp[proceed_call_def, ignore_bind_def] >>
  ntac 2
    (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >-
       (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
     gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (IF_CASES_TAC >- simp[SRULE [] preserves_nonce_code_transfer] >>
     irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  simp[] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]
QED

Theorem preserves_nonce_code_step_call:
  preserves (^nonce_code_rel a) (step_call op)
Proof
  simp[step_call_def, ignore_bind_def] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> pairarg_tac >> simp[] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> gen_tac >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >> gen_tac >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> gen_tac >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (Cases_on `get_delegate (lookup_account (w2w (EL 1 args)) accounts).code`
     >- (simp[] >> irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
     simp[] >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >>
     gen_tac >> irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  Cases >> simp[] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> pairarg_tac >> simp[] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  simp[SRULE [] preserves_nonce_code_proceed_call]
QED

Theorem preserves_nonce_code_access_slot:
  preserves (^nonce_code_rel a) (access_slot sk)
Proof
  rw[preserves_def, access_slot_def, domain_check_def,
     set_domain_def, return_def, fail_def, AllCaseEqs()] >>
  gvs[ignore_bind_def, bind_def, set_domain_def, return_def]
QED

Theorem preserves_nonce_code_write_storage:
  preserves (^nonce_code_rel a) (write_storage b k v)
Proof
  rw[preserves_def, write_storage_def, update_accounts_def, return_def] >>
  Cases_on `a = b` >>
  gvs[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem preserves_nonce_code_sstore_gas:
  preserves (^nonce_code_rel a) (step_sstore_gas_consumption b k v)
Proof
  simp[step_sstore_gas_consumption_def, ignore_bind_def] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_slot]) >> gen_tac >>
  irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]
QED

Theorem preserves_nonce_code_step_sstore:
  preserves (^nonce_code_rel a) (step_sstore transient)
Proof
  simp[step_sstore_def, ignore_bind_def] >>
  ntac 2
    (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >-
       (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (Cases_on `transient` >> simp[SRULE [] preserves_nonce_code_sstore_gas] >>
     irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  simp[] >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> simp[] >>
  Cases_on `transient` >> simp[SRULE [] preserves_nonce_code_write_storage] >>
  rw[preserves_def, write_transient_storage_def, bind_def,
     get_tStorage_def, set_tStorage_def, return_def]
QED

Theorem self_destruct_account_update_nonce_code:
  (lookup_account a
    (update_account sender ((lookup_account sender accounts) with balance := 0)
      (transfer_value sender address value accounts))).nonce =
    (lookup_account a accounts).nonce /\
  (lookup_account a
    (update_account sender ((lookup_account sender accounts) with balance := 0)
      (transfer_value sender address value accounts))).code =
    (lookup_account a accounts).code
Proof
  Cases_on `a = sender` >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  simp[GSYM lookup_account_def, transfer_value_preserves_nonce,
       transfer_value_preserves_code]
QED

Theorem preserves_nonce_code_step_self_destruct:
  preserves (^nonce_code_rel a) step_self_destruct
Proof
  simp[step_self_destruct_def] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >>
  gen_tac >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> ho_match_mp_tac (SRULE [] preserves_nonce_code_ignore_bind) >>
  (conj_tac >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  rw[preserves_def] >>
  gvs[bind_def, ignore_bind_def, get_accounts_def, consume_gas_def,
      get_current_context_def, set_current_context_def, assert_def,
      assert_not_static_def, get_static_def, get_original_def,
      update_accounts_def, add_to_delete_def, finish_def, fail_def,
      return_def, COND_RATOR, AllCaseEqs()] >>
  simp[self_destruct_account_update_nonce_code,
       transfer_value_preserves_nonce, transfer_value_preserves_code]
QED

Theorem cp_nonce_code:
  cp (m:unit execution) ==> preserves_when (\s. s.contexts <> []) (^nonce_code_rel a) m
Proof
  rw[cp_def, preserves_when_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem step_inst_nonce_code:
  s.contexts <> [] /\ step_inst op s = (r,t) ==> ^nonce_code_rel a s t
Proof
  Cases_on `op`
  >~ [`step_inst SStore`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_sstore) >> simp[])
  >~ [`step_inst TStore`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_sstore) >> simp[])
  >~ [`step_inst SelfDestruct`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_self_destruct) >> simp[])
  >~ [`step_inst Create`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_create) >> simp[])
  >~ [`step_inst Create2`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_create) >> simp[])
  >~ [`step_inst Call`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst CallCode`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst DelegateCall`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst StaticCall`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst (Log n)`] >- (
    strip_tac >>
    `preserves (^nonce_code_rel a) (step_inst (Log n))` by
      (irule preserves_nonce_code_of_rollback >>
       irule step_inst_Log_preserves_rollback) >>
    gvs[preserves_def] >> first_x_assum drule >> simp[]) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `m s = (r,t)` >>
  irule (SRULE [preserves_when_def] cp_nonce_code) >>
  simp[] >> qexistsl_tac [`m`,`r`] >> simp[Abbr `m`]
QED

Theorem same_frame_nonce_monotone:
  same_frame_rel s t ==>
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a t.rollback.accounts).nonce
Proof
  rw[same_frame_rel_def, callee_local_changes_def] >>
  Cases_on `a = (FST (HD s.contexts)).msgParams.callee` >> gvs[]
QED

Theorem step_same_frame_positive_nonce:
  wf_state s /\ step s = (r, t) /\
  LENGTH t.contexts = LENGTH s.contexts /\
  0 < (lookup_account a s.rollback.accounts).nonce ==>
  0 < (lookup_account a t.rollback.accounts).nonce
Proof
  strip_tac >>
  `outputTo_consistent s` by
    metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def] >>
  drule_all step_same_frame >> strip_tac >>
  drule same_frame_nonce_monotone >>
  disch_then (qspec_then `a` assume_tac) >> decide_tac
QED

Theorem deposit_code_nonce:
  (lookup_account a
    (update_account b (lookup_account b accounts with code := code)
      accounts)).nonce = (lookup_account a accounts).nonce
Proof
  rw[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem deposit_code_other:
  a <> b ==>
  lookup_account a
    (update_account b (lookup_account b accounts with code := code)
      accounts) = lookup_account a accounts
Proof
  simp[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem handle_create_nonce:
  s.contexts <> [] /\ handle_create e s = (r, t) ==>
  (lookup_account a t.rollback.accounts).nonce =
    (lookup_account a s.rollback.accounts).nonce
Proof
  rw[handle_create_def, bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, return_def] >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `e` >> Cases_on `h0.msgParams.outputTo` >>
  gvs[reraise_def, ignore_bind_def, bind_def, assert_def,
      return_def, fail_def, AllCaseEqs(), consume_gas_def,
      get_current_context_def, set_current_context_def,
      update_accounts_def, deposit_code_nonce]
QED

Theorem handle_create_code_other:
  s.contexts <> [] /\ handle_create e s = (r,t) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a ==>
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  rw[handle_create_def, bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, return_def] >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `e` >> Cases_on `h0.msgParams.outputTo` >>
  gvs[reraise_def, ignore_bind_def, bind_def, assert_def,
      return_def, fail_def, AllCaseEqs(), consume_gas_def,
      get_current_context_def, set_current_context_def,
      update_accounts_def, deposit_code_other]
QED

Theorem handle_create_protected_account:
  s.contexts <> [] /\ handle_create e s = (r,t) /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) /\
  ((FST (HD s.contexts)).msgParams.outputTo = Code a ==>
    0 < (lookup_account a s.rollback.accounts).nonce) ==>
  (lookup_account a t.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a t.rollback.accounts).code
Proof
  strip_tac >> drule_all handle_create_nonce >>
  disch_then (qspec_then `a` assume_tac) >>
  Cases_on `(FST (HD s.contexts)).msgParams.outputTo = Code a` >>
  gvs[] >> drule_all handle_create_code_other >> simp[]
QED

Theorem step_grow_dispatch:
  wf_state s /\ step s = (r,s') /\ LENGTH s.contexts < LENGTH s'.contexts ==>
  r = INL () /\
  ((?op. step_call op s = (INL (),s')) \/
   (?two. step_create two s = (INL (),s')))
Proof
  strip_tac
  >> `s.contexts <> []` by gvs[wf_state_def]
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
  >> `LENGTH r'.contexts >= LENGTH s.contexts` by
      (drule_all same_frame_or_grow_length >> simp[])
  >> `r'.contexts <> []` by (strip_tac >> gvs[] >> Cases_on `s.contexts` >> gvs[])
  >> `LENGTH s'.contexts <= LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts`
  >- (drule handle_step_shrinks_by_one >> simp[])
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
      (irule outputTo_consistent_stack_imp_consistent >> gvs[wf_state_def])
  >> `~vfm_abort y` by (irule step_inner_inr_grow_not_abort
      >> qexistsl_tac [`s`, `r'`] >> simp[Abbr `inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[])
  >> `LENGTH r'.contexts >= 2` by simp[]
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

Theorem step_growth_nonce_code:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts ==>
  ^nonce_code_rel a s t
Proof
  strip_tac >> drule_all step_grow_dispatch >> strip_tac
  >- (drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[]) >>
  drule (SRULE [preserves_def] preserves_nonce_code_step_create) >> simp[]
QED

(* Protection starts with no newly introduced snapshots or Code frames. *)
Theorem collision_protection_initial:
  EVERY (\rb. !a.
    account_already_created (lookup_account a s.rollback.accounts) ==>
    account_already_created (lookup_account a rb.accounts))
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - LENGTH s.contexts) s.contexts)) /\
  EVERY (\cr. !a. (FST cr).msgParams.outputTo = Code a ==>
    ~account_already_created (lookup_account a s.rollback.accounts))
    (TAKE (LENGTH s.contexts - LENGTH s.contexts) s.contexts)
Proof
  simp[]
QED

Theorem step_inst_preserves_created_account:
  s.contexts <> [] /\ step_inst op s = (r,t) /\
  account_already_created (lookup_account a s.rollback.accounts) ==>
  account_already_created (lookup_account a t.rollback.accounts)
Proof
  strip_tac >> drule_all step_inst_nonce_code >>
  disch_then (qspec_then `a` mp_tac) >>
  gvs[account_already_created_def] >> decide_tac
QED

Theorem handle_create_preserves_other_created_account:
  s.contexts <> [] /\ handle_create e s = (r,t) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a /\
  account_already_created (lookup_account a s.rollback.accounts) ==>
  account_already_created (lookup_account a t.rollback.accounts)
Proof
  strip_tac >> drule_all handle_create_nonce >>
  disch_then (qspec_then `a` assume_tac) >>
  drule_all handle_create_code_other >>
  gvs[account_already_created_def]
QED

Theorem call_prefix_delegate_code_selection:
  preserves_when (\s. s.contexts <> [])
    (\s t. cp_rel s t /\ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys)
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

val call_reach_peel =
  drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[call_prefix_leaves]
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[];

Theorem step_call_reaches_proceed_call:
  step_call op s = (r,s') /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH s'.contexts ==>
  ?u sender address value ao az code gas mr.
    cp_rel s u /\ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys /\
    proceed_call op sender address value ao az code gas (Memory mr) u = (r,s') /\
    sender = (FST (HD s.contexts)).msgParams.callee /\
    value <= (lookup_account sender s.rollback.accounts).balance /\
    code = (case get_delegate (lookup_account address s.rollback.accounts).code of
      NONE => (lookup_account address s.rollback.accounts).code
    | SOME d => (lookup_account d s.rollback.accounts).code) /\
    (~call_has_value op ==> value = 0) /\
    (op = Call /\ 0 < value ==> ~(FST (HD s.contexts)).msgParams.static) /\
    az < 2 ** 256
Proof
  simp[step_call_def] >> strip_tac
  >> `cp_rel s s /\ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys`
    by simp[call_prefix_refl]
  >> call_reach_peel >> pairarg_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `proceed_call op _ address value ao az _ _ rd`
  >> call_reach_peel
  >> call_reach_peel
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
  >> call_reach_peel >> pairarg_tac >> gvs[ignore_bind_def]
  >> qpat_x_assum `pop_stack _ _ = _` kall_tac
  >> qpat_x_assum `memory_expansion_info _ _ _ = _` kall_tac
  >> qpat_x_assum `access_address _ _ = _` kall_tac
  >> qpat_x_assum `(case _ of NONE => _ | SOME _ => _) _ = _` kall_tac
  >> qpat_x_assum `get_gas_left _ = _` kall_tac
  >> qpat_x_assum `call_gas _ _ _ _ _ = _` kall_tac
  >> call_reach_peel
  >> drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[] >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> (impl_tac >- (Cases_on `op = Call /\ 0 < value` >> simp[call_prefix_leaves]))
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[]
  >> `op = Call /\ 0 < value ==> ~(FST (HD s.contexts)).msgParams.static`
    by (strip_tac
        >> gvs[assert_not_static_def, get_static_def, get_current_context_def,
               bind_def, assert_def, return_def, fail_def, cp_rel_def, AllCaseEqs()])
  >> call_reach_peel
  >> call_reach_peel
  >> rename1 `get_callee beforeSender = (INL sender,afterSender)`
  >> `sender = (FST (HD s.contexts)).msgParams.callee`
    by gvs[get_callee_def, get_current_context_def, bind_def, return_def,
           fail_def, cp_rel_def, AllCaseEqs()]
  >> gvs[COND_RATOR]
  >> Cases_on `(lookup_account (FST (HD s.contexts)).msgParams.callee
                 s.rollback.accounts).balance < value` >> gvs[]
  >- (drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> call_reach_peel
  >> call_reach_peel >> gvs[COND_RATOR]
  >> rename1 `get_num_contexts depthState = (INL depth,entry)`
  >> Cases_on `depth > 1024` >> gvs[]
  >- (drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> qexistsl_tac [`entry`, `address`, `value`, `ao`, `az`, `stipend`]
  >> simp[] >> gvs[Abbr `rd`]
  >> qexists_tac `<|offset := w2n (EL ((if call_has_value op then 1 else 0) + 4) x);
                   size := w2n (EL ((if call_has_value op then 1 else 0) + 5) x)|>`
  >> simp[] >> simp[Abbr `value`]
  >> simp[Abbr `az`]
  >> qmatch_goalsub_abbrev_tac `w2n w`
  >> mp_tac (Q.ISPEC `w:bytes32` wordsTheory.w2n_lt)
  >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem proceed_call_saved_rollback:
  proceed_call op sender address value ao az code gas rd s = (r, s') /\
  s.contexts <> [] /\ ~fIN address precompile_addresses ==>
  SND (HD s'.contexts) = s.rollback /\
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
QED

Theorem terminal_bind:
  (!x s. ISR (FST (f x s))) ==> ISR (FST (bind g f s))
Proof
  rw[bind_def] >> Cases_on `g s` >> Cases_on `q` >> gvs[]
QED

Theorem terminal_ignore_bind:
  (!s. ISR (FST (f s))) ==> ISR (FST (ignore_bind g f s))
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
  proceed_call op sender address value ao az code gas rd s = (INL (), s') /\
  s.contexts <> [] ==> ~fIN address precompile_addresses
Proof
  strip_tac >> strip_tac
  >> Cases_on `op <> CallCode /\ 0 < value`
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

Theorem proceed_call_saved_accounts:
  s.contexts <> [] /\
  proceed_call op sender address value argsOffset argsSize code stipend
    outputTo s = (r,t) ==>
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  strip_tac >> qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def, get_rollback_def,
       read_memory_def, get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  simp[update_accounts_def, return_def, get_caller_def, get_value_def,
       get_static_def, get_current_context_def, bind_def,
       push_context_def, ignore_bind_def] >>
  qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss` >>
  qmatch_goalsub_abbrev_tac `m ss = _` >> strip_tac >>
  `ss.contexts <> []` by simp[Abbr `ss`] >>
  `cp m` by
    (simp[Abbr `m`] >>
     Cases_on `fIN address precompile_addresses` >> simp[]) >>
  `cp_rel ss t` by
    (qpat_x_assum `cp m` mp_tac >>
     rewrite_tac[cp_eq_preserves_when, preserves_when_def] >>
     disch_then drule >> simp[]) >>
  `SND (HD t.contexts) = SND (HD ss.contexts)` by
    gvs[cp_rel_def] >>
  simp[Abbr `ss`]
QED

Theorem step_call_grow_saved_accounts:
  s.contexts <> [] /\ step_call op s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac >>
  `u.contexts <> []` by
    (gvs[cp_rel_def] >> Cases_on `s.contexts` >> gvs[]) >>
  drule_all proceed_call_saved_accounts >> gvs[cp_rel_def]
QED

Theorem step_create_saved_head_nonce_code:
  step_create two s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a (SND (HD t.contexts)).accounts).nonce /\
  (lookup_account a (SND (HD t.contexts)).accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac >>
  drule_all call_prefix_contexts >> strip_tac >>
  drule_all proceed_create_frame_effects >> strip_tac >>
  gvs[cp_rel_def, increment_nonce_lookup, increment_nonce_code] >>
  Cases_on `a = (FST (HD s.contexts)).msgParams.callee` >> gvs[]
QED

Theorem step_growth_saved_head_nonce_code:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts ==>
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a (SND (HD t.contexts)).accounts).nonce /\
  (lookup_account a (SND (HD t.contexts)).accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_grow_saved_accounts >> simp[]) >>
  drule_all step_create_saved_head_nonce_code >> simp[]
QED

Theorem proceed_call_memory_output:
  s.contexts <> [] /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (r,t) ==>
  (FST (HD t.contexts)).msgParams.outputTo = Memory mr
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, update_accounts_def,
       push_context_def, get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  Cases_on `fIN address precompile_addresses` >> simp[return_def] >>
  strip_tac >> gvs[update_accounts_def, get_current_context_def,
       return_def, initial_context_def, initial_msg_params_def] >>
  qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed` >>
  `pushed.contexts <> []` by simp[Abbr `pushed`] >>
  mp_tac (INST_TYPE [alpha |-> ``:unit``]
    (Q.INST [`a` |-> `address`] preserves_same_frame_dispatch_precompiles)) >>
  rewrite_tac[preserves_same_frame_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[same_frame_rel_def, Abbr `pushed`, initial_context_def,
      initial_msg_params_def]
QED

Theorem step_growth_nonce_certificate:
  wf_state s /\ step s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts /\
  (FST (HD t.contexts)).msgParams.outputTo = Code b ==>
  0 < (lookup_account b t.rollback.accounts).nonce
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_reaches_proceed_call >> strip_tac >>
      drule_all call_prefix_contexts >> strip_tac >>
      drule_all proceed_call_memory_output >> simp[]) >>
  drule_all step_create_growth_effects >> strip_tac >> gvs[]
QED

Theorem set_last_accounts_foreign_lookup:
  ls <> [] /\ a <> address ==>
  MAP (\p. lookup_account a (SND p).accounts)
    (set_last_accounts (update_account address empty_account_state
      (SND (LAST ls)).accounts) ls) =
  MAP (\p. lookup_account a (SND p).accounts) ls
Proof
  Induct_on `ls` using SNOC_INDUCT >>
  simp[set_last_accounts_def, FRONT_SNOC, LAST_SNOC, MAP_SNOC,
       lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem proceed_create_old_snapshot_lookups:
  s.contexts <> [] /\ a <> address /\
  proceed_create sender address value code gas s = (r,t) ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> qhdtm_x_assum `proceed_create` mp_tac >>
  simp[proceed_create_def, ignore_bind_def, bind_def,
       update_accounts_def, get_rollback_def, get_original_def,
       set_original_def, push_context_def, return_def] >>
  strip_tac >> gvs[] >> simp[set_last_accounts_foreign_lookup]
QED

Theorem proceed_call_old_snapshot_lookups:
  proceed_call op sender address value ao az code gas rd s = (r,t) /\
  s.contexts <> [] /\ ~fIN address precompile_addresses ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value` >>
  gvs[proceed_call_def, bind_def, ignore_bind_def,
      get_rollback_def, read_memory_def, get_current_context_def,
      get_caller_def, get_value_def, get_static_def,
      push_context_def, update_accounts_def, return_def, fail_def,
      AllCaseEqs()]
QED

Theorem step_create_old_snapshot_lookups:
  step_create two s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac >>
  drule_all call_prefix_contexts >> strip_tac >>
  `a <> address` by (strip_tac >> gvs[cp_rel_def, account_already_created_def]) >>
  drule_all proceed_create_old_snapshot_lookups >>
  gvs[cp_rel_def] >> Cases_on `s.contexts` >> gvs[]
QED

Theorem step_call_old_snapshot_lookups:
  step_call op s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac >>
  drule_all call_prefix_contexts >> strip_tac >>
  drule_all proceed_call_inl_nonprecompile >> strip_tac >>
  drule_all proceed_call_old_snapshot_lookups >> gvs[cp_rel_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem step_growth_old_snapshot_lookups:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac >>
  metis_tac[step_call_old_snapshot_lookups, step_create_old_snapshot_lookups]
QED

Theorem step_growth_old_snapshot_lookup:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) /\ i < LENGTH s.contexts ==>
  lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
  lookup_account a (SND (EL i s.contexts)).accounts
Proof
  strip_tac >>
  `MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
   MAP (\p. lookup_account a (SND p).accounts) s.contexts`
    by metis_tac[step_growth_old_snapshot_lookups] >>
  pop_assum (mp_tac o Q.AP_TERM `EL i`) >>
  simp[EL_MAP, EL]
QED

(* These are ML abbreviations only; the exported facts have inline predicates. *)
val collision_protected = ``\(B:rollback_state) (rb:rollback_state). !a.
  account_already_created (lookup_account a B.accounts) ==>
  account_already_created (lookup_account a rb.accounts)``;

Theorem step_growth_collision_protection:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY (^collision_protected B)
    (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> fs[] >> conj_tac
  >- (rpt strip_tac >> drule_all step_growth_nonce_code >>
      disch_then (qspec_then `a` mp_tac) >>
      `account_already_created (lookup_account a s.rollback.accounts)` by metis_tac[] >>
      gvs[account_already_created_def] >> decide_tac) >>
  `s.contexts <> [] /\ outputTo_consistent_stack s` by gvs[wf_state_def] >>
  `LENGTH t.contexts = SUC (LENGTH s.contexts)` by
    (`LENGTH t.contexts > LENGTH s.contexts` by simp[] >>
     drule_all step_push_structure >> simp[ADD1]) >>
  simp[EVERY_EL, EL_MAP, LENGTH_TAKE_EQ] >> rpt strip_tac >>
  `account_already_created (lookup_account a s.rollback.accounts)` by metis_tac[] >>
  Cases_on `n`
  >- (simp[EL_TAKE] >> drule_all step_growth_saved_head_nonce_code >>
      disch_then (qspec_then `a` mp_tac) >>
      gvs[account_already_created_def] >> decide_tac) >>
  `n' < LENGTH s.contexts /\ n' < LENGTH s.contexts - d` by decide_tac >>
  `lookup_account a (SND (EL (SUC n') t.contexts)).accounts =
     lookup_account a (SND (EL n' s.contexts)).accounts` by
    (irule step_growth_old_snapshot_lookup >>
     simp[] >> gvs[account_already_created_def] >> metis_tac[]) >>
  gvs[EL_TAKE, EVERY_EL, EL_MAP, LENGTH_TAKE_EQ] >>
  metis_tac[EL_TAKE]
QED

Theorem step_growth_code_provenance:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ^collision_protected B s.rollback ==>
  !a. (FST (HD t.contexts)).msgParams.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts)
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_reaches_proceed_call >> strip_tac >>
      drule_all call_prefix_contexts >> strip_tac >>
      drule_all proceed_call_memory_output >> simp[]) >>
  drule_all step_create_growth_effects >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem step_growth_protected_frames:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ^collision_protected B s.rollback /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts-d) t.contexts))
Proof
  strip_tac >>
  `!a. (FST (HD t.contexts)).msgParams.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts)` by
    (qx_gen_tac `a` >> disch_tac >> fs[] >>
     irule (SRULE [] step_growth_code_provenance) >>
     qexistsl_tac [`r`, `s`, `t`] >> simp[]) >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   LENGTH t.contexts > LENGTH s.contexts` by gvs[wf_state_def] >>
  drule_all step_push_structure >> strip_tac >>
  irule protected_frames_push_transport >>
  conj_tac >- simp[] >>
  simp[] >> qexists_tac `s` >> simp[ADD1]
QED

val step_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code <= context.pc
            then step_inst Stop else step_inst Invalid
  od``;

Theorem step_inst_inc_pc_nonce_code:
  s.contexts <> [] /\
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ==>
  ^nonce_code_rel a s t
Proof
  strip_tac >>
  Cases_on `step_inst op s` >> rename1 `step_inst op s = (q,u)` >>
  `^nonce_code_rel a s u` by metis_tac[step_inst_nonce_code] >>
  `u.contexts <> []` by metis_tac[step_inst_preserves_nonempty_contexts, SND] >>
  Cases_on `q`
  >- (rename1 `step_inst op s = (INL x,u)` >> Cases_on `x` >>
      `inc_pc_or_jump op u = (r,t)` by gvs[ignore_bind_def, bind_def] >>
      `preserves_when (\s. s.contexts <> []) (^nonce_code_rel a)
         (inc_pc_or_jump op)` by (irule cp_nonce_code >> simp[]) >>
      qpat_x_assum `preserves_when _ _ _` mp_tac >>
      simp[preserves_when_def] >> disch_then drule >>
      disch_then drule >> strip_tac >>
      gvs[] >> decide_tac) >>
  gvs[ignore_bind_def, bind_def]
QED

Theorem step_inner_nonce_code:
  s.contexts <> [] /\ ^step_inner s = (r,t) ==>
  ^nonce_code_rel a s t
Proof
  strip_tac >> qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[bind_def, get_current_context_def, return_def] >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc` >> simp[]
  >- (IF_CASES_TAC >> strip_tac >>
      irule (SRULE [] step_inst_nonce_code) >> metis_tac[]) >>
  strip_tac >> irule (SRULE [] step_inst_inc_pc_nonce_code) >> metis_tac[]
QED

Theorem handle_exception_inl_pops:
  s.contexts <> [] /\ handle_exception e s = (INL x,t) ==>
  LENGTH t.contexts + 1 = LENGTH s.contexts
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  Cases_on `t'` >> simp[]
  >- (Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
      simp[handle_exception_def, bind_def, ignore_bind_def,
           get_gas_left_def, get_current_context_def, return_def,
           consume_gas_def, set_return_data_def, set_current_context_def,
           get_num_contexts_def, reraise_def, assert_def, fail_def,
           AllCaseEqs()]) >>
  PairCases_on `h` >> Cases_on `h0.msgParams.outputTo` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, set_return_data_def, set_current_context_def,
       get_num_contexts_def, get_return_data_def, get_output_to_def,
       reraise_def, assert_def, fail_def, inc_pc_def, push_stack_def,
       write_memory_def, pop_and_incorporate_context_def, pop_context_def,
       set_rollback_def, unuse_gas_def, update_gas_refund_def,
       push_logs_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem handle_step_inl_pops:
  s.contexts <> [] /\ handle_step e s = (INL x,t) ==>
  LENGTH t.contexts + 1 = LENGTH s.contexts
Proof
  strip_tac >> qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- simp[reraise_def] >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  drule_all handle_exception_inl_pops >> simp[]
QED

Theorem handle_exception_length_one:
  LENGTH s.contexts = 1 /\ handle_exception e s = (r,t) ==>
  LENGTH t.contexts = 1
Proof
  Cases_on `s.contexts` >> simp[] >> Cases_on `t'` >> simp[] >>
  PairCases_on `h` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, set_return_data_def, set_current_context_def,
       get_num_contexts_def, reraise_def, assert_def, fail_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem handle_exception_rollback_sources:
  s.contexts <> [] /\ handle_exception e s = (r,t) ==>
  t.rollback = s.rollback \/
  (2 <= LENGTH s.contexts /\ t.rollback = SND (HD s.contexts))
Proof
  strip_tac >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- metis_tac[handle_exception_same_length_preserves_rollback] >>
  drule_all handle_exception_shrinks_by_one >> strip_tac >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  `2 <= LENGTH s.contexts` by
    (Cases_on `LENGTH s.contexts = 1`
     >- (drule_all handle_exception_length_one >> simp[]) >>
     Cases_on `s.contexts` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  PairCases_on `h` >>
  `LENGTH t.contexts < LENGTH s.contexts` by (gvs[] >> decide_tac) >>
  drule_all handle_exception_pop_generic_gen >> simp[]
QED

Theorem handle_step_protected_account:
  s.contexts <> [] /\ handle_step e s = (r,t) /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) /\
  (2 <= LENGTH s.contexts ==>
    (lookup_account a (SND (HD s.contexts)).accounts).nonce <> 0 \/
    ~NULL (lookup_account a (SND (HD s.contexts)).accounts).code) /\
  ((FST (HD s.contexts)).msgParams.outputTo = Code a ==>
    0 < (lookup_account a s.rollback.accounts).nonce) ==>
  (lookup_account a t.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a t.rollback.accounts).code
Proof
  strip_tac >> (
  qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[]) >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  `((lookup_account a s'.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a s'.rollback.accounts).code)` by
      (irule (INST_TYPE [alpha |-> ``:unit``] handle_create_protected_account) >>
       metis_tac[]) >>
  drule_all handle_exception_rollback_sources >> strip_tac >> gvs[])
QED

Theorem step_inner_inr_grow_protected_head:
  wf_state s /\ ^step_inner s = (INR e,u) /\
  LENGTH s.contexts < LENGTH u.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) ==>
  (?mr. (FST (HD u.contexts)).msgParams.outputTo = Memory mr) /\
  ((lookup_account a (SND (HD u.contexts)).accounts).nonce <> 0 \/
   ~NULL (lookup_account a (SND (HD u.contexts)).accounts).code)
Proof
  strip_tac >> (
  `s.contexts <> [] /\ outputTo_consistent s` by
    metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
  gvs[bind_def, get_current_context_def, return_def, fail_def,
      COND_RATOR, vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
      ignore_bind_def]
  >~ [`step_inst Stop`]
  >- (`preserves_same_frame (step_inst Stop)` by simp[] >>
      imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  >~ [`step_inst Invalid`]
  >- (`preserves_same_frame (step_inst Invalid)` by simp[] >>
      imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  >- (`preserves_same_frame (inc_pc_or_jump op)` by simp[] >>
      drule_then drule psf_imp_length_contexts_preserved >>
      (impl_tac >-
        (strip_tac >>
         gvs[inc_pc_or_jump_def, COND_RATOR, AllCaseEqs(), return_def] >>
         gvs[bind_def, AllCaseEqs(), get_current_context_def, fail_def])) >>
      strip_tac >> drule step_inst_inl_grew_is_call >> gvs[] >>
      strip_tac >> gvs[inc_pc_or_jump_def, return_def]) >>
  rename1 `step_inst op s = (INR e,u)` >>
  drule step_inst_inr_grew_is_call_family >>
  (impl_tac >- gvs[]) >>
  reverse (Cases_on `step_inst op s = step_call op s`)
  >- (strip_tac >> gvs[step_inst_def]) >>
  gvs[] >>
  `(SND (HD u.contexts)).accounts = s.rollback.accounts` by
    (irule step_call_grow_saved_accounts >> metis_tac[]) >>
  strip_tac >>
  drule step_call_inr_grow_structure >>
  disch_then (qspecl_then [`u`,`op`,`e`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[])
QED

Theorem step_continuing_collision_current:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  ^collision_protected B t.rollback
Proof
  simp[] >> strip_tac >> qx_gen_tac `a` >> disch_tac >>
  `account_already_created (lookup_account a s.rollback.accounts)` by metis_tac[] >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >>
  simp[step_def, handle_def] >>
  Cases_on `^step_inner s` >> rename1 `^step_inner s = (q,u)` >>
  `^nonce_code_rel a s u` by
    (irule step_inner_nonce_code >> metis_tac[]) >>
  `same_frame_or_grow ^step_inner` by simp[] >>
  `LENGTH s.contexts <= LENGTH u.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `u.contexts <> []` by (strip_tac >> gvs[]) >>
  `account_already_created (lookup_account a u.rollback.accounts)` by
    (gvs[account_already_created_def] >> decide_tac) >>
  Cases_on `q` >> simp[] >> strip_tac
  >- gvs[] >>
  rename1 `handle_step e u = (INL (),t)` >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (drule_all handle_step_inl_pops >> strip_tac >>
      `d < LENGTH s.contexts` by decide_tac >>
      `same_frame_rel s u` by
        (drule_all same_frame_or_grow_eq_length >> simp[]) >>
      `account_already_created (lookup_account a (SND (HD s.contexts)).accounts) /\
       (FST (HD s.contexts)).msgParams.outputTo <> Code a` by
        (Cases_on `s.contexts` >> gvs[] >> metis_tac[]) >>
      `(lookup_account a t.rollback.accounts).nonce <> 0 \/
       ~NULL (lookup_account a t.rollback.accounts).code`
        suffices_by simp[account_already_created_def] >>
      irule handle_step_protected_account >>
      qexistsl_tac [`e`, `INL ()`, `u`] >>
      gvs[same_frame_rel_def, account_already_created_def]) >>
  `LENGTH s.contexts < LENGTH u.contexts` by decide_tac >>
  `((lookup_account a s.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a s.rollback.accounts).code)` by
    gvs[account_already_created_def] >>
  drule_at (Pat `bind _ _ _ = _`) step_inner_inr_grow_protected_head >>
  disch_then (qspec_then `a` mp_tac) >> simp[] >> strip_tac >>
  `(lookup_account a t.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a t.rollback.accounts).code`
    suffices_by simp[account_already_created_def] >>
  irule handle_step_protected_account >>
  qexistsl_tac [`e`, `INL ()`, `u`] >>
  gvs[account_already_created_def]
QED

Theorem step_continuing_collision_protection:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  EVERY (^collision_protected B)
    (t.rollback :: MAP SND (TAKE (LENGTH t.contexts-d) t.contexts))
Proof
  strip_tac >>
  `^collision_protected B t.rollback` by
    (irule step_continuing_collision_current >>
     qexistsl_tac [`d`, `s`, `x`] >> simp[]) >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   outputTo_consistent s /\ EVERY (wf_context o FST) s.contexts` by
    (gvs[wf_state_def] >> metis_tac[outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule step_growth_collision_protection >> simp[] >>
      qexistsl_tac [`INL x`, `s`] >> fs[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by (irule step_same_frame >> metis_tac[]) >>
      irule protected_rollbacks_same_frame_transport >> simp[] >>
      qexists_tac `s` >> fs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_structure >> strip_tac >>
  irule protected_rollbacks_pop_transport >> simp[] >>
  qexistsl_tac [`HD s.contexts`, `parent`, `s`] >> fs[]
QED

Theorem step_continuing_protected_frames:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts-d) t.contexts))
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   outputTo_consistent s /\ EVERY (wf_context o FST) s.contexts` by
    (gvs[wf_state_def] >> metis_tac[outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule step_growth_protected_frames >> simp[] >>
      qexistsl_tac [`INL x`, `s`] >> fs[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by (irule step_same_frame >> metis_tac[]) >>
      irule protected_frames_same_frame_transport >>
      qexists_tac `s` >> simp[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_structure >> strip_tac >>
  irule protected_frames_pop_transport >> simp[] >>
  qexistsl_tac [`HD s.contexts`, `parent`, `s`] >> fs[]
QED

(* Single-step preservation of run_call_inv, by length-change cases. *)

Theorem run_call_inv_step:
  ∀es s s' q r.
    es.contexts ≠ [] ∧
    run_call_inv es q s ∧ ISL q ∧
    LENGTH es.contexts ≤ LENGTH s.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es r s'
Proof
  rpt gen_tac >> strip_tac >>
  fs[run_call_inv_def] >>
  `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[]) >>
  `s.contexts <> [] /\ outputTo_consistent s` by
    metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
  `wf_state s'` by metis_tac[step_preserves_wf_state, SND] >>
  `s'.txParams = es.txParams` by
    metis_tac[vfmTxParamsTheory.step_preserves_txParams, SND] >>
  simp[run_call_inv_def] >>
  conj_tac >- gvs[wf_state_def] >>
  conj_tac >- suspend "storage" >>
  strip_tac >> Cases_on `r` >> gvs[] >>
  conj_tac
  >- (`EVERY (^collision_protected es.rollback)
        (s'.rollback :: MAP SND
          (TAKE (LENGTH s'.contexts - LENGTH es.contexts) s'.contexts))`
        suffices_by simp[] >>
      irule step_continuing_collision_protection >>
      simp[] >> qexists_tac `s` >> simp[]) >>
  irule step_continuing_protected_frames >>
  simp[] >> qexists_tac `s` >> simp[]
QED

Resume run_call_inv_step[storage]:
  qmatch_goalsub_abbrev_tac `EVERY P (active_rollbacks _ s')` >>
  `EVERY P (active_rollbacks (LENGTH es.contexts) s)` by fs[Abbr `P`] >>
  `P s.rollback` by gvs[active_rollbacks_def] >>
  Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s s'` by metis_tac[step_same_frame] >>
      irule active_rollbacks_same_frame_transport >>
      reverse conj_tac >- (qexists_tac `s` >> simp[]) >>
      simp[Abbr `P`] >> rpt gen_tac >> disch_tac >>
      drule_all step_preserves_non_accessed_storage >> strip_tac >>
      `~fIN (SK a k) s.rollback.accesses.storageKeys` by
        (fs[same_frame_rel_def, SUBSET_DEF, finite_setTheory.fIN_IN] >>
         metis_tac[]) >> fs[]) >>
  Cases_on `LENGTH s.contexts < LENGTH s'.contexts`
  >- suspend "push_storage" >>
  suspend "pop_storage"
QED

Resume run_call_inv_step[push_storage]:
  drule step_push_structure >> (impl_tac >- simp[]) >> strip_tac >>
  `P s'.rollback` by
    (simp[Abbr `P`] >> rpt gen_tac >> disch_tac >>
     irule storage_slots_compose >> simp[] >>
     qexists_tac `s.rollback` >> fs[] >>
     qx_gen_tac `address` >> qx_gen_tac `key` >> disch_tac >>
     qpat_x_assum `!a. _ \/ _` (qspec_then `address` strip_assume_tac) >>
     simp[lookup_storage_def, empty_storage_def]) >>
  irule active_rollbacks_push_transport >> simp[ADD1] >>
  qexistsl_tac [`P`,
    `\rb next. toSet rb.accesses.storageKeys SUBSET toSet next.accesses.storageKeys /\
       (!a. (lookup_account a next.accounts).storage =
            (lookup_account a rb.accounts).storage)`, `s`] >>
  simp[] >>
  map_every qx_gen_tac [`rb`, `next`] >> strip_tac >>
  fs[Abbr `P`] >> rpt gen_tac >> disch_tac >>
  `~fIN (SK a k) rb.accesses.storageKeys` by
    (fs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[]) >>
  fs[]
QED

Resume run_call_inv_step[pop_storage]:
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  `EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  drule_all step_pop_structure >>
  disch_then (qx_choosel_then [`head`, `parent`, `rest`] strip_assume_tac) >>
  `2 <= LENGTH s.contexts` by
    (qpat_assum `s.contexts = _` (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `P (SND (HD s.contexts))` by
    (`MEM (SND (HD s.contexts)) (active_rollbacks (LENGTH es.contexts) s)` by
       (irule (cj 2 active_rollbacks_pop_sources) >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `?source. P source /\
    toSet source.accesses.storageKeys SUBSET toSet s'.rollback.accesses.storageKeys /\
    (!a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a source.accounts).storage)` by metis_tac[] >>
  `P s'.rollback` by
    (fs[Abbr `P`] >> rpt gen_tac >> disch_tac >>
     `~fIN (SK a k) source.accesses.storageKeys` by
       (fs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[]) >>
     fs[] >> metis_tac[]) >>
  irule active_rollbacks_pop_transport >>
  simp[] >> qexistsl_tac [`HD s.contexts`, `parent`, `s`] >> fs[]
QED

Finalise run_call_inv_step

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
    run_call_inv es res es'
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by fs[wf_state_def]
  >> gvs[run_call_def]
  >> `(λ p. run_call_inv es (FST p) (SND p)) (res, es')` suffices_by simp[]
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
  >> qexistsl_tac [`r''`, `s''`]
  >> simp[]
QED

(* A slot nobody accessed keeps its value, unless a CREATE cleared the
   storage of an address that had no nonce and no code (EELS
   process_create_message destroys the old storage). *)
Theorem run_call_preserves_storage_outside_accessed_slots:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def, active_rollbacks_saved]
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
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)
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
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)
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
