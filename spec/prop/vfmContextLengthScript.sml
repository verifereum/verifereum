(* Context-stack length theorems for run and run_call.
 * Non-abort termination exits at the relevant frame boundary. *)
Theory vfmContextLength
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  While vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame vfmStepLength vfmMsdomainPreserved vfmHandleStep
  vfmRunWithinFrame vfmRunCall
Libs
  BasicProvers dep_rewrite

(* handle_step length on non-abort INR outputs. *)

Theorem handle_step_inr_not_abort_length:
  handle_step e s = (INR e', s') ∧ s.contexts ≠ [] ∧ EVERY (wf_context o FST) s.contexts ∧ ¬vfm_abort e ⇒
    if LENGTH s.contexts ≥ 2 then LENGTH s'.contexts = LENGTH s.contexts - 1
    else LENGTH s'.contexts = LENGTH s.contexts
Proof
  rpt strip_tac >> IF_CASES_TAC
  >- (
    `LENGTH s'.contexts + 1 = LENGTH s.contexts`
      by metis_tac[handle_step_not_abort_pops] >>
    simp[])
  >- (
    `LENGTH s.contexts = 1` by (
      Cases_on`s.contexts` >> gvs[]
      >> Cases_on`t` >> gvs[] ) >>
    metis_tac[handle_step_preserves_length_1])
QED

Theorem handle_step_inr_not_abort_length_bound:
  handle_step e s = (INR e', s') ∧ s.contexts ≠ [] ∧ EVERY (wf_context o FST) s.contexts ∧ ¬vfm_abort e ⇒
    LENGTH s'.contexts = LENGTH s.contexts ∨
    LENGTH s'.contexts + 1 = LENGTH s.contexts
Proof
  rpt strip_tac
  >> Cases_on `LENGTH s.contexts ≥ 2`
  >- (
    `LENGTH s'.contexts + 1 = LENGTH s.contexts`
      by metis_tac[handle_step_not_abort_pops] >>
    disj2_tac >> simp[])
  >- (
    `LENGTH s.contexts = 1` by (
      Cases_on`s.contexts` >> gvs[] >>
      Cases_on`t` >> gvs[] ) >>
    `LENGTH s'.contexts = 1`
        by metis_tac[handle_step_preserves_length_1] >>
    disj1_tac >> simp[])
QED

(* step length on non-abort INR outputs. *)

Theorem step_inr_not_abort_length:
  step s = (INR e, s') ∧ s.contexts ≠ [] ∧ EVERY (wf_context o FST) s.contexts ∧
  outputTo_consistent s ∧ ¬vfm_abort e ⇒
    LENGTH s'.contexts = LENGTH s.contexts ∨
    LENGTH s'.contexts + 1 = LENGTH s.contexts
Proof
  rpt strip_tac
  >> qhdtm_x_assum `step` mp_tac
  >> simp[step_eq_handle_step_inner, handle_def]
  >> Cases_on `step_inner s` >> Cases_on `q` >> gvs[]
  >> rename1 `step_inner s = (INR e_inner, s_mid)`
  >> strip_tac
  >> `same_frame_or_grow step_inner` by simp[]
  >> `s_mid.contexts ≠ []`
       by (strip_tac
           >> drule_all same_frame_or_grow_length >> simp[]
           >> Cases_on`s.contexts` >> gvs[])
  >> `EVERY (wf_context o FST) s_mid.contexts`
       by (mp_tac decreases_gas_cred_step_inner >>
           gvs[decreases_gas_cred_def] >>
           disch_then(qspec_then`s` mp_tac) >> rw[] )
  >> Cases_on `LENGTH s_mid.contexts = LENGTH s.contexts`
  >- (
    (* inner same-frame *)
    `same_frame_rel s s_mid`
        by (drule_all same_frame_or_grow_eq_length >> simp[]) >>
    drule handle_step_inr_not_abort_length_bound >> simp[] >>
    impl_keep_tac
    >- (
      strip_tac >>
        (* vfm_abort e_inner: handle_step reraises, so e = e_inner *)
        gvs[handle_step_def] >>
        `¬vfm_abort e` by simp[] >>
        gvs[reraise_def])
      >> simp[])
  >- (
    (* inner grew by exactly 1 *)
    `LENGTH s_mid.contexts = LENGTH s.contexts + 1`
        by (
          qpat_x_assum `step_inner s = _` mp_tac >>
          simp[step_inner_def] >> strip_tac >>
          drule_then drule step_inner_grows_by_exactly_one >>
          disch_then irule >>
          drule same_frame_or_grow_length >>
          simp[step_inner_def] >> disch_then drule >> simp[]) >>
    `¬vfm_abort e_inner`
        by (irule step_inner_inr_grow_not_abort >>
          qpat_x_assum `step_inner s = _` mp_tac >> simp[step_inner_def] >>
          strip_tac >> goal_assum $ drule_at Any >> simp[] ) >>
    `LENGTH s_mid.contexts ≥ 2` by (
      Cases_on`s_mid.contexts` >> gvs[] >>
      Cases_on`s.contexts` >> gvs[] ) >>
    `LENGTH s'.contexts + 1 = LENGTH s_mid.contexts`
        by metis_tac[handle_step_not_abort_pops] >>
    disj1_tac >> simp[])
QED

(* At depth ≥ 2, non-abort handle_step returns INL. *)

Theorem handle_step_not_abort_returns_inl:
  handle_step e s = (q, s') ∧ LENGTH s.contexts ≥ 2 ∧
  EVERY (wf_context o FST) s.contexts ∧ stack_room_ok s ∧ gas_stack_ok s ∧
  ¬vfm_abort e ⇒
    ISL q
Proof
  rpt strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def]
  >> CASE_TAC
  >> CASE_TAC
  >> rw[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> `s.contexts <> []` by (strip_tac >> gs[])
  >> drule_at(Pat`handle_create`) handle_create_preserves_wf_contexts
  >> impl_tac >- (gs[]) >> strip_tac
  >> `stack_room_ok s1` by metis_tac[handle_create_preserves_stack_room_ok]
  >> `gas_stack_ok s1` by metis_tac[handle_create_preserves_gas_stack_ok]
  >> drule_at(Pat`handle_exception`) handle_exception_ge_2_inl
  >> simp[] >> disch_then irule
  >> drule handle_create_preserves_length
  >> rw[]
QED

(* A step cannot return non-abort INR at depth ≥ 2. *)

Theorem step_ge2_inr_is_abort:
  step s = (INR e, s') ∧ LENGTH s.contexts ≥ 2 ∧
  wf_state s ∧ outputTo_consistent s ∧ ¬vfm_abort e ⇒
    F
Proof
  rpt strip_tac
  >> qhdtm_x_assum `step` mp_tac
  >> simp[step_eq_handle_step_inner, handle_def]
  >> Cases_on `step_inner s` >> Cases_on `q` >> gvs[]
  >> rename1 `step_inner s = (INR e_inner, s_mid)`
  >> strip_tac
  >> `same_frame_or_grow step_inner` by simp[]
  >> `s.contexts ≠ []` by (strip_tac >> gvs[])
  >> `s_mid.contexts ≠ []`
       by (strip_tac >> drule_all same_frame_or_grow_length >> simp[])
  >> `EVERY (wf_context o FST) s_mid.contexts`
       by (mp_tac decreases_gas_cred_step_inner >>
           gvs[decreases_gas_cred_def] >>
           disch_then(qspec_then`s` mp_tac) >> rw[] >>
           gvs[wf_state_def] )
  >> `stack_room_ok s_mid ∧ gas_stack_ok s_mid`
       by (irule step_inner_preserves_stack_room_gas_ok >> metis_tac[])
  >> Cases_on `vfm_abort e_inner`
  >- (
    (* aborts reraise, contradicting the final non-abort result *)
    `handle_step e_inner s_mid = (INR e_inner, s_mid)`
        by (gvs[handle_step_def, reraise_def])
    >> gvs[])
  >- (
    (* ¬vfm_abort e_inner *)
    Cases_on `LENGTH s_mid.contexts ≥ 2`
    >- (
      drule handle_step_not_abort_returns_inl >> simp[]
      >> `handle_step e_inner s_mid = (INR e, s')` by simp[]
      >> gvs[])
    >> (* LENGTH s_mid ≥ LENGTH s ≥ 2, contradiction. *)
       `LENGTH s_mid.contexts ≥ LENGTH s.contexts`
           by (drule_all same_frame_or_grow_length >> simp[])
       >> gvs[])
QED

(* run terminates at depth 1 under non-abort termination. *)

Theorem run_contexts_length_1:
  run s = SOME (r, es') ∧ wf_state s ∧ (∀e. r = INR e ⇒ ¬vfm_abort e)
  ⇒ LENGTH es'.contexts = 1
Proof
  rpt strip_tac
  >> `s.contexts <> []` by (strip_tac >> gvs[wf_state_def])
  >> `es'.contexts ≠ []`
       by (drule_all run_preserves_nonempty_contexts >> simp[])
  >> `LENGTH es'.contexts ≥ 1` by (Cases_on`es'.contexts` >> gvs[])
  >> CCONTR_TAC
  >> `LENGTH es'.contexts ≥ 2` by simp[]
  >> qpat_x_assum `run s = SOME _` mp_tac
  >> simp[run_def]
  >> strip_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac`OWHILE G f s1 = SOME s2`
  >> `(λp. wf_state (SND p) ∧
           ∀e. FST p = INR e ∧ ¬vfm_abort e ⇒
               LENGTH (SND p).contexts = 1) s2` by (
    irule (MP_CANON OWHILE_INV_IND)
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> simp[Abbr`s1`]
    >> rpt gen_tac
    >> PairCases_on `x` >> gvs[Abbr`G`, Abbr`f`]
    >> Cases_on `step x1` >> simp[]
    >> strip_tac
    >> conj_tac >- (drule step_preserves_wf_state >> simp[])
    >> rpt strip_tac >> gvs[]
    >> rename1 `step x1 = (INR e, st')`
    >> `x1.contexts ≠ []` by gvs[wf_state_def]
    >> `outputTo_consistent x1`
    by (
        gvs[wf_state_def,outputTo_consistent_def] >>
        gvs[outputTo_consistent_stack_def] >>
        Cases_on`x1.contexts` >> gvs[outputTo_consistent_ctx_def] >>
        strip_tac >> gvs[] )
    >> Cases_on `LENGTH x1.contexts ≥ 2`
    >- (drule step_ge2_inr_is_abort >> simp[])
    >> `LENGTH x1.contexts = 1`
    by (Cases_on `x1.contexts` >> gvs[] >> Cases_on `t` >> gvs[])
    >> `wf_state st'` by (drule step_preserves_wf_state >> simp[])
    >> drule step_inr_not_abort_length >> simp[]
    >> gvs[wf_state_def])
  >> gvs[Abbr`s2`, Abbr`G`]
  >> drule OWHILE_ENDCOND
  >> Cases_on `r` >> gvs[]
QED

(* Single-context convenience form: *)
Theorem run_length_1_single:
  es.contexts = [(ctx, es.rollback)] ∧ wf_context ctx ∧
  wf_accounts es.rollback.accounts ∧
  outputTo_consistent_ctx ctx ∧
  run es = SOME (r, es') ∧ (∀e. r = INR e ⇒ ¬vfm_abort e) ⇒
    LENGTH es'.contexts = 1
Proof
  rpt strip_tac
  >> `LENGTH es.contexts = 1` by simp[]
  >> drule run_contexts_length_1 >> simp[]
  >> disch_then irule
  >> gvs[wf_state_def, all_accounts_def]
  >> gvs[stack_room_ok_def,gas_stack_ok_def,outputTo_consistent_stack_def]
  >> gvs[outputTo_consistent_def,outputTo_consistent_ctx_def]
QED

(* run_call exits at the starting-frame boundary. *)

Theorem run_call_inr_length:
  wf_state es ∧ run_call es = SOME (INR e, es') ∧ ¬vfm_abort e ⇒
    LENGTH es'.contexts = LENGTH es.contexts
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by fs[wf_state_def]
  >> Cases_on `LENGTH es.contexts = 1`
  >- (
    (* singleton call is just run *)
    drule run_call_eq_run_single_context >> simp[]
    >> strip_tac
    >> `run es = SOME (INR e, es')` by fs[]
    >> irule run_contexts_length_1 >> simp[]
    >> goal_assum $ drule_at Any
    >> simp[] )
  >- (
    (* depth ≥ 2 cannot terminate with non-abort INR *)
    spose_not_then assume_tac
    >> gvs[run_call_def]
    >> qabbrev_tac `n = LENGTH es.contexts`
    >> `(λp. wf_state (SND p) ∧
             ∀e. FST p = (INR e:unit + exception option) ∧
                         ¬vfm_abort e ⇒ F) (INR e, es')` by (
      irule (MP_CANON OWHILE_INV_IND)
      >> qmatch_asmsub_abbrev_tac`OWHILE G f`
      >> qexistsl_tac[`G`,`f`]
      >> goal_assum $ drule_at Any
      >> simp[]
      >> rpt gen_tac
      >> PairCases_on `x` >> gvs[Abbr`f`]
      >> Cases_on `step x1` >> simp[]
      >> strip_tac
      >> conj_tac >- (drule step_preserves_wf_state >> simp[])
      >> rpt strip_tac >> gvs[]
      >> rename1 `step s1 = (INR e', st')`
      >> drule step_ge2_inr_is_abort
      >> simp[Abbr`n`] >> strip_tac >> gvs[Abbr`G`]
      >- (Cases_on`es.contexts` >> gvs[] >> Cases_on`t` >> gvs[])
      >> gvs[outputTo_consistent_def, wf_state_def, outputTo_consistent_stack_def]
      >> Cases_on`s1.contexts` >> fs[]
      >> gs[outputTo_consistent_ctx_def] )
    >> gvs[] )
QED

Theorem step_length_not_drop_more_than_one:
  wf_state s ∧ step s = (r, s') ⇒
    LENGTH s.contexts ≤ LENGTH s'.contexts + 1
Proof
  rpt strip_tac
  >> Cases_on `LENGTH s'.contexts < LENGTH s.contexts`
  >- (
    drule step_pop_structure
    >> impl_tac >- gvs[wf_state_def]
    >> strip_tac >> gvs[]
    >> Cases_on`s.contexts` >> gvs[] )
  >> decide_tac
QED

Theorem run_call_inl_length:
  wf_state es ∧ run_call es = SOME (INL (), es') ⇒
    LENGTH es'.contexts + 1 = LENGTH es.contexts
Proof
  rpt strip_tac
  >> gvs[run_call_def]
  >> qabbrev_tac `n = LENGTH es.contexts`
  >> `(λp. wf_state (SND p) ∧ n ≤ LENGTH (SND p).contexts + 1)
        (INL () : unit + exception option, es')` by (
    irule (MP_CANON OWHILE_INV_IND)
    >> goal_assum $ drule_at Any
    >> simp[Abbr`n`]
    >> qx_gen_tac`s`
    >> PairCases_on `s` >> simp[]
    >> strip_tac
    >> Cases_on `step s1` >> simp[]
    >> conj_tac >- (drule step_preserves_wf_state >> simp[])
    >> drule step_length_not_drop_more_than_one >> simp[])
  >> gvs[Abbr`n`]
  >> drule OWHILE_ENDCOND
  >> simp[]
QED

Theorem run_call_length:
  wf_state es ∧ run_call es = SOME (r, es') ∧
  (∀e. r = INR e ⇒ ¬vfm_abort e) ⇒
    case r of
    | INR e => LENGTH es'.contexts = LENGTH es.contexts
    | INL () => LENGTH es'.contexts + 1 = LENGTH es.contexts
Proof
  Cases_on `r` >> simp[]
  >- metis_tac[run_call_inl_length]
  >> metis_tac[run_call_inr_length]
QED

(* At starting depth ≥ 2, INR termination must be aborting. *)
Theorem run_call_inr_requires_abort_ge2:
  LENGTH es.contexts ≥ 2 ∧ wf_state es ∧
  run_call es = SOME (INR e, es')
  ⇒ vfm_abort e
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> `¬vfm_abort e` by simp[]
  >> gvs[run_call_def]
  >> `(λp. wf_state (SND p) ∧
           ∀e. FST p = INR e ∧ ¬vfm_abort e ⇒ F)
      (INR e : unit + exception option, es')` by (
    irule (MP_CANON OWHILE_INV_IND)
    >> goal_assum $ drule_at Any
    >> simp[]
    >> qx_gen_tac`s`
    >> PairCases_on `s` >> gvs[]
    >> Cases_on `step s1` >> simp[] >> strip_tac
    >> conj_tac >- (drule step_preserves_wf_state >> simp[])
    >> rpt strip_tac >> gvs[]
    >> rename1 `step s1 = (INR e', st')`
    >> drule step_ge2_inr_is_abort
    >> simp[]
    >> gvs[outputTo_consistent_def,wf_state_def,outputTo_consistent_stack_def]
    >> Cases_on`s1.contexts` >> gvs[outputTo_consistent_ctx_def]
    >> strip_tac >> gvs[] )
  >> gvs[]
QED

(* Single-context convenience form: *)
Theorem run_call_inr_length_single:
  outputTo_consistent_ctx ctx ∧ wf_context ctx ∧ ctx.jumpDest = NONE ∧
  wf_accounts es.rollback.accounts ∧
  es.contexts = [(ctx, es.rollback)] ∧
  run_call es = SOME (INR e, es') ∧ ¬vfm_abort e ⇒
    LENGTH es'.contexts = 1
Proof
  rpt strip_tac
  >> drule_at Any run_call_inr_length
  >> disch_then(drule_at Any)
  >> simp[] >> disch_then irule
  >> gvs[outputTo_consistent_stack_def, wf_state_def, all_accounts_def,
         storage_slot_preserved_def, gas_stack_ok_def, stack_room_ok_def]
QED
