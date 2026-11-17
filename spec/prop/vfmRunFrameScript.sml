Theory vfmRunFrame
Ancestors
  arithmetic combin list option pair sum While
  vfmExecution vfmExecutionProp vfmDecreasesGas vfmStepLength
  vfmHandleStep vfmContextLength vfmWfState
Libs
  BasicProvers

Theorem step_frame_inl_eq_step[local]:
  step_frame s = (INL (),t) ==> step s = (INL (),t)
Proof
  simp[step_frame_def, GSYM step_inner_def,
       step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> simp[] >>
  rename1 `step_inner s = (INR e,u)` >>
  Cases_on `vfm_abort e` >> simp[reraise_def] >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts` >> simp[] >>
  simp[handle_step_def, handle_def] >>
  metis_tac[handle_create_INR, sumTheory.INL_11, sumTheory.INR_neq_INL,
            pairTheory.PAIR_EQ]
QED

Theorem step_frame_inl_length[local]:
  wf_state s /\ step_frame s = (INL (),t) ==>
  LENGTH s.contexts <= LENGTH t.contexts
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  drule step_frame_inl_eq_step >> strip_tac >>
  qhdtm_x_assum `step_frame` mp_tac >>
  simp[step_frame_def, GSYM step_inner_def, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> simp[]
  >- (strip_tac >> gvs[] >>
      drule_at (Pat `m s = _`) same_frame_or_grow_length >> simp[]) >>
  rename1 `step_inner s = (INR e,u)` >>
  Cases_on `vfm_abort e` >> simp[reraise_def] >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- metis_tac[handle_create_INR, sumTheory.INR_neq_INL,
               pairTheory.PAIR_EQ] >>
  strip_tac >>
  `handle_step e u = (INL (),t)` by
    gvs[step_eq_handle_step_inner, handle_def] >>
  `LENGTH s.contexts <= LENGTH u.contexts` by
    (qpat_assum `step_inner s = _`
       (mp_then (Pat `m s = _`) mp_tac same_frame_or_grow_length) >> simp[]) >>
  `u.contexts <> []` by (strip_tac >> gvs[]) >>
  drule_at (Pat `handle_step`) handle_step_shrinks_by_one >> simp[]
QED

Theorem step_frame_nonabort_boundary[local]:
  wf_state s /\ step_frame s = (INR e,t) /\ ~vfm_abort e ==>
  LENGTH t.contexts = LENGTH s.contexts /\
  step s = handle_exception e t /\
  ~(ISL (FST (handle_exception e t)) /\
    LENGTH (SND (handle_exception e t)).contexts >= LENGTH s.contexts)
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step_frame` mp_tac >>
  simp[step_frame_def, GSYM step_inner_def, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> simp[] >>
  rename1 `step_inner s = (INR err,u)` >>
  Cases_on `vfm_abort err`
  >- (simp[reraise_def] >> rpt strip_tac >> gvs[]) >>
  simp[] >>
  `LENGTH s.contexts <= LENGTH u.contexts` by
    (drule_at (Pat `m s = _`) same_frame_or_grow_length >> simp[]) >>
  `u.contexts <> []` by (strip_tac >> gvs[]) >>
  `EVERY (wf_context o FST) u.contexts` by
    (mp_tac decreases_gas_cred_step_inner >>
     simp[decreases_gas_cred_def] >>
     disch_then (qspec_then `s` mp_tac) >> gvs[wf_state_def]) >>
  `stack_room_ok u /\ gas_stack_ok u` by
    (irule vfmRunCallTheory.step_inner_preserves_stack_room_gas_ok >>
     metis_tac[]) >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (simp[] >> strip_tac >>
      `LENGTH t.contexts = LENGTH s.contexts` by
        metis_tac[handle_create_preserves_length] >>
      simp[] >> conj_tac
      >- simp[step_eq_handle_step_inner, handle_def, handle_step_def] >>
      `t.contexts <> []` by (strip_tac >> gvs[]) >>
      Cases_on `handle_exception e t` >> Cases_on `q` >> simp[] >>
      drule_all vfmRunCallTheory.handle_exception_inl_pops >> simp[]) >>
  simp[] >> strip_tac >>
  `handle_step err u = (INR e,t)` by
    simp[handle_step_def, handle_def] >>
  `LENGTH u.contexts >= 2` by
    (Cases_on `s.contexts` >> gvs[]) >>
  drule handle_step_not_abort_returns_inl >> simp[]
QED

Theorem frame_loop_terminates_if_continuations_agree[local]:
  (!s. ISL (FST ((f:'a -> (unit + 'b) # 'a) s)) ==> f s = g s) /\
  OWHILE (ISL o FST) (g o SND) p = SOME z ==>
  ?w. OWHILE (ISL o FST) (f o SND) p = SOME w
Proof
  strip_tac >>
  qpat_x_assum `OWHILE _ _ _ = _` mp_tac >>
  map_every qid_spec_tac [`z`, `p`] >>
  ho_match_mp_tac OWHILE_IND >> conj_tac
  >- (rpt strip_tac >> simp[Once OWHILE_THM]) >>
  rpt strip_tac >>
  rename1 `(ISL o FST) q` >>
  Cases_on `ISL (FST (f (SND q)))`
  >- (simp[Once OWHILE_THM] >> gvs[]) >>
  simp[Once OWHILE_THM] >>
  qexists_tac `f (SND q)` >> simp[Once OWHILE_THM]
QED

Theorem run_frame_inr:
  run_frame es = SOME (r, es1) ⇒ ISR r
Proof
  simp[run_frame_def] >> strip_tac >>
  drule OWHILE_ENDCOND >> Cases_on `r` >> simp[]
QED

Theorem run_frame_length:
  wf_state es ∧ run_frame es = SOME (INR e, es1) ∧ ¬vfm_abort e ⇒
  LENGTH es1.contexts = LENGTH es.contexts
Proof
  cheat
QED

Theorem run_frame_call:
  wf_state es ∧ run_frame es = SOME (INR e, es1) ∧ ¬vfm_abort e ⇒
  run_call es = SOME (handle_exception e es1)
Proof
  cheat
QED

Theorem run_call_imp_run_frame:
  run_call es = SOME r ⇒
  ∃e es1. run_frame es = SOME (INR e, es1)
Proof
  cheat
QED
