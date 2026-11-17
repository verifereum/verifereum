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

Theorem run_frame_loop_boundary[local]:
  !n p z.
  OWHILE (ISL o FST)
    (\(r,u). if LENGTH u.contexts = n then step_frame u else step u)
    p = SOME z ==>
  (~ISL (FST p) ==> p = z) /\
  !s e t. p = (INL (),s) /\ z = (INR e,t) /\
    wf_state s /\ 0 < n /\ n <= LENGTH s.contexts /\ ~vfm_abort e ==>
    LENGTH t.contexts = n /\
    OWHILE (\(r,u). ISL r /\ LENGTH u.contexts >= n)
      (step o SND) (INL (),s) = SOME (handle_exception e t)
Proof
  gen_tac >> ho_match_mp_tac OWHILE_IND >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (Cases_on `FST p` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `LENGTH s.contexts = n`
  >- (gvs[] >> Cases_on `step_frame s` >> Cases_on `q` >> gvs[]
      >- (drule_all step_frame_inl_length >> strip_tac >>
          drule step_frame_inl_eq_step >> strip_tac >>
          `wf_state r` by metis_tac[step_preserves_wf_state, SND] >>
          simp[Once OWHILE_THM] >> first_x_assum irule >> simp[]) >>
      drule_all step_frame_nonabort_boundary >> strip_tac >>
      Cases_on `handle_exception e r` >> Cases_on `q` >> gvs[] >>
      simp[Once OWHILE_THM] >> simp[Once OWHILE_THM]) >>
  gvs[] >> Cases_on `step s` >> Cases_on `q` >> gvs[]
  >- (drule_all step_length_not_drop_more_than_one >> strip_tac >>
      `wf_state r` by metis_tac[step_preserves_wf_state, SND] >>
      `n <= LENGTH r.contexts` by decide_tac >>
      simp[Once OWHILE_THM] >> first_x_assum irule >> simp[]) >>
  `outputTo_consistent s` by
    metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
  `LENGTH s.contexts >= 2` by decide_tac >>
  metis_tac[step_ge2_inr_is_abort]
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
  simp[run_frame_def] >> strip_tac >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  drule (cj 2 run_frame_loop_boundary) >> simp[]
QED

Theorem run_frame_call:
  wf_state es ∧ run_frame es = SOME (INR e, es1) ∧ ¬vfm_abort e ⇒
  run_call es = SOME (handle_exception e es1)
Proof
  simp[run_frame_def, run_call_def] >> strip_tac >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  drule (cj 2 run_frame_loop_boundary) >> simp[]
QED

Theorem run_call_imp_run_frame:
  run_call es = SOME r ⇒
  ∃e es1. run_frame es = SOME (INR e, es1)
Proof
  strip_tac >>
  `?z. OWHILE (ISL o FST) (step o SND) (INL (),es) = SOME z` by
    (mp_tac (Q.SPEC `es` (GEN_ALL run_eq_tr)) >>
     Cases_on `run_tr (step es)` >> simp[run_def]) >>
  `?w. OWHILE (ISL o FST)
    ((\s. if LENGTH s.contexts = LENGTH es.contexts
          then step_frame s else step s) o SND) (INL (),es) = SOME w` by
    (irule frame_loop_terminates_if_continuations_agree >>
     qexistsl_tac [`step`, `z`] >> simp[] >>
     gen_tac >> Cases_on `LENGTH s.contexts = LENGTH es.contexts` >>
     simp[] >> Cases_on `step_frame s` >> Cases_on `q` >>
     simp[] >> rename1 `step_frame s = (INL a,t)` >>
     Cases_on `a` >> drule step_frame_inl_eq_step >> simp[]) >>
  `?w. run_frame es = SOME w` by
    (gvs[run_frame_def, o_DEF, ELIM_UNCURRY]) >>
  rename1 `run_frame es = SOME out` >>
  Cases_on `out` >> drule run_frame_inr >>
  Cases_on `q` >> simp[] >> metis_tac[]
QED
