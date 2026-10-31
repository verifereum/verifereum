Theory vfmCallReturn
Ancestors vfmCallInner vfmRunCall vfmContextLength vfmDomainCollection
          vfmExecutionProp vfmExecution vfmState vfmContext vfmTypes
          vfmDecreasesGas vfmStepLength arithmetic list pair While

Theorem call_meter_step_collect_not_outside:
  s.msdomain = Collect dd /\ step s = (r,t) ==>
  r <> INR (SOME (OutsideDomain x))
Proof
  strip_tac >> mp_tac step_computes_minimal_domain >>
  rewrite_tac[computes_minimal_domain_def] >> disch_then drule >> simp[]
QED

Theorem call_meter_step_inner_handler_state:
  wf_state s /\ 2 <= LENGTH s.contexts /\ step_inner s = (r,t) ==>
  2 <= LENGTH t.contexts /\ EVERY (wf_context o FST) t.contexts /\
  stack_room_ok t /\ gas_stack_ok t
Proof
  rpt strip_tac
  >- (`s.contexts <> []` by (strip_tac >> gvs[]) >>
      `LENGTH s.contexts <= LENGTH t.contexts` by
        metis_tac[same_frame_or_grow_step_inner_named,
                  same_frame_or_grow_length, GREATER_EQ] >> decide_tac)
  >- (irule step_inner_contexts_wf >> goal_assum (drule_at Any) >>
      gvs[wf_state_def])
  >- metis_tac[step_inner_preserves_stack_room_gas_ok] >>
  metis_tac[step_inner_preserves_stack_room_gas_ok]
QED

Theorem call_meter_step_collect_inl:
  wf_state s /\ call_meter_budget n ceiling s /\
  2 <= n /\ n <= LENGTH s.contexts /\ s.msdomain = Collect dd /\
  step s = (r,t) ==> ISL r
Proof
  strip_tac >>
  `0 < n /\ 2 <= LENGTH s.contexts /\ s.contexts <> []` by
    (Cases_on `s.contexts` >> gvs[]) >>
  `!x. r <> INR (SOME (OutsideDomain x))` by
    metis_tac[call_meter_step_collect_not_outside] >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> gvs[] >>
  rename1 `step_inner s = (INR err, mid)` >> strip_tac >>
  `0 < n /\ n <= LENGTH s.contexts` by simp[] >>
  `err <> SOME Impossible /\ err <> SOME Unimplemented` by
    (drule_all call_meter_step_inner_budget >> simp[]) >>
  Cases_on `vfm_abort err`
  >- (gvs[handle_step_def, reraise_def] >>
      Cases_on `err` >> gvs[vfm_abort_def] >>
      Cases_on `x` >> gvs[vfm_abort_def] >> metis_tac[]) >>
  `2 <= LENGTH s.contexts` by decide_tac >>
  drule_all call_meter_step_inner_handler_state >> strip_tac >>
  irule handle_step_not_abort_returns_inl >>
  goal_assum (drule_at Any) >> simp[GREATER_EQ] >> metis_tac[]
QED

Theorem call_meter_run_call_collect_inl:
  wf_state es /\ call_meter_budget (LENGTH es.contexts) ceiling es /\
  es.msdomain = Collect dd /\ 2 <= LENGTH es.contexts /\
  run_call es = SOME (r,t) ==> ISL r
Proof
  strip_tac >>
  `(\p. ISL (FST p) /\ wf_state (SND p) /\
      call_meter_budget (LENGTH es.contexts) ceiling (SND p) /\
      ?d. (SND p).msdomain = Collect d) (r,t)` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  qexists `\(r,s). ISL r /\ LENGTH es.contexts <= LENGTH s.contexts` >>
  qexists `step o SND` >>
  qexists `(INL () : unit + exception option,es)` >> simp[] >>
  reverse conj_tac >- fs[run_call_def, GREATER_EQ, UNCURRY] >>
  qx_gen_tac `st` >> PairCases_on `st` >> simp[] >> strip_tac >>
  Cases_on `step st1` >> simp[] >>
  conj_tac >- metis_tac[call_meter_step_collect_inl] >>
  conj_tac >- (drule step_preserves_wf_state >> simp[]) >>
  conj_tac >- (drule_all call_meter_step_budget >> simp[]) >>
  irule step_preserves_collect >> metis_tac[]
QED

Theorem call_meter_run_call_preserves_collect:
  es.msdomain = Collect dd /\ run_call es = SOME (r,t) ==>
  ?dd'. t.msdomain = Collect dd'
Proof
  strip_tac >>
  `(\p. ?d. (SND p).msdomain = Collect d) (r,t)` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  qexists `\(r,s). ISL r /\ LENGTH es.contexts <= LENGTH s.contexts` >>
  qexists `step o SND` >>
  qexists `(INL () : unit + exception option,es)` >> simp[] >>
  reverse conj_tac >- fs[run_call_def, GREATER_EQ, UNCURRY] >>
  qx_gen_tac `st` >> PairCases_on `st` >> simp[] >> strip_tac >>
  Cases_on `step st1` >> simp[] >>
  irule step_preserves_collect >> metis_tac[]
QED

Theorem call_meter_run_call_collect_returns:
  wf_state es /\ call_meter_budget (LENGTH es.contexts) ceiling es /\
  es.msdomain = Collect dd /\ 2 <= LENGTH es.contexts ==>
  ?t dd'. run_call es = SOME (INL (),t) /\
    LENGTH t.contexts + 1 = LENGTH es.contexts /\ t.msdomain = Collect dd'
Proof
  strip_tac >> Cases_on `run_call_tr (LENGTH es.contexts) (step es)` >>
  `run_call es = SOME (q,r)` by simp[run_call_eq_tr] >>
  `ISL q` by metis_tac[call_meter_run_call_collect_inl] >>
  Cases_on `q` >> gvs[] >>
  drule_all run_call_inl_length >>
  drule_all call_meter_run_call_preserves_collect >> metis_tac[]
QED
