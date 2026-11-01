Theory vfmCallReturn
Ancestors vfmCallInner vfmCallBudget vfmCallMeterBase vfmRunCall vfmContextLength vfmDomainCollection
          vfmExecutionProp vfmExecution vfmState vfmContext vfmTypes
          vfmDecreasesGas vfmStepLength vfmHandleStep vfmBuffer
          vfmConstants vfmSameFrame vfmTxParams vfmRunWithinFrame
          vfmAccountFrame vfmStaticCalls vfmStoragePredicates
          arithmetic list pair While combin words

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

(* Refund is measured after failure restoration, not before it. *)
Definition call_return_gas_def:
  call_return_gas e c =
    if e = NONE then c.msgParams.gasLimit - c.gasUsed
    else if e = SOME Reverted then
      c.msgParams.gasLimit - (c.gasUsed - c.stateGasSpilled)
    else 0
End

Definition call_return_data_def:
  call_return_data e c =
    if e = NONE \/ e = SOME Reverted then c.returnData else []
End

Definition call_return_context_def:
  call_return_context e c caller mr =
    let success = (e = NONE);
        out = call_return_data e c;
        merged = absorb_state_gas
          (caller with gasUsed := caller.gasUsed - call_return_gas e c)
          (if success then c.stateGasLeft else c.stateGasBaseline)
          (if success then c.stateGasSpilled else 0) c.stateGasCommitted;
        credit = if c.msgParams.newAccountCharged then new_account_state_gas else 0;
        settled = call_meter_settle success credit
          (caller.logs ++ c.logs) (caller.addRefund + c.addRefund)
          (caller.subRefund + c.subRefund) merged
    in settled with <|
      stack := b2w success :: caller.stack;
      pc := SUC caller.pc;
      memory := buffer_write mr.offset (TAKE mr.size out) caller.memory;
      returnData := out |>
End

Theorem call_return_gas_bound:
  call_meter_backed c /\ c.gasUsed <= c.msgParams.gasLimit ==>
  call_return_gas e c <= call_meter_claim c
Proof
  simp[call_return_gas_def, call_meter_backed_def, call_meter_claim_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem call_return_restored_gas_bound:
  call_meter_backed c /\ c.gasUsed <= c.msgParams.gasLimit ==>
  c.msgParams.gasLimit -
    (c.gasUsed - (if e = NONE then 0 else c.stateGasSpilled)) <=
      call_meter_claim c
Proof
  simp[call_meter_backed_def, call_meter_claim_def] >>
  strip_tac >> IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem call_return_root_refund:
  call_meter_budget n ceiling s /\ LENGTH s.contexts = n /\
  s.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit ==>
  call_return_gas e c <= ceiling /\
  c.msgParams.gasLimit -
    (c.gasUsed - (if e = NONE then 0 else c.stateGasSpilled)) <= ceiling
Proof
  strip_tac >>
  `0 < n /\ n <= LENGTH s.contexts` by gvs[] >>
  `call_meter_backed c` by metis_tac[call_meter_budget_top] >>
  `call_meter_claim c <= ceiling` by metis_tac[call_meter_budget_root_claim] >>
  metis_tac[call_return_gas_bound, call_return_restored_gas_bound, LESS_EQ_TRANS]
QED

Theorem call_return_handle_exception_memory:
  s.contexts = (c,saved)::(caller,cb)::rest /\
  c.msgParams.outputTo = Memory mr /\
  c.gasUsed <= c.msgParams.gasLimit /\
  c.msgParams.gasLimit -
    (c.gasUsed - (if e = NONE then 0 else c.stateGasSpilled)) <= caller.gasUsed /\
  LENGTH caller.stack < stack_limit ==>
  handle_exception e s = (INL (),s with <|
    contexts := (call_return_context e c caller mr,cb)::rest;
    rollback := if e = NONE then s.rollback else saved |>)
Proof
  strip_tac >> Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  Cases_on `c.msgParams.newAccountCharged` >>
  gvs[call_return_context_def, call_meter_settle_def,
      call_return_gas_def, call_return_data_def,
      LET_THM, restore_state_gas_def, forfeit_remaining_gas_def,
      repay_state_gas_spill_def, credit_new_account_def,
      credit_state_gas_refund_def, absorb_state_gas_def,
      repay_state_gas_spill_context_def,
      handle_exception_def, pop_and_incorporate_context_def,
      get_gas_left_def, get_num_contexts_def, get_output_to_def,
      get_return_data_def, get_current_context_def, pop_context_def,
      consume_gas_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
      set_rollback_def, set_current_context_def, set_return_data_def,
      inc_pc_def, push_stack_def, write_memory_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      combinTheory.o_DEF, combinTheory.C_DEF] >>
  cong_tac (SOME 4) >> simp[context_component_equality, ADD_COMM]
QED

(* Structural reachability facts, independent of the callee safety proof. *)
Theorem call_return_DROP_TL[local]:
  0 < k /\ l1 <> [] /\ l2 <> [] /\ TL l1 = TL l2 ==>
  DROP k l1 = DROP k l2
Proof
  Cases_on `k` >> Cases_on `l1` >> Cases_on `l2` >> gvs[]
QED

Theorem call_return_DROP_push[local]:
  0 < k /\ 2 <= LENGTH l' /\ l <> [] /\ TL (TL l') = TL l ==>
  DROP (SUC k) l' = DROP k l
Proof
  Cases_on `k` >> Cases_on `l` >> gvs[] >>
  Cases_on `l'` >> gvs[] >> Cases_on `t'` >> gvs[]
QED

Theorem call_return_DROP_pop[local]:
  L <= SUC (LENGTH rest) ==>
  DROP (LENGTH (x::rest) + 1 - L) (x::rest) =
  DROP (LENGTH (a::b::rest) + 1 - L) (a::b::rest)
Proof
  strip_tac >>
  `LENGTH (a::b::rest) + 1 - L = SUC (SUC (SUC (LENGTH rest) - L)) /\
   LENGTH (x::rest) + 1 - L = SUC (SUC (LENGTH rest) - L)` by simp[] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem call_return_step_push_tail:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts ==>
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  TL (TL t.contexts) = TL s.contexts
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_push_foreign >> strip_tac >>
  drule_all step_grow_dispatch >> strip_tac >> gvs[]
  >- (drule step_call_push_structure >> simp[]) >>
  drule step_create_reaches_proceed_create >> simp[] >> strip_tac >>
  gvs[cp_rel_def, proceed_create_def, update_accounts_def, get_rollback_def,
      get_original_def, set_original_def, push_context_def, get_accounts_def,
      drain_state_gas_reservoir_def, get_current_context_def, set_current_context_def,
      ignore_bind_def, bind_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem call_return_outer_contexts:
  wf_state es /\ run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts ==>
  DROP (LENGTH s.contexts + 1 - LENGTH es.contexts) s.contexts = TL es.contexts
Proof
  strip_tac >>
  `(\s. wf_state s /\ (LENGTH es.contexts <= LENGTH s.contexts ==>
    DROP (LENGTH s.contexts + 1 - LENGTH es.contexts) s.contexts = TL es.contexts)) s`
    suffices_by simp[] >>
  irule run_call_reaches_inv >> qexists `es` >> simp[] >> conj_tac
  >- (`es.contexts <> []` by gvs[wf_state_def] >> Cases_on `es.contexts` >> gvs[]) >>
  qx_genl_tac [`t`,`t'`] >> strip_tac >>
  `wf_state t'` by metis_tac[step_preserves_wf_state, SND] >> simp[] >> strip_tac >>
  `t.contexts <> []` by gvs[wf_state_def] >>
  `DROP (LENGTH t.contexts + 1 - LENGTH es.contexts) t.contexts = TL es.contexts`
    by metis_tac[] >> qpat_x_assum `_ ==> _` kall_tac >>
  Cases_on `LENGTH t'.contexts = LENGTH t.contexts`
  >- (`outputTo_consistent t` by
        metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
      drule_all step_same_frame >> rw[same_frame_rel_def] >>
      `t'.contexts <> []` by gvs[wf_state_def] >>
      qpat_x_assum `DROP _ _ = _` (SUBST1_TAC o SYM) >>
      irule call_return_DROP_TL >> simp[]) >>
  Cases_on `LENGTH t.contexts < LENGTH t'.contexts`
  >- (drule_all call_return_step_push_tail >> strip_tac >>
      qpat_x_assum `DROP _ _ = _` (SUBST1_TAC o SYM) >>
      `LENGTH t'.contexts + 1 - LENGTH es.contexts =
        SUC (LENGTH t.contexts + 1 - LENGTH es.contexts)` by simp[] >>
      pop_assum SUBST1_TAC >>
      `0 < LENGTH t.contexts` by (Cases_on `t.contexts` >> fs[]) >>
      irule call_return_DROP_push >> simp[]) >>
  `LENGTH t'.contexts < LENGTH t.contexts` by decide_tac >>
  `outputTo_consistent_stack t /\ EVERY (wf_context o FST) t.contexts`
    by gvs[wf_state_def] >>
  drule_all step_pop_structure >> strip_tac >>
  `LENGTH es.contexts <= SUC (LENGTH rest)` by gvs[] >>
  qpat_x_assum `DROP _ _ = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `t'.contexts = _` SUBST1_TAC >>
  qpat_x_assum `t.contexts = _` (fn th => ONCE_REWRITE_TAC[th]) >>
  irule call_return_DROP_pop >> simp[]
QED

Theorem call_return_step_metadata:
  wf_state s /\ step s = (r,t) /\ 2 <= n /\
  n <= LENGTH s.contexts /\ n <= LENGTH t.contexts ==>
  (SND (EL (LENGTH t.contexts - n) t.contexts),
   (FST (EL (LENGTH t.contexts - n) t.contexts)).msgParams) =
  (SND (EL (LENGTH s.contexts - n) s.contexts),
   (FST (EL (LENGTH s.contexts - n) s.contexts)).msgParams)
Proof
  strip_tac >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      qpat_x_assum `!y. _` kall_tac >> qpat_x_assum `wf_state _` kall_tac >>
      qpat_x_assum `step _ = _` kall_tac >>
      Cases_on `s.contexts` >- gvs[] >> Cases_on `t.contexts` >- gvs[] >>
      gvs[] >> Cases_on `SUC (LENGTH t') - n` >> gvs[]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_all call_return_step_push_tail >> strip_tac >>
      drule_all step_push_foreign >> strip_tac >>
      `2 <= LENGTH s.contexts` by decide_tac >>
      `LENGTH t.contexts - n = SUC (LENGTH s.contexts - n)` by decide_tac >>
      qpat_x_assum `!y. _` kall_tac >> qpat_x_assum `wf_state _` kall_tac >>
      qpat_x_assum `step _ = _` kall_tac >>
      Cases_on `s.contexts` >- gvs[] >> Cases_on `t.contexts` >- gvs[] >>
      rename1 `t.contexts = a::tail` >> Cases_on `tail` >- gvs[] >> gvs[] >>
      `SUC (SUC (LENGTH t')) - n = SUC (SUC (LENGTH t') - n)` by decide_tac >>
      asm_rewrite_tac[] >> Cases_on `SUC (LENGTH t') - n` >> gvs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_foreign >> strip_tac >>
  qpat_x_assum `wf_state _` kall_tac >> qpat_x_assum `step _ = _` kall_tac >>
  qpat_x_assum `s.contexts = _` (fn th => ONCE_REWRITE_TAC[th]) >>
  `n <= SUC (LENGTH rest)` by gvs[] >>
  `SUC (SUC (LENGTH rest)) - n = SUC (SUC (LENGTH rest) - n)` by decide_tac >>
  simp[] >> asm_rewrite_tac[] >> Cases_on `SUC (LENGTH rest) - n` >> gvs[]
QED

Theorem call_return_reaches_metadata:
  wf_state es /\ run_call_reaches es t /\
  2 <= n /\ n <= LENGTH es.contexts /\ n <= LENGTH t.contexts ==>
  (SND (EL (LENGTH t.contexts - n) t.contexts),
   (FST (EL (LENGTH t.contexts - n) t.contexts)).msgParams) =
  (SND (EL (LENGTH es.contexts - n) es.contexts),
   (FST (EL (LENGTH es.contexts - n) es.contexts)).msgParams)
Proof
  strip_tac >>
  `(\s. wf_state s /\ (n <= LENGTH s.contexts ==>
    (SND (EL (LENGTH s.contexts - n) s.contexts),
     (FST (EL (LENGTH s.contexts - n) s.contexts)).msgParams) =
    (SND (EL (LENGTH es.contexts - n) es.contexts),
     (FST (EL (LENGTH es.contexts - n) es.contexts)).msgParams))) t`
    suffices_by simp[] >>
  irule run_call_reaches_inv >> qexists `es` >> simp[] >>
  qx_genl_tac [`s`,`s'`] >> strip_tac >>
  `wf_state s'` by metis_tac[step_preserves_wf_state, SND] >> simp[] >> strip_tac >>
  `n <= LENGTH s.contexts` by decide_tac >>
  drule_all call_return_step_metadata >> simp[]
QED

Theorem call_return_root_metadata:
  wf_state es /\ 2 <= LENGTH es.contexts /\ run_call_reaches es t /\
  LENGTH t.contexts = LENGTH es.contexts ==>
  SND (HD t.contexts) = SND (HD es.contexts) /\
  (FST (HD t.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  strip_tac >>
  drule (Q.INST [`n` |-> `LENGTH es.contexts`] call_return_reaches_metadata) >>
  disch_then (qspec_then `t` mp_tac) >> simp[]
QED

Theorem call_return_last_step:
  run_call es = SOME (INL (),t) ==>
  ?n before. FUNPOW (step o SND) n (INL (),es) = (INL (),before) /\
    run_call_reaches es before /\ LENGTH es.contexts <= LENGTH before.contexts /\
    step before = (INL (),t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >> Cases_on `n`
  >- gvs[] >> rename1 `FUNPOW (step o SND) (SUC n) _ = _` >>
  `ISL (FST (FUNPOW (step o SND) n (INL (),es))) /\
   LENGTH es.contexts <= LENGTH (SND (FUNPOW (step o SND) n (INL (),es))).contexts`
    by (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `run_call_reaches es (SND (FUNPOW (step o SND) n (INL (),es)))` by
    (irule run_call_trace_reaches >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexistsl [`n`, `SND (FUNPOW (step o SND) n (INL (),es))`] >>
  gvs[FUNPOW_SUC] >>
  Cases_on `FUNPOW (step o SND) n (INL (),es)` >> gvs[] >>
  Cases_on `q` >> gvs[] >> first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem call_return_last_pop:
  wf_state es /\ run_call es = SOME (INL (),t) ==>
  ?n before err mid.
    FUNPOW (step o SND) n (INL (),es) = (INL (),before) /\
    run_call_reaches es before /\ wf_state before /\
    LENGTH before.contexts = LENGTH es.contexts /\
    TL before.contexts = TL es.contexts /\
    t.txParams = es.txParams /\ step before = (INL (),t) /\
    step_inner before = (INR err,mid) /\ handle_step err mid = (INL (),t)
Proof
  strip_tac >> drule call_return_last_step >> strip_tac >>
  `wf_state before` by metis_tac[run_call_reaches_wf_state] >>
  `LENGTH t.contexts + 1 = LENGTH es.contexts` by metis_tac[run_call_inl_length] >>
  `LENGTH before.contexts <= LENGTH t.contexts + 1` by
    metis_tac[step_length_not_drop_more_than_one] >>
  `LENGTH before.contexts = LENGTH es.contexts` by decide_tac >>
  `TL before.contexts = TL es.contexts` by
    (drule_all call_return_outer_contexts >> simp[] >> Cases_on `before.contexts` >> gvs[]) >>
  `before.txParams = es.txParams` by
    (`(\s. s.txParams = es.txParams) before` suffices_by simp[] >>
     irule run_call_reaches_inv >> qexists `es` >> simp[] >> rpt strip_tac >>
     metis_tac[step_preserves_txParams, SND]) >>
  `t.txParams = es.txParams` by metis_tac[step_preserves_txParams, SND] >>
  qpat_x_assum `step before = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner before` >> Cases_on `q` >> simp[]
  >- (strip_tac >> gvs[] >>
      `same_frame_or_grow step_inner` by simp[] >>
      `before.contexts <> []` by gvs[wf_state_def] >>
      drule_all same_frame_or_grow_length >> simp[]) >>
  strip_tac >> qexistsl [`n`, `before`, `y`, `r`] >>
  simp[GSYM step_eq_handle_step_inner]
QED

Theorem call_return_handle_step_noncode:
  s.contexts <> [] /\
  (!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a) /\
  handle_step e s = (INL (),t) ==>
  handle_exception e s = (INL (),t)
Proof
  strip_tac >> qpat_x_assum `handle_step e s = _` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC >- simp[reraise_def] >>
  simp[handle_def] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises) >>
  disch_then (fn th => rewrite_tac[th]) >> simp[reraise_def]
QED

Theorem call_return_inner_final_frame:
  wf_state s /\ step_inner s = (INR err,mid) /\
  handle_step err mid = (INL (),t) /\
  LENGTH t.contexts + 1 = LENGTH s.contexts ==>
  same_frame_rel s mid /\ EVERY (wf_context o FST) mid.contexts /\
  stack_room_ok mid /\ gas_stack_ok mid
Proof
  strip_tac >> `s.contexts <> []` by fs[wf_state_def] >>
  `same_frame_or_grow step_inner` by simp[] >>
  `LENGTH s.contexts <= LENGTH mid.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `mid.contexts <> []` by
    (Cases_on `mid.contexts` >> simp[] >>
     qpat_x_assum `LENGTH s.contexts <= _` mp_tac >> simp[] >>
     Cases_on `s.contexts` >> fs[]) >>
  `LENGTH mid.contexts = LENGTH s.contexts` by
    (drule_all handle_step_shrinks_by_one >> strip_tac >> decide_tac) >>
  conj_tac >- (drule_all same_frame_or_grow_eq_length >> simp[]) >> conj_tac
  >- (mp_tac decreases_gas_cred_step_inner >> simp[decreases_gas_cred_def] >>
      disch_then (qspec_then `s` mp_tac) >> simp[] >> fs[wf_state_def]) >>
  metis_tac[step_inner_preserves_stack_room_gas_ok]
QED

Theorem call_return_reaches_budget:
  wf_state es /\ call_meter_budget n ceiling es /\ 2 <= n /\
  n <= LENGTH es.contexts /\ run_call_reaches es t /\ n <= LENGTH t.contexts ==>
  call_meter_budget n ceiling t
Proof
  strip_tac >>
  `(\s. wf_state s /\ (n <= LENGTH s.contexts ==> call_meter_budget n ceiling s)) t`
    suffices_by simp[] >>
  irule run_call_reaches_inv >> qexists `es` >> simp[] >>
  qx_genl_tac [`s`,`s'`] >> strip_tac >> conj_tac
  >- metis_tac[step_preserves_wf_state, SND] >> strip_tac >>
  `n <= LENGTH s.contexts` by decide_tac >>
  `call_meter_budget n ceiling s` by metis_tac[] >>
  drule_all call_meter_step_budget >> simp[]
QED

Theorem call_memory_final_pop:
  wf_state es /\ es.contexts = (callee,saved)::(caller,cb)::rest /\
  call_meter_budget (LENGTH es.contexts) ceiling es /\ ceiling <= caller.gasUsed /\
  callee.msgParams.outputTo = Memory mr /\ run_call_reaches es before /\
  LENGTH before.contexts = LENGTH es.contexts /\
  TL before.contexts = TL es.contexts /\
  step_inner before = (INR err,mid) /\ handle_step err mid = (INL (),t) /\
  LENGTH t.contexts + 1 = LENGTH es.contexts ==>
  ?cc. mid.contexts = (cc,saved)::(caller,cb)::rest /\
    cc.msgParams = callee.msgParams /\ call_return_gas err cc <= ceiling /\
    t.contexts = (call_return_context err cc caller mr,cb)::rest /\
    t.rollback = (if err = NONE then mid.rollback else saved)
Proof
  strip_tac >> `2 <= LENGTH es.contexts` by simp[] >>
  `wf_state before` by metis_tac[run_call_reaches_wf_state] >>
  `LENGTH t.contexts + 1 = LENGTH before.contexts` by decide_tac >>
  drule_all call_return_inner_final_frame >> strip_tac >>
  `SND (HD before.contexts) = saved /\
   (FST (HD before.contexts)).msgParams = callee.msgParams` by
    (drule_all call_return_root_metadata >> simp[]) >>
  `SND (HD mid.contexts) = saved /\
   (FST (HD mid.contexts)).msgParams = callee.msgParams /\
   TL mid.contexts = (caller,cb)::rest /\ mid.contexts <> []` by
    (fs[same_frame_rel_def] >> Cases_on `mid.contexts` >> fs[]) >>
  `mid.contexts = (FST (HD mid.contexts),saved)::(caller,cb)::rest` by
    (Cases_on `mid.contexts` >- fs[] >> PairCases_on `h` >> fs[]) >>
  qmatch_asmsub_abbrev_tac `mid.contexts = (cc,saved)::(caller,cb)::rest` >>
  `cc.msgParams = callee.msgParams` by simp[Abbr `cc`] >>
  `cc.gasUsed <= cc.msgParams.gasLimit /\ LENGTH caller.stack < stack_limit` by
    fs[wf_context_def, stack_room_ok_def] >>
  `call_meter_budget (LENGTH es.contexts) ceiling before` by
    metis_tac[call_return_reaches_budget, LESS_EQ_REFL] >>
  `0 < LENGTH es.contexts /\ LENGTH es.contexts <= LENGTH before.contexts` by simp[] >>
  `call_meter_budget (LENGTH es.contexts) ceiling mid` by
    (drule_all call_meter_step_inner_budget >> simp[]) >>
  `LENGTH mid.contexts = LENGTH es.contexts` by simp[] >>
  drule_all call_return_root_refund >> disch_then (qspec_then `err` strip_assume_tac) >>
  `cc.msgParams.gasLimit -
    (cc.gasUsed - (if err = NONE then 0 else cc.stateGasSpilled)) <= caller.gasUsed`
    by metis_tac[LESS_EQ_TRANS] >>
  `!a. (FST (HD mid.contexts)).msgParams.outputTo <> Code a` by simp[] >>
  `cc.msgParams.outputTo = Memory mr` by simp[] >>
  drule_all call_return_handle_step_noncode >>
  drule_all call_return_handle_exception_memory >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem call_return_FUNPOW_guarded[local]:
  !stop f n x. (!i. i < n ==> ~stop (FUNPOW f i x)) ==>
  FUNPOW (\x. if stop x then x else f x) n x = FUNPOW f n x
Proof
  Induct_on `n` >- simp[] >> rpt gen_tac >> strip_tac >>
  `!i. i < n ==> ~stop (FUNPOW f i x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `~stop (FUNPOW f n x)` by
    (qpat_x_assum `!i. i < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  simp[FUNPOW_SUC]
QED

Theorem call_return_guarded_wf[local]:
  !n r. wf_state (SND r) ==>
  wf_state (SND (FUNPOW
    (\r. if ISR (FST r) then r else step (SND r)) n r))
Proof
  Induct_on `n` >- simp[] >> gen_tac >> strip_tac >>
  simp[FUNPOW_SUC] >> IF_CASES_TAC >> simp[] >>
  metis_tac[step_preserves_wf_state]
QED

Theorem call_return_guarded_trace:
  wf_state es /\ run_call es = SOME (INL (),t) ==>
  ?k. FUNPOW (\r. if ISR (FST r) then r else step (SND r))
    k (INL (),es) = (INL (),t) /\ wf_state t
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  `!i. i < n ==> ~ISR (FST (FUNPOW (step o SND) i (INL (),es)))` by
    (gen_tac >> disch_tac >> first_x_assum drule >>
     Cases_on `FST (FUNPOW (step o SND) i (INL (),es))` >> simp[]) >>
  `FUNPOW (\r. if ISR (FST r) then r else step (SND r)) n (INL (),es) =
    FUNPOW (step o SND) n (INL (),es)` by
    (qspecl_then [`ISR o FST`, `step o SND`, `n`, `(INL (),es)`]
       mp_tac call_return_FUNPOW_guarded >> simp[]) >>
  qexists `n` >> simp[] >>
  qspecl_then [`n`, `(INL (),es)`] mp_tac call_return_guarded_wf >> simp[]
QED

(* Stipend footprint observations are layered on this exact meter interface. *)
Theorem run_call_memory_returns:
  wf_state es /\ es.contexts = (callee,saved)::(caller,cb)::rest /\
  call_meter_budget (LENGTH es.contexts) ceiling es /\ ceiling <= caller.gasUsed /\
  es.msdomain = Collect dd /\ callee.msgParams.outputTo = Memory mr ==>
  ?k t dd' cc err mid.
    FUNPOW (\r. if ISR (FST r) then r else step (SND r))
      k (INL (),es) = (INL (),t) /\ wf_state t /\
    run_call es = SOME (INL (),t) /\
    t.msdomain = Collect dd' /\ t.txParams = es.txParams /\
    run_call_reaches es mid /\
    call_return_gas err cc <= ceiling /\ cc.msgParams = callee.msgParams /\
    t.contexts = (call_return_context err cc caller mr,cb)::rest /\
    (~(err = NONE) ==> t.rollback = saved)
Proof
  strip_tac >> `2 <= LENGTH es.contexts` by simp[] >>
  drule_all call_meter_run_call_collect_returns >> strip_tac >>
  drule_all call_return_last_pop >> strip_tac >>
  drule_all call_memory_final_pop >> strip_tac >>
  drule_all call_return_guarded_trace >> strip_tac >>
  qexistsl [`k`,`t`,`dd'`,`cc`,`err`,`before`] >> simp[] >> metis_tac[]
QED

Theorem call_return_context_observations:
  (call_return_context e c caller mr).stack = b2w (e = NONE)::caller.stack /\
  (call_return_context e c caller mr).pc = SUC caller.pc /\
  (call_return_context e c caller mr).memory = buffer_write mr.offset
    (TAKE mr.size (call_return_data e c)) caller.memory /\
  (call_return_context e c caller mr).returnData = call_return_data e c /\
  (call_return_context e c caller mr).msgParams = caller.msgParams /\
  (call_return_context e c caller mr).jumpDest = caller.jumpDest /\
  (call_return_context e c caller mr).stateGasBaseline = caller.stateGasBaseline /\
  (call_return_context e c caller mr).stateGasCommitted =
    caller.stateGasCommitted + c.stateGasCommitted /\
  (call_return_context e c caller mr).logs =
    caller.logs ++ (if e = NONE then c.logs else []) /\
  (call_return_context e c caller mr).addRefund =
    caller.addRefund + (if e = NONE then c.addRefund else 0) /\
  (call_return_context e c caller mr).subRefund =
    caller.subRefund + (if e = NONE then c.subRefund else 0)
Proof
  Cases_on `e = NONE` >>
  simp[call_return_context_def, call_meter_settle_def, LET_THM,
       absorb_state_gas_def, repay_state_gas_spill_context_def]
QED

Theorem call_return_context_meter:
  let sg = caller.stateGasLeft +
        (if e = NONE then c.stateGasLeft else c.stateGasBaseline);
      sp = caller.stateGasSpilled + (if e = NONE then c.stateGasSpilled else 0);
      paid = if e = NONE then MIN sg sp else
        MIN (if c.msgParams.newAccountCharged then new_account_state_gas else 0) sp
  in
    (call_return_context e c caller mr).gasUsed =
      caller.gasUsed - call_return_gas e c - paid /\
    (call_return_context e c caller mr).stateGasLeft =
      (if e = NONE then sg - paid else sg +
        ((if c.msgParams.newAccountCharged then new_account_state_gas else 0) - paid)) /\
    (call_return_context e c caller mr).stateGasSpilled = sp - paid
Proof
  Cases_on `e = NONE` >>
  simp[call_return_context_def, call_meter_settle_def, LET_THM,
       absorb_state_gas_def, repay_state_gas_spill_context_def]
QED
