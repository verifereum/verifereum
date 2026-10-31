Theory vfmCallGrant
Ancestors vfmCallReserve vfmCallEntryStep vfmCallEntry vfmCallPrecompile
          vfmCallMeterOps vfmCallMeterSafe vfmCallMeter vfmCallBudget
          vfmCallMeterProbe vfmExecution vfmContext vfmState vfmTypes arithmetic list

Theorem call_meter_reserved_consume_success:
  call_meter_reserved c 0 rb rest s /\ margin <= cost /\
  consume_gas cost s = (INL (),t) ==>
  call_meter_reserved c margin rb rest t
Proof
  simp[call_meter_reserved_def] >> rpt strip_tac >>
  `call_meter_backed d` by (simp[call_meter_backed_def] >> decide_tac) >>
  drule_all call_meter_consume_margin >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem call_meter_reserved_consume:
  margin <= cost ==>
  call_meter_safe (call_meter_reserved c 0 rb rest) (consume_gas cost)
    (\r t. case r of INL x => call_meter_reserved c margin rb rest t
                      | INR e => call_meter_result c rb rest t)
Proof
  strip_tac >> rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  drule call_meter_reserved_ready >> strip_tac >>
  `call_meter_result c rb rest s` by metis_tac[call_meter_reserved_forget] >>
  gvs[call_meter_ready_def] >>
  mp_tac (GEN_ALL call_meter_safe_consume) >>
  rewrite_tac[call_meter_safe_def] >> BETA_TAC >> disch_then drule_all >> strip_tac >> simp[] >> Cases_on `r`
  >- (Cases_on `x` >> simp[] >> metis_tac[call_meter_reserved_consume_success]) >>
  simp[] >> irule call_meter_result_trans >> metis_tac[call_meter_ready_def]
QED

Theorem call_meter_reserved_withhold:
  call_meter_safe (call_meter_reserved c 0 rb rest) withhold_create_gas
    (\r t. ?grant. r = INL grant /\ call_meter_reserved c grant rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_reserved_def] >>
  `call_meter_backed d` by (simp[call_meter_backed_def] >> decide_tac) >>
  drule_all call_meter_withhold_grant >> strip_tac >>
  gvs[call_meter_grant_result_def] >>
  simp[call_meter_reserved_def] >> goal_assum (drule_at Any) >>
  simp[] >> decide_tac
QED

Theorem call_meter_reserved_restore_child:
  call_meter_safe (call_meter_reserved c grant rb rest)
    (restore_child_gas grant reservoir)
    (\r t. r = INL () /\ call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_reserved_def] >>
  `d.stateGasSpilled + d.stateGasCommitted + grant <= d.gasUsed` by decide_tac >>
  drule_all call_meter_restore_child_claim >> strip_tac >> simp[] >>
  simp[call_meter_result_def] >> goal_assum (drule_at Any) >>
  simp[] >> decide_tac
QED

Theorem call_meter_reserved_call_payment:
  (if value = 0 then 0 else call_stipend) <= margin /\
  call_gas value requested (d.msgParams.gasLimit - d.gasUsed) 0 0 = (paid,grant) ==>
  call_meter_safe
    (\s. call_meter_reserved c margin rb rest s /\ s.contexts = (d,rb)::rest)
    (consume_gas paid)
    (\r t. r = INL () /\ call_meter_reserved c grant rb rest t)
Proof
  strip_tac >> rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_reserved_def] >>
  `d.stateGasSpilled + d.stateGasCommitted + margin <= d.gasUsed` by decide_tac >>
  drule_all call_meter_call_gas_margin >> strip_tac >>
  gvs[consume_gas_def, get_current_context_def, set_current_context_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  simp[call_meter_reserved_def] >>
  gvs[call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_reserved_proceed_call:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest ==>
  call_meter_safe (call_meter_reserved c grant rb rest)
    (proceed_call op sender addr value ao az code grant output)
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_reserved_def] >>
  `d.stateGasSpilled + d.stateGasCommitted + grant <= d.gasUsed` by decide_tac >>
  `call_meter_claim d + grant <= call_meter_claim c` by decide_tac >>
  `n <= LENGTH u.contexts` by simp[] >>
  drule_all call_meter_proceed_call_all_budget >> simp[]
QED

Theorem call_meter_reserved_proceed_create:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest ==>
  call_meter_safe (call_meter_reserved c grant rb rest)
    (proceed_create sender addr value code grant)
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_reserved_def] >>
  `d.stateGasSpilled + d.stateGasCommitted + grant <= d.gasUsed` by decide_tac >>
  `call_meter_claim d + grant <= call_meter_claim c` by decide_tac >>
  `n <= LENGTH u.contexts` by simp[] >>
  drule_all call_meter_proceed_create_budget >> strip_tac >> simp[]
QED

Theorem call_meter_reserved_unuse:
  call_meter_safe (call_meter_reserved c grant rb rest) (unuse_gas grant)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_reserved_def] >>
  `grant <= d.gasUsed` by decide_tac >>
  drule call_meter_unuse_pair >> simp[] >> strip_tac >> gvs[] >>
  simp[call_meter_result_def, call_meter_backed_def, call_meter_claim_def] >>
  gvs[call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_result_push_stack:
  call_meter_safe (call_meter_result c rb rest) (push_stack v)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_consequence >>
  qexistsl [`call_meter_reserved c 0 rb rest`,
            `\r t. call_meter_reserved c 0 rb rest t`] >>
  simp[call_meter_reserved_push_stack, call_meter_reserved_zero]
QED

Theorem call_meter_result_inc_pc:
  call_meter_safe (call_meter_result c rb rest) inc_pc
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_consequence >>
  qexistsl [`call_meter_reserved c 0 rb rest`,
            `\r t. call_meter_reserved c 0 rb rest t`] >>
  simp[call_meter_reserved_inc_pc, call_meter_reserved_zero]
QED

Theorem call_meter_reserved_abort_unuse:
  call_meter_safe (call_meter_reserved c grant rb rest) (abort_unuse grant)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[abort_unuse_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_reserved_unuse] >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_result_push_stack, call_meter_result_inc_pc]
QED

Theorem call_meter_reserved_abort_call_value:
  call_meter_safe (call_meter_reserved c grant rb rest) (abort_call_value grant)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[abort_call_value_def] >>
  irule call_meter_safe_ignore_bind >>
  qexists `call_meter_reserved c grant rb rest` >> conj_tac
  >- (irule call_meter_safe_consequence >>
      qexistsl [`call_meter_reserved c grant rb rest`,
                `\r t. call_meter_reserved c grant rb rest t`] >>
      simp[call_meter_reserved_push_stack] >> rpt strip_tac >>
      Cases_on `r` >> simp[] >> metis_tac[call_meter_reserved_forget]) >>
  irule call_meter_safe_ignore_bind >>
  qexists `call_meter_reserved c grant rb rest` >> conj_tac
  >- (irule call_meter_safe_consequence >>
      qexistsl [`call_meter_reserved c grant rb rest`,
                `\r t. call_meter_reserved c grant rb rest t`] >>
      simp[call_meter_reserved_set_return_data] >> rpt strip_tac >>
      Cases_on `r` >> simp[] >> metis_tac[call_meter_reserved_forget]) >>
  rewrite_tac[ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_reserved_unuse, call_meter_result_inc_pc]
QED

Theorem call_meter_result_abort_create:
  call_meter_safe (call_meter_result c rb rest) abort_create
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[abort_create_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_result_push_stack, call_meter_result_inc_pc]
QED

Theorem call_meter_result_abort_create_exists:
  call_meter_safe (call_meter_result c rb rest) (abort_create_exists sender)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[abort_create_exists_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
      simp[call_meter_result_push_stack, call_meter_result_inc_pc]) >>
  irule call_meter_safe_result_lift >> gen_tac >>
  irule call_meter_safe_consequence >>
  qexistsl [`call_meter_ready d rb rest`, `\r t. call_meter_ready d rb rest t`] >>
  simp[call_meter_safe_update_accounts, call_meter_ready_result]
QED
