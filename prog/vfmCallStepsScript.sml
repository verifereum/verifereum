Theory vfmCallSteps
Ancestors vfmCallGrant vfmCallReserve vfmCallEntryStep vfmCallEntry
          vfmCallPrecompile vfmCallMeterOps vfmCallMeterSafe vfmCallMeter
          vfmCallBudget vfmCallMeterProbe vfmExecution vfmContext vfmState
          vfmTypes vfmExecutionProp arithmetic list

Theorem call_meter_reserved_credit_abort_value:
  call_meter_safe (call_meter_reserved c grant rb rest)
    (ignore_bind (credit_new_account charged) (abort_call_value grant))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_bind >>
  qexists `call_meter_reserved c grant rb rest` >> reverse conj_tac
  >- simp[call_meter_reserved_abort_call_value] >>
  irule call_meter_safe_consequence >>
  qexistsl [`call_meter_reserved c grant rb rest`,
            `\r t. call_meter_reserved c grant rb rest t`] >>
  simp[call_meter_reserved_credit_account] >> rpt strip_tac >>
  Cases_on `r` >> simp[] >> metis_tac[call_meter_reserved_forget]
QED

Theorem call_meter_reserved_credit_abort_depth:
  call_meter_safe (call_meter_reserved c grant rb rest)
    (ignore_bind (credit_new_account charged) (abort_unuse grant))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_bind >>
  qexists `call_meter_reserved c grant rb rest` >> reverse conj_tac
  >- simp[call_meter_reserved_abort_unuse] >>
  irule call_meter_safe_consequence >>
  qexistsl [`call_meter_reserved c grant rb rest`,
            `\r t. call_meter_reserved c grant rb rest t`] >>
  simp[call_meter_reserved_credit_account] >> rpt strip_tac >>
  Cases_on `r` >> simp[] >> metis_tac[call_meter_reserved_forget]
QED

Theorem call_meter_safe_anchor_budget:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  call_meter_safe P m (\r t. call_meter_result c rb rest t) ==>
  call_meter_safe P m (\r t. call_meter_budget n ceiling t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt strip_tac >>
  metis_tac[call_meter_result_budget]
QED

Theorem call_meter_reserved_depth_tail:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest ==>
  call_meter_safe (call_meter_reserved c grant rb rest)
    (bind get_num_contexts (\depth.
      if depth > 1024 then
        ignore_bind (credit_new_account charged) (abort_unuse grant)
      else proceed_call op sender addr value ao az code grant output))
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> irule call_meter_safe_bind >>
  qexists `\depth s. call_meter_reserved c grant rb rest s` >> reverse conj_tac
  >- (irule call_meter_safe_consequence >>
      qexistsl [`call_meter_reserved c grant rb rest`,
                `\r t. r = INL (LENGTH t.contexts) /\ call_meter_reserved c grant rb rest t`] >>
      simp[call_meter_reserved_num_contexts_reader] >> rpt strip_tac >> gvs[]) >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC
  >- (irule call_meter_safe_anchor_budget >>
      qexistsl [`c`, `rb`, `rest`, `u`] >>
      simp[] >>
      mp_tac (GEN_ALL call_meter_reserved_credit_abort_depth) >>
      simp[call_meter_safe_def] >> metis_tac[]) >>
  drule_all call_meter_reserved_proceed_call >>
  simp[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_reserved_budget_bind:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  call_meter_safe (call_meter_reserved c k rb rest) m
    (\r t. call_meter_reserved c k rb rest t) /\
  (!x. call_meter_safe (call_meter_reserved c k rb rest) (f x)
         (\r t. call_meter_budget n ceiling t)) ==>
  call_meter_safe (call_meter_reserved c k rb rest) (bind m f)
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> irule call_meter_safe_bind >>
  qexists `\x s. call_meter_reserved c k rb rest s` >> reverse conj_tac
  >- (irule call_meter_safe_consequence >>
      qexistsl [`call_meter_reserved c k rb rest`,
                `\r t. call_meter_reserved c k rb rest t`] >> simp[] >>
      rpt strip_tac >> Cases_on `r` >> simp[] >>
      metis_tac[call_meter_reserved_forget, call_meter_result_budget]) >>
  gvs[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_reserved_call_tail:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest ==>
  call_meter_safe (call_meter_reserved c grant rb rest)
    (bind get_callee (\sender.
      if (lookup_account sender accounts).balance < value then
        ignore_bind (credit_new_account charged) (abort_call_value grant)
      else ignore_bind (set_return_data [])
        (bind get_num_contexts (\depth.
          if depth > 1024 then
            ignore_bind (credit_new_account charged) (abort_unuse grant)
          else proceed_call op sender addr value ao az code grant output))))
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> irule call_meter_reserved_budget_bind >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC
      >- (irule call_meter_safe_anchor_budget >>
          qexistsl [`c`, `rb`, `rest`, `u`] >> simp[] >>
          mp_tac (GEN_ALL call_meter_reserved_credit_abort_value) >>
          simp[call_meter_safe_def] >> metis_tac[]) >>
      rewrite_tac[ignore_bind_def] >>
      irule call_meter_reserved_budget_bind >>
      conj_tac
      >- (gen_tac >> BETA_TAC >>
          drule_all call_meter_reserved_depth_tail >>
          simp[call_meter_safe_def, ignore_bind_def] >> metis_tac[]) >>
      conj_tac >- (qexists `u` >> simp[]) >>
      simp[call_meter_reserved_set_return_data]) >>
  conj_tac >- (qexists `u` >> simp[]) >>
  irule call_meter_safe_consequence >>
  qexistsl [`call_meter_reserved c grant rb rest`,
            `\r t. ?d. t.contexts = (d,rb)::rest /\ r = INL d.msgParams.callee /\
                         call_meter_reserved c grant rb rest t`] >>
  simp[call_meter_reserved_callee_reader] >> metis_tac[]
QED

Theorem call_meter_reserved_payment_tail:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  (if value = 0 then 0 else call_stipend) <= margin /\
  call_gas value requested (d.msgParams.gasLimit - d.gasUsed) 0 0 = (paid,grant) ==>
  call_meter_safe
    (\s. call_meter_reserved c margin rb rest s /\ s.contexts = (d,rb)::rest)
    (ignore_bind (consume_gas paid)
      (bind get_callee (\sender.
        if (lookup_account sender accounts).balance < value then
          ignore_bind (credit_new_account charged) (abort_call_value grant)
        else ignore_bind (set_return_data [])
          (bind get_num_contexts (\depth.
            if depth > 1024 then
              ignore_bind (credit_new_account charged) (abort_unuse grant)
            else proceed_call op sender addr value ao az code grant output)))))
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> irule call_meter_safe_ignore_bind >>
  qexists `call_meter_reserved c grant rb rest` >> reverse conj_tac
  >- (drule_all call_meter_reserved_call_tail >>
      simp[call_meter_safe_def] >> metis_tac[]) >>
  irule call_meter_safe_consequence >>
  qexistsl [`\s. call_meter_reserved c margin rb rest s /\ s.contexts = (d,rb)::rest`,
            `\r t. r = INL () /\ call_meter_reserved c grant rb rest t`] >>
  simp[] >> drule_all call_meter_reserved_call_payment >>
  simp[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_reserved_gas_tail:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  (if value = 0 then 0 else call_stipend) <= margin ==>
  call_meter_safe (call_meter_reserved c margin rb rest)
    (bind get_gas_left (\gasLeft.
      case call_gas value requested gasLeft 0 0 of (paid,grant) =>
      ignore_bind (consume_gas paid)
        (bind get_callee (\sender.
          if (lookup_account sender accounts).balance < value then
            ignore_bind (credit_new_account charged) (abort_call_value grant)
          else ignore_bind (set_return_data [])
            (bind get_num_contexts (\depth.
              if depth > 1024 then
                ignore_bind (credit_new_account charged) (abort_unuse grant)
              else proceed_call op sender addr value ao az code grant output))))))
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> irule call_meter_safe_bind >>
  qexists `\gasLeft s. ?d. s.contexts = (d,rb)::rest /\
      gasLeft = d.msgParams.gasLimit - d.gasUsed /\ call_meter_reserved c margin rb rest s` >>
  reverse conj_tac
  >- (irule call_meter_safe_consequence >>
      qexistsl [`call_meter_reserved c margin rb rest`,
                `\r t. ?d. t.contexts = (d,rb)::rest /\
                  r = INL (d.msgParams.gasLimit - d.gasUsed) /\
                  call_meter_reserved c margin rb rest t`] >>
      simp[call_meter_reserved_gas_left_reader] >> rpt strip_tac >>
      Cases_on `r` >> gvs[] >> metis_tac[]) >>
  gen_tac >> BETA_TAC >> rewrite_tac[call_meter_safe_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `call_gas value requested (d.msgParams.gasLimit - d.gasUsed) 0 0` >>
  gvs[] >> `n <= LENGTH u.contexts` by simp[] >>
  drule_all call_meter_reserved_payment_tail >>
  rewrite_tac[call_meter_safe_def] >> BETA_TAC >> disch_then drule_all >> simp[]
QED

Theorem call_meter_reserved_charge_memory_bind:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  call_meter_safe (call_meter_reserved c k rb rest) m
    (\r t. call_meter_budget n ceiling t) ==>
  call_meter_safe (call_meter_reserved c k rb rest)
    (ignore_bind (charge_new_account charged)
      (ignore_bind (if check then assert_not_static else return ())
        (ignore_bind (expand_memory amount) m)))
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> rewrite_tac[ignore_bind_def] >>
  irule call_meter_reserved_budget_bind >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_reserved_budget_bind >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_reserved_budget_bind >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              gvs[call_meter_safe_def] >> metis_tac[]) >>
          conj_tac >- (qexists `u` >> simp[]) >>
          simp[call_meter_reserved_expand_memory]) >>
      conj_tac >- (qexists `u` >> simp[]) >>
      Cases_on `check`
      >- (mp_tac (GEN_ALL call_meter_reserved_assert_not_static) >>
          simp[call_meter_safe_def] >> metis_tac[]) >>
      simp[call_meter_safe_def, return_def]) >>
  conj_tac >- (qexists `u` >> simp[]) >>
  simp[call_meter_reserved_charge_account]
QED

Theorem call_meter_reserved_consume_budget_bind:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\ margin <= cost /\
  call_meter_safe (call_meter_reserved c margin rb rest) m
    (\r t. call_meter_budget n ceiling t) ==>
  call_meter_safe (call_meter_reserved c 0 rb rest)
    (ignore_bind (consume_gas cost) m)
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> rewrite_tac[ignore_bind_def] >>
  irule call_meter_safe_bind >>
  qexists `\x s. call_meter_reserved c margin rb rest s` >>
  reverse conj_tac
  >- (drule call_meter_reserved_consume >>
      simp[call_meter_safe_def] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >> simp[] >>
      Cases_on `r` >> gvs[] >>
      `n <= LENGTH u.contexts` by simp[] >>
      drule_all call_meter_result_budget >> simp[]) >>
  gvs[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_reserved_cost_tail:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  (if value = 0 then 0 else call_stipend) <= cost ==>
  call_meter_safe (call_meter_reserved c 0 rb rest)
    (ignore_bind (consume_gas cost)
      (ignore_bind (charge_new_account charged)
        (ignore_bind (if op = Call /\ 0 < value then assert_not_static else return ())
          (ignore_bind (expand_memory amount)
            (bind get_gas_left (\gasLeft.
              case call_gas value requested gasLeft 0 0 of (paid,grant) =>
              ignore_bind (consume_gas paid)
                (bind get_callee (\sender.
                  if (lookup_account sender accounts).balance < value then
                    ignore_bind (credit_new_account charged) (abort_call_value grant)
                  else ignore_bind (set_return_data [])
                    (bind get_num_contexts (\depth.
                      if depth > 1024 then
                        ignore_bind (credit_new_account charged) (abort_unuse grant)
                      else proceed_call op sender addr value ao az code grant output))))))))))
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> irule call_meter_reserved_consume_budget_bind >>
  conj_tac >- (qexists `u` >> simp[]) >>
  qexists `(if value = 0 then 0 else call_stipend)` >> simp[] >>
  irule call_meter_reserved_charge_memory_bind >>
  conj_tac >- (qexists `u` >> simp[]) >>
  `(if value = 0 then 0 else call_stipend) <=
   (if value = 0 then 0 else call_stipend)` by simp[] >>
  drule_all call_meter_reserved_gas_tail >>
  simp[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_reserved_pop_stack_zero:
  call_meter_safe (call_meter_reserved c 0 rb rest) (pop_stack sz)
    (\r t. call_meter_reserved c 0 rb rest t)
Proof
  `call_meter_safe (call_meter_result c rb rest) (pop_stack sz)
     (\r t. call_meter_result c rb rest t)` by
    (irule call_meter_safe_result_lift >> simp[call_meter_safe_pop_stack]) >>
  gvs[call_meter_safe_def, call_meter_reserved_zero] >> metis_tac[]
QED

Theorem call_meter_reserved_memory_info:
  call_meter_safe (call_meter_reserved c k rb rest) (memory_expansion_info offset len)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_ready_lift >>
  simp[call_meter_safe_memory_expansion_info]
QED

Theorem call_meter_reserved_accounts:
  call_meter_safe (call_meter_reserved c k rb rest) get_accounts
    (\r t. call_meter_reserved c k rb rest t)
Proof
  mp_tac (GEN_ALL call_meter_safe_accounts_reader) >>
  simp[call_meter_safe_def] >> metis_tac[]
QED


Theorem call_meter_reserved_delegate:
  call_meter_safe (call_meter_reserved c k rb rest)
    (case get_delegate (account:account_state).code of
       NONE => return (account.code,0)
     | SOME delegate => bind (access_address delegate) (\cost.
         return ((lookup_account delegate accounts).code,cost)))
    (\r t. call_meter_reserved c k rb rest t)
Proof
  Cases_on `get_delegate account.code` >> simp[]
  >- simp[call_meter_safe_def, return_def] >>
  irule call_meter_safe_bind >>
  qexists `\cost s. call_meter_reserved c k rb rest s` >>
  simp[call_meter_safe_def, return_def] >>
  mp_tac (GEN_ALL call_meter_reserved_access_address) >>
  simp[call_meter_safe_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> Cases_on `r` >> gvs[]
QED

Theorem call_meter_reserved_step_call:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest ==>
  call_meter_safe (call_meter_reserved c 0 rb rest) (step_call op)
    (\r t. call_meter_budget n ceiling t)
Proof
  strip_tac >> rewrite_tac[step_call_def, LET_THM] >> BETA_TAC >>
  irule call_meter_reserved_budget_bind >> conj_tac
  >- (gen_tac >> BETA_TAC >> pairarg_tac >> simp[] >>
      irule call_meter_reserved_budget_bind >> conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule call_meter_reserved_budget_bind >> conj_tac
          >- (gen_tac >> BETA_TAC >>
              irule call_meter_reserved_budget_bind >> conj_tac
              >- (gen_tac >> BETA_TAC >>
                  irule call_meter_reserved_budget_bind >> conj_tac
                  >- (gen_tac >> pairarg_tac >> simp[] >>
                      rewrite_tac[pairTheory.UNCURRY_pair_CASE, combinTheory.C_DEF] >> BETA_TAC >>
                      irule call_meter_reserved_cost_tail >>
                      conj_tac
                      >- (qmatch_goalsub_abbrev_tac `if value = 0 then 0 else call_stipend` >>
                          Cases_on `value = 0` >>
                          simp[vfmConstantsTheory.call_stipend_def,
                               vfmConstantsTheory.call_value_cost_def]) >>
                      qexists `u` >> simp[]) >>
                  conj_tac >- (qexists `u` >> simp[]) >>
                  simp[SF ETA_ss] >> irule (SRULE [SF ETA_ss] call_meter_reserved_delegate)) >>
              conj_tac >- (qexists `u` >> simp[]) >>
              simp[call_meter_reserved_accounts]) >>
          conj_tac >- (qexists `u` >> simp[]) >>
          simp[call_meter_reserved_access_address]) >>
      conj_tac >- (qexists `u` >> simp[]) >>
      simp[call_meter_reserved_memory_info]) >>
  conj_tac >- (qexists `u` >> simp[]) >>
  simp[call_meter_reserved_pop_stack_zero]
QED

Theorem call_meter_step_call_budget:
  wf_state s /\ call_meter_budget n ceiling s /\
  0 < n /\ n <= LENGTH s.contexts /\ step_call op s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `n <= LENGTH s.contexts` by simp[] >>
  `call_meter_backed h0` by (drule_all call_meter_budget_top >> simp[]) >>
  `h0.gasUsed <= h0.msgParams.gasLimit` by
    gvs[wf_state_def, wf_context_def] >>
  `call_meter_reserved h0 0 h1 t' s` by
    simp[call_meter_reserved_zero, call_meter_result_same] >>
  drule_all call_meter_reserved_step_call >>
  simp[call_meter_safe_def] >> disch_then drule_all >> simp[]
QED
