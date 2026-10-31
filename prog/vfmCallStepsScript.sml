Theory vfmCallSteps
Ancestors vfmCallGrant vfmCallReserve vfmCallEntryStep vfmCallEntry
          vfmCallPrecompile vfmCallMeterOps vfmCallMeterSafe vfmCallMeter
          vfmCallBudget vfmCallMeterProbe vfmExecution vfmContext vfmState
          vfmTypes arithmetic list

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
