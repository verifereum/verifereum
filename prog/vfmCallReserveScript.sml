Theory vfmCallReserve
Ancestors vfmCallEntryStep vfmCallMeterOps vfmCallMeterSafe vfmCallMeter
          vfmCallMeterProbe vfmExecution vfmContext vfmState vfmTypes arithmetic list

Definition call_meter_reserved_def:
  call_meter_reserved c k rb rest s <=>
    ?d. s.contexts = (d,rb)::rest /\
        d.gasUsed <= d.msgParams.gasLimit /\
        d.stateGasSpilled + d.stateGasCommitted + k <= d.gasUsed /\
        call_meter_claim d + k <= call_meter_claim c
End

Theorem call_meter_reserved_zero:
  call_meter_reserved c 0 rb rest s <=> call_meter_result c rb rest s
Proof
  simp[call_meter_reserved_def, call_meter_result_def, call_meter_backed_def] >>
  metis_tac[]
QED

Theorem call_meter_reserved_weaken:
  call_meter_reserved c k rb rest s /\ j <= k ==>
  call_meter_reserved c j rb rest s
Proof
  simp[call_meter_reserved_def] >> rpt strip_tac >> qexists `d` >> simp[] >> decide_tac
QED

Theorem call_meter_reserved_forget:
  call_meter_reserved c k rb rest s ==> call_meter_result c rb rest s
Proof
  metis_tac[call_meter_reserved_zero, call_meter_reserved_weaken, ZERO_LESS_EQ]
QED

Theorem call_meter_reserved_neutral:
  call_meter_reserved c k rb rest s /\ s.contexts = (d,rb)::rest /\
  t.contexts = (d',rb)::rest /\ call_meter_neutral d d' ==>
  call_meter_reserved c k rb rest t
Proof
  simp[call_meter_reserved_def, call_meter_neutral_def, call_meter_claim_def] >>
  rpt strip_tac >> gvs[] >> qexists `d'` >> simp[]
QED

Theorem call_meter_reserved_ready:
  call_meter_reserved c k rb rest s ==>
  ?d. call_meter_ready d rb rest s
Proof
  simp[call_meter_reserved_def, call_meter_ready_def, call_meter_backed_def] >>
  rpt strip_tac >> qexists `d` >> simp[] >> decide_tac
QED

Theorem call_meter_safe_reserved_neutral:
  (!d s r t. call_meter_ready d rb rest s /\ m s = (r,t) ==>
    (?d'. t.contexts = (d',rb)::rest /\ call_meter_neutral d d')) /\
  (!d. call_meter_safe (call_meter_ready d rb rest) m
          (\r t. call_meter_result d rb rest t)) ==>
  call_meter_safe (call_meter_reserved c k rb rest) m
    (\r t. call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt strip_tac >>
  drule call_meter_reserved_ready >> strip_tac >>
  first_assum drule_all >> strip_tac >>
  metis_tac[call_meter_reserved_neutral, call_meter_ready_def]
QED

Theorem call_meter_safe_reserved_context_update:
  (!d. call_meter_neutral d (f d)) ==>
  call_meter_safe (call_meter_reserved c k rb rest)
    (bind get_current_context (\d. set_current_context (f d)))
    (\r t. call_meter_reserved c k rb rest t)
Proof
  strip_tac >> irule call_meter_safe_reserved_neutral >> conj_tac
  >- (simp[call_meter_ready_def, get_current_context_def, set_current_context_def,
           bind_def, return_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[call_meter_safe_context_update]
QED

Theorem call_meter_reserved_expand_memory:
  call_meter_safe (call_meter_reserved c k rb rest) (expand_memory n)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[expand_memory_def] >>
  ho_match_mp_tac call_meter_safe_reserved_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_reserved_set_return_data:
  call_meter_safe (call_meter_reserved c k rb rest) (set_return_data bytes)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[set_return_data_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_reserved_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_reserved_inc_pc:
  call_meter_safe (call_meter_reserved c k rb rest) inc_pc
    (\r t. call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[inc_pc_def] >>
  ho_match_mp_tac call_meter_safe_reserved_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_reserved_push_stack:
  call_meter_safe (call_meter_reserved c k rb rest) (push_stack v)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_neutral >>
  simp[call_meter_safe_push_stack] >>
  simp[call_meter_ready_def, push_stack_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> simp[call_meter_neutral_def]
QED

Theorem call_meter_reserved_assert_not_static:
  call_meter_safe (call_meter_reserved c k rb rest) assert_not_static
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_neutral >> conj_tac
  >- (simp[call_meter_ready_def, assert_not_static_def, get_static_def,
           get_current_context_def, bind_def, ignore_bind_def, return_def,
           assert_def, fail_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> simp[call_meter_neutral_def]) >>
  gen_tac >> irule call_meter_safe_consequence >>
  qexistsl [`call_meter_ready d rb rest`, `\r t. call_meter_ready d rb rest t`] >>
  simp[call_meter_safe_assert_not_static, call_meter_ready_result]
QED

Theorem call_meter_safe_reserved_ready_lift:
  (!d. call_meter_safe (call_meter_ready d rb rest) m
         (\r t. call_meter_ready d rb rest t)) ==>
  call_meter_safe (call_meter_reserved c k rb rest) m
    (\r t. call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `?d. call_meter_ready d rb rest s` by metis_tac[call_meter_reserved_ready] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[call_meter_ready_def, call_meter_reserved_def] >> metis_tac[]
QED

Theorem call_meter_reserved_access_address:
  call_meter_safe (call_meter_reserved c k rb rest) (access_address a)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_ready_lift >> simp[call_meter_safe_access_address]
QED

Theorem call_meter_reserved_ensure_storage:
  call_meter_safe (call_meter_reserved c k rb rest) (ensure_storage_in_domain a)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_ready_lift >> simp[call_meter_safe_ensure_storage]
QED

Theorem call_meter_reserved_context_reader:
  !f. call_meter_safe (call_meter_reserved c k rb rest)
    (bind get_current_context (\d. return (f d)))
    (\r t. ?d. t.contexts = (d,rb)::rest /\ r = INL (f d) /\
                call_meter_reserved c k rb rest t)
Proof
  simp[call_meter_safe_def, get_current_context_def, bind_def, return_def] >>
  rpt strip_tac >>
  drule call_meter_reserved_ready >> strip_tac >>
  gvs[call_meter_ready_def]
QED

Theorem call_meter_reserved_gas_left_reader:
  call_meter_safe (call_meter_reserved c k rb rest) get_gas_left
    (\r t. ?d. t.contexts = (d,rb)::rest /\
                r = INL (d.msgParams.gasLimit - d.gasUsed) /\
                call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[get_gas_left_def] >>
  Q.ISPEC_THEN `\d:context. d.msgParams.gasLimit - d.gasUsed` (MATCH_ACCEPT_TAC o BETA_RULE)
    call_meter_reserved_context_reader
QED

Theorem call_meter_reserved_callee_reader:
  call_meter_safe (call_meter_reserved c k rb rest) get_callee
    (\r t. ?d. t.contexts = (d,rb)::rest /\ r = INL d.msgParams.callee /\
                call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[get_callee_def] >>
  Q.ISPEC_THEN `\d:context. d.msgParams.callee` (MATCH_ACCEPT_TAC o BETA_RULE)
    call_meter_reserved_context_reader
QED

Theorem call_meter_reserved_num_contexts_reader:
  call_meter_safe (call_meter_reserved c k rb rest) get_num_contexts
    (\r t. r = INL (LENGTH t.contexts) /\ call_meter_reserved c k rb rest t)
Proof
  simp[call_meter_safe_num_contexts_reader]
QED

Theorem call_meter_safe_reserved_from_margin:
  (!d s r t. s.contexts = (d,rb)::rest /\
      d.stateGasSpilled + d.stateGasCommitted + k <= d.gasUsed /\
      d.gasUsed <= d.msgParams.gasLimit /\ m s = (r,t) ==>
    ?d'. t.contexts = (d',rb)::rest /\
      d'.stateGasSpilled + d'.stateGasCommitted + k <= d'.gasUsed /\
      d'.gasUsed <= d'.msgParams.gasLimit /\ call_meter_claim d' <= call_meter_claim d) /\
  (!d. call_meter_safe (call_meter_ready d rb rest) m
         (\r t. call_meter_result d rb rest t)) ==>
  call_meter_safe (call_meter_reserved c k rb rest) m
    (\r t. call_meter_reserved c k rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?d. call_meter_ready d rb rest s` by metis_tac[call_meter_reserved_ready] >>
  `!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented`
    by metis_tac[] >>
  simp[] >>
  gvs[call_meter_reserved_def, call_meter_ready_def] >>
  qpat_x_assum `!d s r t. _ ==> ?d'. _` drule_all >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem call_meter_reserved_charge:
  call_meter_safe (call_meter_reserved c k rb rest) (charge_state_gas amount)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_from_margin >>
  simp[call_meter_safe_charge] >> rpt gen_tac >> strip_tac >>
  `d.stateGasSpilled + d.stateGasCommitted + k <= d.gasUsed` by decide_tac >>
  drule_all call_meter_charge_margin >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem call_meter_reserved_credit:
  call_meter_safe (call_meter_reserved c k rb rest) (credit_state_gas_refund amount)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  irule call_meter_safe_reserved_from_margin >>
  simp[call_meter_safe_credit] >> rpt gen_tac >> strip_tac >>
  `d.stateGasSpilled + d.stateGasCommitted + k <= d.gasUsed` by decide_tac >>
  drule_all call_meter_credit_margin >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem call_meter_reserved_charge_account:
  call_meter_safe (call_meter_reserved c k rb rest) (charge_new_account charged)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  Cases_on `charged` >>
  simp[charge_new_account_def, call_meter_reserved_charge,
       call_meter_safe_return]
QED

Theorem call_meter_reserved_credit_account:
  call_meter_safe (call_meter_reserved c k rb rest) (credit_new_account charged)
    (\r t. call_meter_reserved c k rb rest t)
Proof
  Cases_on `charged` >>
  simp[credit_new_account_def, call_meter_reserved_credit,
       call_meter_safe_return]
QED
