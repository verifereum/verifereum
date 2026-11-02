Theory vfmCallEntryStep
Ancestors vfmCallEntry vfmCallPrecompile vfmCallMeterSafe vfmCallMeterOps
          vfmCallBudget vfmCallMeter vfmCallMeterBase vfmExecution vfmContext vfmState vfmTypes
          arithmetic list

Theorem call_meter_proceed_call_all_budget:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\ s.contexts = (parent,rb)::rest /\
  parent.stateGasSpilled + parent.stateGasCommitted + grant <= parent.gasUsed /\
  call_meter_claim parent + grant <= call_meter_claim c /\
  proceed_call op sender addr value ao az code grant output s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  Cases_on `fIN addr precompile_addresses`
  >- (Cases_on `op <> CallCode /\ 0 < value` >> rpt gen_tac >> strip_tac >>
      gvs[proceed_call_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          get_accounts_def, get_rollback_def, update_accounts_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          push_context_def, bind_def, ignore_bind_def, return_def, LET_THM] >>
      qmatch_asmsub_abbrev_tac `dispatch_precompiles addr entered` >>
      `call_meter_budget n ceiling entered` by
        (irule call_meter_entry_budget >>
         simp[Abbr `entered`, initial_context_def, initial_msg_params_def,
              call_meter_backed_def, call_meter_claim_def] >>
         qexistsl [`c`, `parent`, `u`] >>
         gvs[call_meter_claim_def] >> decide_tac) >>
      drule_at (Pat `dispatch_precompiles _ _ = _`) call_meter_dispatch_budget >>
      simp[Abbr `entered`, initial_context_def, initial_msg_params_def,
           call_meter_backed_def] >>
      disch_then irule >>
      gvs[initial_context_def, initial_msg_params_def])
  >> rpt strip_tac >> drule_all call_meter_proceed_call_budget >> simp[]
QED

(* State-gas charging preserves any execution-gas margin already paid for
   the value stipend, including when the charge spills into execution gas. *)
Theorem call_meter_charge_margin:
  s.contexts = (c,rb)::rest /\
  c.stateGasSpilled + c.stateGasCommitted + margin <= c.gasUsed /\
  c.gasUsed <= c.msgParams.gasLimit /\ charge_state_gas amount s = (r,t) ==>
  ?d. t.contexts = (d,rb)::rest /\
      d.stateGasSpilled + d.stateGasCommitted + margin <= d.gasUsed /\
      d.gasUsed <= d.msgParams.gasLimit /\
      call_meter_claim d <= call_meter_claim c
Proof
  rpt strip_tac >> Cases_on `amount <= c.stateGasLeft`
  >- (gvs[charge_state_gas_def, get_current_context_def, set_current_context_def,
          bind_def, return_def] >> simp[call_meter_claim_def]) >>
  Cases_on `amount <= c.stateGasLeft + (c.msgParams.gasLimit - c.gasUsed)`
  >- (gvs[charge_state_gas_def, get_current_context_def, set_current_context_def,
          consume_gas_def, bind_def, ignore_bind_def, return_def, assert_def,
          fail_def, AllCaseEqs()] >>
      simp[call_meter_claim_def] >> decide_tac) >>
  gvs[charge_state_gas_def, get_current_context_def, bind_def, return_def, fail_def] >>
  qexists `c` >> simp[]
QED

Theorem call_meter_credit_margin:
  s.contexts = (c,rb)::rest /\
  c.stateGasSpilled + c.stateGasCommitted + margin <= c.gasUsed /\
  c.gasUsed <= c.msgParams.gasLimit /\ credit_state_gas_refund amount s = (r,t) ==>
  ?d. t.contexts = (d,rb)::rest /\
      d.stateGasSpilled + d.stateGasCommitted + margin <= d.gasUsed /\
      d.gasUsed <= d.msgParams.gasLimit /\
      call_meter_claim d = call_meter_claim c
Proof
  simp[credit_state_gas_refund_def, get_current_context_def, set_current_context_def,
       bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  simp[call_meter_claim_def] >>
  gvs[MIN_DEF] >> IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem call_meter_consume_margin:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ margin <= cost /\
  consume_gas cost s = (INL (),t) ==>
  ?d. t.contexts = (d,rb)::rest /\
      d.stateGasSpilled + d.stateGasCommitted + margin <= d.gasUsed /\
      d.gasUsed <= d.msgParams.gasLimit /\
      call_meter_claim d + margin <= call_meter_claim c
Proof
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[call_meter_backed_def, call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_call_gas_margin:
  c.stateGasSpilled + c.stateGasCommitted + margin <= c.gasUsed /\
  c.gasUsed <= c.msgParams.gasLimit /\
  (if value = 0 then 0 else call_stipend) <= margin /\
  call_gas value requested (c.msgParams.gasLimit - c.gasUsed) 0 0 = (paid,grant) ==>
  paid <= c.msgParams.gasLimit - c.gasUsed /\
  c.stateGasSpilled + c.stateGasCommitted + grant <= c.gasUsed + paid /\
  call_meter_claim (c with gasUsed := c.gasUsed + paid) + grant <=
    call_meter_claim c + margin
Proof
  rewrite_tac[call_gas_def, LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `left DIV 64` >>
  qmatch_goalsub_abbrev_tac `left - withheld` >>
  Cases_on `value = 0` >> simp[] >> rpt strip_tac >>
  gvs[call_meter_claim_def, MIN_DEF, Abbr `left`] >> decide_tac
QED
