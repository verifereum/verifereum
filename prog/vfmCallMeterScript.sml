Theory vfmCallMeter
Ancestors vfmCallBudget vfmCallMeterBase vfmExecution vfmContext vfmState vfmTypes arithmetic list

(* All result states, not only INL results, retain the suspended tail. *)
Definition call_meter_result_def:
  call_meter_result c rb rest t <=>
    ?d. t.contexts = (d,rb)::rest /\ call_meter_backed d /\
        d.gasUsed <= d.msgParams.gasLimit /\
        call_meter_claim d <= call_meter_claim c
End

Theorem call_meter_result_same:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit ==> call_meter_result c rb rest s
Proof
  rpt strip_tac >> simp[call_meter_result_def] >> qexists `c` >> simp[]
QED

Theorem call_meter_consume_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ consume_gas n s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), call_meter_result_def] >>
  gvs[call_meter_backed_def, call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_charge_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ charge_state_gas n s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  rpt strip_tac >> Cases_on `n <= c.stateGasLeft`
  >- (gvs[charge_state_gas_def, get_current_context_def, set_current_context_def,
          bind_def, return_def, call_meter_result_def] >>
      gvs[call_meter_backed_def, call_meter_claim_def]) >>
  Cases_on `n <= c.stateGasLeft + (c.msgParams.gasLimit - c.gasUsed)`
  >- (gvs[charge_state_gas_def, get_current_context_def, set_current_context_def,
          consume_gas_def, bind_def, ignore_bind_def, return_def, assert_def,
          fail_def, AllCaseEqs(), call_meter_result_def] >>
          gvs[call_meter_backed_def, call_meter_claim_def] >> decide_tac) >>
  gvs[charge_state_gas_def, get_current_context_def, bind_def, return_def, fail_def] >>
  irule call_meter_result_same >> simp[]
QED

Theorem call_meter_credit_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ credit_state_gas_refund n s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[credit_state_gas_refund_def, get_current_context_def, set_current_context_def,
       bind_def, return_def] >> rpt strip_tac >> gvs[call_meter_result_def] >>
  gvs[call_meter_backed_def, call_meter_claim_def, MIN_DEF] >>
  IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem call_meter_restore_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ restore_state_gas s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[restore_state_gas_def, get_current_context_def, set_current_context_def,
       bind_def, return_def] >> rpt strip_tac >>
  gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_restore_entry_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ restore_state_gas_to_entry sg s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[restore_state_gas_to_entry_def, get_current_context_def, set_current_context_def,
       bind_def, return_def] >> rpt strip_tac >>
  gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_commit_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ commit_state_gas s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[commit_state_gas_def, get_current_context_def, set_current_context_def,
       bind_def, return_def] >> rpt strip_tac >>
  gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_drain_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ drain_state_gas_reservoir s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[drain_state_gas_reservoir_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def] >> rpt strip_tac >>
  gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def]
QED

Theorem call_meter_forfeit_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ forfeit_remaining_gas s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[forfeit_remaining_gas_def, get_gas_left_def, consume_gas_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def] >>
  decide_tac
QED

Theorem call_meter_charge_account_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ charge_new_account charged s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  Cases_on `charged` >> simp[charge_new_account_def, return_def] >>
  metis_tac[call_meter_result_same, call_meter_charge_result]
QED

Theorem call_meter_credit_account_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ credit_new_account charged s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  Cases_on `charged` >> simp[credit_new_account_def, return_def] >>
  metis_tac[call_meter_result_same, call_meter_credit_result]
QED

(* Execution grants intentionally transfer claim rather than decrease it. *)
Definition call_meter_grant_result_def:
  call_meter_grant_result c amount rb rest t <=>
    ?d. t.contexts = (d,rb)::rest /\
        d.stateGasSpilled + d.stateGasCommitted + amount <= d.gasUsed /\
        d.gasUsed <= d.msgParams.gasLimit /\
        call_meter_claim d + amount = call_meter_claim c
End

Theorem call_meter_grant_consume:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  consume_gas amount s = (INL (),t) ==>
  call_meter_grant_result c amount rb rest t
Proof
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), call_meter_grant_result_def, call_meter_backed_def,
      call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_unuse_pair:
  s.contexts = (c,rb)::rest ==>
  unuse_gas amount s =
    if amount <= c.gasUsed then
      (INL (), s with contexts := (c with gasUsed := c.gasUsed - amount,rb)::rest)
    else (INR (SOME Impossible),s)
Proof
  simp[unuse_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem call_meter_restore_child_pair:
  s.contexts = (c,rb)::rest ==>
  restore_child_gas amount reservoir s =
    if amount <= c.gasUsed then
      (INL (), s with contexts :=
        (c with <|gasUsed := c.gasUsed - amount;
          stateGasLeft := c.stateGasLeft + reservoir|>,rb)::rest)
    else (INR (SOME Impossible),s)
Proof
  simp[restore_child_gas_def, unuse_gas_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def] >> strip_tac >> IF_CASES_TAC >>
  simp[] >> cong_tac (SOME 3) >> simp[context_component_equality, combinTheory.o_DEF]
QED

Theorem call_meter_restore_child_claim:
  s.contexts = (c,rb)::rest /\
  c.stateGasSpilled + c.stateGasCommitted + amount <= c.gasUsed /\
  c.gasUsed <= c.msgParams.gasLimit /\
  restore_child_gas amount reservoir s = (r,t) ==>
  r = INL () /\
  ?d. t.contexts = (d,rb)::rest /\ call_meter_backed d /\
      d.gasUsed <= d.msgParams.gasLimit /\
      call_meter_claim d = call_meter_claim c + amount
Proof
  rpt strip_tac >> drule call_meter_restore_child_pair >>
  disch_then (qspecl_then [`reservoir`, `amount`] assume_tac) >>
  `amount <= c.gasUsed` by decide_tac >>
  gvs[call_meter_backed_def, call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_withhold_pair:
  s.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit ==>
  let left = c.msgParams.gasLimit - c.gasUsed;
      amount = left - left DIV 64
  in withhold_create_gas s =
    (INL amount, s with contexts := (c with gasUsed := c.gasUsed + amount,rb)::rest)
Proof
  simp[withhold_create_gas_def, get_gas_left_def, consume_gas_def,
       get_current_context_def, set_current_context_def, bind_def, ignore_bind_def,
       return_def, assert_def, fail_def, LET_THM] >> rpt strip_tac >>
  `c.gasUsed + (c.msgParams.gasLimit - c.gasUsed -
    (c.msgParams.gasLimit - c.gasUsed) DIV 64) <= c.msgParams.gasLimit` by decide_tac >>
  simp[]
QED

Theorem call_meter_withhold_grant:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ withhold_create_gas s = (r,t) ==>
  ?amount. r = INL amount /\ call_meter_grant_result c amount rb rest t
Proof
  rpt strip_tac >> drule_all call_meter_withhold_pair >>
  gvs[LET_THM, call_meter_grant_result_def, call_meter_backed_def,
      call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_result_budget:
  call_meter_budget n grant s /\ n <= LENGTH s.contexts /\
  s.contexts = (c,rb)::rest /\ call_meter_result c rb rest t ==>
  call_meter_budget n grant t
Proof
  simp[call_meter_result_def] >> rpt strip_tac >>
  irule call_meter_budget_replace >> metis_tac[]
QED

Theorem call_meter_repay_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ repay_state_gas_spill s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[repay_state_gas_spill_def, repay_state_gas_spill_context_def,
       get_current_context_def, set_current_context_def, bind_def, return_def] >>
  rpt strip_tac >>
  gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def, MIN_DEF] >>
  IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem call_meter_return_grant:
  call_meter_grant_result c amount rb rest s /\
  restore_child_gas amount reservoir s = (r,t) ==>
  r = INL () /\ call_meter_result c rb rest t
Proof
  simp[call_meter_grant_result_def] >> strip_tac >>
  `d.stateGasSpilled + d.stateGasCommitted + amount <= d.gasUsed` by decide_tac >>
  drule_all call_meter_restore_child_claim >>
  strip_tac >> simp[call_meter_result_def] >> metis_tac[ADD_COMM]
QED

Theorem call_meter_restore_forfeit_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\
  ignore_bind restore_state_gas forfeit_remaining_gas s = (r,t) ==>
  call_meter_result c rb rest t
Proof
  simp[restore_state_gas_def, forfeit_remaining_gas_def, consume_gas_def,
       get_gas_left_def, get_current_context_def, set_current_context_def,
       ignore_bind_def, bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[call_meter_result_def, call_meter_backed_def, call_meter_claim_def] >>
  decide_tac
QED
