Theory vfmCallMeterProbe
Ancestors vfmExecution vfmContext vfmState vfmTypes vfmConstants arithmetic list

(* Internal callee invariant: no claim is made about a suspended external
   caller admitted by the exported CALL rules. *)
Definition call_meter_backed_def:
  call_meter_backed c <=> c.stateGasSpilled + c.stateGasCommitted <= c.gasUsed
End

Theorem call_meter_initial:
  call_meter_backed (initial_context callee code static output charged sg tx)
Proof
  simp[call_meter_backed_def, initial_context_def]
QED

Theorem call_meter_credit:
  s.contexts = (c,cb)::cs /\ call_meter_backed c /\
  credit_state_gas_refund n s = (INL (),t) ==>
  call_meter_backed (FST (HD t.contexts))
Proof
  simp[credit_state_gas_refund_def, get_current_context_def,
       set_current_context_def, bind_def, return_def] >>
  rpt strip_tac >> gvs[call_meter_backed_def, MIN_DEF] >>
  IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem call_meter_commit:
  s.contexts = (c,cb)::cs /\ call_meter_backed c /\
  commit_state_gas s = (INL (),t) ==>
  call_meter_backed (FST (HD t.contexts))
Proof
  simp[commit_state_gas_def, get_current_context_def,
       set_current_context_def, bind_def, return_def] >>
  rpt strip_tac >> gvs[call_meter_backed_def, ADD_COMM]
QED

Theorem call_meter_restore:
  s.contexts = (c,cb)::cs /\ call_meter_backed c /\
  restore_state_gas s = (INL (),t) ==>
  call_meter_backed (FST (HD t.contexts))
Proof
  simp[restore_state_gas_def, get_current_context_def,
       set_current_context_def, bind_def, return_def] >>
  rpt strip_tac >> gvs[call_meter_backed_def] >> decide_tac
QED

Theorem call_meter_restore_to_entry:
  s.contexts = (c,cb)::cs /\ call_meter_backed c /\
  restore_state_gas_to_entry sg s = (INL (),t) ==>
  call_meter_backed (FST (HD t.contexts))
Proof
  simp[restore_state_gas_to_entry_def, get_current_context_def,
       set_current_context_def, bind_def, return_def] >>
  rpt strip_tac >> gvs[call_meter_backed_def]
QED

Theorem call_meter_charge:
  s.contexts = (c,cb)::cs /\ call_meter_backed c /\
  charge_state_gas n s = (INL (),t) ==>
  call_meter_backed (FST (HD t.contexts))
Proof
  rpt strip_tac >>
  Cases_on `n <= c.stateGasLeft`
  >- gvs[charge_state_gas_def, get_current_context_def,
         set_current_context_def, bind_def, return_def, call_meter_backed_def] >>
  Cases_on `n <= c.stateGasLeft + (c.msgParams.gasLimit - c.gasUsed)` >>
  gvs[charge_state_gas_def, get_current_context_def,
      set_current_context_def, consume_gas_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      AllCaseEqs(), call_meter_backed_def] >> decide_tac
QED

(* A creation charge may spill by d. An existing refundable balance backed
   by g cannot erase a fresh execution charge cost when it is credited. *)
Theorem call_meter_credit_preserves_margin:
  !sp sc g cost stipend d n.
  sp + sc <= g /\ stipend <= cost ==>
  (sp + d - MIN n (sp + d)) + sc + stipend <=
    (g + cost + d) - MIN n (sp + d)
Proof
  rpt gen_tac >> strip_tac >> simp[MIN_DEF] >>
  IF_CASES_TAC >> decide_tac
QED

Theorem call_meter_stipend_after_credit:
  !sp sc g cost stipend stateCost sg.
  sp + sc <= g /\ stipend <= cost ==>
  stipend <= (g + cost + (stateCost - sg)) -
    MIN stateCost (sp + (stateCost - sg))
Proof
  rpt strip_tac >>
  drule_all call_meter_credit_preserves_margin >>
  disch_then (qspecl_then [`stateCost - sg`, `stateCost`] mp_tac) >>
  decide_tac
QED

(* This tests actual charge/credit sequencing, rather than assuming that the
   numeric spill increment is what the semantics implements. *)
Theorem call_meter_charge_credit_stipend:
  s.contexts = (c,cb)::cs /\ call_meter_backed c /\
  stipend <= cost /\
  ignore_bind (consume_gas cost)
    (ignore_bind (charge_new_account charged) (credit_new_account charged)) s =
      (INL (),t) ==>
  stipend <= (FST (HD t.contexts)).gasUsed
Proof
  rpt strip_tac >> Cases_on `charged` >>
  gvs[charge_new_account_def, credit_new_account_def,
      charge_state_gas_def, credit_state_gas_refund_def,
      consume_gas_def, get_current_context_def, set_current_context_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      AllCaseEqs(), call_meter_backed_def] >>
  Cases_on `new_account_state_gas <= c.stateGasLeft`
  >- (gvs[get_current_context_def, set_current_context_def,
          bind_def, return_def, MIN_DEF] >> IF_CASES_TAC >> decide_tac) >>
  Cases_on `new_account_state_gas <=
    c.stateGasLeft + (c.msgParams.gasLimit - (cost + c.gasUsed))` >>
  gvs[get_current_context_def, set_current_context_def, consume_gas_def,
      bind_def, return_def, assert_def, fail_def, AllCaseEqs()] >>
  simp[MIN_DEF] >> IF_CASES_TAC >> decide_tac
QED

Theorem call_meter_credit_pair:
  s.contexts = (c,cb)::cs ==>
  credit_state_gas_refund n s =
    (INL (), s with contexts :=
      (c with <|
        gasUsed := c.gasUsed - MIN n c.stateGasSpilled;
        stateGasSpilled := c.stateGasSpilled - MIN n c.stateGasSpilled;
        stateGasLeft := c.stateGasLeft + (n - MIN n c.stateGasSpilled)
       |>,cb)::cs)
Proof
  simp[credit_state_gas_refund_def, get_current_context_def,
       set_current_context_def, bind_def, return_def] >>
  strip_tac >> cong_tac (SOME 4) >> simp[context_component_equality]
QED

(* CREATE no-entry aborts do not return a withheld grant in this semantics.
   Unlike CALL's credited abort they need no incoming meter premise. *)
Theorem call_meter_abort_create_pair:
  s.contexts = (c,cb)::cs /\ LENGTH c.stack < stack_limit ==>
  abort_create s =
    (INL (), s with contexts :=
      (c with <|stack := b2w F::c.stack; pc := SUC c.pc|>,cb)::cs)
Proof
  simp[abort_create_def, push_stack_def, inc_pc_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[stack_limit_def] >>
  cong_tac (SOME 4) >> simp[context_component_equality]
QED
