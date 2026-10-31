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

(* Exact return boundary, also valid when the parent is the arbitrary external
   caller: backing is deliberately not among its premises. *)
Theorem call_meter_pop_pair:
  s.contexts = (callee, saved)::(caller, callerSaved)::rest /\
  callee.msgParams.gasLimit - callee.gasUsed <= caller.gasUsed ==>
  pop_and_incorporate_context success s =
    let merged = absorb_state_gas
          (caller with gasUsed := caller.gasUsed -
             (callee.msgParams.gasLimit - callee.gasUsed))
          callee.stateGasLeft callee.stateGasSpilled callee.stateGasCommitted;
        credit = if callee.msgParams.newAccountCharged then new_account_state_gas else 0;
        settled = if success then
          repay_state_gas_spill_context (merged with <|
            logs := caller.logs ++ callee.logs;
            addRefund := caller.addRefund + callee.addRefund;
            subRefund := caller.subRefund + callee.subRefund |> )
          else merged with <|
            gasUsed := merged.gasUsed - MIN credit merged.stateGasSpilled;
            stateGasSpilled := merged.stateGasSpilled - MIN credit merged.stateGasSpilled;
            stateGasLeft := merged.stateGasLeft + (credit - MIN credit merged.stateGasSpilled) |>
    in (INL (), s with <|
      contexts := (settled, callerSaved)::rest;
      rollback := if success then s.rollback else saved
    |>)
Proof
  strip_tac >> Cases_on `success` >>
  Cases_on `callee.msgParams.newAccountCharged` >>
  simp[LET_THM, repay_state_gas_spill_def, credit_new_account_def,
       credit_state_gas_refund_def, absorb_state_gas_def,
       repay_state_gas_spill_context_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_current_context_def, pop_context_def, unuse_gas_def,
       push_logs_def, update_gas_refund_def, set_rollback_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def, combinTheory.o_DEF, combinTheory.C_DEF,
       context_component_equality] >>
  cong_tac (SOME 4) >> simp[context_component_equality]
QED

(* Both selected frames may be individually backed, yet returning an unused
   child grant destroys the parent's backing. All relevant meters are concrete;
   unrelated context fields and rollback data remain arbitrary. *)
Theorem call_meter_individual_pop_counterexample:
  let parent = c with <|gasUsed := 10; stateGasLeft := 0;
        stateGasSpilled := 10; stateGasCommitted := 0|>;
      child = c with <|gasUsed := 0; stateGasLeft := 0;
        stateGasSpilled := 0; stateGasCommitted := 0;
        msgParams := c.msgParams with <|gasLimit := 10; newAccountCharged := F |> |>;
      s = es with contexts := [(child,rb);(parent,rb)]
  in call_meter_backed parent /\ call_meter_backed child /\
     ISL (FST (pop_and_incorporate_context T s)) /\
     ~call_meter_backed
       (FST (HD (SND (pop_and_incorporate_context T s)).contexts))
Proof
  simp[LET_THM, call_meter_backed_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_current_context_def, pop_context_def, unuse_gas_def,
       push_logs_def, update_gas_refund_def, repay_state_gas_spill_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def, combinTheory.o_DEF, combinTheory.C_DEF,
       absorb_state_gas_def, repay_state_gas_spill_context_def]
QED

(* The exact sufficient parent margin includes the child's refundable meter
   as well as its unused execution grant. Reservoir repayment cancels the same
   quantity from backing and usage. *)
Theorem call_meter_success_pop_backed:
  caller.stateGasSpilled + caller.stateGasCommitted +
    (callee.msgParams.gasLimit - callee.gasUsed) +
    callee.stateGasSpilled + callee.stateGasCommitted <= caller.gasUsed ==>
  call_meter_backed (repay_state_gas_spill_context
    (absorb_state_gas
      (caller with gasUsed := caller.gasUsed -
        (callee.msgParams.gasLimit - callee.gasUsed))
      callee.stateGasLeft callee.stateGasSpilled callee.stateGasCommitted))
Proof
  simp[call_meter_backed_def, repay_state_gas_spill_context_def,
       absorb_state_gas_def, MIN_DEF] >>
  IF_CASES_TAC >> decide_tac
QED

Theorem call_meter_failure_credit_backed:
  caller.stateGasSpilled + caller.stateGasCommitted +
    gasLeft + sp + sc <= caller.gasUsed ==>
  let merged = absorb_state_gas (caller with gasUsed := caller.gasUsed - gasLeft)
        sg sp sc
  in call_meter_backed (merged with <|
    gasUsed := merged.gasUsed - MIN credit merged.stateGasSpilled;
    stateGasSpilled := merged.stateGasSpilled - MIN credit merged.stateGasSpilled;
    stateGasLeft := merged.stateGasLeft + (credit - MIN credit merged.stateGasSpilled) |>)
Proof
  simp[LET_THM, call_meter_backed_def, absorb_state_gas_def, MIN_DEF] >>
  IF_CASES_TAC >> decide_tac
QED

(* The refund claim is unchanged when a failed child restores its refundable
   meter. This is the bridge from the pre-restoration margin to the actual
   larger execution-gas refund of a REVERT. *)
Theorem call_meter_restore_grant:
  call_meter_backed c /\ c.gasUsed <= c.msgParams.gasLimit ==>
  c.msgParams.gasLimit - (c.gasUsed - c.stateGasSpilled - c.stateGasCommitted) =
    c.msgParams.gasLimit - c.gasUsed + c.stateGasSpilled + c.stateGasCommitted
Proof
  simp[call_meter_backed_def] >> decide_tac
QED

Theorem call_meter_call_push:
  s.contexts = (c,rb)::cs /\ ~fIN addr precompile_addresses /\
  c.stateGasSpilled + c.stateGasCommitted + grant <= c.gasUsed /\
  proceed_call op sender addr value ao az code grant output s = (r,t) ==>
  let child = FST (HD t.contexts);
      parent = FST (HD (TL t.contexts))
  in call_meter_backed child /\
     parent.stateGasSpilled + parent.stateGasCommitted +
       (child.msgParams.gasLimit - child.gasUsed) +
       child.stateGasSpilled + child.stateGasCommitted <= parent.gasUsed
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value` >>
  gvs[proceed_call_def, get_accounts_def, drain_state_gas_reservoir_def,
      set_current_context_def, get_rollback_def, read_memory_def,
      get_current_context_def, update_accounts_def,
      get_caller_def, get_value_def, get_static_def, push_context_def,
      bind_def, ignore_bind_def, return_def, LET_THM,
      initial_context_def, initial_msg_params_def, call_meter_backed_def]
QED

Theorem call_meter_create_push:
  s.contexts = (c,rb)::cs /\
  c.stateGasSpilled + c.stateGasCommitted + grant <= c.gasUsed /\
  proceed_create sender addr value code grant s = (r,t) ==>
  let child = FST (HD t.contexts);
      parent = FST (HD (TL t.contexts))
  in call_meter_backed child /\
     parent.stateGasSpilled + parent.stateGasCommitted +
       (child.msgParams.gasLimit - child.gasUsed) +
       child.stateGasSpilled + child.stateGasCommitted <= parent.gasUsed
Proof
  simp[proceed_create_def, drain_state_gas_reservoir_def,
       get_current_context_def, set_current_context_def,
       get_accounts_def, get_rollback_def, update_accounts_def,
       get_original_def, set_original_def, push_context_def,
       bind_def, ignore_bind_def, return_def, LET_THM,
       initial_context_def, initial_msg_params_def, call_meter_backed_def] >>
  rpt strip_tac >> gvs[]
QED
