Theory vfmProgCallTailProbe
Ancestors vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmTypes vfmBuffer words list arithmetic finite_map

Theorem return_destination_case_const[local]:
  !(x : return_destination) (r : execution_state -> 'a execution_result).
    return_destination_CASE x (\m : memory_range. r) (\a : address. r) = r
Proof
  Cases_on `x` >> simp[return_destination_CASE_rator]
QED

Theorem handle_create_not_none[local]:
  !e s. e <> NONE /\ s.contexts <> [] ==> handle_create e s = reraise e s
Proof
  rpt strip_tac >> Cases_on `e` >>
  gvs[handle_create_def, get_return_data_def, get_output_to_def,
      reraise_def, bind_def, return_def, ignore_bind_def,
      get_current_context_def, return_destination_case_const, CaseEq "bool"]
QED

Theorem repay_absorb_meter_fields[local]:
  (repay_state_gas_spill_context (absorb_state_gas c sg sp cm)).gasUsed =
    c.gasUsed - MIN (c.stateGasLeft + sg) (c.stateGasSpilled + sp) /\
  (repay_state_gas_spill_context (absorb_state_gas c sg sp cm)).stateGasLeft =
    c.stateGasLeft + sg - MIN (c.stateGasLeft + sg) (c.stateGasSpilled + sp) /\
  (repay_state_gas_spill_context (absorb_state_gas c sg sp cm)).stateGasSpilled =
    c.stateGasSpilled + sp - MIN (c.stateGasLeft + sg) (c.stateGasSpilled + sp) /\
  (repay_state_gas_spill_context (absorb_state_gas c sg sp cm)).stateGasBaseline =
    c.stateGasBaseline /\
  (repay_state_gas_spill_context (absorb_state_gas c sg sp cm)).stateGasCommitted =
    c.stateGasCommitted + cm
Proof
  simp[repay_state_gas_spill_context_def, absorb_state_gas_def]
QED

Theorem restored_unused_gas[local]:
  x <= limit ==> limit - (x - sp) = (limit - x) + MIN sp x
Proof
  strip_tac >> Cases_on `sp <= x` >> simp[MIN_DEF] >> decide_tac
QED

Theorem restored_unused_gas_bound[local]:
  x <= limit /\ (limit - x) + MIN sp x <= callerGas ==>
  limit - (x - sp) <= callerGas
Proof
  strip_tac >> asm_simp_tac pure_ss [restored_unused_gas]
QED

Theorem restored_unused_gas_sub[local]:
  x <= limit ==>
  callerGas - (limit - (x - sp)) = callerGas - (limit - x) - MIN sp x
Proof
  strip_tac >> asm_simp_tac pure_ss [restored_unused_gas] >> decide_tac
QED

Theorem proceed_call_precompile_success_meter[local]:
  s.contexts = (parent,prb)::rest /\ s.rollback = rb /\
  parent.msgParams.callee = sender /\
  data = buffer_take argsOffset argsSize parent.memory /\
  fIN addr precompile_addresses /\
  (!s ctxt crb rest.
    s.contexts = (ctxt,crb)::rest /\
    ctxt.msgParams.data = buffer_of_list data /\
    ctxt.msgParams.gasLimit = stipend /\
    ctxt.gasUsed = 0 /\ ctxt.returnData = [] ==>
    (dispatch_precompiles addr s : unit execution_result) =
      (INR NONE, s with contexts :=
        (ctxt with <|gasUsed := pg; returnData := out|>,crb)::rest)) ==>
  ?c. c.msgParams.outputTo = outputTo /\
      c.msgParams.gasLimit = stipend /\ c.gasUsed = pg /\
      c.returnData = out /\
      c.logs = transfer_log sender
        (if op = CallCode \/ op = DelegateCall then sender else addr) value /\
      c.addRefund = 0 /\ c.subRefund = 0 /\
      c.stateGasLeft = parent.stateGasLeft /\ c.stateGasSpilled = 0 /\
      c.stateGasCommitted = 0 /\ c.stateGasBaseline = parent.stateGasLeft /\
      proceed_call op sender addr value argsOffset argsSize code stipend outputTo s =
        (INR NONE, s with <|
          rollback := rb with accounts updated_by
            (if op <> CallCode /\ 0 < value
             then transfer_value sender addr value else I);
          contexts := (c,rb)::(parent with <|stateGasLeft := 0|>,prb)::rest |> )
Proof
  strip_tac >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  simp[proceed_call_def, drain_state_gas_reservoir_def,
       get_rollback_def, get_accounts_def, read_memory_def,
       update_accounts_def, get_caller_def, get_value_def, get_static_def,
       get_current_context_def, set_current_context_def, push_context_def,
       bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `CONS (ctxt,rb)` >>
  qmatch_goalsub_abbrev_tac `dispatch_precompiles addr ds` >>
  `ds.contexts = (ctxt,rb)::(parent with stateGasLeft := 0,prb)::rest` by
    simp[Abbr `ds`] >>
  `ctxt.msgParams.data = buffer_of_list data /\
   ctxt.msgParams.gasLimit = stipend /\ ctxt.gasUsed = 0 /\
   ctxt.returnData = []` by
    simp[Abbr `ctxt`, initial_context_def, initial_msg_params_def] >>
  qpat_x_assum `!s ctxt crb rest. _` drule_all >>
  disch_then SUBST1_TAC >>
  qexists_tac `ctxt with <|gasUsed := pg; returnData := out|>` >>
  simp[Abbr `ctxt`, initial_context_def, initial_msg_params_def,
       Abbr `ds`, execution_state_component_equality,
       rollback_state_component_equality]
QED

Theorem proceed_call_precompile_success[local]:
  s.contexts = (parent,prb)::rest /\ s.rollback = rb /\
  parent.msgParams.callee = sender /\
  data = buffer_take argsOffset argsSize parent.memory /\
  fIN addr precompile_addresses /\
  (!s ctxt crb rest.
    s.contexts = (ctxt,crb)::rest /\
    ctxt.msgParams.data = buffer_of_list data /\
    ctxt.msgParams.gasLimit = stipend /\
    ctxt.gasUsed = 0 /\ ctxt.returnData = [] ==>
    (dispatch_precompiles addr s : unit execution_result) =
      (INR NONE, s with contexts :=
        (ctxt with <|gasUsed := pg; returnData := out|>,crb)::rest)) ==>
  ?c. c.msgParams.outputTo = outputTo /\
      c.msgParams.gasLimit = stipend /\ c.gasUsed = pg /\
      c.returnData = out /\
      c.logs = transfer_log sender
        (if op = CallCode \/ op = DelegateCall then sender else addr) value /\
      c.addRefund = 0 /\ c.subRefund = 0 /\
      proceed_call op sender addr value argsOffset argsSize code stipend outputTo s =
        (INR NONE, s with <|
          rollback := rb with accounts updated_by
            (if op <> CallCode /\ 0 < value
             then transfer_value sender addr value else I);
          contexts := (c,rb)::(parent with <|stateGasLeft := 0|>,prb)::rest |> )
Proof
  strip_tac >> drule_all proceed_call_precompile_success_meter >>
  disch_then (qspecl_then [`value`, `outputTo`, `op`, `code`] strip_assume_tac) >>
  qexists_tac `c` >> simp[]
QED

Theorem handle_step_success_memory_exact[local]:
  s.contexts = (c,crb)::(parent,prb)::rest /\
  c.msgParams.outputTo = Memory mr /\
  c.addRefund = 0 /\ c.subRefund = 0 /\
  c.msgParams.gasLimit - c.gasUsed <= parent.gasUsed /\
  LENGTH parent.stack < stack_limit /\
  merged = repay_state_gas_spill_context
             (absorb_state_gas
                (parent with gasUsed :=
                   parent.gasUsed - (c.msgParams.gasLimit - c.gasUsed))
                c.stateGasLeft c.stateGasSpilled c.stateGasCommitted) ==>
  handle_step NONE s =
    (INL (), s with contexts :=
      (merged with <|
         pc := parent.pc + 1; returnData := c.returnData;
         stack := 1w::parent.stack;
         memory := buffer_write mr.offset (TAKE mr.size c.returnData) parent.memory;
         logs := parent.logs ++ c.logs
       |>,prb)::rest)
Proof
  strip_tac >> qpat_x_assum `merged = _` SUBST1_TAC >>
  simp[repay_state_gas_spill_def, repay_state_gas_spill_context_def,
       absorb_state_gas_def,
       handle_step_def, handle_create_def, handle_exception_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       pop_context_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
       inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       get_current_context_def, set_current_context_def,
       handle_def, reraise_def, bind_def, ignore_bind_def, return_def,
       assert_def, stack_limit_def,
       execution_state_component_equality, context_component_equality]
QED


Theorem handle_step_invalid_outermost_exact[local]:
  s.contexts = [(c,cb)] /\
  c.gasUsed - c.stateGasSpilled <= c.msgParams.gasLimit ==>
  handle_step (SOME InvalidOpcode) s =
    (INR (SOME InvalidOpcode), s with contexts :=
      [(c with <|returnData := []; gasUsed := c.msgParams.gasLimit;
         addRefund := 0; subRefund := 0;
         stateGasLeft := c.stateGasBaseline; stateGasSpilled := 0|>,cb)])
Proof
  strip_tac >>
  `c.msgParams.gasLimit - (c.gasUsed - c.stateGasSpilled) +
     (c.gasUsed - c.stateGasSpilled) = c.msgParams.gasLimit` by decide_tac >>
  simp[handle_step_def, vfm_abort_def, handle_create_not_none,
       handle_def, reraise_def, handle_exception_def,
       restore_state_gas_def, forfeit_remaining_gas_def,
       get_gas_left_def, consume_gas_def, set_return_data_def,
       get_num_contexts_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def,
       execution_state_component_equality, context_component_equality]
QED

(* Independent copy of the context refill interface from vfmProg. *)
Definition credit_new_account_context_def:
  credit_new_account_context ctxt charged =
    ctxt with <|
      gasUsed := ctxt.gasUsed -
                 MIN (if charged then new_account_state_gas else 0)
                     ctxt.stateGasSpilled;
      stateGasSpilled := ctxt.stateGasSpilled -
                 MIN (if charged then new_account_state_gas else 0)
                     ctxt.stateGasSpilled;
      stateGasLeft := ctxt.stateGasLeft +
                 ((if charged then new_account_state_gas else 0) -
                  MIN (if charged then new_account_state_gas else 0)
                      ctxt.stateGasSpilled) |>
End

Theorem handle_step_invalid_inner_exact[local]:
  s.contexts = (c,cb)::(parent,pb)::rest /\
  c.gasUsed - c.stateGasSpilled <= c.msgParams.gasLimit /\
  LENGTH parent.stack < stack_limit /\
  merged = credit_new_account_context
    (absorb_state_gas parent c.stateGasBaseline 0 c.stateGasCommitted)
    c.msgParams.newAccountCharged ==>
  handle_step (SOME InvalidOpcode) s =
    (INL (), s with <|rollback := cb; contexts :=
      (merged with <|pc := SUC parent.pc; stack := 0w::parent.stack;
                      returnData := []|>,pb)::rest|>)
Proof
  strip_tac >> qpat_x_assum `merged = _` SUBST1_TAC >>
  `c.msgParams.gasLimit - (c.gasUsed - c.stateGasSpilled) +
     (c.gasUsed - c.stateGasSpilled) = c.msgParams.gasLimit` by decide_tac >>
  simp[handle_step_def, vfm_abort_def, handle_create_not_none,
       handle_def, reraise_def, handle_exception_def,
       restore_state_gas_def, forfeit_remaining_gas_def,
       get_gas_left_def, consume_gas_def, set_return_data_def,
       get_num_contexts_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def] >>
  Cases_on `c.msgParams.outputTo` >>
  Cases_on `c.msgParams.newAccountCharged` >>
  simp[pop_and_incorporate_context_def, get_return_data_def, get_output_to_def,
       get_gas_left_def, pop_context_def, unuse_gas_def,
       absorb_state_gas_def, credit_new_account_def, credit_state_gas_refund_def,
       credit_new_account_context_def, set_rollback_def, stack_limit_def,
       AC ADD_ASSOC ADD_COMM,
       inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def,
       execution_state_component_equality, context_component_equality]
QED

Theorem handle_exception_success_outermost_exact[local]:
  s.contexts = [(c,cb)] ==>
  handle_exception NONE s = (INR NONE,s)
Proof
  simp[handle_exception_def, get_num_contexts_def, reraise_def,
       bind_def, ignore_bind_def, return_def]
QED

Theorem handle_exception_success_memory_exact[local]:
  s.contexts = (c,crb)::(parent,prb)::rest /\
  c.msgParams.outputTo = Memory mr /\
  c.msgParams.gasLimit - c.gasUsed <= parent.gasUsed /\
  LENGTH parent.stack < stack_limit /\
  merged = repay_state_gas_spill_context
             (absorb_state_gas
                (parent with gasUsed :=
                   parent.gasUsed - (c.msgParams.gasLimit - c.gasUsed))
                c.stateGasLeft c.stateGasSpilled c.stateGasCommitted) ==>
  handle_exception NONE s =
    (INL (), s with contexts :=
      (merged with <|
         pc := SUC parent.pc; returnData := c.returnData;
         stack := 1w::parent.stack;
         memory := buffer_write mr.offset (TAKE mr.size c.returnData) parent.memory;
         logs := parent.logs ++ c.logs;
         addRefund := parent.addRefund + c.addRefund;
         subRefund := parent.subRefund + c.subRefund
       |>,prb)::rest)
Proof
  strip_tac >> qpat_x_assum `merged = _` SUBST1_TAC >>
  simp[repay_state_gas_spill_def, repay_state_gas_spill_context_def,
       absorb_state_gas_def, handle_exception_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       pop_context_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
       inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       get_current_context_def, set_current_context_def,
       reraise_def, bind_def, ignore_bind_def, return_def,
       assert_def, stack_limit_def,
       execution_state_component_equality, context_component_equality]
QED

Theorem handle_exception_success_code_exact[local]:
  s.contexts = (c,crb)::(parent,prb)::rest /\
  c.msgParams.outputTo = Code addr /\
  c.msgParams.gasLimit - c.gasUsed <= parent.gasUsed /\
  LENGTH parent.stack < stack_limit /\
  merged = repay_state_gas_spill_context
             (absorb_state_gas
                (parent with gasUsed :=
                   parent.gasUsed - (c.msgParams.gasLimit - c.gasUsed))
                c.stateGasLeft c.stateGasSpilled c.stateGasCommitted) ==>
  handle_exception NONE s =
    (INL (), s with contexts :=
      (merged with <|
         pc := SUC parent.pc; returnData := [];
         stack := w2w addr::parent.stack;
         logs := parent.logs ++ c.logs;
         addRefund := parent.addRefund + c.addRefund;
         subRefund := parent.subRefund + c.subRefund
       |>,prb)::rest)
Proof
  strip_tac >> qpat_x_assum `merged = _` SUBST1_TAC >>
  simp[repay_state_gas_spill_def, repay_state_gas_spill_context_def,
       absorb_state_gas_def, handle_exception_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       pop_context_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
       inc_pc_def, set_return_data_def, push_stack_def,
       get_current_context_def, set_current_context_def,
       reraise_def, bind_def, ignore_bind_def, return_def,
       assert_def, stack_limit_def,
       execution_state_component_equality, context_component_equality]
QED

Theorem handle_create_empty_memory_exact[local]:
  s.contexts = (c,cb)::rest /\ c.returnData = [] /\
  c.msgParams.outputTo = Memory mr ==>
  (handle_create NONE s : unit execution_result) = (INR NONE,s)
Proof
  simp[handle_create_def, get_return_data_def, get_output_to_def,
       get_current_context_def, bind_def, return_def, reraise_def]
QED

Theorem handle_create_empty_code_exact[local]:
  s.contexts = (c,cb)::rest /\ c.returnData = [] /\
  c.msgParams.outputTo = Code addr /\ c.gasUsed <= c.msgParams.gasLimit ==>
  (handle_create NONE s : unit execution_result) =
    (INR NONE,s with rollback := s.rollback with accounts :=
      update_account addr
        (lookup_account addr s.rollback.accounts with code := [])
        s.rollback.accounts)
Proof
  simp[handle_create_def, get_return_data_def, get_output_to_def,
       get_current_context_def, set_current_context_def,
       consume_gas_def, charge_state_gas_def, update_accounts_def,
       get_accounts_def, bind_def, ignore_bind_def, return_def,
       assert_def, reraise_def, word_size_def, max_code_size_def,
       rollback_state_component_equality,
       execution_state_component_equality, context_component_equality]
QED

Theorem handle_step_empty_memory_exact[local]:
  s.contexts = (c,cb)::rest /\ c.returnData = [] /\
  c.msgParams.outputTo = Memory mr ==>
  handle_step NONE s = handle_exception NONE s
Proof
  strip_tac >>
  simp[handle_step_def, vfm_abort_def, handle_create_empty_memory_exact,
       handle_def]
QED

Theorem handle_step_empty_code_exact[local]:
  s.contexts = (c,cb)::rest /\ c.returnData = [] /\
  c.msgParams.outputTo = Code addr /\ c.gasUsed <= c.msgParams.gasLimit ==>
  handle_step NONE s =
    handle_exception NONE
      (s with rollback := s.rollback with accounts :=
        update_account addr
          (lookup_account addr s.rollback.accounts with code := [])
          s.rollback.accounts)
Proof
  strip_tac >>
  drule_all handle_create_empty_code_exact >>
  strip_tac >>
  simp[handle_step_def, vfm_abort_def, handle_def]
QED
