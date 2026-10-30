Theory vfmCallRefundProbe
Ancestors vfmProg vfmExecution vfmExecutionProp vfmContext vfmState
  vfmConstants vfmTypes finite_map list

Definition refund_probe_context_def:
  refund_probe_context = <|
    stack := [0w; 256w; 1w; 0w; 0w; 0w; 0w];
    memory := empty_buffer; pc := 0; jumpDest := NONE; returnData := [];
    gasUsed := 0; addRefund := 0; subRefund := 0;
    stateGasLeft := 183600; stateGasSpilled := 183600;
    stateGasBaseline := 183600; stateGasCommitted := 0; logs := [];
    msgParams := <|caller := 0w; callee := 0w; code := [0xf1w];
      parsed := parse_code 0 FEMPTY [0xf1w]; value := 0; gasLimit := 1000000;
      data := empty_buffer; static := F; outputTo := Memory <|offset := 0; size := 0|>;
      newAccountCharged := F|> |>
End

Definition refund_probe_rollback_def:
  refund_probe_rollback = <|accounts := K empty_account_state;
    tStorage := empty_transient_storage; accesses := <|addresses := fEMPTY; storageKeys := fEMPTY|>;
    toDelete := []|>
End

Definition refund_probe_state_def:
  refund_probe_state = <|
    contexts := [(refund_probe_context, refund_probe_rollback)];
    txParams := ARB; rollback := refund_probe_rollback;
    originalAccounts := K empty_account_state; msdomain := Collect empty_domain |>
End

Theorem refund_probe_impossible:
  let out = step_call Call refund_probe_state in
  FST out = INR (SOME Impossible) /\
  (FST (HD (SND out).contexts)).gasUsed = 0 /\
  (FST (HD (SND out).contexts)).stateGasLeft = 0 /\
  (FST (HD (SND out).contexts)).stateGasSpilled = 0 /\
  (FST (HD (SND out).contexts)).stack = [0w] /\
  (FST (HD (SND out).contexts)).pc = 0
Proof
  simp[refund_probe_state_def, refund_probe_context_def, refund_probe_rollback_def,
       call_has_value_def, step_call_def, pop_stack_def, memory_expansion_info_def,
       max_expansion_range_def, word_size_def, get_delegate_def,
       vfmBufferTheory.buffer_length_def, vfmBufferTheory.empty_buffer_def,
       call_value_cost_def, call_gas_def, call_stipend_def,
       access_address_def, access_check_def, domain_check_def,
       msdomain_add_def, accesses_add_def, set_domain_def,
       is_delegation_def, assert_not_static_def, get_static_def,
       new_account_state_gas_def, cost_per_state_byte_def,
       state_bytes_per_new_account_def, cold_access_cost_def,
       memory_expansion_cost_def,
       delegate_check_def,
       get_accounts_def, get_gas_left_def, get_callee_def,
       get_num_contexts_def, consume_gas_def, charge_new_account_def,
       charge_state_gas_def, credit_new_account_def, credit_state_gas_refund_def,
       abort_call_value_def, unuse_gas_def, expand_memory_def,
       push_stack_def, set_return_data_def, inc_pc_def, stack_limit_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       lookup_account_def, empty_account_state_def, account_empty_def] >>
  EVAL_TAC
QED

Theorem refund_probe_execution_cost:
  static_gas Call + cold_access_cost + call_value_cost = 14300 /\
  call_gas 1 0 (1000000 - 14300) 0 0 = (0,2300) /\
  new_account_state_gas = 183600
Proof
  EVAL_TAC
QED

Theorem refund_probe_nonempty:
  refund_probe_state.contexts <> []
Proof
  simp[refund_probe_state_def]
QED

Theorem refund_probe_nonempty_safety_false:
  ~(!s r t. s.contexts <> [] /\ step_call Call s = (r,t) ==>
      !e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  strip_tac >>
  first_x_assum (qspecl_then [`refund_probe_state`,
    `FST (step_call Call refund_probe_state)`,
    `SND (step_call Call refund_probe_state)`] mp_tac) >>
  mp_tac refund_probe_impossible >>
  simp[LET_THM, refund_probe_nonempty]
QED
