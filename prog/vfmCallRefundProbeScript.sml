Theory vfmCallRefundProbe
Ancestors vfmProg vfmExecution vfmExecutionProp vfmContext vfmState
  vfmConstants vfmTypes finite_map list
Libs wordsLib

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

Theorem refund_probe_wf:
  wf_state refund_probe_state
Proof
  simp[refund_probe_state_def, refund_probe_context_def, refund_probe_rollback_def,
       wf_state_def, wf_context_def, all_accounts_def, wf_accounts_def,
       stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def,
       outputTo_consistent_ctx_def, context_limit_def, stack_limit_def,
       empty_account_state_def, lookup_account_def] >>
  EVAL_TAC
QED

Theorem refund_probe_opcode[local]:
  parse_opcode [0xf1w] = SOME Call
Proof
  rewrite_tac[vfmOperationTheory.parse_opcode_cond_thm] >> EVAL_TAC
QED

Theorem refund_probe_step:
  step refund_probe_state = step_call Call refund_probe_state
Proof
  assume_tac refund_probe_opcode >>
  `FLOOKUP (parse_code 0 FEMPTY [0xf1w]) 0 = SOME Call` by
    (once_rewrite_tac[parse_code_def] >>
     simp[vfmOperationTheory.opcode_def] >>
     once_rewrite_tac[parse_code_def] >> simp[FLOOKUP_UPDATE]) >>
  mp_tac refund_probe_impossible >> simp[LET_THM] >> strip_tac >>
  simp[Once step_def, get_current_context_def, handle_def, bind_def, return_def,
       refund_probe_state_def, refund_probe_context_def] >>
  rewrite_tac[GSYM refund_probe_context_def, GSYM refund_probe_state_def] >>
  simp[step_inst_def, ignore_bind_def, bind_def] >>
  Cases_on `step_call Call refund_probe_state` >>
  gvs[handle_step_def, vfm_abort_def, reraise_def] >>
  qpat_x_assum `_ = step_call Call _` (fn th => rewrite_tac[GSYM th]) >>
  simp[vfm_abort_def, reraise_def]
QED

Theorem refund_probe_next_iterates:
  !n. FST (FUNPOW (\x. if ISR (FST x) then x else step (SND x)) n
        (INL (), refund_probe_state)) =
      (if n = 0 then INL () else INR (SOME Impossible))
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_SUC] >>
  Cases_on `n = 0` >> gvs[]
  >- (simp[refund_probe_step] >>
      mp_tac refund_probe_impossible >> simp[LET_THM]) >>
  Cases_on `FUNPOW (\x. if ISR (FST x) then x else step (SND x)) n
                  (INL (), refund_probe_state)` >> gvs[]
QED

(* All arithmetic conditions hold, but the destination is a precompile. *)
Theorem refund_probe_arithmetic_conditions:
  let ss = refund_probe_context.stack;
      p = refund_probe_context.msgParams;
      rb = refund_probe_rollback;
      d = Collect empty_domain;
      toAccount = lookup_account (256w:address) rb.accounts in
  6 + 1 <= LENGTH ss /\
  1 = (if call_has_value Call then 1 else 0) /\
  ISL (INL ():unit + exception option) /\
  0 = w2n (EL 0 ss) /\ (256w:address) = w2w (EL 1 ss) /\
  1 = (if 0 < 1 then w2n (EL 2 ss) else 0) /\
  0 = w2n (EL (1 + 2) ss) /\ 0 = w2n (EL (1 + 3) ss) /\
  0 = w2n (EL (1 + 4) ss) /\ 0 = w2n (EL (1 + 5) ss) /\
  max_expansion_range (0,0) (0,0) = (0,0) /\
  empty_buffer = expanded_memory empty_buffer 0 0 /\
  call_value_cost = (if 0 < 1 then call_value_cost else 0) /\
  T = (Call = Call /\ 0 < 1 /\ account_empty toAccount) /\
  183600 = (if T then new_account_state_gas else 0) /\
  (if T then new_account_state_gas else 0) <= 183600 /\
  delegate_check toAccount.code (msdomain_add 256w d)
    (accesses_add 256w rb) 0 (accesses_add 256w rb) (msdomain_add 256w d) /\
  0 = memory_cost empty_buffer 0 0 /\
  call_gas 1 0 (p.gasLimit - (0 + (static_gas Call +
      access_cost rb 256w + call_value_cost + 0 + 0))) 0 0 = (0,2300) /\
  14300 = static_gas Call + access_cost rb 256w + call_value_cost + 0 + 0 + 0 /\
  0 + 14300 <= p.gasLimit /\
  is_call Call /\ Call <> Create /\ Call <> Create2 /\
  (0 < 1 ==> ~p.static) /\
  d = Collect empty_domain /\ 2300 <= call_stipend
Proof
  simp[refund_probe_context_def, refund_probe_rollback_def, LET_THM,
       call_has_value_def, max_expansion_range_def, expanded_memory_def,
       memory_cost_def, memory_expansion_info_def, word_size_def,
       memory_expansion_cost_def, vfmBufferTheory.empty_buffer_def,
       vfmBufferTheory.buffer_length_def, lookup_account_def,
       empty_account_state_def, account_empty_def, delegate_check_def,
       get_delegate_def, is_delegation_def, access_cost_def,
       call_value_cost_def, cold_access_cost_def, new_account_state_gas_def,
       call_gas_def, call_stipend_def, is_call_def] >>
  EVAL_TAC
QED

Theorem refund_probe_destination_is_precompile:
  fIN (256w:address) precompile_addresses
Proof
  rewrite_tac[precompile_addresses_def, finite_setTheory.fIN_fset_ABS] >> EVAL_TAC
QED

Definition refund_candidate_context_def:
  refund_candidate_context = refund_probe_context with
    stack := [0w; 100w; 1w; 0w; 0w; 0w; 0w]
End

Definition refund_candidate_state_def:
  refund_candidate_state = refund_probe_state with
    contexts := [(refund_candidate_context, refund_probe_rollback)]
End

Theorem refund_candidate_not_precompile:
  ~fIN (100w:address) precompile_addresses
Proof
  rewrite_tac[precompile_addresses_def, finite_setTheory.fIN_fset_ABS] >> EVAL_TAC
QED

Theorem refund_candidate_impossible:
  let out = step_call Call refund_candidate_state in
  FST out = INR (SOME Impossible) /\
  (FST (HD (SND out).contexts)).gasUsed = 0 /\
  (FST (HD (SND out).contexts)).stateGasLeft = 0 /\
  (FST (HD (SND out).contexts)).stateGasSpilled = 0 /\
  (FST (HD (SND out).contexts)).stack = [0w] /\
  (FST (HD (SND out).contexts)).pc = 0
Proof
  simp[refund_candidate_state_def, refund_candidate_context_def,
       refund_probe_state_def, refund_probe_context_def, refund_probe_rollback_def,
       call_has_value_def, step_call_def, pop_stack_def, memory_expansion_info_def,
       max_expansion_range_def, word_size_def, get_delegate_def,
       vfmBufferTheory.buffer_length_def, vfmBufferTheory.empty_buffer_def,
       call_value_cost_def, call_gas_def, call_stipend_def,
       access_address_def, access_check_def, domain_check_def,
       msdomain_add_def, accesses_add_def, set_domain_def,
       is_delegation_def, assert_not_static_def, get_static_def,
       new_account_state_gas_def, cost_per_state_byte_def,
       state_bytes_per_new_account_def, cold_access_cost_def,
       memory_expansion_cost_def, delegate_check_def,
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

Theorem refund_candidate_wf:
  wf_state refund_candidate_state
Proof
  simp[refund_candidate_state_def, refund_candidate_context_def,
       refund_probe_state_def, refund_probe_context_def, refund_probe_rollback_def,
       wf_state_def, wf_context_def, all_accounts_def, wf_accounts_def,
       stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def,
       outputTo_consistent_ctx_def, context_limit_def, stack_limit_def,
       empty_account_state_def, lookup_account_def] >> EVAL_TAC
QED

Theorem refund_candidate_step:
  step refund_candidate_state = step_call Call refund_candidate_state
Proof
  assume_tac refund_probe_opcode >>
  `FLOOKUP (parse_code 0 FEMPTY [0xf1w]) 0 = SOME Call` by
    (once_rewrite_tac[parse_code_def] >> simp[vfmOperationTheory.opcode_def] >>
     once_rewrite_tac[parse_code_def] >> simp[FLOOKUP_UPDATE]) >>
  `get_current_context refund_candidate_state =
     (INL refund_candidate_context, refund_candidate_state)` by
    simp[get_current_context_def, return_def, refund_candidate_state_def] >>
  `FLOOKUP refund_candidate_context.msgParams.parsed
          refund_candidate_context.pc = SOME Call` by
    simp[refund_candidate_context_def, refund_probe_context_def] >>
  mp_tac refund_candidate_impossible >> simp[LET_THM] >> strip_tac >>
  simp[Once step_def, handle_def, bind_def, return_def,
       step_inst_def, ignore_bind_def] >>
  Cases_on `step_call Call refund_candidate_state` >>
  gvs[handle_step_def, vfm_abort_def, reraise_def] >>
  qpat_x_assum `_ = step_call Call _` (fn th => rewrite_tac[GSYM th]) >>
  simp[vfm_abort_def, reraise_def]
QED

Theorem refund_candidate_next_iterates:
  !n. FST (FUNPOW (\x. if ISR (FST x) then x else step (SND x)) n
        (INL (), refund_candidate_state)) =
      (if n = 0 then INL () else INR (SOME Impossible))
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_SUC] >>
  Cases_on `n = 0` >> gvs[]
  >- (simp[refund_candidate_step] >>
      mp_tac refund_candidate_impossible >> simp[LET_THM]) >>
  Cases_on `FUNPOW (\x. if ISR (FST x) then x else step (SND x)) n
                  (INL (), refund_candidate_state)` >> gvs[]
QED

Theorem refund_candidate_rule_conditions:
  let ss = refund_candidate_context.stack;
      p = refund_candidate_context.msgParams;
      rb = refund_probe_rollback;
      d = Collect empty_domain;
      toAccount = lookup_account (100w:address) rb.accounts in
  6 + 1 <= LENGTH ss /\
  1 = (if call_has_value Call then 1 else 0) /\
  ISL (INL ():unit + exception option) /\
  0 = w2n (EL 0 ss) /\ (100w:address) = w2w (EL 1 ss) /\
  1 = (if 0 < 1 then w2n (EL 2 ss) else 0) /\
  0 = w2n (EL (1 + 2) ss) /\ 0 = w2n (EL (1 + 3) ss) /\
  0 = w2n (EL (1 + 4) ss) /\ 0 = w2n (EL (1 + 5) ss) /\
  max_expansion_range (0,0) (0,0) = (0,0) /\
  empty_buffer = expanded_memory empty_buffer 0 0 /\
  call_value_cost = (if 0 < 1 then call_value_cost else 0) /\
  T = (Call = Call /\ 0 < 1 /\ account_empty toAccount) /\
  183600 = (if T then new_account_state_gas else 0) /\
  (if T then new_account_state_gas else 0) <= 183600 /\
  delegate_check toAccount.code (msdomain_add 100w d)
    (accesses_add 100w rb) 0 (accesses_add 100w rb) (msdomain_add 100w d) /\
  0 = memory_cost empty_buffer 0 0 /\
  call_gas 1 0 (p.gasLimit - (0 + (static_gas Call +
      access_cost rb 100w + call_value_cost + 0 + 0))) 0 0 = (0,2300) /\
  14300 = static_gas Call + access_cost rb 100w + call_value_cost + 0 + 0 + 0 /\
  0 + 14300 <= p.gasLimit /\
  is_call Call /\ Call <> Create /\ Call <> Create2 /\
  (0 < 1 ==> ~p.static) /\ ~fIN (100w:address) precompile_addresses /\
  d = Collect empty_domain /\ 2300 <= call_stipend
Proof
  simp[refund_candidate_not_precompile,
       refund_candidate_context_def, refund_probe_context_def,
       refund_probe_rollback_def, LET_THM,
       call_has_value_def, max_expansion_range_def, expanded_memory_def,
       memory_cost_def, memory_expansion_info_def, word_size_def,
       memory_expansion_cost_def, vfmBufferTheory.empty_buffer_def,
       vfmBufferTheory.buffer_length_def, lookup_account_def,
       empty_account_state_def, account_empty_def, delegate_check_def,
       get_delegate_def, is_delegation_def, access_cost_def,
       call_value_cost_def, cold_access_cost_def, new_account_state_gas_def,
       call_gas_def, call_stipend_def, is_call_def] >> EVAL_TAC
QED

Theorem refund_candidate_no_normal_successor_pc:
  !n. let out = FUNPOW (\x. if ISR (FST x) then x else step (SND x)) n
                       (INL (), refund_candidate_state) in
      ~(ISL (FST out) /\ (FST (HD (SND out).contexts)).pc = 1)
Proof
  gen_tac >> Cases_on `n = 0`
  >- simp[refund_candidate_state_def, refund_candidate_context_def,
          refund_probe_context_def] >>
  simp[LET_THM, refund_candidate_next_iterates]
QED
