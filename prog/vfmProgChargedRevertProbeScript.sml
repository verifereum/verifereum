Theory vfmProgChargedRevertProbe
Ancestors vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmTypes vfmBuffer vfmOperation words list arithmetic finite_map
Libs wordsLib

Definition probe_params_def:
  probe_params = <|caller := 0w; callee := 0w; code := []; parsed := FEMPTY;
    value := 0; gasLimit := 0; data := empty_buffer; static := F;
    outputTo := Memory <|offset := 0; size := 0|>; newAccountCharged := T|>
End

Definition probe_context_def:
  probe_context = <|stack := []; memory := empty_buffer; pc := 0;
    jumpDest := NONE; returnData := []; gasUsed := 0; addRefund := 0;
    subRefund := 0; stateGasLeft := 0; stateGasSpilled := 0;
    stateGasBaseline := 0; stateGasCommitted := 0; logs := [];
    msgParams := probe_params|>
End

Definition probe_initial_def:
  probe_initial = <|contexts := []; rollback := <|accounts := empty_accounts;
    tStorage := empty_transient_storage;
    accesses := <|addresses := fEMPTY; storageKeys := fEMPTY|>; toDelete := []|>;
    txParams := <|origin := 0w; gasPrice := 0; baseFeePerGas := 0;
      baseFeePerBlobGas := 0; blockNumber := 0; slotNumber := 0;
      blockTimeStamp := 0; blockCoinBase := 0w; blockGasLimit := 0;
      prevRandao := 0w; prevHashes := []; blobHashes := []; chainId := 0;
      authRefund := 0; stateGasReservoir := 0|>;
    originalAccounts := empty_accounts; msdomain := Collect empty_domain|>
End

(* Exactly the frozen inner_revert_spill_execution construction, instantiated
   with the three concrete records above. The step-equality conjunct fails. *)
Theorem inner_revert_spill_execution_charged_counterexample:
  let params = probe_params; ctx_base = probe_context; initial = probe_initial;
      p = params with <|code := [253w]; parsed := parse_code 0 FEMPTY [253w];
          gasLimit := 10; outputTo := Memory <|offset := 0; size := 0|> |>;
      q = params with <|code := []; parsed := FEMPTY; gasLimit := 20;
          outputTo := Memory <|offset := 0; size := 0|> |>;
      child = ctx_base with <|msgParams := p; stack := [0w;0w]; pc := 0;
          memory := empty_buffer; gasUsed := 0; stateGasSpilled := 1;
          stateGasBaseline := 0; stateGasLeft := 0; stateGasCommitted := 0|>;
      parent = ctx_base with <|msgParams := q; stack := []; pc := 0;
          memory := empty_buffer; gasUsed := 11; stateGasSpilled := 0;
          stateGasBaseline := 0; stateGasLeft := 0; stateGasCommitted := 0|>;
      rb = initial.rollback with accounts := empty_accounts;
      s = initial with <|contexts := [(child,rb);(parent,rb)]; rollback := rb|>;
      out = initial with <|contexts := [(parent with <|stack := [0w]; pc := 1;
          returnData := []; gasUsed := 1|>,rb)]; rollback := rb|>
  in (FST (HD (SND (step s)).contexts)).stateGasLeft = 183600 /\
     (FST (HD out.contexts)).stateGasLeft = 0 /\
     step s <> (INL (),out)
Proof
  simp[LET_THM] >>
  `parse_opcode [253w] = SOME Revert` by
    (rewrite_tac[vfmOperationTheory.parse_opcode_cond_thm] >> EVAL_TAC) >>
  `FLOOKUP (parse_code 0 FEMPTY [253w]) 0 = SOME Revert` by
    (once_rewrite_tac[parse_code_def] >>
     simp[vfmOperationTheory.opcode_def] >>
     once_rewrite_tac[parse_code_def] >> simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[step_def, get_current_context_def, bind_def, return_def, handle_def,
       probe_params_def, probe_context_def, probe_initial_def] >>
  simp[step_inst_def, step_return_def, ignore_bind_def, pop_stack_def,
       assert_def, set_current_context_def, memory_expansion_info_def,
       consume_gas_def, expand_memory_def, read_memory_def,
       set_return_data_def, revert_def, handle_step_def, handle_create_def,
       reraise_def, get_return_data_def, get_output_to_def,
       handle_exception_def, get_num_contexts_def, restore_state_gas_def,
       pop_and_incorporate_context_def, get_gas_left_def, pop_context_def,
       unuse_gas_def, set_rollback_def, inc_pc_def, push_stack_def,
       write_memory_def, absorb_state_gas_def,
       bind_def, ignore_bind_def, return_def, get_current_context_def,
       set_current_context_def, handle_def, assert_def,
       empty_buffer_def, buffer_length_def] >>
  simp[buffer_take_def, Once read_bytes_def, credit_new_account_def,
       credit_state_gas_refund_def, new_account_state_gas_def,
       bind_def, ignore_bind_def, return_def, get_current_context_def,
       set_current_context_def, context_component_equality,
       execution_state_component_equality] >> EVAL_TAC
QED
