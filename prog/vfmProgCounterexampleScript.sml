Theory vfmProgCounterexample
Ancestors
  vfmExecution vfmContext vfmConstants vfmState vfmTypes vfmBuffer
  words pair list arithmetic option combin

(* Full antecedents and the negation of the frozen memory-return helper.
   Uninspected fields are arbitrary: the witness works for every base record. *)
Theorem handle_step_success_memory_exact_counterexample:
  let mr = <|offset := 0; size := 0|>;
      c = child with <|
        msgParams := child.msgParams with <|outputTo := Memory mr; gasLimit := 0|>;
        gasUsed := 0; addRefund := 0; subRefund := 0;
        stateGasLeft := 0; stateGasSpilled := 0; stateGasBaseline := 0;
        stateGasCommitted := 1; returnData := []; logs := [] |>;
      parent = parent_base with <|
        gasUsed := 0; addRefund := 0; subRefund := 0; stack := [];
        stateGasLeft := 0; stateGasSpilled := 0; stateGasBaseline := 0;
        stateGasCommitted := 0 |>;
      s = initial with contexts := [(c,crb); (parent,prb)]
  in
  s.contexts = (c,crb)::(parent,prb)::[] /\
  c.msgParams.outputTo = Memory mr /\
  c.addRefund = 0 /\ c.subRefund = 0 /\
  c.msgParams.gasLimit - c.gasUsed <= parent.gasUsed /\
  LENGTH parent.stack < stack_limit /\
  handle_step NONE s <>
    (INL (), s with contexts :=
      (parent with <|
         gasUsed := parent.gasUsed - (c.msgParams.gasLimit - c.gasUsed);
         pc := parent.pc + 1; returnData := c.returnData;
         stack := 1w::parent.stack;
         memory := buffer_write mr.offset (TAKE mr.size c.returnData) parent.memory;
         logs := parent.logs ++ c.logs
       |>,prb)::[])
Proof
  simp[LET_THM, stack_limit_def] >>
  simp[handle_step_def, handle_create_def, handle_exception_def,
       pop_and_incorporate_context_def, get_gas_left_def,
       get_return_data_def, get_output_to_def, get_num_contexts_def,
       pop_context_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
       inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       get_current_context_def, set_current_context_def,
       absorb_state_gas_def, repay_state_gas_spill_def,
       repay_state_gas_spill_context_def,
       handle_def, reraise_def, bind_def, ignore_bind_def, return_def,
       assert_def, stack_limit_def,
       execution_state_component_equality, context_component_equality]
QED
