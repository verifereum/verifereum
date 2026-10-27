Theory vfmPopGasProbe
Ancestors vfmExecution

(* Diagnostic witness for the frozen handle_exception_pop_generic_gen.
   Unspecified record fields are arbitrary: the failure uses only gas fields. *)
Definition pop_gas_child_def:
  pop_gas_child c = c with <|
    msgParams := c.msgParams with <| gasLimit := 0;
      outputTo := Memory <| offset := 0; size := 0 |> |>;
    gasUsed := 0; stateGasLeft := 0; stateGasSpilled := 0;
    stateGasCommitted := 0; returnData := [] |>
End

Definition pop_gas_parent_def:
  pop_gas_parent c = c with <| gasUsed := 1; stateGasLeft := 1;
    stateGasSpilled := 1; stack := [] |>
End

Theorem handle_exception_pop_generic_gen_counterexample:
  !s c rb.
    let callee = pop_gas_child c in
    let parent = (pop_gas_parent c, rb) in
    let s0 = s with contexts := [(callee, rb); parent] in
    let out = handle_exception NONE s0 in
    s0.contexts = (callee, rb)::parent::[] /\
    handle_exception NONE s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ~(( (SND out).rollback = s0.rollback \/
         (SND out).rollback = rb) /\
      ?new_parent_ctx.
        (SND out).contexts = [(new_parent_ctx, SND parent)] /\
        new_parent_ctx.msgParams = (FST parent).msgParams /\
        new_parent_ctx.gasUsed >=
          (FST parent).gasUsed -
          (callee.msgParams.gasLimit - callee.gasUsed))
Proof
  simp[pop_gas_child_def, pop_gas_parent_def,
       handle_exception_def, bind_def, ignore_bind_def,
       return_def, get_num_contexts_def, get_return_data_def,
       get_output_to_def, pop_and_incorporate_context_def,
       get_gas_left_def, get_current_context_def, pop_context_def,
       unuse_gas_def, set_current_context_def, absorb_state_gas_def,
       push_logs_def, update_gas_refund_def, repay_state_gas_spill_def,
       repay_state_gas_spill_context_def, inc_pc_def, set_return_data_def,
       push_stack_def, assert_def, write_memory_def]
QED

(* Failure branch: restoration refunds spilled execution gas before pop. *)
Definition reverted_pop_gas_child_def:
  reverted_pop_gas_child c = c with <|
    msgParams := c.msgParams with <| gasLimit := 1;
      outputTo := Memory <| offset := 0; size := 0 |> |>;
    gasUsed := 1; stateGasLeft := 0; stateGasSpilled := 1;
    stateGasBaseline := 0; stateGasCommitted := 0; returnData := [] |>
End

Definition reverted_pop_gas_parent_def:
  reverted_pop_gas_parent c = c with <| gasUsed := 2; stateGasLeft := 0;
    stateGasSpilled := 0; stack := [] |>
End

Theorem handle_exception_reverted_pop_generic_gen_counterexample:
  !s c rb.
    let callee = reverted_pop_gas_child c in
    let parent = (reverted_pop_gas_parent c, rb) in
    let s0 = s with contexts := [(callee, rb); parent] in
    let out = handle_exception (SOME Reverted) s0 in
    s0.contexts = (callee, rb)::parent::[] /\
    handle_exception (SOME Reverted) s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ~(((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
      ?new_parent_ctx.
        (SND out).contexts = [(new_parent_ctx, SND parent)] /\
        new_parent_ctx.msgParams = (FST parent).msgParams /\
        new_parent_ctx.gasUsed >=
          (FST parent).gasUsed -
          (callee.msgParams.gasLimit - callee.gasUsed) -
          MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
              ((FST parent).stateGasSpilled + callee.stateGasSpilled))
Proof
  simp[reverted_pop_gas_child_def, reverted_pop_gas_parent_def,
       handle_exception_def, restore_state_gas_def, bind_def, ignore_bind_def,
       return_def, get_num_contexts_def, get_return_data_def,
       get_output_to_def, pop_and_incorporate_context_def,
       get_gas_left_def, get_current_context_def, pop_context_def,
       unuse_gas_def, set_current_context_def, absorb_state_gas_def,
       set_rollback_def, inc_pc_def, set_return_data_def,
       push_stack_def, assert_def, write_memory_def]
QED

Theorem handle_exception_pop_generic_gen_corrected_instance:
  !s c rb.
    let callee = pop_gas_child c in
    let parent = (pop_gas_parent c, rb) in
    let s0 = s with contexts := [(callee, rb); parent] in
    let out = handle_exception NONE s0 in
    let leftAfter = callee.msgParams.gasLimit - callee.gasUsed in
    s0.contexts = (callee, rb)::parent::[] /\
    handle_exception NONE s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
    ?new_parent_ctx.
      (SND out).contexts = [(new_parent_ctx, SND parent)] /\
      new_parent_ctx.msgParams = (FST parent).msgParams /\
      new_parent_ctx.gasUsed >= (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled)
Proof
  simp[pop_gas_child_def, pop_gas_parent_def,
       handle_exception_def, bind_def, ignore_bind_def,
       return_def, get_num_contexts_def, get_return_data_def,
       get_output_to_def, pop_and_incorporate_context_def,
       get_gas_left_def, get_current_context_def, pop_context_def,
       unuse_gas_def, set_current_context_def, absorb_state_gas_def,
       push_logs_def, update_gas_refund_def, repay_state_gas_spill_def,
       repay_state_gas_spill_context_def, inc_pc_def, set_return_data_def,
       push_stack_def, assert_def, write_memory_def]
QED

Theorem handle_exception_reverted_pop_generic_gen_corrected_instance:
  !s c rb.
    let callee = reverted_pop_gas_child c in
    let parent = (reverted_pop_gas_parent c, rb) in
    let s0 = s with contexts := [(callee, rb); parent] in
    let out = handle_exception (SOME Reverted) s0 in
    let leftAfter = callee.msgParams.gasLimit -
      (callee.gasUsed - MIN callee.stateGasSpilled callee.gasUsed) in
    s0.contexts = (callee, rb)::parent::[] /\
    handle_exception (SOME Reverted) s0 = out /\
    LENGTH (SND out).contexts < LENGTH s0.contexts /\
    ((SND out).rollback = s0.rollback \/ (SND out).rollback = rb) /\
    ?new_parent_ctx.
      (SND out).contexts = [(new_parent_ctx, SND parent)] /\
      new_parent_ctx.msgParams = (FST parent).msgParams /\
      new_parent_ctx.gasUsed >= (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled)
Proof
  simp[reverted_pop_gas_child_def, reverted_pop_gas_parent_def,
       handle_exception_def, restore_state_gas_def, bind_def, ignore_bind_def,
       return_def, get_num_contexts_def, get_return_data_def,
       get_output_to_def, pop_and_incorporate_context_def,
       get_gas_left_def, get_current_context_def, pop_context_def,
       unuse_gas_def, set_current_context_def, absorb_state_gas_def,
       set_rollback_def, inc_pc_def, set_return_data_def,
       push_stack_def, assert_def, write_memory_def]
QED
