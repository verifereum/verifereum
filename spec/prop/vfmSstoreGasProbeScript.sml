Theory vfmSstoreGasProbe
Ancestors vfmSameFrame vfmExecutionProp vfmExecution vfmState
Libs wordsLib

(* Witness that `step_inst_same_frame_gas_monotone` is false under the
   state-gas model: a slot-clearing SSTORE on a frame that has already
   spilled ends below its starting `gasUsed`.  `sstore_probe_gas_decreases`
   is the weakened form the shipped statements use. *)
Definition sstore_probe_frame_def:
  sstore_probe_frame c = c with <|
    stack := [0w; 0w]; gasUsed := 30000; stateGasSpilled := 30000;
    stateGasLeft := 0; addRefund := 0; subRefund := 0;
    msgParams := c.msgParams with <| callee := 0w; static := F;
      gasLimit := 100000; code := []; parsed := parse_code 0 FEMPTY [] |> |>
End

Definition sstore_probe_state_def:
  sstore_probe_state s c a d = s with <|
    contexts := [(sstore_probe_frame c, s.rollback)];
    originalAccounts := K (a with storage := K 0w);
    rollback := s.rollback with <|
      accounts := K (a with storage := K 1w);
      accesses := s.rollback.accesses with storageKeys := fINSERT (SK 0w 0w) fEMPTY |>;
    msdomain := Enforce (d with storageKeys := fINSERT (SK 0w 0w) fEMPTY) |>
End

Theorem sstore_probe_gas_decreases:
  let s0 = sstore_probe_state s c a d in
  let out = step_inst SStore s0 in
    ISL (FST out) /\
    (FST (HD (SND out).contexts)).gasUsed <
    (FST (HD s0.contexts)).gasUsed
Proof
  simp[sstore_probe_state_def, sstore_probe_frame_def, step_inst_def,
       step_sstore_def, step_sstore_gas_consumption_def,
       pop_stack_def, get_callee_def, get_gas_left_def, get_accounts_def,
       get_original_def, access_slot_def, domain_check_def,
       update_gas_refund_def, credit_state_gas_refund_def,
       consume_gas_def, charge_state_gas_def, assert_not_static_def,
       write_storage_def, update_accounts_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def, lookup_account_def, lookup_storage_def,
       sstore_base_gas_def, sstore_refund_updates_def,
       sstore_state_gas_refund_def, sstore_state_gas_def]
  >> EVAL_TAC
QED

Theorem step_inst_same_frame_gas_monotone_counterexample:
  let s0 = sstore_probe_state s c a d in
  let out = step_inst SStore s0 in
    step_inst SStore s0 = out /\
    same_frame_rel s0 (SND out) /\
    EVERY (wf_context o FST) s0.contexts /\
    (FST (HD (SND out).contexts)).gasUsed <
    (FST (HD s0.contexts)).gasUsed
Proof
  simp[LET_THM]
  >> conj_tac
  >- (`preserves_same_frame (step_inst SStore)` by simp[] >>
      pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def] >>
      disch_then irule >>
      conj_tac >- simp[sstore_probe_state_def] >>
      qexists_tac `FST (step_inst SStore (sstore_probe_state s c a d))` >> simp[])
  >> conj_tac
  >- simp[sstore_probe_state_def, sstore_probe_frame_def, wf_context_def,
          vfmConstantsTheory.stack_limit_def]
  >> mp_tac sstore_probe_gas_decreases >> simp[]
QED
