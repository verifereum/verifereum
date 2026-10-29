Theory vfmCallDrainProbe
Ancestors vfmExecution
Libs wordsLib

Theorem call_drain_destination_not_precompile:
  ~fIN (100w : address) precompile_addresses
Proof
  rewrite_tac[vfmContextTheory.precompile_addresses_def,
              finite_setTheory.fIN_fset_ABS] >> EVAL_TAC
QED

(* The unspecified fields are immaterial.  The only required input
   meter field is a nonzero reservoir. *)
Theorem proceed_call_push_structure_counterexample:
  !s c rb.
    let s0 = s with contexts := [(c with stateGasLeft := 1, rb)] in
    let out = proceed_call Call 0w 100w 0 0 0 [] 0
                (Memory <| offset := 0; size := 0 |>) s0 in
    s0.contexts <> [] /\
    FST out = INL () /\
    LENGTH (SND out).contexts = 2 /\
    (FST (HD s0.contexts)).stateGasLeft = 1 /\
    (FST (HD (TL (SND out).contexts))).stateGasLeft = 0 /\
    TL (SND out).contexts <> s0.contexts
Proof
  simp[proceed_call_def, drain_state_gas_reservoir_def,
       bind_def, ignore_bind_def, return_def, get_accounts_def,
       get_current_context_def,
       set_current_context_def, get_rollback_def, read_memory_def,
       get_caller_def, get_value_def, get_static_def, push_context_def,
       call_drain_destination_not_precompile] >>
  rpt strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `\c. c.stateGasLeft`) >> simp[]
QED

(* Historical witness for the superseded CREATE exact-tail statement. *)
Theorem proceed_create_push_structure_counterexample:
  !s c rb.
    let s0 = s with contexts := [(c with stateGasLeft := 1, rb)] in
    let out = proceed_create 0w 100w 0 [] 0 s0 in
    s0.contexts <> [] /\
    FST out = INL () /\
    LENGTH (SND out).contexts = 2 /\
    (FST (HD s0.contexts)).stateGasLeft = 1 /\
    (FST (HD (TL (SND out).contexts))).stateGasLeft = 0 /\
    MAP FST (TL (SND out).contexts) <> MAP FST s0.contexts
Proof
  simp[proceed_create_def, drain_state_gas_reservoir_def,
       bind_def, ignore_bind_def, return_def, get_accounts_def,
       get_current_context_def,
       set_current_context_def, update_accounts_def, get_rollback_def,
       get_original_def, set_original_def, push_context_def] >>
  rpt strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `\c. c.stateGasLeft`) >> simp[]
QED
