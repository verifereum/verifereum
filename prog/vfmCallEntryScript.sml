Theory vfmCallEntry
Ancestors vfmCallMeter vfmCallBudget vfmCallMeterProbe vfmExecution vfmContext
          vfmState vfmTypes arithmetic list

Theorem call_meter_proceed_create_shape:
  s.contexts = (parent,rb)::rest /\
  proceed_create sender addr value code grant s = (r,t) ==>
  r = INL () /\
  ?child saved. t.contexts =
    (child,saved)::(parent with stateGasLeft := 0,rb)::rest /\
    call_meter_backed child /\ call_meter_claim child = grant /\
    child.gasUsed = 0 /\ child.msgParams.gasLimit = grant
Proof
  simp[proceed_create_def, drain_state_gas_reservoir_def,
       get_current_context_def, set_current_context_def,
       get_accounts_def, get_rollback_def, update_accounts_def,
       get_original_def, set_original_def, push_context_def,
       bind_def, ignore_bind_def, return_def, LET_THM,
       initial_context_def, initial_msg_params_def, call_meter_backed_def,
       call_meter_claim_def] >> rpt strip_tac >>
  gvs[return_def, call_meter_backed_def, call_meter_claim_def]
QED

Theorem call_meter_proceed_call_shape:
  s.contexts = (parent,rb)::rest /\ ~fIN addr precompile_addresses /\
  proceed_call op sender addr value ao az code grant output s = (r,t) ==>
  r = INL () /\
  ?child saved. t.contexts =
    (child,saved)::(parent with stateGasLeft := 0,rb)::rest /\
    call_meter_backed child /\ call_meter_claim child = grant /\
    child.gasUsed = 0 /\ child.msgParams.gasLimit = grant
Proof
  Cases_on `op <> CallCode /\ 0 < value` >>
  simp[proceed_call_def, drain_state_gas_reservoir_def,
       get_current_context_def, set_current_context_def,
       get_accounts_def, get_rollback_def, update_accounts_def,
       read_memory_def, get_caller_def, get_value_def, get_static_def,
       push_context_def, bind_def, ignore_bind_def, return_def, LET_THM,
       initial_context_def, initial_msg_params_def, call_meter_backed_def,
       call_meter_claim_def] >> rpt strip_tac >>
  gvs[return_def, call_meter_backed_def, call_meter_claim_def]
QED

(* This lifting law compares the child entry to the frame before grant payment.
   The intermediate parent's unused grant alone does not bound the new pair. *)
Theorem call_meter_entry_budget:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\
  t.contexts = (child,saved)::(parent with stateGasLeft := 0,rb)::rest /\
  call_meter_backed child /\ call_meter_claim child = grant /\
  parent.stateGasSpilled + parent.stateGasCommitted + grant <= parent.gasUsed /\
  call_meter_claim parent + grant <= call_meter_claim c ==>
  call_meter_budget n ceiling t
Proof
  rpt strip_tac >> irule call_meter_budget_push >>
  simp[call_meter_claim_def] >>
  qexistsl [`c`, `rb`, `u`] >>
  gvs[call_meter_claim_def] >> decide_tac
QED

Theorem call_meter_proceed_create_budget:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\ s.contexts = (parent,rb)::rest /\
  parent.stateGasSpilled + parent.stateGasCommitted + grant <= parent.gasUsed /\
  call_meter_claim parent + grant <= call_meter_claim c /\
  proceed_create sender addr value code grant s = (r,t) ==>
  r = INL () /\ call_meter_budget n ceiling t
Proof
  strip_tac >> drule_all call_meter_proceed_create_shape >> strip_tac >> simp[] >>
  irule call_meter_entry_budget >> metis_tac[]
QED

Theorem call_meter_proceed_call_budget:
  call_meter_budget n ceiling u /\ n <= LENGTH u.contexts /\
  u.contexts = (c,rb)::rest /\ s.contexts = (parent,rb)::rest /\
  parent.stateGasSpilled + parent.stateGasCommitted + grant <= parent.gasUsed /\
  call_meter_claim parent + grant <= call_meter_claim c /\
  ~fIN addr precompile_addresses /\
  proceed_call op sender addr value ao az code grant output s = (r,t) ==>
  r = INL () /\ call_meter_budget n ceiling t
Proof
  strip_tac >> drule_all call_meter_proceed_call_shape >> strip_tac >> simp[] >>
  irule call_meter_entry_budget >> metis_tac[]
QED
