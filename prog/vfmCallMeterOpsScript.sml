Theory vfmCallMeterOps
Ancestors vfmCallMeterSafe vfmCallMeter vfmCallMeterBase vfmExecution
          vfmContext vfmState vfmTypes arithmetic list

(* Reservoir and ordinary context fields are intentionally unconstrained. *)
Definition call_meter_neutral_def:
  call_meter_neutral c d <=>
    d.msgParams.gasLimit = c.msgParams.gasLimit /\
    d.gasUsed = c.gasUsed /\
    d.stateGasSpilled = c.stateGasSpilled /\
    d.stateGasCommitted = c.stateGasCommitted
End

Definition call_meter_ready_def:
  call_meter_ready c rb rest s <=>
    s.contexts = (c,rb)::rest /\ call_meter_backed c /\
    c.gasUsed <= c.msgParams.gasLimit
End

Theorem call_meter_neutral_result:
  call_meter_ready c rb rest s /\ t.contexts = (d,rb)::rest /\
  call_meter_neutral c d ==> call_meter_result c rb rest t
Proof
  simp[call_meter_ready_def, call_meter_neutral_def, call_meter_result_def,
       call_meter_backed_def, call_meter_claim_def] >>
  rpt strip_tac >> qexists `d` >> simp[]
QED

Theorem call_meter_safe_neutral:
  (!s r t. call_meter_ready c rb rest s /\ m s = (r,t) ==>
    (?d. t.contexts = (d,rb)::rest /\ call_meter_neutral c d)) /\
  (!s e t. call_meter_ready c rb rest s /\ m s = (INR e,t) ==>
    e <> SOME Impossible /\ e <> SOME Unimplemented) ==>
  call_meter_safe (call_meter_ready c rb rest) m
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt strip_tac >>
  metis_tac[call_meter_neutral_result]
QED

(* Reader interface keeps the returned value available to a continuation. *)
Theorem call_meter_safe_reader:
  call_meter_safe P (\s. return (f s) s) (\r t. r = INL (f t) /\ P t)
Proof
  simp[call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_context_reader:
  call_meter_safe (call_meter_ready c rb rest)
    (bind get_current_context (\d. return (f d)))
    (\r t. r = INL (f c) /\ call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, get_current_context_def,
       bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem call_meter_safe_context_update:
  call_meter_neutral c (f c) ==>
  call_meter_safe (call_meter_ready c rb rest)
    (bind get_current_context (\d. set_current_context (f d)))
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def, get_current_context_def, set_current_context_def,
      bind_def, return_def] >>
  irule call_meter_neutral_result >> simp[] >>
  qexists `s` >> simp[call_meter_ready_def]
QED

Theorem call_meter_safe_finish:
  call_meter_safe P finish (\r s. r = INR NONE /\ P s)
Proof
  simp[call_meter_safe_def, finish_def]
QED

Theorem call_meter_safe_revert:
  call_meter_safe P revert (\r s. r = INR (SOME Reverted) /\ P s)
Proof
  simp[call_meter_safe_def, revert_def]
QED

Theorem call_meter_safe_assert:
  e <> Impossible /\ e <> Unimplemented ==>
  call_meter_safe P (assert b e) (\r s. P s)
Proof
  Cases_on `b` >> simp[call_meter_safe_def, assert_def]
QED

Theorem call_meter_safe_expand_memory:
  call_meter_safe (call_meter_ready c rb rest) (expand_memory n)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[expand_memory_def] >> ho_match_mp_tac call_meter_safe_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_write_memory:
  call_meter_safe (call_meter_ready c rb rest) (write_memory offset bytes)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[write_memory_def] >> ho_match_mp_tac call_meter_safe_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_read_memory:
  call_meter_safe (call_meter_ready c rb rest) (read_memory offset len)
    (\r t. r = INL (buffer_take offset len c.memory) /\
           call_meter_ready c rb rest t)
Proof
  simp[read_memory_def, call_meter_safe_def, call_meter_ready_def,
       get_current_context_def, bind_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem call_meter_safe_pop_stack:
  call_meter_safe (call_meter_ready c rb rest) (pop_stack n)
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, pop_stack_def,
       get_current_context_def, set_current_context_def, bind_def,
       ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), call_meter_result_def] >>
  gvs[call_meter_backed_def, call_meter_claim_def]
QED

Theorem call_meter_safe_push_stack:
  call_meter_safe (call_meter_ready c rb rest) (push_stack v)
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, push_stack_def,
       get_current_context_def, set_current_context_def, bind_def,
       ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), call_meter_result_def] >>
  gvs[call_meter_backed_def, call_meter_claim_def]
QED

Theorem call_meter_safe_state_update:
  (!s. (f s).contexts = s.contexts) ==>
  call_meter_safe (call_meter_ready c rb rest)
    (\s. return x (f s)) (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, return_def, call_meter_ready_def]
QED

Theorem call_meter_ready_result:
  call_meter_ready c rb rest s ==> call_meter_result c rb rest s
Proof
  simp[call_meter_ready_def, call_meter_result_same]
QED

Theorem call_meter_safe_access_address:
  call_meter_safe (call_meter_ready c rb rest) (access_address a)
    (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, access_address_def,
       domain_check_def, set_domain_def, ignore_bind_def, bind_def,
       return_def, fail_def] >> rpt strip_tac >>
  Cases_on `s.msdomain` >> gvs[AllCaseEqs()]
QED

Theorem call_meter_safe_update_accounts:
  call_meter_safe (call_meter_ready c rb rest) (update_accounts f)
    (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, update_accounts_def, return_def, call_meter_ready_def]
QED

Theorem call_meter_safe_set_return_data:
  call_meter_safe (call_meter_ready c rb rest) (set_return_data bytes)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[set_return_data_def, LET_THM] >> BETA_TAC >> ho_match_mp_tac call_meter_safe_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_memory_expansion_info:
  call_meter_safe (call_meter_ready c rb rest) (memory_expansion_info offset len)
    (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, memory_expansion_info_def,
       get_current_context_def, bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem call_meter_safe_accounts_reader:
  call_meter_safe P get_accounts (\r t. r = INL t.rollback.accounts /\ P t)
Proof
  simp[call_meter_safe_def, get_accounts_def, return_def]
QED

Theorem call_meter_safe_num_contexts_reader:
  call_meter_safe P get_num_contexts (\r t. r = INL (LENGTH t.contexts) /\ P t)
Proof
  simp[call_meter_safe_def, get_num_contexts_def, return_def]
QED

Theorem call_meter_safe_charge:
  call_meter_safe (call_meter_ready c rb rest) (charge_state_gas n)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_charge_result >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `n <= c.stateGasLeft` >>
  Cases_on `n <= c.stateGasLeft + (c.msgParams.gasLimit - c.gasUsed)` >>
  gvs[charge_state_gas_def, consume_gas_def, get_current_context_def,
      set_current_context_def, bind_def, ignore_bind_def, return_def,
      assert_def, fail_def, AllCaseEqs()]
QED

Theorem call_meter_safe_credit:
  call_meter_safe (call_meter_ready c rb rest) (credit_state_gas_refund n)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_credit_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[credit_state_gas_refund_def, get_current_context_def,
      set_current_context_def, bind_def, return_def]
QED

Theorem call_meter_safe_charge_account:
  call_meter_safe (call_meter_ready c rb rest) (charge_new_account charged)
    (\r t. call_meter_result c rb rest t)
Proof
  Cases_on `charged` >> simp[charge_new_account_def, call_meter_safe_charge] >>
  irule call_meter_safe_return >> simp[call_meter_ready_result]
QED

Theorem call_meter_safe_credit_account:
  call_meter_safe (call_meter_ready c rb rest) (credit_new_account charged)
    (\r t. call_meter_result c rb rest t)
Proof
  Cases_on `charged` >> simp[credit_new_account_def, call_meter_safe_credit] >>
  irule call_meter_safe_return >> simp[call_meter_ready_result]
QED

Theorem call_meter_safe_drain:
  call_meter_safe (call_meter_ready c rb rest) drain_state_gas_reservoir
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_drain_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[drain_state_gas_reservoir_def, get_current_context_def,
      set_current_context_def, bind_def, ignore_bind_def, return_def]
QED

Theorem call_meter_safe_callee_reader:
  call_meter_safe (call_meter_ready c rb rest) get_callee
    (\r t. r = INL c.msgParams.callee /\ call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, get_callee_def,
       get_current_context_def, bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem call_meter_safe_gas_left_reader:
  call_meter_safe (call_meter_ready c rb rest) get_gas_left
    (\r t. r = INL (c.msgParams.gasLimit - c.gasUsed) /\ call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, get_gas_left_def,
       get_current_context_def, bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem call_meter_safe_call_data_reader:
  call_meter_safe (call_meter_ready c rb rest) get_call_data
    (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, get_call_data_def,
       get_current_context_def, bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem call_meter_safe_assert_not_static:
  call_meter_safe (call_meter_ready c rb rest) assert_not_static
    (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, assert_not_static_def,
       get_static_def, get_current_context_def, bind_def, return_def, assert_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem call_meter_safe_inc_pc:
  call_meter_safe (call_meter_ready c rb rest) inc_pc
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[inc_pc_def] >> ho_match_mp_tac call_meter_safe_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_ensure_storage:
  call_meter_safe (call_meter_ready c rb rest) (ensure_storage_in_domain a)
    (\r t. call_meter_ready c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, ensure_storage_in_domain_def,
       domain_check_def, set_domain_def, ignore_bind_def, bind_def,
       return_def, fail_def] >> rpt strip_tac >>
  Cases_on `s.msdomain` >> gvs[AllCaseEqs()]
QED

Theorem call_meter_safe_restore:
  call_meter_safe (call_meter_ready c rb rest) restore_state_gas
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_restore_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[restore_state_gas_def, get_current_context_def,
      set_current_context_def, bind_def, return_def]
QED

Theorem call_meter_safe_commit:
  call_meter_safe (call_meter_ready c rb rest) commit_state_gas
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_commit_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[commit_state_gas_def, get_current_context_def,
      set_current_context_def, bind_def, return_def]
QED

Theorem call_meter_safe_forfeit:
  call_meter_safe (call_meter_ready c rb rest) forfeit_remaining_gas
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_forfeit_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[forfeit_remaining_gas_def, get_gas_left_def, consume_gas_def,
      get_current_context_def, set_current_context_def, bind_def,
      ignore_bind_def, return_def, assert_def, fail_def, AllCaseEqs()]
QED

Theorem call_meter_safe_repay:
  call_meter_safe (call_meter_ready c rb rest) repay_state_gas_spill
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_repay_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[repay_state_gas_spill_def, get_current_context_def,
      set_current_context_def, bind_def, return_def]
QED

Theorem call_meter_safe_restore_entry:
  call_meter_safe (call_meter_ready c rb rest) (restore_state_gas_to_entry sg)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >> conj_tac
  >- (irule call_meter_restore_entry_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[restore_state_gas_to_entry_def, get_current_context_def,
      set_current_context_def, bind_def, return_def]
QED

Theorem call_meter_safe_withhold:
  call_meter_safe (call_meter_ready c rb rest) withhold_create_gas
    (\r t. ?amount. r = INL amount /\ call_meter_grant_result c amount rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[call_meter_ready_def] >>
  drule_all call_meter_withhold_grant >> strip_tac >> simp[]
QED
