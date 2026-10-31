Theory vfmCallInner
Ancestors vfmCallSteps vfmCallGrant vfmCallPrecompile vfmCallMeterOps
          vfmCallMeterSafe vfmCallMeter vfmCallBudget vfmExecution vfmContext
          vfmState vfmTypes vfmExecutionProp vfmCallMeterProbe arithmetic list

Theorem call_meter_safe_pop_inv:
  call_meter_safe (call_meter_result c rb rest) (pop_stack n)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_pop_stack]
QED

Theorem call_meter_safe_binop_inv:
  call_meter_safe (call_meter_result c rb rest) (step_binop op f)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_binop_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_result_push_stack]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_monop_inv:
  call_meter_safe (call_meter_result c rb rest) (step_monop op f)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_monop_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_result_push_stack]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_modop_inv:
  call_meter_safe (call_meter_result c rb rest) (step_modop op f)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_modop_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_result_push_stack]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_current_inv:
  call_meter_safe (call_meter_result c rb rest) get_current_context
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_result_def, get_current_context_def,
       return_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem call_meter_safe_tx_inv:
  call_meter_safe (call_meter_result c rb rest) get_tx_params
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, get_tx_params_def, return_def]
QED

Theorem call_meter_safe_context_inv:
  call_meter_safe (call_meter_result c rb rest) (step_context op f)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_context_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_current_inv, call_meter_result_push_stack]) >>
  simp[call_meter_safe_consume_inv]
QED

Theorem call_meter_safe_msgParams_inv:
  call_meter_safe (call_meter_result c rb rest) (step_msgParams op f)
    (\r t. call_meter_result c rb rest t)
Proof
  simp[step_msgParams_def, call_meter_safe_context_inv]
QED

Theorem call_meter_safe_txParams_inv:
  call_meter_safe (call_meter_result c rb rest) (step_txParams op f)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_txParams_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_tx_inv, call_meter_result_push_stack]) >>
  simp[call_meter_safe_consume_inv]
QED

Theorem call_meter_safe_exp_inv:
  call_meter_safe (call_meter_result c rb rest) step_exp
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_exp_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_result_push_stack]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_memory_info_inv:
  call_meter_safe (call_meter_result c rb rest) (memory_expansion_info offset len)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  mp_tac (GEN_ALL call_meter_safe_memory_expansion_info) >>
  simp[call_meter_safe_def] >> metis_tac[call_meter_ready_result]
QED

Theorem call_meter_safe_read_memory_inv:
  call_meter_safe (call_meter_result c rb rest) (read_memory offset len)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  mp_tac (GEN_ALL call_meter_safe_read_memory) >>
  simp[call_meter_safe_def] >> metis_tac[call_meter_ready_result]
QED

Theorem call_meter_safe_expand_inv:
  call_meter_safe (call_meter_result c rb rest) (expand_memory n)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_expand_memory]
QED

Theorem call_meter_safe_write_inv:
  call_meter_safe (call_meter_result c rb rest) (write_memory offset bytes)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_write_memory]
QED

Theorem call_meter_safe_keccak_inv:
  call_meter_safe (call_meter_result c rb rest) step_keccak256
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_keccak256_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
                  simp[call_meter_safe_read_memory_inv, call_meter_result_push_stack]) >>
              simp[call_meter_safe_expand_inv]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_memory_info_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_mload_inv:
  call_meter_safe (call_meter_result c rb rest) step_mload
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_mload_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
                  simp[call_meter_safe_read_memory_inv, call_meter_result_push_stack]) >>
              simp[call_meter_safe_expand_inv]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_memory_info_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_mstore_inv:
  call_meter_safe (call_meter_result c rb rest) (step_mstore op)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_mstore_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
              simp[call_meter_safe_expand_inv, call_meter_safe_write_inv]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_memory_info_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_current_reader:
  call_meter_safe (call_meter_result c rb rest) get_current_context
    (\r t. ?ctx. r = INL ctx /\ ctx = FST (HD t.contexts) /\
                  call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_result_def, get_current_context_def,
       return_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem call_meter_safe_saved_context:
  (!d. call_meter_safe (call_meter_ready d rb rest) (f d)
         (\r t. call_meter_result d rb rest t)) ==>
  call_meter_safe (call_meter_result c rb rest) (bind get_current_context f)
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> irule call_meter_safe_result_lift >> gen_tac >>
  gvs[call_meter_safe_def, call_meter_ready_def, get_current_context_def,
      bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem call_meter_safe_set_neutral:
  call_meter_neutral d e ==>
  call_meter_safe (call_meter_ready d rb rest) (set_current_context e)
    (\r t. call_meter_result d rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_ready_def, set_current_context_def,
       return_def] >> rpt strip_tac >> gvs[] >>
  irule call_meter_neutral_result >> simp[] >>
  qexists `s` >> simp[call_meter_ready_def]
QED

Theorem call_meter_safe_step_push_inv:
  call_meter_safe (call_meter_result c rb rest) (step_push n ws)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_push_def] >> irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_consume_inv, call_meter_result_push_stack]
QED

Theorem call_meter_safe_step_pop_inv:
  call_meter_safe (call_meter_result c rb rest) step_pop
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_pop_def] >> irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_consume_inv, call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_jump_dest_inv:
  call_meter_safe (call_meter_result c rb rest) (set_jump_dest dest)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  rewrite_tac[set_jump_dest_def] >> irule call_meter_safe_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_step_jump_inv:
  call_meter_safe (call_meter_result c rb rest) step_jump
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_jump_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_safe_jump_dest_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_step_jumpi_inv:
  call_meter_safe (call_meter_result c rb rest) step_jumpi
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_jumpi_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_safe_jump_dest_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_ready_assert_prefix:
  e <> Impossible /\ e <> Unimplemented /\
  call_meter_safe (call_meter_ready d rb rest) m
    (\r t. call_meter_result d rb rest t) ==>
  call_meter_safe (call_meter_ready d rb rest) (ignore_bind (assert b e) m)
    (\r t. call_meter_result d rb rest t)
Proof
  Cases_on `b` >>
  simp[call_meter_safe_def, assert_def, ignore_bind_def, bind_def,
       return_def, fail_def, call_meter_ready_result] >> metis_tac[]
QED

Theorem call_meter_safe_step_dup_inv:
  call_meter_safe (call_meter_result c rb rest) (step_dup n)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_dup_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
          simp[call_meter_safe_assert, call_meter_result_push_stack]) >>
      simp[call_meter_safe_current_inv]) >>
  simp[call_meter_safe_consume_inv]
QED

Theorem call_meter_safe_step_dupn_inv:
  call_meter_safe (call_meter_result c rb rest) step_dupn
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_dupn_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
              simp[call_meter_safe_assert, call_meter_result_push_stack]) >>
          simp[call_meter_safe_assert]) >>
      simp[call_meter_safe_current_inv]) >>
  simp[call_meter_safe_consume_inv]
QED

Theorem call_meter_safe_step_swap_inv:
  call_meter_safe (call_meter_result c rb rest) (step_swap n)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_swap_def] >> irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_consume_inv] >>
  irule call_meter_safe_saved_context >> gen_tac >> simp[LET_THM] >>
  irule call_meter_safe_ready_assert_prefix >> simp[] >>
  irule call_meter_safe_set_neutral >> simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_step_swapn_inv:
  call_meter_safe (call_meter_result c rb rest) step_swapn
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_swapn_def] >> irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_consume_inv] >>
  irule call_meter_safe_saved_context >> gen_tac >> simp[LET_THM] >>
  irule call_meter_safe_ready_assert_prefix >> simp[] >>
  irule call_meter_safe_ready_assert_prefix >> simp[] >>
  irule call_meter_safe_set_neutral >> simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_step_exchange_inv:
  call_meter_safe (call_meter_result c rb rest) step_exchange
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_exchange_def] >> irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_consume_inv] >>
  irule call_meter_safe_saved_context >> gen_tac >> simp[LET_THM] >>
  irule call_meter_safe_ready_assert_prefix >> simp[] >>
  irule call_meter_safe_ready_assert_prefix >> simp[] >>
  irule call_meter_safe_set_neutral >> simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_inc_pc_or_jump_inv:
  call_meter_safe (call_meter_result c rb rest) (inc_pc_or_jump op)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[inc_pc_or_jump_def] >> IF_CASES_TAC
  >- simp[call_meter_safe_def, return_def] >>
  simp[LET_THM] >> irule call_meter_safe_saved_context >> gen_tac >>
  BETA_TAC >> Cases_on `d.jumpDest`
  >- (simp[] >> irule call_meter_safe_set_neutral >> simp[call_meter_neutral_def]) >>
  simp[LET_THM] >> irule call_meter_safe_ready_assert_prefix >> simp[] >>
  irule call_meter_safe_set_neutral >> simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_accounts_inv:
  call_meter_safe (call_meter_result c rb rest) get_accounts
    (\r t. call_meter_result c rb rest t)
Proof
  mp_tac (GEN_ALL call_meter_safe_accounts_reader) >>
  simp[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_safe_callee_inv:
  call_meter_safe (call_meter_result c rb rest) get_callee
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[get_callee_def] >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_current_inv, call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_access_inv:
  call_meter_safe (call_meter_result c rb rest) (access_address a)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  mp_tac (GEN_ALL call_meter_safe_access_address) >>
  simp[call_meter_safe_def] >> metis_tac[call_meter_ready_result]
QED

Theorem call_meter_safe_source_readers_inv:
  call_meter_safe (call_meter_result c rb rest) get_current_code
    (\r t. call_meter_result c rb rest t) /\
  call_meter_safe (call_meter_result c rb rest) get_return_data
    (\r t. call_meter_result c rb rest t) /\
  call_meter_safe (call_meter_result c rb rest) (get_code a)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[get_current_code_def, get_return_data_def, get_code_def] >>
  rpt conj_tac >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_current_inv, call_meter_safe_accounts_inv,
       call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_checked_data_inv:
  call_meter_safe (call_meter_result c rb rest) (get_return_data_check offset len)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[get_return_data_check_def, ignore_bind_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_assert, call_meter_safe_def, return_def]) >>
  simp[call_meter_safe_source_readers_inv]
QED

Theorem call_meter_safe_copy_source_inv:
  (!f. source = SOME f ==>
    call_meter_safe (call_meter_result c rb rest) f
      (\r t. call_meter_result c rb rest t)) ==>
  call_meter_safe (call_meter_result c rb rest)
    (case source of
       SOME f => bind f (\bytes. ignore_bind (expand_memory amount)
                   (return (take_pad_0 len (DROP offset bytes))))
     | NONE => ignore_bind (expand_memory amount) (read_memory offset len))
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> Cases_on `source` >> simp[]
  >- (irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_expand_inv, call_meter_safe_read_memory_inv]) >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_expand_inv, call_meter_safe_def, return_def]) >>
  metis_tac[]
QED

Theorem call_meter_safe_copy_memory_inv:
  (!f. source = SOME f ==>
    call_meter_safe (call_meter_result c rb rest) f
      (\r t. call_meter_result c rb rest t)) ==>
  call_meter_safe (call_meter_result c rb rest)
    (copy_to_memory gas offset sourceOffset len source)
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> rewrite_tac[copy_to_memory_def, LET_THM] >> BETA_TAC >>
  pairarg_tac >> simp[] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> simp[LET_THM] >> irule call_meter_safe_ignore_invariant >> conj_tac
      >- simp[call_meter_safe_consume_inv] >>
      irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_copy_source_inv, call_meter_safe_write_inv]) >>
  simp[call_meter_safe_memory_info_inv]
QED

Theorem call_meter_safe_call_data_inv:
  call_meter_safe (call_meter_result c rb rest) get_call_data
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[get_call_data_def] >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_current_inv, call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_step_copy_inv:
  (!f. source = SOME f ==>
    call_meter_safe (call_meter_result c rb rest) f
      (\r t. call_meter_result c rb rest t)) ==>
  call_meter_safe (call_meter_result c rb rest) (step_copy_to_memory op source)
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> rewrite_tac[step_copy_to_memory_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_copy_memory_inv, call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_return_data_copy_inv:
  call_meter_safe (call_meter_result c rb rest) step_return_data_copy
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_return_data_copy_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_copy_memory_inv, call_meter_safe_checked_data_inv,
       call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_ext_code_copy_inv:
  call_meter_safe (call_meter_result c rb rest) step_ext_code_copy
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_ext_code_copy_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
      simp[call_meter_safe_access_inv, call_meter_safe_copy_memory_inv,
           call_meter_safe_source_readers_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_balance_inv:
  call_meter_safe (call_meter_result c rb rest) step_balance
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_balance_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
              simp[call_meter_safe_accounts_inv, call_meter_result_push_stack]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_access_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_ext_code_size_inv:
  call_meter_safe (call_meter_result c rb rest) step_ext_code_size
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_ext_code_size_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
              simp[call_meter_safe_accounts_inv, call_meter_result_push_stack]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_access_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_ext_code_hash_inv:
  call_meter_safe (call_meter_result c rb rest) step_ext_code_hash
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_ext_code_hash_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
              simp[call_meter_safe_accounts_inv, call_meter_result_push_stack]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_access_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_call_data_load_inv:
  call_meter_safe (call_meter_result c rb rest) step_call_data_load
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_call_data_load_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
          simp[call_meter_safe_call_data_inv, call_meter_result_push_stack]) >>
      simp[call_meter_safe_consume_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_block_hash_inv:
  call_meter_safe (call_meter_result c rb rest) step_block_hash
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_block_hash_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
          simp[call_meter_safe_tx_inv, call_meter_result_push_stack]) >>
      simp[call_meter_safe_consume_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_blob_hash_inv:
  call_meter_safe (call_meter_result c rb rest) step_blob_hash
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_blob_hash_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
          simp[call_meter_safe_tx_inv, call_meter_result_push_stack]) >>
      simp[call_meter_safe_consume_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_self_balance_inv:
  call_meter_safe (call_meter_result c rb rest) step_self_balance
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_self_balance_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
          simp[call_meter_safe_callee_inv, call_meter_result_push_stack]) >>
      simp[call_meter_safe_accounts_inv]) >>
  simp[call_meter_safe_consume_inv]
QED

Theorem call_meter_safe_not_static_inv:
  call_meter_safe (call_meter_result c rb rest) assert_not_static
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[assert_not_static_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- simp[call_meter_safe_assert] >>
  rewrite_tac[get_static_def] >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_current_inv, call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_logs_inv:
  call_meter_safe (call_meter_result c rb rest) (push_logs ls)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  rewrite_tac[push_logs_def] >> irule call_meter_safe_context_update >>
  simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_log_inv:
  call_meter_safe (call_meter_result c rb rest) (step_log n)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_log_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
                  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
                      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
                          simp[call_meter_safe_read_memory_inv, call_meter_safe_logs_inv]) >>
                      simp[call_meter_safe_callee_inv]) >>
                  simp[call_meter_safe_not_static_inv]) >>
              simp[call_meter_safe_expand_inv]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_memory_info_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_copy_instances_inv:
  call_meter_safe (call_meter_result c rb rest)
    (step_copy_to_memory CallDataCopy (SOME get_call_data))
    (\r t. call_meter_result c rb rest t) /\
  call_meter_safe (call_meter_result c rb rest)
    (step_copy_to_memory CodeCopy (SOME get_current_code))
    (\r t. call_meter_result c rb rest t) /\
  call_meter_safe (call_meter_result c rb rest)
    (step_copy_to_memory MCopy NONE)
    (\r t. call_meter_result c rb rest t)
Proof
  rpt conj_tac >> irule call_meter_safe_step_copy_inv >>
  simp[call_meter_safe_call_data_inv, call_meter_safe_source_readers_inv]
QED

Theorem call_meter_safe_charge_inv:
  call_meter_safe (call_meter_result c rb rest) (charge_state_gas n)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_charge]
QED

Theorem call_meter_safe_credit_inv:
  call_meter_safe (call_meter_result c rb rest) (credit_state_gas_refund n)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_credit]
QED

Theorem call_meter_safe_slot_inv:
  call_meter_safe (call_meter_result c rb rest) (access_slot key)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  simp[call_meter_safe_def, call_meter_ready_def, access_slot_def,
       domain_check_def, set_domain_def, ignore_bind_def, bind_def,
       return_def, fail_def] >> rpt strip_tac >>
  Cases_on `s.msdomain` >> gvs[AllCaseEqs()] >>
  irule call_meter_result_same >> simp[]
QED

Theorem call_meter_safe_original_inv:
  call_meter_safe (call_meter_result c rb rest) get_original
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, call_meter_result_def, get_original_def,
       return_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem call_meter_safe_tStorage_inv:
  call_meter_safe (call_meter_result c rb rest) get_tStorage
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, get_tStorage_def, return_def]
QED

Theorem call_meter_safe_write_storage_inv:
  call_meter_safe (call_meter_result c rb rest) (write_storage a k v)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  rewrite_tac[write_storage_def] >>
  mp_tac (GEN_ALL call_meter_safe_update_accounts) >>
  simp[call_meter_safe_def] >> metis_tac[call_meter_ready_result]
QED

Theorem call_meter_safe_set_tStorage_inv:
  call_meter_safe (call_meter_result c rb rest) (set_tStorage x)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  simp[call_meter_safe_def, set_tStorage_def, return_def,
       call_meter_ready_def] >> rpt strip_tac >>
  irule call_meter_result_same >> simp[]
QED

Theorem call_meter_safe_write_transient_inv:
  call_meter_safe (call_meter_result c rb rest) (write_transient_storage a k v)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[write_transient_storage_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_tStorage_inv, call_meter_safe_set_tStorage_inv]
QED

Theorem call_meter_safe_update_refund_inv:
  call_meter_safe (call_meter_result c rb rest) (update_gas_refund delta)
    (\r t. call_meter_result c rb rest t)
Proof
  PairCases_on `delta` >> irule call_meter_safe_result_lift >> gen_tac >>
  rewrite_tac[update_gas_refund_def] >>
  ho_match_mp_tac call_meter_safe_context_update >> simp[call_meter_neutral_def]
QED

Theorem call_meter_safe_gas_left_inv:
  call_meter_safe (call_meter_result c rb rest) get_gas_left
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[get_gas_left_def] >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_current_inv, call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_storage_reader_inv:
  call_meter_safe (call_meter_result c rb rest)
    (if transient then bind get_tStorage (\ts. return (lookup_transient_storage a ts))
     else bind get_accounts (\acc. return (lookup_account a acc).storage))
    (\r t. call_meter_result c rb rest t)
Proof
  Cases_on `transient` >> simp[] >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_tStorage_inv, call_meter_safe_accounts_inv,
       call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_sload_inv:
  call_meter_safe (call_meter_result c rb rest) (step_sload transient)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_sload_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
                  simp[call_meter_safe_storage_reader_inv, call_meter_result_push_stack]) >>
              simp[call_meter_safe_consume_inv]) >>
          Cases_on `transient`
          >- simp[call_meter_safe_def, return_def] >>
          simp[call_meter_safe_slot_inv]) >>
      simp[call_meter_safe_callee_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_sstore_gas_tail_inv:
  call_meter_safe (call_meter_result c rb rest)
    (ignore_bind (update_gas_refund delta)
      (ignore_bind (if refund = 0 then return () else credit_state_gas_refund refund)
        (ignore_bind (consume_gas gas) (charge_state_gas stateGas))))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_update_refund_inv] >>
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- (Cases_on `refund = 0`
      >- simp[call_meter_safe_def, return_def] >>
      simp[call_meter_safe_credit_inv]) >>
  irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_consume_inv, call_meter_safe_charge_inv]
QED

Theorem call_meter_safe_sstore_gas_inv:
  call_meter_safe (call_meter_result c rb rest)
    (step_sstore_gas_consumption address key value)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_sstore_gas_consumption_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >> conj_tac
      >- simp[call_meter_safe_assert] >>
      irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >>
              simp[call_meter_safe_slot_inv, call_meter_safe_sstore_gas_tail_inv]) >>
          simp[call_meter_safe_original_inv]) >>
      simp[call_meter_safe_accounts_inv]) >>
  simp[call_meter_safe_gas_left_inv]
QED

Theorem call_meter_safe_sstore_inv:
  call_meter_safe (call_meter_result c rb rest) (step_sstore transient)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_sstore_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >> conj_tac
          >- (Cases_on `transient` >> simp[call_meter_safe_consume_inv,
                                          call_meter_safe_sstore_gas_inv]) >>
          irule call_meter_safe_ignore_invariant >> conj_tac
          >- simp[call_meter_safe_not_static_inv] >>
          Cases_on `transient` >> simp[call_meter_safe_write_storage_inv,
                                      call_meter_safe_write_transient_inv]) >>
      simp[call_meter_safe_callee_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_terminal_inv:
  call_meter_safe (call_meter_result c rb rest) finish
    (\r t. call_meter_result c rb rest t) /\
  call_meter_safe (call_meter_result c rb rest) revert
    (\r t. call_meter_result c rb rest t) /\
  call_meter_safe (call_meter_result c rb rest) (fail InvalidOpcode)
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, finish_def, revert_def, fail_def]
QED

Theorem call_meter_safe_return_data_inv:
  call_meter_safe (call_meter_result c rb rest) (set_return_data bytes)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_set_return_data]
QED

Theorem call_meter_safe_stop_inv:
  call_meter_safe (call_meter_result c rb rest)
    (ignore_bind (set_return_data []) finish)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_return_data_inv, call_meter_safe_terminal_inv]
QED

Theorem call_meter_safe_return_inv:
  call_meter_safe (call_meter_result c rb rest) (step_return b)
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_return_def, ignore_bind_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
                  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
                      >- (Cases_on `b` >> simp[call_meter_safe_terminal_inv]) >>
                      simp[call_meter_safe_return_data_inv]) >>
                  simp[call_meter_safe_read_memory_inv]) >>
              simp[call_meter_safe_expand_inv]) >>
          simp[call_meter_safe_consume_inv]) >>
      simp[call_meter_safe_memory_info_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_charge_account_inv:
  call_meter_safe (call_meter_result c rb rest) (charge_new_account charged)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_charge_account]
QED

Theorem call_meter_safe_update_accounts_inv:
  call_meter_safe (call_meter_result c rb rest) (update_accounts f)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  mp_tac (GEN_ALL call_meter_safe_update_accounts) >>
  simp[call_meter_safe_def] >> metis_tac[call_meter_ready_result]
QED

Theorem call_meter_safe_delete_inv:
  call_meter_safe (call_meter_result c rb rest) (add_to_delete a)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  simp[call_meter_safe_def, add_to_delete_def, return_def,
       call_meter_ready_def] >> rpt strip_tac >>
  irule call_meter_result_same >> simp[]
QED

Theorem call_meter_safe_self_destruct_tail_inv:
  call_meter_safe (call_meter_result c rb rest)
    (ignore_bind (update_accounts f)
      (ignore_bind (push_logs logs)
        (bind get_original (\original.
          ignore_bind (if account_empty (lookup_account a original)
                       then add_to_delete a else return ()) finish))))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_update_accounts_inv] >>
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_logs_inv] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >> conj_tac
      >- (IF_CASES_TAC
          >- simp[call_meter_safe_delete_inv] >>
          simp[call_meter_safe_def, return_def]) >>
      simp[call_meter_safe_terminal_inv]) >>
  simp[call_meter_safe_original_inv]
QED

Theorem call_meter_safe_self_destruct_inv:
  call_meter_safe (call_meter_result c rb rest) step_self_destruct
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[step_self_destruct_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
          >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >> conj_tac
              >- simp[call_meter_safe_return_data_inv] >>
              irule call_meter_safe_bind_invariant >> conj_tac
              >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >> conj_tac
                  >- simp[call_meter_safe_consume_inv] >>
                  irule call_meter_safe_ignore_invariant >> conj_tac
                  >- simp[call_meter_safe_charge_account_inv] >>
                  irule call_meter_safe_ignore_invariant >>
                  simp[call_meter_safe_not_static_inv, call_meter_safe_self_destruct_tail_inv]) >>
              simp[call_meter_safe_accounts_inv]) >>
          simp[call_meter_safe_callee_inv]) >>
      simp[call_meter_safe_access_inv]) >>
  simp[call_meter_safe_pop_inv]
QED

Theorem call_meter_safe_ordinary_inst_inv:
  ~is_call op ==>
  call_meter_safe (call_meter_result c rb rest) (step_inst op)
    (\r t. call_meter_result c rb rest t)
Proof
  Cases_on `op` >>
  simp[is_call_def, step_inst_def, ignore_bind_def,
       call_meter_safe_binop_inv, call_meter_safe_monop_inv,
       call_meter_safe_modop_inv, call_meter_safe_exp_inv,
       call_meter_safe_context_inv, call_meter_safe_msgParams_inv,
       call_meter_safe_txParams_inv, call_meter_safe_keccak_inv,
       call_meter_safe_balance_inv, call_meter_safe_call_data_load_inv,
       call_meter_safe_copy_instances_inv, call_meter_safe_ext_code_size_inv,
       call_meter_safe_ext_code_copy_inv, call_meter_safe_ext_code_hash_inv,
       call_meter_safe_return_data_copy_inv, call_meter_safe_block_hash_inv,
       call_meter_safe_blob_hash_inv, call_meter_safe_self_balance_inv,
       call_meter_safe_step_pop_inv, call_meter_safe_mload_inv,
       call_meter_safe_mstore_inv, call_meter_safe_sload_inv,
       call_meter_safe_sstore_inv, call_meter_safe_step_jump_inv,
       call_meter_safe_step_jumpi_inv, call_meter_safe_consume_inv,
       call_meter_safe_step_push_inv, call_meter_safe_step_dup_inv,
       call_meter_safe_step_swap_inv, call_meter_safe_log_inv,
       call_meter_safe_step_dupn_inv, call_meter_safe_step_swapn_inv,
       call_meter_safe_step_exchange_inv, call_meter_safe_return_inv,
       call_meter_safe_self_destruct_inv, call_meter_safe_terminal_inv] >>
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_return_data_inv, call_meter_safe_terminal_inv]
QED

Theorem call_meter_step_ordinary_budget:
  ~is_call op /\ wf_state s /\ call_meter_budget n ceiling s /\
  0 < n /\ n <= LENGTH s.contexts /\ step_inst op s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `n <= LENGTH s.contexts` by simp[] >>
  `call_meter_backed h0` by (drule_all call_meter_budget_top >> simp[]) >>
  `h0.gasUsed <= h0.msgParams.gasLimit` by
    gvs[wf_state_def, wf_context_def] >>
  `call_meter_result h0 h1 t' s` by simp[call_meter_result_same] >>
  drule call_meter_safe_ordinary_inst_inv >>
  disch_then (qspecl_then [`t'`, `h1`, `h0`] mp_tac) >>
  simp[call_meter_safe_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  drule_all call_meter_result_budget >> simp[]
QED

Theorem call_meter_step_inst_budget:
  wf_state s /\ call_meter_budget n ceiling s /\
  0 < n /\ n <= LENGTH s.contexts /\ step_inst op s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  Cases_on `is_call op`
  >- (Cases_on `op` >> gvs[is_call_def, step_inst_def] >>
      metis_tac[call_meter_step_call_budget, call_meter_step_create_budget]) >>
  metis_tac[call_meter_step_ordinary_budget]
QED

Theorem call_meter_safe_ordinary_sequence_inv:
  ~is_call op ==>
  call_meter_safe (call_meter_result c rb rest)
    (ignore_bind (step_inst op) (inc_pc_or_jump op))
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_ordinary_inst_inv, call_meter_safe_inc_pc_or_jump_inv]
QED

Theorem call_meter_step_sequence_budget:
  wf_state s /\ call_meter_budget n ceiling s /\
  0 < n /\ n <= LENGTH s.contexts /\
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  Cases_on `is_call op`
  >- (simp[inc_pc_or_jump_def, ignore_bind_def, bind_def, return_def] >>
      rpt strip_tac >> Cases_on `step_inst op s` >> Cases_on `q` >> gvs[] >>
      drule_all call_meter_step_inst_budget >> simp[]) >>
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `n <= LENGTH s.contexts` by simp[] >>
  `call_meter_backed h0` by (drule_all call_meter_budget_top >> simp[]) >>
  `h0.gasUsed <= h0.msgParams.gasLimit` by
    gvs[wf_state_def, wf_context_def] >>
  `call_meter_result h0 h1 t' s` by simp[call_meter_result_same] >>
  drule call_meter_safe_ordinary_sequence_inv >>
  disch_then (qspecl_then [`t'`, `h1`, `h0`] mp_tac) >>
  simp[call_meter_safe_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  drule_all call_meter_result_budget >> simp[]
QED

Theorem call_meter_step_inner_budget:
  wf_state s /\ call_meter_budget n ceiling s /\
  0 < n /\ n <= LENGTH s.contexts /\ step_inner s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `n <= LENGTH s.contexts` by simp[] >>
  qpat_x_assum `step_inner s = _` mp_tac >>
  simp[step_inner_def, get_current_context_def, bind_def, return_def] >>
  Cases_on `FLOOKUP h0.msgParams.parsed h0.pc` >> simp[]
  >- (IF_CASES_TAC >> strip_tac >> drule_all call_meter_step_inst_budget >> simp[]) >>
  rewrite_tac[GSYM ignore_bind_def] >> strip_tac >>
  drule_all call_meter_step_sequence_budget >> simp[]
QED

Theorem call_meter_safe_reraise_inv:
  e <> SOME Impossible /\ e <> SOME Unimplemented ==>
  call_meter_safe (call_meter_result c rb rest) (reraise e)
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, reraise_def]
QED

Theorem call_meter_safe_output_to_inv:
  call_meter_safe (call_meter_result c rb rest) get_output_to
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[get_output_to_def] >> irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_current_inv, call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_deposit_inv:
  call_meter_safe (call_meter_result c rb rest)
    (ignore_bind (assert valid InvalidContractPrefix)
      (ignore_bind (consume_gas gas)
        (ignore_bind (assert sizeOK OutOfGas)
          (ignore_bind (charge_state_gas stateGas)
            (ignore_bind (update_accounts f) (reraise NONE))))))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_assert] >>
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_consume_inv] >>
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_assert] >>
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- simp[call_meter_safe_charge_inv] >>
  irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_update_accounts_inv, call_meter_safe_reraise_inv]
QED

Theorem call_meter_safe_handle_create_inv:
  e <> SOME Impossible /\ e <> SOME Unimplemented ==>
  call_meter_safe (call_meter_result c rb rest) (handle_create e)
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> rewrite_tac[handle_create_def, LET_THM] >> BETA_TAC >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_bind_invariant >> conj_tac
      >- (gen_tac >> BETA_TAC >> Cases_on `e` >> Cases_on `x'` >>
          simp[call_meter_safe_reraise_inv, call_meter_safe_deposit_inv]) >>
      simp[call_meter_safe_output_to_inv]) >>
  simp[call_meter_safe_source_readers_inv]
QED


Theorem call_meter_pop_internal_budget:
  call_meter_budget n ceiling s /\ n < LENGTH s.contexts /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  parent.gasUsed <= parent.msgParams.gasLimit /\
  pop_and_incorporate_context success s = (r,t) ==>
  r = INL () /\ call_meter_budget n ceiling t
Proof
  strip_tac >>
  `parent.stateGasSpilled + parent.stateGasCommitted + call_meter_claim child <=
    parent.gasUsed` by (drule_all call_meter_budget_parent_margin >> simp[]) >>
  `child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed` by
    (gvs[call_meter_claim_def] >> decide_tac) >>
  drule_all call_meter_pop_settle_pair >>
  disch_then (qspec_then `success` assume_tac) >> gvs[LET_THM] >>
  irule call_meter_budget_pop >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[call_meter_settle_pop_backed, call_meter_settle_pop_claim, ADD_COMM]
QED

Theorem call_meter_pop_root_budget:
  LENGTH s.contexts = n /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed /\
  pop_and_incorporate_context success s = (r,t) ==>
  r = INL () /\ call_meter_budget n ceiling t
Proof
  strip_tac >> drule_all call_meter_pop_settle_pair >>
  disch_then (qspec_then `success` assume_tac) >> gvs[LET_THM] >>
  irule call_meter_budget_root_exit >> qexists `s` >> simp[]
QED

Theorem call_meter_handle_create_budget:
  wf_state s /\ call_meter_budget n ceiling s /\
  0 < n /\ n <= LENGTH s.contexts /\
  e <> SOME Impossible /\ e <> SOME Unimplemented /\
  handle_create e s = (r,t) ==>
  call_meter_budget n ceiling t /\
  (!ex. r = INR ex ==> ex <> SOME Impossible /\ ex <> SOME Unimplemented)
Proof
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  `n <= LENGTH s.contexts` by simp[] >>
  `call_meter_backed h0` by (drule_all call_meter_budget_top >> simp[]) >>
  `h0.gasUsed <= h0.msgParams.gasLimit` by
    gvs[wf_state_def, wf_context_def] >>
  `call_meter_result h0 h1 t' s` by simp[call_meter_result_same] >>
  drule call_meter_safe_handle_create_inv >>
  disch_then (qspecl_then [`t'`, `h1`, `h0`] mp_tac) >>
  simp[call_meter_safe_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  drule_all call_meter_result_budget >> simp[]
QED

Theorem call_meter_safe_restore_inv:
  call_meter_safe (call_meter_result c rb rest) restore_state_gas
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_restore]
QED

Theorem call_meter_safe_forfeit_inv:
  call_meter_safe (call_meter_result c rb rest) forfeit_remaining_gas
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_forfeit]
QED

Theorem call_meter_safe_exception_prepare_inv:
  call_meter_safe (call_meter_result c rb rest)
    (ignore_bind (if success then return () else restore_state_gas)
      (if ~success /\ e <> SOME Reverted then
        ignore_bind forfeit_remaining_gas (set_return_data [])
       else return ()))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_invariant >> conj_tac
  >- (Cases_on `success`
      >- simp[call_meter_safe_def, return_def] >>
      simp[call_meter_safe_restore_inv]) >>
  Cases_on `~success /\ e <> SOME Reverted`
  >- (simp[] >> irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_forfeit_inv, call_meter_safe_return_data_inv]) >>
  simp[call_meter_safe_def, return_def]
QED
