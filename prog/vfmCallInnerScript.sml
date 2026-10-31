Theory vfmCallInner
Ancestors vfmCallSteps vfmCallGrant vfmCallPrecompile vfmCallMeterOps
          vfmCallMeterSafe vfmCallMeter vfmCallBudget vfmExecution vfmContext
          vfmState vfmTypes arithmetic list

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
