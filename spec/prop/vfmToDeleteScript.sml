(*
 * Execution never reads the deletion queue.
 *
 * rollback.toDelete is only ever extended (SELFDESTRUCT conses onto it),
 * copied into a frame's saved rollback when a call pushes it, and restored
 * from that copy when the frame reverts; the queue is read only when the
 * transaction is settled (process_deletions). So two states that differ
 * only in their queues run in lockstep, and end in states that differ only
 * in their queues.
 *)
Theory vfmToDelete
Ancestors
  arithmetic list pair While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp vfmOriginalState

(* Two states that differ only in their deletion queues: the current
   rollback's and the saved rollbacks' in every frame. *)
Definition erase_toDelete_def:
  erase_toDelete (s:execution_state) =
    s with <| rollback := s.rollback with toDelete := [];
              contexts := MAP (λ(c,rb). (c, rb with toDelete := [])) s.contexts |>
End

Definition TD_rollback_def:
  TD_rollback (a:rollback_state) b <=>
    (a with toDelete := []) = (b with toDelete := [])
End

Definition TD_frame_def:
  TD_frame (c,a) (d,b) <=> c = d /\ TD_rollback a b
End

Definition TD_exec_def:
  TD_exec R f g <=>
    !s t. erase_toDelete s = erase_toDelete t ==>
      sum$SUM_REL R (=) (FST (f s)) (FST (g t)) /\
      erase_toDelete (SND (f s)) = erase_toDelete (SND (g t))
End

Theorem TD_rollback_fields[local]:
  TD_rollback a b <=>
    a.accounts = b.accounts /\ a.tStorage = b.tStorage /\
    a.accesses = b.accesses
Proof
  simp[TD_rollback_def, rollback_state_component_equality]
QED

Theorem erase_toDelete_fields[local]:
  erase_toDelete s = erase_toDelete t <=>
    MAP (\(c,rb). (c, rb with toDelete := [])) s.contexts =
    MAP (\(c,rb). (c, rb with toDelete := [])) t.contexts /\
    s.txParams = t.txParams /\ TD_rollback s.rollback t.rollback /\
    s.originalAccounts = t.originalAccounts /\ s.msdomain = t.msdomain
Proof
  simp[erase_toDelete_def, execution_state_component_equality,
       TD_rollback_def, EQ_SYM_EQ, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem TD_exec_return[local]:
  R x y ==> TD_exec R (return x) (return y)
Proof
  simp[TD_exec_def, return_def]
QED

Theorem TD_exec_bind[local]:
  TD_exec R f g /\ (!x y. R x y ==> TD_exec Q (k x) (l y)) ==>
  TD_exec Q (bind f k) (bind g l)
Proof
  rw[TD_exec_def] >>
  first_x_assum drule >>
  namedCases_on `f s` ["r1 s1"] >> namedCases_on `g t` ["r2 t1"] >>
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[bind_def] >> metis_tac[]
QED

Theorem TD_exec_ignore_bind[local]:
  TD_exec R f g /\ TD_exec Q k l ==>
  TD_exec Q (ignore_bind f k) (ignore_bind g l)
Proof
  rw[ignore_bind_def] >> irule TD_exec_bind >> metis_tac[]
QED

Theorem TD_exec_handle[local]:
  TD_exec R f g /\ (!e. TD_exec R (h e) (k e)) ==>
  TD_exec R (handle f h) (handle g k)
Proof
  rw[TD_exec_def] >>
  qpat_x_assum `!s t. _` (qspecl_then [`s`,`t`] mp_tac) >>
  simp[] >> strip_tac >>
  namedCases_on `f s` ["r1 s1"] >> namedCases_on `g t` ["r2 t1"] >>
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[handle_def] >> metis_tac[]
QED

Theorem TD_exec_fail[local]:
  TD_exec R (fail e) (fail e)
Proof simp[TD_exec_def, fail_def]
QED

Theorem TD_exec_finish[local]:
  TD_exec R finish finish
Proof simp[TD_exec_def, finish_def]
QED

Theorem TD_exec_revert[local]:
  TD_exec R revert revert
Proof simp[TD_exec_def, revert_def]
QED

Theorem TD_exec_reraise[local]:
  TD_exec R (reraise e) (reraise e)
Proof simp[TD_exec_def, reraise_def]
QED

Theorem TD_exec_assert[local]:
  TD_exec (=) (assert b e) (assert b e)
Proof Cases_on `b` >> simp[TD_exec_def, assert_def]
QED

Theorem erase_toDelete_contexts[local]:
  erase_toDelete s = erase_toDelete t ==>
  LENGTH s.contexts = LENGTH t.contexts /\
  (s.contexts = [] <=> t.contexts = [])
Proof
  rw[erase_toDelete_fields] >>
  qpat_x_assum `MAP _ _ = MAP _ _`
    (mp_tac o AP_TERM ``LENGTH : (context # rollback_state) list -> num``) >>
  simp[] >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> simp[]
QED

Theorem TD_exec_get_rollback[local]:
  TD_exec TD_rollback get_rollback get_rollback
Proof
  simp[TD_exec_def, get_rollback_def, return_def, erase_toDelete_fields]
QED

Theorem TD_exec_set_rollback[local]:
  TD_rollback a b ==> TD_exec (=) (set_rollback a) (set_rollback b)
Proof
  simp[TD_exec_def, set_rollback_def, return_def, erase_toDelete_fields]
QED

Theorem TD_exec_push_context[local]:
  TD_frame a b ==> TD_exec (=) (push_context a) (push_context b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[TD_frame_def, TD_exec_def, push_context_def, return_def,
       erase_toDelete_fields, TD_rollback_def]
QED

Theorem TD_exec_pop_context[local]:
  TD_exec TD_frame pop_context pop_context
Proof
  rw[TD_exec_def] >>
  drule erase_toDelete_contexts >>
  namedCases_on `s.contexts` ["", "c1 cs1"] >>
  namedCases_on `t.contexts` ["", "c2 cs2"] >>
  gvs[pop_context_def, fail_def, return_def, erase_toDelete_fields] >>
  PairCases_on `c1` >> PairCases_on `c2` >>
  gvs[TD_frame_def, TD_rollback_def, erase_toDelete_fields]
QED

Theorem TD_exec_add_to_delete[local]:
  TD_exec (=) (add_to_delete a) (add_to_delete a)
Proof
  simp[TD_exec_def, add_to_delete_def, return_def,
       erase_toDelete_fields, TD_rollback_fields]
QED

Theorem TD_exec_get_current_context[local]:
  TD_exec (=) get_current_context get_current_context
Proof
  rw[TD_exec_def] >> drule erase_toDelete_contexts >>
  namedCases_on `s.contexts` ["", "c1 cs1"] >>
  namedCases_on `t.contexts` ["", "c2 cs2"] >>
  gvs[get_current_context_def, fail_def, return_def, erase_toDelete_fields] >>
  PairCases_on `c1` >> PairCases_on `c2` >> gvs[]
QED

Theorem TD_exec_set_current_context[local]:
  TD_exec (=) (set_current_context c) (set_current_context c)
Proof
  rw[TD_exec_def] >> drule erase_toDelete_contexts >>
  namedCases_on `s.contexts` ["", "c1 cs1"] >>
  namedCases_on `t.contexts` ["", "c2 cs2"] >>
  gvs[set_current_context_def, fail_def, return_def, erase_toDelete_fields] >>
  PairCases_on `c1` >> PairCases_on `c2` >>
  gvs[erase_toDelete_fields]
QED

Theorem TD_exec_get_num_contexts[local]:
  TD_exec (=) get_num_contexts get_num_contexts
Proof
  rw[TD_exec_def, get_num_contexts_def, return_def] >>
  metis_tac[erase_toDelete_contexts]
QED

Theorem TD_exec_get_tx_params[local]:
  TD_exec (=) get_tx_params get_tx_params
Proof simp[TD_exec_def, get_tx_params_def, return_def, erase_toDelete_fields]
QED

Theorem TD_exec_get_accounts[local]:
  TD_exec (=) get_accounts get_accounts
Proof
  simp[TD_exec_def, get_accounts_def, return_def, erase_toDelete_fields,
       TD_rollback_fields]
QED

Theorem TD_exec_update_accounts[local]:
  TD_exec (=) (update_accounts f) (update_accounts f)
Proof
  simp[TD_exec_def, update_accounts_def, return_def, erase_toDelete_fields,
       TD_rollback_fields]
QED

Theorem TD_exec_get_tStorage[local]:
  TD_exec (=) get_tStorage get_tStorage
Proof
  simp[TD_exec_def, get_tStorage_def, return_def, erase_toDelete_fields,
       TD_rollback_fields]
QED

Theorem TD_exec_set_tStorage[local]:
  TD_exec (=) (set_tStorage v) (set_tStorage v)
Proof
  simp[TD_exec_def, set_tStorage_def, return_def, erase_toDelete_fields,
       TD_rollback_fields]
QED

Theorem TD_exec_get_original[local]:
  TD_exec (=) get_original get_original
Proof
  rw[TD_exec_def] >> drule erase_toDelete_contexts >>
  gvs[erase_toDelete_fields] >>
  Cases_on `s.contexts = []` >>
  simp[get_original_def, fail_def, return_def]
QED

Theorem TD_exec_set_original[local]:
  TD_exec (=) (set_original a) (set_original a)
Proof
  rw[TD_exec_def] >> drule erase_toDelete_contexts >>
  gvs[erase_toDelete_fields] >>
  Cases_on `s.contexts = []` >>
  simp[set_original_def, fail_def, return_def, erase_toDelete_fields]
QED

Theorem TD_exec_get_gas_left[local]:
  TD_exec (=) get_gas_left get_gas_left
Proof
  rewrite_tac[get_gas_left_def] >> irule TD_exec_bind >>
  qexists_tac `(=)` >> simp[TD_exec_get_current_context, TD_exec_return]
QED

(* Structural composition at the relational-monad boundary. *)
fun td_compose ths goal =
  FIRST [first_assum MATCH_ACCEPT_TAC, FIRST (map MATCH_ACCEPT_TAC ths),
         irule TD_exec_return >> simp[],
         irule TD_exec_assert,
         irule TD_exec_fail,
         irule TD_exec_finish,
         irule TD_exec_revert,
         irule TD_exec_reraise,
         irule TD_exec_ignore_bind >> conj_tac
           >- (qexists_tac `(=)` >> td_compose ths) >> td_compose ths,
         irule TD_exec_bind >> qexists_tac `(=)` >> reverse conj_tac
           >- td_compose ths >>
           rpt gen_tac >> disch_then SUBST1_TAC >> BETA_TAC >> td_compose ths,
         CHANGED_TAC (rewrite_tac[ignore_bind_def]) >> td_compose ths,
         irule TD_exec_push_context >> simp[TD_frame_def],
         irule TD_exec_bind >> qexists_tac `TD_rollback` >> reverse conj_tac
           >- MATCH_ACCEPT_TAC TD_exec_get_rollback >>
           rpt gen_tac >> disch_tac >> BETA_TAC >> td_compose ths,
         IF_CASES_TAC >> td_compose ths,
         CASE_TAC >> simp[] >> td_compose ths,
         pairarg_tac >> simp[] >> td_compose ths] goal;

Theorem TD_exec_get_callee[local]:
  TD_exec (=) get_callee get_callee
Proof
  rewrite_tac[get_callee_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_caller[local]:
  TD_exec (=) get_caller get_caller
Proof
  rewrite_tac[get_caller_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_value[local]:
  TD_exec (=) get_value get_value
Proof
  rewrite_tac[get_value_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_output_to[local]:
  TD_exec (=) get_output_to get_output_to
Proof
  rewrite_tac[get_output_to_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_return_data[local]:
  TD_exec (=) get_return_data get_return_data
Proof
  rewrite_tac[get_return_data_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_return_data_check[local]:
  TD_exec (=) (get_return_data_check off sz) (get_return_data_check off sz)
Proof
  rewrite_tac[get_return_data_check_def] >> td_compose [TD_exec_get_return_data]
QED

Theorem TD_exec_set_return_data[local]:
  TD_exec (=) (set_return_data rd) (set_return_data rd)
Proof
  simp[set_return_data_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_get_static[local]:
  TD_exec (=) get_static get_static
Proof
  rewrite_tac[get_static_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_code[local]:
  TD_exec (=) (get_code a) (get_code a)
Proof
  rewrite_tac[get_code_def] >> td_compose [TD_exec_get_accounts]
QED

Theorem TD_exec_get_current_code[local]:
  TD_exec (=) get_current_code get_current_code
Proof
  rewrite_tac[get_current_code_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_get_call_data[local]:
  TD_exec (=) get_call_data get_call_data
Proof
  rewrite_tac[get_call_data_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_set_jump_dest[local]:
  TD_exec (=) (set_jump_dest j) (set_jump_dest j)
Proof
  rewrite_tac[set_jump_dest_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_push_logs[local]:
  TD_exec (=) (push_logs ls) (push_logs ls)
Proof
  rewrite_tac[push_logs_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_update_gas_refund[local]:
  TD_exec (=) (update_gas_refund p) (update_gas_refund p)
Proof
  Cases_on `p` >> rewrite_tac[update_gas_refund_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_consume_gas[local]:
  TD_exec (=) (consume_gas n) (consume_gas n)
Proof
  simp[consume_gas_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_unuse_gas[local]:
  TD_exec (=) (unuse_gas n) (unuse_gas n)
Proof
  simp[unuse_gas_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_pop_stack[local]:
  TD_exec (=) (pop_stack n) (pop_stack n)
Proof
  simp[pop_stack_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_push_stack[local]:
  TD_exec (=) (push_stack v) (push_stack v)
Proof
  simp[push_stack_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_set_domain[local]:
  TD_exec (=) (set_domain d) (set_domain d)
Proof
  simp[TD_exec_def, set_domain_def, return_def, erase_toDelete_fields]
QED

Theorem TD_exec_domain_check[local]:
  TD_exec (=) cont cont ==>
  TD_exec (=) (domain_check err check upd cont) (domain_check err check upd cont)
Proof
  strip_tac >> pure_rewrite_tac[TD_exec_def] >> rpt gen_tac >> disch_tac >>
  `s.msdomain = t.msdomain` by gvs[erase_toDelete_fields] >>
  namedCases_on `t.msdomain` ["dom", "dom"] >> fs[] >> simp[domain_check_def]
  >- (IF_CASES_TAC >> simp[fail_def] >>
      fs[TD_exec_def] >> first_x_assum drule >> simp[]) >>
  `TD_exec (=) (ignore_bind (set_domain (Collect (upd dom))) cont)
                   (ignore_bind (set_domain (Collect (upd dom))) cont)`
    by (irule TD_exec_ignore_bind >> simp[] >> qexists_tac `(=)` >>
        simp[TD_exec_set_domain]) >>
  fs[TD_exec_def] >> first_x_assum drule >> simp[]
QED

Theorem TD_exec_access_address[local]:
  TD_exec (=) (access_address a) (access_address a)
Proof
  rewrite_tac[access_address_def] >> irule TD_exec_domain_check >>
  simp[TD_exec_def, return_def, erase_toDelete_fields, TD_rollback_fields]
QED

Theorem TD_exec_access_slot[local]:
  TD_exec (=) (access_slot k) (access_slot k)
Proof
  rewrite_tac[access_slot_def] >> irule TD_exec_domain_check >>
  simp[TD_exec_def, return_def, erase_toDelete_fields, TD_rollback_fields]
QED

Theorem TD_exec_ensure_storage_in_domain[local]:
  TD_exec (=) (ensure_storage_in_domain a) (ensure_storage_in_domain a)
Proof
  rewrite_tac[ensure_storage_in_domain_def] >>
  irule TD_exec_domain_check >> simp[TD_exec_return]
QED

Theorem TD_exec_memory_expansion_info[local]:
  TD_exec (=) (memory_expansion_info off sz) (memory_expansion_info off sz)
Proof
  simp[memory_expansion_info_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_expand_memory[local]:
  TD_exec (=) (expand_memory n) (expand_memory n)
Proof
  rewrite_tac[expand_memory_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_read_memory[local]:
  TD_exec (=) (read_memory off sz) (read_memory off sz)
Proof
  rewrite_tac[read_memory_def] >> td_compose [TD_exec_get_current_context]
QED

Theorem TD_exec_write_memory[local]:
  TD_exec (=) (write_memory off bs) (write_memory off bs)
Proof
  rewrite_tac[write_memory_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_write_storage[local]:
  TD_exec (=) (write_storage a k v) (write_storage a k v)
Proof
  rewrite_tac[write_storage_def] >> td_compose [TD_exec_update_accounts]
QED

Theorem TD_exec_write_transient_storage[local]:
  TD_exec (=) (write_transient_storage a k v) (write_transient_storage a k v)
Proof
  simp[write_transient_storage_def] >>
  td_compose [TD_exec_get_tStorage, TD_exec_set_tStorage]
QED

Theorem TD_exec_assert_not_static[local]:
  TD_exec (=) assert_not_static assert_not_static
Proof
  rewrite_tac[assert_not_static_def] >> td_compose [TD_exec_get_static]
QED

Theorem TD_exec_copy_to_memory[local]:
  (!f. src = SOME f ==> TD_exec (=) f f) ==>
  TD_exec (=) (copy_to_memory gas off soff sz src)
              (copy_to_memory gas off soff sz src)
Proof
  Cases_on `src`
  >- (simp[copy_to_memory_def] >> pairarg_tac >> simp[] >>
      td_compose [TD_exec_memory_expansion_info, TD_exec_consume_gas,
                  TD_exec_expand_memory, TD_exec_read_memory, TD_exec_write_memory]) >>
  simp[copy_to_memory_def] >> strip_tac >>
  td_compose [TD_exec_memory_expansion_info,
              TD_exec_consume_gas, TD_exec_expand_memory, TD_exec_write_memory]
QED

(* EIP-8037: the state-gas meter actions the Amsterdam step definitions
   added.  Each reads or writes only the current frame's state-gas and gas
   fields, none of which the deletion queue is part of, so each is its own
   lockstep witness. *)

Theorem TD_exec_charge_state_gas[local]:
  TD_exec (=) (charge_state_gas n) (charge_state_gas n)
Proof
  simp[charge_state_gas_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context,
              TD_exec_consume_gas]
QED

Theorem TD_exec_credit_state_gas_refund[local]:
  TD_exec (=) (credit_state_gas_refund n) (credit_state_gas_refund n)
Proof
  simp[credit_state_gas_refund_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_charge_new_account[local]:
  TD_exec (=) (charge_new_account charged) (charge_new_account charged)
Proof
  Cases_on `charged` >> simp[charge_new_account_def] >>
  td_compose [TD_exec_charge_state_gas]
QED

Theorem TD_exec_credit_new_account[local]:
  TD_exec (=) (credit_new_account charged) (credit_new_account charged)
Proof
  Cases_on `charged` >> simp[credit_new_account_def] >>
  td_compose [TD_exec_credit_state_gas_refund]
QED

Theorem TD_exec_restore_state_gas[local]:
  TD_exec (=) restore_state_gas restore_state_gas
Proof
  simp[restore_state_gas_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_repay_state_gas_spill[local]:
  TD_exec (=) repay_state_gas_spill repay_state_gas_spill
Proof
  simp[repay_state_gas_spill_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

Theorem TD_exec_forfeit_remaining_gas[local]:
  TD_exec (=) forfeit_remaining_gas forfeit_remaining_gas
Proof
  simp[forfeit_remaining_gas_def] >>
  td_compose [TD_exec_get_gas_left, TD_exec_consume_gas]
QED

Theorem TD_exec_withhold_create_gas[local]:
  TD_exec (=) withhold_create_gas withhold_create_gas
Proof
  simp[withhold_create_gas_def] >>
  td_compose [TD_exec_get_gas_left, TD_exec_consume_gas]
QED

Theorem TD_exec_drain_state_gas_reservoir[local]:
  TD_exec (=) drain_state_gas_reservoir drain_state_gas_reservoir
Proof
  simp[drain_state_gas_reservoir_def] >>
  td_compose [TD_exec_get_current_context, TD_exec_set_current_context]
QED

val td_primitives =
  [TD_exec_get_current_context, TD_exec_set_current_context,
   TD_exec_get_tx_params, TD_exec_get_accounts, TD_exec_update_accounts,
   TD_exec_get_tStorage, TD_exec_set_tStorage, TD_exec_get_original,
   TD_exec_get_gas_left, TD_exec_get_callee, TD_exec_get_caller,
   TD_exec_get_value, TD_exec_get_output_to, TD_exec_get_return_data,
   TD_exec_set_return_data, TD_exec_get_static, TD_exec_get_code,
   TD_exec_get_current_code, TD_exec_get_call_data, TD_exec_set_jump_dest,
   TD_exec_push_logs, TD_exec_update_gas_refund, TD_exec_consume_gas,
   TD_exec_unuse_gas, TD_exec_pop_stack, TD_exec_push_stack,
   TD_exec_access_address, TD_exec_access_slot, TD_exec_ensure_storage_in_domain,
   TD_exec_memory_expansion_info, TD_exec_expand_memory, TD_exec_read_memory,
   TD_exec_write_memory, TD_exec_write_storage, TD_exec_write_transient_storage,
   TD_exec_assert_not_static, TD_exec_add_to_delete,
   TD_exec_charge_state_gas, TD_exec_credit_state_gas_refund,
   TD_exec_charge_new_account, TD_exec_credit_new_account,
   TD_exec_restore_state_gas, TD_exec_repay_state_gas_spill,
   TD_exec_forfeit_remaining_gas, TD_exec_withhold_create_gas,
   TD_exec_drain_state_gas_reservoir];

Theorem TD_exec_step_binop[local]:
  TD_exec (=) (step_binop op f) (step_binop op f)
Proof
  simp[step_binop_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_monop[local]:
  TD_exec (=) (step_monop op f) (step_monop op f)
Proof
  simp[step_monop_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_modop[local]:
  TD_exec (=) (step_modop op f) (step_modop op f)
Proof
  simp[step_modop_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_context[local]:
  TD_exec (=) (step_context op f) (step_context op f)
Proof
  simp[step_context_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_msgParams[local]:
  TD_exec (=) (step_msgParams op f) (step_msgParams op f)
Proof
  simp[step_msgParams_def, TD_exec_step_context]
QED

Theorem TD_exec_step_txParams[local]:
  TD_exec (=) (step_txParams op f) (step_txParams op f)
Proof
  simp[step_txParams_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_exp[local]:
  TD_exec (=) step_exp step_exp
Proof
  simp[step_exp_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_keccak256[local]:
  TD_exec (=) step_keccak256 step_keccak256
Proof
  simp[step_keccak256_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_sload[local]:
  TD_exec (=) (step_sload b) (step_sload b)
Proof
  Cases_on `b` >> simp[step_sload_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_sstore_gas_consumption[local]:
  TD_exec (=) (step_sstore_gas_consumption a k v)
              (step_sstore_gas_consumption a k v)
Proof
  simp[step_sstore_gas_consumption_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_sstore[local]:
  TD_exec (=) (step_sstore b) (step_sstore b)
Proof
  Cases_on `b` >> simp[step_sstore_def] >>
  td_compose (TD_exec_step_sstore_gas_consumption :: td_primitives)
QED

Theorem TD_exec_step_balance[local]:
  TD_exec (=) step_balance step_balance
Proof
  simp[step_balance_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_call_data_load[local]:
  TD_exec (=) step_call_data_load step_call_data_load
Proof
  simp[step_call_data_load_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_copy_to_memory[local]:
  (!f. src = SOME f ==> TD_exec (=) f f) ==>
  TD_exec (=) (step_copy_to_memory op src) (step_copy_to_memory op src)
Proof
  strip_tac >> simp[step_copy_to_memory_def] >>
  irule TD_exec_bind >> qexists_tac `(=)` >> conj_tac
  >- (rpt gen_tac >> disch_then SUBST1_TAC >> simp[] >>
      irule TD_exec_copy_to_memory >> simp[]) >>
  simp[TD_exec_pop_stack]
QED

Theorem TD_exec_step_return_data_copy[local]:
  TD_exec (=) step_return_data_copy step_return_data_copy
Proof
  simp[step_return_data_copy_def] >>
  irule TD_exec_bind >> qexists_tac `(=)` >> conj_tac
  >- (rpt gen_tac >> disch_then SUBST1_TAC >> simp[] >>
      irule TD_exec_copy_to_memory >> simp[TD_exec_get_return_data_check]) >>
  simp[TD_exec_pop_stack]
QED

Theorem TD_exec_step_ext_code_size[local]:
  TD_exec (=) step_ext_code_size step_ext_code_size
Proof
  simp[step_ext_code_size_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_ext_code_copy[local]:
  TD_exec (=) step_ext_code_copy step_ext_code_copy
Proof
  simp[step_ext_code_copy_def] >>
  irule TD_exec_bind >> qexists_tac `(=)` >> conj_tac
  >- (rpt gen_tac >> disch_then SUBST1_TAC >> simp[] >>
      irule TD_exec_bind >> qexists_tac `(=)` >> conj_tac
      >- (rpt gen_tac >> disch_then SUBST1_TAC >> simp[] >>
          irule TD_exec_copy_to_memory >> simp[TD_exec_get_code]) >>
      simp[TD_exec_access_address]) >> simp[TD_exec_pop_stack]
QED

Theorem TD_exec_step_ext_code_hash[local]:
  TD_exec (=) step_ext_code_hash step_ext_code_hash
Proof
  simp[step_ext_code_hash_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_block_hash[local]:
  TD_exec (=) step_block_hash step_block_hash
Proof
  simp[step_block_hash_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_blob_hash[local]:
  TD_exec (=) step_blob_hash step_blob_hash
Proof
  simp[step_blob_hash_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_self_balance[local]:
  TD_exec (=) step_self_balance step_self_balance
Proof
  simp[step_self_balance_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_mload[local]:
  TD_exec (=) step_mload step_mload
Proof
  simp[step_mload_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_mstore[local]:
  TD_exec (=) (step_mstore op) (step_mstore op)
Proof
  simp[step_mstore_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_jump[local]:
  TD_exec (=) step_jump step_jump
Proof
  simp[step_jump_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_jumpi[local]:
  TD_exec (=) step_jumpi step_jumpi
Proof
  simp[step_jumpi_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_push[local]:
  TD_exec (=) (step_push n ws) (step_push n ws)
Proof
  simp[step_push_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_pop[local]:
  TD_exec (=) step_pop step_pop
Proof
  simp[step_pop_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_dup[local]:
  TD_exec (=) (step_dup n) (step_dup n)
Proof
  simp[step_dup_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_swap[local]:
  TD_exec (=) (step_swap n) (step_swap n)
Proof
  simp[step_swap_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_log[local]:
  TD_exec (=) (step_log n) (step_log n)
Proof
  simp[step_log_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_return[local]:
  TD_exec (=) (step_return b) (step_return b)
Proof
  Cases_on `b` >> simp[step_return_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_self_destruct[local]:
  TD_exec (=) step_self_destruct step_self_destruct
Proof
  simp[step_self_destruct_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_ecrecover[local]:
  TD_exec (=) precompile_ecrecover precompile_ecrecover
Proof
  simp[precompile_ecrecover_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_identity[local]:
  TD_exec (=) precompile_identity precompile_identity
Proof
  simp[precompile_identity_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_modexp[local]:
  TD_exec (=) precompile_modexp precompile_modexp
Proof
  simp[precompile_modexp_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_sha2_256[local]:
  TD_exec (=) precompile_sha2_256 precompile_sha2_256
Proof
  simp[precompile_sha2_256_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_ripemd_160[local]:
  TD_exec (=) precompile_ripemd_160 precompile_ripemd_160
Proof
  simp[precompile_ripemd_160_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_ecadd[local]:
  TD_exec (=) precompile_ecadd precompile_ecadd
Proof
  simp[precompile_ecadd_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_ecmul[local]:
  TD_exec (=) precompile_ecmul precompile_ecmul
Proof
  simp[precompile_ecmul_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_ecpairing[local]:
  TD_exec (=) precompile_ecpairing precompile_ecpairing
Proof
  simp[precompile_ecpairing_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_blake2f[local]:
  TD_exec (=) precompile_blake2f precompile_blake2f
Proof
  simp[precompile_blake2f_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_point_eval[local]:
  TD_exec (=) precompile_point_eval precompile_point_eval
Proof
  simp[precompile_point_eval_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_g1add[local]:
  TD_exec (=) precompile_bls_g1add precompile_bls_g1add
Proof
  simp[precompile_bls_g1add_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_g1msm[local]:
  TD_exec (=) precompile_bls_g1msm precompile_bls_g1msm
Proof
  simp[precompile_bls_g1msm_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_g2add[local]:
  TD_exec (=) precompile_bls_g2add precompile_bls_g2add
Proof
  simp[precompile_bls_g2add_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_g2msm[local]:
  TD_exec (=) precompile_bls_g2msm precompile_bls_g2msm
Proof
  simp[precompile_bls_g2msm_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_pairing[local]:
  TD_exec (=) precompile_bls_pairing precompile_bls_pairing
Proof
  simp[precompile_bls_pairing_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_map_fp_to_g1[local]:
  TD_exec (=) precompile_bls_map_fp_to_g1 precompile_bls_map_fp_to_g1
Proof
  simp[precompile_bls_map_fp_to_g1_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_bls_map_fp2_to_g2[local]:
  TD_exec (=) precompile_bls_map_fp2_to_g2 precompile_bls_map_fp2_to_g2
Proof
  simp[precompile_bls_map_fp2_to_g2_def] >> td_compose td_primitives
QED

Theorem TD_exec_precompile_p256verify[local]:
  TD_exec (=) precompile_p256verify precompile_p256verify
Proof
  simp[precompile_p256verify_def] >> td_compose td_primitives
QED

val td_precompiles =
  [TD_exec_precompile_ecrecover, TD_exec_precompile_identity,
   TD_exec_precompile_modexp, TD_exec_precompile_sha2_256,
   TD_exec_precompile_ripemd_160, TD_exec_precompile_ecadd,
   TD_exec_precompile_ecmul, TD_exec_precompile_ecpairing,
   TD_exec_precompile_blake2f, TD_exec_precompile_point_eval,
   TD_exec_precompile_bls_g1add, TD_exec_precompile_bls_g1msm,
   TD_exec_precompile_bls_g2add, TD_exec_precompile_bls_g2msm,
   TD_exec_precompile_bls_pairing, TD_exec_precompile_bls_map_fp_to_g1,
   TD_exec_precompile_bls_map_fp2_to_g2, TD_exec_precompile_p256verify];

Theorem TD_exec_dispatch_precompiles[local]:
  TD_exec (=) (dispatch_precompiles a) (dispatch_precompiles a)
Proof
  rewrite_tac[dispatch_precompiles_def] >> td_compose td_precompiles
QED

Theorem TD_exec_inc_pc[local]:
  TD_exec (=) inc_pc inc_pc
Proof
  simp[inc_pc_def] >> td_compose td_primitives
QED

Theorem TD_exec_abort_create[local]:
  TD_exec (=) abort_create abort_create
Proof
  simp[abort_create_def] >> td_compose (TD_exec_inc_pc :: td_primitives)
QED

Theorem TD_exec_abort_unuse[local]:
  TD_exec (=) (abort_unuse n) (abort_unuse n)
Proof
  simp[abort_unuse_def] >> td_compose (TD_exec_inc_pc :: td_primitives)
QED

Theorem TD_exec_abort_create_exists[local]:
  TD_exec (=) (abort_create_exists a) (abort_create_exists a)
Proof
  simp[abort_create_exists_def] >> td_compose (TD_exec_inc_pc :: td_primitives)
QED

Theorem TD_exec_abort_call_value[local]:
  TD_exec (=) (abort_call_value n) (abort_call_value n)
Proof
  simp[abort_call_value_def] >> td_compose (TD_exec_inc_pc :: td_primitives)
QED

Theorem TD_exec_proceed_create[local]:
  TD_exec (=) (proceed_create sender a value code gas)
              (proceed_create sender a value code gas)
Proof
  simp[proceed_create_def] >>
  td_compose (TD_exec_set_original :: td_primitives)
QED

Theorem TD_exec_proceed_call[local]:
  TD_exec (=) (proceed_call op sender a value off sz code gas dest)
              (proceed_call op sender a value off sz code gas dest)
Proof
  simp[proceed_call_def] >>
  td_compose (TD_exec_dispatch_precompiles :: td_primitives)
QED

Theorem TD_exec_step_create[local]:
  TD_exec (=) (step_create b) (step_create b)
Proof
  simp[step_create_def] >>
  td_compose ([TD_exec_proceed_create, TD_exec_abort_unuse,
               TD_exec_abort_create, TD_exec_abort_create_exists,
               TD_exec_get_num_contexts] @ td_primitives)
QED

Theorem TD_exec_step_call[local]:
  TD_exec (=) (step_call op) (step_call op)
Proof
  simp[step_call_def] >>
  td_compose ([TD_exec_proceed_call, TD_exec_abort_unuse,
               TD_exec_abort_call_value, TD_exec_get_num_contexts] @ td_primitives)
QED

Theorem TD_exec_set_rollback_snd[local]:
  TD_frame a b ==> TD_exec (=) (set_rollback (SND a)) (set_rollback (SND b))
Proof
  Cases_on `a` >> Cases_on `b` >> simp[TD_frame_def] >>
  irule TD_exec_set_rollback >> first_assum ACCEPT_TAC
QED

Theorem TD_exec_pop_and_incorporate_context[local]:
  TD_exec (=) (pop_and_incorporate_context b) (pop_and_incorporate_context b)
Proof
  simp[pop_and_incorporate_context_def] >>
  irule TD_exec_bind >> qexists_tac `(=)` >> reverse conj_tac
  >- simp[TD_exec_get_gas_left] >>
  rpt gen_tac >> disch_then SUBST1_TAC >> BETA_TAC >>
  irule TD_exec_bind >> qexists_tac `TD_frame` >> reverse conj_tac
  >- simp[TD_exec_pop_context] >>
  qx_gen_tac `frame1` >> qx_gen_tac `frame2` >> strip_tac >>
  `TD_exec (=) (set_rollback (SND frame1)) (set_rollback (SND frame2))`
    by (irule TD_exec_set_rollback_snd >> first_assum ACCEPT_TAC) >>
  Cases_on `b` >> simp[] >>
  td_compose ([TD_exec_unuse_gas, TD_exec_get_current_context,
               TD_exec_set_current_context, TD_exec_push_logs,
               TD_exec_update_gas_refund, TD_exec_repay_state_gas_spill,
               TD_exec_credit_new_account] @ td_primitives)
QED

Theorem TD_exec_handle_create[local]:
  TD_exec (=) (handle_create e) (handle_create e)
Proof
  simp[handle_create_def] >> td_compose td_primitives
QED

Theorem TD_exec_handle_exception[local]:
  TD_exec (=) (handle_exception e) (handle_exception e)
Proof
  simp[handle_exception_def] >>
  td_compose ([TD_exec_pop_and_incorporate_context, TD_exec_inc_pc,
               TD_exec_get_num_contexts] @ td_primitives)
QED

Theorem TD_exec_handle_step[local]:
  TD_exec (=) (handle_step e) (handle_step e)
Proof
  rewrite_tac[handle_step_def] >> IF_CASES_TAC
  >- simp[TD_exec_reraise] >>
  irule TD_exec_handle >>
  simp[TD_exec_handle_create, TD_exec_handle_exception]
QED

Theorem TD_exec_inc_pc_or_jump[local]:
  TD_exec (=) (inc_pc_or_jump op) (inc_pc_or_jump op)
Proof
  simp[inc_pc_or_jump_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_dupn[local]:
  TD_exec (=) step_dupn step_dupn
Proof
  simp[step_dupn_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_swapn[local]:
  TD_exec (=) step_swapn step_swapn
Proof
  simp[step_swapn_def] >> td_compose td_primitives
QED

Theorem TD_exec_step_exchange[local]:
  TD_exec (=) step_exchange step_exchange
Proof
  simp[step_exchange_def] >> td_compose td_primitives
QED

val td_instructions =
  [TD_exec_step_binop, TD_exec_step_monop, TD_exec_step_modop,
   TD_exec_step_context, TD_exec_step_msgParams, TD_exec_step_txParams,
   TD_exec_step_exp, TD_exec_step_keccak256, TD_exec_step_sload,
   TD_exec_step_sstore, TD_exec_step_balance, TD_exec_step_call_data_load,
   TD_exec_step_return_data_copy, TD_exec_step_ext_code_size,
   TD_exec_step_ext_code_copy, TD_exec_step_ext_code_hash,
   TD_exec_step_block_hash, TD_exec_step_blob_hash, TD_exec_step_self_balance,
   TD_exec_step_mload, TD_exec_step_mstore, TD_exec_step_jump,
   TD_exec_step_jumpi, TD_exec_step_push, TD_exec_step_pop,
   TD_exec_step_dup, TD_exec_step_swap, TD_exec_step_log,
   TD_exec_step_return, TD_exec_step_self_destruct,
   TD_exec_step_call, TD_exec_step_create, TD_exec_step_dupn,
   TD_exec_step_swapn, TD_exec_step_exchange];

Theorem TD_exec_step_inst[local]:
  TD_exec (=) (step_inst op) (step_inst op)
Proof
  Cases_on `op` >> rewrite_tac[step_inst_def] >>
  FIRST [td_compose (td_instructions @ td_primitives),
         irule TD_exec_step_copy_to_memory >>
         simp[TD_exec_get_call_data, TD_exec_get_current_code]]
QED

Theorem TD_exec_step[local]:
  TD_exec (=) step step
Proof
  simp[step_def] >> irule TD_exec_handle >> conj_tac
  >- simp[TD_exec_handle_step] >>
  td_compose ([TD_exec_step_inst, TD_exec_inc_pc_or_jump] @ td_primitives)
QED

(* One step of states that differ only in their deletion queues. *)
Theorem step_toDelete:
  erase_toDelete s = erase_toDelete t ==>
  FST (step s) = FST (step t) /\
  erase_toDelete (SND (step s)) = erase_toDelete (SND (step t))
Proof
  mp_tac TD_exec_step >> simp[TD_exec_def]
QED

Theorem TD_call_loop[local]:
  !x z.
    OWHILE (\(r,s). ISL r /\ LENGTH s.contexts >= n) (step o SND) x = SOME z ==>
    !y. FST x = FST y /\ erase_toDelete (SND x) = erase_toDelete (SND y) ==>
    ?w. OWHILE (\(r,s). ISL r /\ LENGTH s.contexts >= n) (step o SND) y = SOME w /\
        FST z = FST w /\ erase_toDelete (SND z) = erase_toDelete (SND w)
Proof
  ho_match_mp_tac OWHILE_simulation >> conj_tac
  >- (qx_gen_tac `a` >> qx_gen_tac `b` >>
      PairCases_on `a` >> PairCases_on `b` >>
      simp[] >> metis_tac[erase_toDelete_contexts]) >>
  qx_gen_tac `a` >> qx_gen_tac `b` >>
  PairCases_on `a` >> PairCases_on `b` >>
  simp[] >> metis_tac[step_toDelete]
QED

(* Proof intuition: step preserves "equal up to erase_toDelete" and returns
   the same result: add_to_delete conses onto both queues, a push saves
   related current rollbacks, a pop restores related saved rollbacks or
   keeps the related current ones, and nothing else reads or writes a
   queue (process_deletions runs only at settlement, outside run_call).
   run_call's loop guard reads only the result and the number of frames,
   which agree, so the two loops run in lockstep. get_rollback and
   pop_context return values that differ in toDelete, so a lemma of the form
   "each op preserves the relation and returns equal values" stops at them;
   push and pop are handled where they're used (proceed_call, step_create,
   pop_and_incorporate_context). *)
Theorem run_call_toDelete:
  erase_toDelete s1 = erase_toDelete s2 ∧ run_call s1 = SOME (r, t1) ⇒
  ∃t2. run_call s2 = SOME (r, t2) ∧ erase_toDelete t2 = erase_toDelete t1
Proof
  strip_tac >>
  `LENGTH s1.contexts = LENGTH s2.contexts` by
    metis_tac[erase_toDelete_contexts] >>
  fs[run_call_def] >> drule TD_call_loop >>
  disch_then (qspec_then `(INL (),s2)` mp_tac) >>
  simp[] >> strip_tac >> PairCases_on `w` >> gvs[] >>
  metis_tac[]
QED

Theorem erase_toDelete_idem:
  erase_toDelete (erase_toDelete s) = erase_toDelete s
Proof
  simp[erase_toDelete_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

(* Well-formedness reads no deletion queue. *)
Theorem wf_state_erase_toDelete:
  wf_state (erase_toDelete s) <=> wf_state s
Proof
  `!x. FST ((\(c:context,rb:rollback_state). (c, rb with toDelete := [])) x) = FST x /\
       (SND ((\(c:context,rb:rollback_state). (c, rb with toDelete := [])) x)).accounts =
       (SND x).accounts` by simp[FORALL_PROD] >>
  simp[erase_toDelete_def, wf_state_def, all_accounts_def, stack_room_ok_def,
       gas_stack_ok_def, outputTo_consistent_stack_def] >>
  Cases_on `s.contexts` >>
  simp[EVERY_MAP, EL_MAP, GSYM MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF,
       MAP_FRONT, ETA_THM] >>
  simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o, MAP_FRONT]
QED
