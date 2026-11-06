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
  vfmTypes vfmState vfmContext vfmExecution

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
  Cases_on `f s` >> Cases_on `g t` >>
  Cases_on `q` >> Cases_on `q'` >>
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
  Cases_on `f s` >> Cases_on `g t` >>
  Cases_on `q` >> Cases_on `q'` >>
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
  Cases_on `s.contexts` >> Cases_on `t.contexts` >>
  gvs[pop_context_def, fail_def, return_def, erase_toDelete_fields] >>
  PairCases_on `h` >> PairCases_on `h'` >>
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
  Cases_on `s.contexts` >> Cases_on `t.contexts` >>
  gvs[get_current_context_def, fail_def, return_def, erase_toDelete_fields] >>
  PairCases_on `h` >> PairCases_on `h'` >> gvs[]
QED

Theorem TD_exec_set_current_context[local]:
  TD_exec (=) (set_current_context c) (set_current_context c)
Proof
  rw[TD_exec_def] >> drule erase_toDelete_contexts >>
  Cases_on `s.contexts` >> Cases_on `t.contexts` >>
  gvs[set_current_context_def, fail_def, return_def, erase_toDelete_fields] >>
  PairCases_on `h` >> PairCases_on `h'` >>
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
         irule TD_exec_bind >> qexists_tac `(=)` >> conj_tac
           >- (rpt gen_tac >> disch_then SUBST1_TAC >>
               BETA_TAC >> td_compose ths) >> td_compose ths,
         CHANGED_TAC (rewrite_tac[ignore_bind_def]) >> td_compose ths] goal;

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
  Cases_on `t.msdomain` >> fs[] >> simp[domain_check_def] 
  >- (IF_CASES_TAC >> simp[fail_def] >>
      fs[TD_exec_def] >> first_x_assum drule >> simp[]) >>
  `TD_exec (=) (ignore_bind (set_domain (Collect (upd d))) cont)
                   (ignore_bind (set_domain (Collect (upd d))) cont)`
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
  cheat
QED
