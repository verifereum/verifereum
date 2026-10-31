(* CALL to arbitrary code, as one SPEC step for the caller: control comes
   back to the caller's frame with the callee's effects confined to the
   rollback state, msdomain, originalAccounts, logs, refunds and return
   data. *)
Theory vfmProgCall
Ancestors
  vfmCallReturn vfmCallBudget vfmProg vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmDecreasesGas vfmRunCall vfmContextLength vfmAccountFrame vfmStaticCalls
  vfmRunWithinFrame vfmSameFrame vfmDomainCollection vfmStepLength
  vfmTypes vfmBuffer vfmHandleStep
  prog set_sep pred_set pair list arithmetic option finite_map combin

(* Structural reachability and final-pop facts live in vfmCallReturnTheory. *)

Theorem delegate_check_collect_frame[local]:
  delegate_check code (Collect dd) rb dc saved dom ⇒
  ∃dd'. dom = Collect dd' ∧ saved.accounts = rb.accounts ∧
    saved.toDelete = rb.toDelete
Proof
  Cases_on `get_delegate code` >>
  simp[delegate_check_def, access_check_def, msdomain_add_def,
       accesses_add_def] >> rpt strip_tac >> simp[]
QED

Theorem call_gas_charged_bound[local]:
  call_gas value gas left mc
    (ac + (if 0 < value then call_value_cost else 0) + nc + dc) = (dg,cg) ⇒
  cg ≤ dg + mc
Proof
  strip_tac >>
  irule call_gas_stipend_le_consumed >>
  goal_assum (drule_at Any) >>
  Cases_on `0 < value` >> simp[call_stipend_def, call_value_cost_def]
QED

Theorem call_operand_drop_room[local]:
  LENGTH ss ≤ stack_limit ∧ 0 < n ∧ n ≤ LENGTH ss ⇒
  LENGTH (DROP n ss) < stack_limit
Proof
  simp[LENGTH_DROP] >> decide_tac
QED

Theorem step_call_success_dispatch[local]:
  s.contexts = (c,cb)::cs ∧ FLOOKUP c.msgParams.parsed c.pc = SOME op ∧
  is_call op ∧ op ≠ Create ∧ op ≠ Create2 ∧
  step_call op s = (INL (),t) ⇒ step s = (INL (),t)
Proof
  strip_tac >>
  `step_inst op = step_call op` by
    (Cases_on `op` >> fs[is_call_def, step_inst_def]) >>
  simp[step_def, get_current_context_def, handle_def, bind_def,
       ignore_bind_def, return_def, inc_pc_or_jump_def]
QED

Theorem call_delegate_resolution[local]:
  delegate_check code s.msdomain s.rollback dc rb' dom' ==>
  (case get_delegate code of
     NONE => return (code,0)
   | SOME a => bind (access_address a)
       (\cost. return ((lookup_account a s.rollback.accounts).code,cost))) s =
  (INL ((case get_delegate code of NONE => code
           | SOME a => (lookup_account a s.rollback.accounts).code),dc),
   s with <|rollback := rb'; msdomain := dom'|>)
Proof
  Cases_on `get_delegate code` >>
  simp[delegate_check_def, access_address_split, bind_def, return_def] >>
  rpt strip_tac >> gvs[execution_state_component_equality]
QED

Theorem call_abort_pair[local]:
  s.contexts = (c,cb)::cs /\ cg <= c.gasUsed /\
  LENGTH c.stack < stack_limit ==>
  let result = (INL (), s with contexts :=
       (c with <|stack := b2w F::c.stack; returnData := [];
                 gasUsed := c.gasUsed-cg; pc := SUC c.pc|>,cb)::cs)
  in abort_call_value cg s = result /\
     ignore_bind (set_return_data []) (abort_unuse cg) s = result
Proof
  simp_tac std_ss [LET_THM] >> strip_tac >> fs[stack_limit_def] >>
  simp[abort_call_value_def, abort_unuse_def, push_stack_def,
       set_return_data_def, unuse_gas_def, inc_pc_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  cong_tac (SOME 4) >> simp[context_component_equality]
QED

Theorem call_charge_new_account_pair[local]:
  s.contexts = (c,cb)::cs /\
  stateCost = (if charged then new_account_state_gas else 0) /\
  stateCost <= c.stateGasLeft ==>
  charge_new_account charged s =
    (INL (), s with contexts :=
      (c with stateGasLeft := c.stateGasLeft - stateCost,cb)::cs)
Proof
  Cases_on `charged` >>
  simp[charge_new_account_def, charge_state_gas_def,
       get_current_context_def, set_current_context_def,
       bind_def, return_def] >> rpt strip_tac >>
  gvs[execution_state_component_equality]
QED

Theorem call_credit_abort_pair[local]:
  s.contexts = (c,cb)::cs /\
  stateCost = (if charged then new_account_state_gas else 0) /\
  creditBack = MIN stateCost c.stateGasSpilled /\
  cg <= c.gasUsed - creditBack /\ LENGTH c.stack < stack_limit ==>
  let credited = c with <|
        gasUsed := c.gasUsed - creditBack;
        stateGasSpilled := c.stateGasSpilled - creditBack;
        stateGasLeft := c.stateGasLeft + (stateCost - creditBack) |>;
      result = (INL (), s with contexts :=
        (credited with <|stack := b2w F::c.stack; returnData := [];
          gasUsed := credited.gasUsed - cg; pc := SUC c.pc|>,cb)::cs)
  in ignore_bind (credit_new_account charged) (abort_call_value cg) s = result /\
     ignore_bind (set_return_data [])
       (ignore_bind (credit_new_account charged) (abort_unuse cg)) s = result
Proof
  Cases_on `charged` >>
  simp[LET_THM, credit_new_account_def, credit_state_gas_refund_def,
       abort_call_value_def, abort_unuse_def, push_stack_def,
       set_return_data_def, unuse_gas_def, inc_pc_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  rpt strip_tac >> gvs[stack_limit_def] >>
  cong_tac (SOME 4) >> simp[context_component_equality]
QED

Theorem call_entry_failure_normalize[local]:
  prepared.contexts = (caller,cb)::cs /\
  stateCost = (if charged then new_account_state_gas else 0) /\
  creditBack = MIN stateCost caller.stateGasSpilled /\
  cg <= caller.gasUsed - creditBack /\
  LENGTH caller.stack < stack_limit ==>
  (if balanceFail then
     ignore_bind (credit_new_account charged) (abort_call_value cg) prepared
   else ignore_bind (set_return_data [])
     (if depthFail then ignore_bind (credit_new_account charged) (abort_unuse cg)
      else proceed) prepared) =
  (if balanceFail \/ depthFail then
     ignore_bind (credit_new_account charged) (abort_call_value cg) prepared
   else ignore_bind (set_return_data []) proceed prepared)
Proof
  strip_tac >> drule_all call_credit_abort_pair >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  Cases_on `balanceFail` >> Cases_on `depthFail` >> simp[]
QED

Theorem proceed_call_pair[local]:
  s.contexts = (c,cb)::cs /\ ~fIN addr precompile_addresses ==>
  proceed_call op sender addr value ao az code cg output s =
  let callee = if op = CallCode \/ op = DelegateCall then sender else addr;
      tx = <|from := if op = DelegateCall then c.msgParams.caller else sender;
             to := SOME callee;
             value := if op = DelegateCall then c.msgParams.value else value;
             gasLimit := cg; data := buffer_take ao az c.memory;
             nonce := 0; gasPrice := 0; accessList := [];
             blobVersionedHashes := []; maxFeePerGas := NONE;
             maxFeePerBlobGas := NONE; authorizationList := []|>
  in (INL (), s with <|
    contexts := (initial_context callee code
      (op = StaticCall \/ c.msgParams.static) output
      (op = Call /\ 0 < value /\
       account_empty (lookup_account addr s.rollback.accounts)) c.stateGasLeft tx
        with logs := transfer_log sender callee value,s.rollback)::
      (c with stateGasLeft := 0,cb)::cs;
    rollback := s.rollback with accounts updated_by
      (if op <> CallCode /\ 0 < value then transfer_value sender addr value else I)
  |>)
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value` >>
  simp[proceed_call_def, get_accounts_def, drain_state_gas_reservoir_def,
       set_current_context_def, get_rollback_def, read_memory_def,
       get_current_context_def, update_accounts_def,
       get_caller_def, get_value_def, get_static_def, push_context_def,
       bind_def, ignore_bind_def, return_def] >>
  simp[execution_state_component_equality, rollback_state_component_equality]
QED


(* Scoped safety and exact finite memory returns are supplied by
   vfmCallReturnTheory; unrestricted nonempty-frame safety is invalid. *)

(* Protected persistent footprint and fixed-limit descendant invariant. *)
Definition call_footprint_def:
  call_footprint A D oa s <=>
    s.rollback.accounts = A /\ s.rollback.toDelete = D /\
    s.originalAccounts = oa
End

Definition call_stipend_prefix_def:
  call_stipend_prefix n A D oa s <=>
    2 <= n /\ n <= LENGTH s.contexts /\ call_footprint A D oa s /\
    EVERY (\(c,rb). c.msgParams.gasLimit <= call_stipend /\
                   (!a. c.msgParams.outputTo <> Code a))
      (TAKE (LENGTH s.contexts - n + 1) s.contexts) /\
    EVERY (\(c,rb). rb.accounts = A /\ rb.toDelete = D)
      (TAKE (LENGTH s.contexts - n) s.contexts)
End

Theorem call_footprint_contexts[local]:
  call_footprint A D oa (s with contexts := cs) <=>
  call_footprint A D oa s
Proof
  simp[call_footprint_def]
QED

Theorem call_stipend_prefix_bookkeeping[local]:
  call_stipend_prefix n A D oa
    (s with <| msdomain := dom; rollback := accesses_add addr s.rollback |>) <=>
  call_stipend_prefix n A D oa s
Proof
  simp[call_stipend_prefix_def, call_footprint_def, accesses_add_def]
QED

Theorem cp_preserves_stipend_prefix[local]:
  cp m /\ call_stipend_prefix n A D oa s /\ m s = (r,t) ==>
  call_stipend_prefix n A D oa t
Proof
  strip_tac >>
  `s.contexts <> []` by
    (gvs[call_stipend_prefix_def] >> strip_tac >> gvs[]) >>
  drule (iffLR cp_def) >>
  disch_then (qspecl_then [`s`, `r`, `t`] mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  gvs[call_stipend_prefix_def, call_footprint_def] >>
  Cases_on `SUC (LENGTH t') - n` >> gvs[]
QED

Theorem call_stipend_prefix_nonmutating_inst[local]:
  op <> SStore /\ op <> TStore /\ (!k. op <> Log k) /\
  op <> SelfDestruct /\ op <> Create /\ op <> Create2 /\
  op <> Call /\ op <> CallCode /\ op <> DelegateCall /\ op <> StaticCall /\
  call_stipend_prefix n A D oa s /\ step_inst op s = (r,t) ==>
  call_stipend_prefix n A D oa t
Proof
  strip_tac >> irule (INST_TYPE [alpha |-> ``:unit``] cp_preserves_stipend_prefix) >>
  qexistsl_tac [`step_inst op`, `r`, `s`] >> simp[]
QED

Theorem sstore_stipend_sentry[local]:
  s.contexts <> [] /\
  (FST (HD s.contexts)).msgParams.gasLimit <= call_stipend ==>
  step_sstore_gas_consumption addr key value s = (INR (SOME OutOfGas),s)
Proof
  strip_tac >>
  `(FST (HD s.contexts)).msgParams.gasLimit -
    (FST (HD s.contexts)).gasUsed <= call_stipend` by decide_tac >>
  simp[step_sstore_gas_consumption_def, get_gas_left_def,
       get_current_context_def, bind_def, ignore_bind_def,
       return_def, assert_def, fail_def]
QED

Theorem call_stipend_prefix_head[local]:
  call_stipend_prefix n A D oa s ==>
  s.contexts <> [] /\
  (FST (HD s.contexts)).msgParams.gasLimit <= call_stipend /\
  (!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a)
Proof
  simp[call_stipend_prefix_def] >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
QED

Theorem call_stipend_prefix_sstore[local]:
  call_stipend_prefix n A D oa s /\ step_sstore F s = (r,t) ==>
  call_stipend_prefix n A D oa t
Proof
  strip_tac >>
  `cp (pop_stack 2)` by simp[] >>
  Cases_on `pop_stack 2 s` >>
  `call_stipend_prefix n A D oa r'` by
    (drule_all cp_preserves_stipend_prefix >> simp[]) >>
  qpat_x_assum `step_sstore F s = _` mp_tac >>
  simp[step_sstore_def, bind_def, ignore_bind_def] >>
  Cases_on `q` >> simp[]
  >- (drule call_stipend_prefix_head >> strip_tac >>
      simp[get_callee_def, get_current_context_def, bind_def, return_def] >>
      simp[sstore_stipend_sentry] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

Theorem consume_gas_stipend_exceeded[local]:
  s.contexts <> [] /\
  (FST (HD s.contexts)).msgParams.gasLimit <= call_stipend /\
  call_stipend < k ==>
  consume_gas k s = (INR (SOME OutOfGas),s)
Proof
  strip_tac >>
  `~((FST (HD s.contexts)).gasUsed + k <=
     (FST (HD s.contexts)).msgParams.gasLimit)` by decide_tac >>
  simp[consume_gas_def, get_current_context_def, bind_def,
       ignore_bind_def, return_def, assert_def, fail_def]
QED

Theorem call_stipend_prefix_cp_bind[local]:
  cp m /\
  (!x s r t. call_stipend_prefix n A D oa s /\ f x s = (r,t) ==>
      call_stipend_prefix n A D oa t) ==>
  !s r t. call_stipend_prefix n A D oa s /\ bind m f s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind m f s = _` mp_tac >> simp[bind_def] >>
  Cases_on `m s` >> Cases_on `q` >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[cp_preserves_stipend_prefix]
QED

Theorem call_stipend_prefix_charge_cutoff[local]:
  call_stipend < cost ==>
  !s r t. call_stipend_prefix n A D oa s /\
    bind (consume_gas cost) suffix s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rpt strip_tac >> drule call_stipend_prefix_head >> strip_tac >>
  `consume_gas cost s = (INR (SOME OutOfGas),s)` by
    (irule consume_gas_stipend_exceeded >> simp[]) >>
  gvs[bind_def]
QED

Theorem call_stipend_prefix_create[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_create two s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rewrite_tac[step_create_def, ignore_bind_def] >> simp[] >>
  ntac 2 (ho_match_mp_tac call_stipend_prefix_cp_bind >>
    conj_tac >- simp[] >> gen_tac >> simp[]) >>
  ho_match_mp_tac call_stipend_prefix_charge_cutoff >>
  Cases_on `two` >> simp[call_stipend_def]
QED

Theorem call_stipend_prefix_self_destruct[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_self_destruct s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rewrite_tac[step_self_destruct_def, ignore_bind_def] >> simp[] >>
  ntac 5 (ho_match_mp_tac call_stipend_prefix_cp_bind >>
    conj_tac >- simp[] >> gen_tac >> simp[]) >>
  ho_match_mp_tac call_stipend_prefix_charge_cutoff >>
  simp[call_stipend_def] >> decide_tac
QED

Theorem call_stipend_prefix_head_update[local]:
  s.contexts = (c,rb)::cs /\ ctx.msgParams = c.msgParams ==>
  (call_stipend_prefix n A D oa
    (s with contexts := (ctx,rb)::cs) <=> call_stipend_prefix n A D oa s)
Proof
  strip_tac >> simp[call_stipend_prefix_def, call_footprint_def] >>
  Cases_on `SUC (LENGTH cs) - n` >> gvs[]
QED

Theorem call_stipend_prefix_write_transient[local]:
  !s r t. call_stipend_prefix n A D oa s /\
    write_transient_storage addr key value s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  simp[write_transient_storage_def, get_tStorage_def, set_tStorage_def,
       bind_def, return_def, call_stipend_prefix_def, call_footprint_def] >>
  rpt strip_tac >>
  `LENGTH s.contexts + 1 - n = LENGTH s.contexts - n + 1` by decide_tac >>
  pop_assum (fn th => pure_once_rewrite_tac [th]) >> first_assum ACCEPT_TAC
QED

Theorem call_stipend_prefix_tstore[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_sstore T s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rewrite_tac[step_sstore_def, ignore_bind_def] >> simp[] >>
  ntac 4 (ho_match_mp_tac call_stipend_prefix_cp_bind >>
    conj_tac >- simp[] >> gen_tac >> simp[]) >>
  rpt strip_tac >> drule_all call_stipend_prefix_write_transient >> simp[]
QED

Theorem call_stipend_prefix_push_logs[local]:
  !s r t. call_stipend_prefix n A D oa s /\ push_logs ls s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rpt strip_tac >>
  `s.contexts <> []` by metis_tac[call_stipend_prefix_head] >>
  qpat_x_assum `push_logs ls s = _` mp_tac >>
  simp[push_logs_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def] >> strip_tac >> gvs[] >>
  irule (iffRL call_stipend_prefix_head_update) >>
  simp[] >> qexists_tac `FST (HD s.contexts)` >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
QED

Theorem call_stipend_prefix_log[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_log k s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rewrite_tac[step_log_def, ignore_bind_def] >> simp[] >>
  ntac 7 (ho_match_mp_tac call_stipend_prefix_cp_bind >>
    conj_tac >- simp[] >> gen_tac >> simp[]) >>
  rpt strip_tac >> drule_all call_stipend_prefix_push_logs >> simp[]
QED

Theorem call_stipend_prefix_noncall_dispatch[local]:
  op <> Call /\ op <> CallCode /\ op <> DelegateCall /\ op <> StaticCall /\
  call_stipend_prefix n A D oa s /\ step_inst op s = (r,t) ==>
  call_stipend_prefix n A D oa t
Proof
  strip_tac >>
  Cases_on `op = SStore`
  >- (gvs[step_inst_def] >> drule_all call_stipend_prefix_sstore >> simp[]) >>
  Cases_on `op = TStore`
  >- (gvs[step_inst_def] >> drule_all call_stipend_prefix_tstore >> simp[]) >>
  Cases_on `op = SelfDestruct`
  >- (gvs[step_inst_def] >> drule_all call_stipend_prefix_self_destruct >> simp[]) >>
  Cases_on `op = Create`
  >- (gvs[step_inst_def] >> drule_all call_stipend_prefix_create >> simp[]) >>
  Cases_on `op = Create2`
  >- (gvs[step_inst_def] >> drule_all call_stipend_prefix_create >> simp[]) >>
  Cases_on `?k. op = Log k`
  >- (gvs[step_inst_def] >> metis_tac[call_stipend_prefix_log]) >>
  irule call_stipend_prefix_nonmutating_inst >>
  qexistsl_tac [`op`, `r`, `s`] >> simp[] >> metis_tac[]
QED

Theorem call_gas_stipend_budget[local]:
  L <= call_stipend /\ call_gas v gas L mc oc = (dg,cg) /\
  sc + dg + mc <= L /\ (0 < v ==> call_value_cost <= oc) ==>
  v = 0 /\ cg <= L
Proof
  simp[call_gas_def, LET_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs(), call_stipend_def, call_value_cost_def] >>
  decide_tac
QED

Theorem call_stipend_prefix_root[local]:
  call_footprint A D oa s /\ s.contexts = (c,rb)::cs /\
  1 <= LENGTH cs /\ c.msgParams.gasLimit <= call_stipend /\
  (!a. c.msgParams.outputTo <> Code a) ==>
  call_stipend_prefix (LENGTH s.contexts) A D oa s
Proof
  simp[call_stipend_prefix_def]
QED

Theorem call_stipend_prefix_push[local]:
  call_stipend_prefix n A D oa s /\
  c.msgParams.gasLimit <= call_stipend /\
  (!a. c.msgParams.outputTo <> Code a) ==>
  call_stipend_prefix n A D oa
    (s with contexts := (c,s.rollback)::s.contexts)
Proof
  simp[call_stipend_prefix_def, call_footprint_def] >> strip_tac >>
  `SUC (LENGTH s.contexts) - n = SUC (LENGTH s.contexts - n)` by decide_tac >>
  simp[ADD1] >>
  `LENGTH s.contexts + 1 - n = LENGTH s.contexts - n + 1` by decide_tac >>
  pop_assum (fn th => pure_once_rewrite_tac [th]) >>
  first_assum ACCEPT_TAC
QED

Theorem call_stipend_prefix_precompiles[local]:
  call_stipend_prefix n A D oa s /\ dispatch_precompiles addr s = (r,t) ==>
  call_stipend_prefix n A D oa t
Proof
  strip_tac >> irule cp_preserves_stipend_prefix >>
  qexistsl_tac [`dispatch_precompiles addr`, `r`, `s`] >> simp[]
QED

Theorem call_stipend_prefix_proceed_zero[local]:
  cg <= call_stipend /\ (!a. output <> Code a) ==>
  !s r t. call_stipend_prefix n A D oa s /\
    proceed_call op sender addr 0 ao az code cg output s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `s.contexts <> []` by metis_tac[call_stipend_prefix_head] >>
  qpat_x_assum `proceed_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[proceed_call_def, get_rollback_def, read_memory_def, get_accounts_def,
       drain_state_gas_reservoir_def, set_current_context_def,
       get_current_context_def, get_caller_def, get_value_def, get_static_def,
       push_context_def, bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `(if _ then _ else _) pushed` >>
  `call_stipend_prefix n A D oa pushed` by
    (simp[Abbr `pushed`] >>
     qmatch_goalsub_abbrev_tac `CONS (child,s.rollback)` >>
     `s with contexts updated_by CONS (child,s.rollback) =
      s with contexts := (child,s.rollback)::s.contexts` by
       simp[execution_state_component_equality] >>
     pop_assum (fn th => rewrite_tac[th]) >>
     Cases_on `s.contexts` >- fs[] >> PairCases_on `h` >>
     gvs[call_stipend_prefix_def, call_footprint_def] >>
     `SUC (SUC (LENGTH t)) - n = SUC (SUC (LENGTH t) - n)` by decide_tac >>
     `SUC (SUC (LENGTH t)) - (n + 1) = SUC (LENGTH t) - n` by decide_tac >>
     simp[Abbr `child`, initial_context_def, initial_msg_params_def] >>
     Cases_on `SUC (LENGTH t) - n` >> gvs[]) >>
  IF_CASES_TAC >> simp[return_def] >> strip_tac >> gvs[] >>
  drule_all call_stipend_prefix_precompiles >> simp[]
QED

Theorem consume_gas_affordable[local]:
  s.contexts <> [] /\ consume_gas cost s = (INL (),t) ==>
  cost <= (FST (HD s.contexts)).msgParams.gasLimit -
          (FST (HD s.contexts)).gasUsed
Proof
  simp[consume_gas_def, get_current_context_def, bind_def,
       ignore_bind_def, return_def, assert_def, fail_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem call_stipend_prefix_call_charge[local]:
  (0 < (value:num) ==> call_value_cost <= cost) /\
  (!s r t. value = 0 /\ call_stipend_prefix n A D oa s /\
    suffix s = (r,t) ==> call_stipend_prefix n A D oa t) ==>
  !s r t. call_stipend_prefix n A D oa s /\
    bind (consume_gas cost) (\u. suffix) s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule call_stipend_prefix_head >> strip_tac >>
  qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[bind_def] >> Cases_on `consume_gas cost s` >>
  rename1 `consume_gas cost s = (res,mid)` >>
  `call_stipend_prefix n A D oa mid` by
    (irule (INST_TYPE [alpha |-> ``:unit``] cp_preserves_stipend_prefix) >>
     qexistsl_tac [`consume_gas cost`, `res`, `s`] >> simp[]) >>
  Cases_on `res` >> simp[]
  >- (Cases_on `x` >> drule_all consume_gas_affordable >> strip_tac >>
      `value = 0` by
        (gvs[call_stipend_def, call_value_cost_def] >> decide_tac) >>
      strip_tac >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

Theorem call_stipend_prefix_zero_gas[local]:
  (!dg cg s r t. cg <= call_stipend /\ call_stipend_prefix n A D oa s /\
    suffix dg cg s = (r,t) ==> call_stipend_prefix n A D oa t) ==>
  !s r t. call_stipend_prefix n A D oa s /\
    bind get_gas_left (\left.
      let (dg,cg) = call_gas 0 gas left 0 0 in suffix dg cg) s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule call_stipend_prefix_head >> strip_tac >>
  qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[get_gas_left_def, get_current_context_def, bind_def, return_def] >>
  Cases_on `call_gas 0 gas
    ((FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed) 0 0` >>
  rename1 `call_gas 0 gas _ 0 0 = (dg,cg)` >> simp[] >>
  `cg <= call_stipend` by
    (qpat_x_assum `call_gas _ _ _ _ _ = _` mp_tac >>
     simp[call_gas_def, LET_THM] >> strip_tac >> gvs[] >> decide_tac) >>
  metis_tac[]
QED

Theorem call_stipend_prefix_call[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_call op s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rewrite_tac[step_call_def, ignore_bind_def] >> simp[] >>
  ho_match_mp_tac call_stipend_prefix_cp_bind >>
  conj_tac >- simp[] >> gen_tac >> simp[] >> pairarg_tac >> simp[] >>
  ntac 3 (ho_match_mp_tac call_stipend_prefix_cp_bind >>
    conj_tac >- simp[] >> gen_tac >> simp[]) >>
  pop_assum kall_tac >>
  ho_match_mp_tac call_stipend_prefix_cp_bind >>
  conj_tac >- (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  qx_gen_tac `code_cost` >> PairCases_on `code_cost` >> simp[] >>
  qmatch_goalsub_abbrev_tac `charge_new_account (op = Call /\ 0 < v /\ _)` >>
  ho_match_mp_tac (Q.INST [`value` |-> `v`] call_stipend_prefix_call_charge) >>
  conj_tac >- (simp[Abbr `v`] >> IF_CASES_TAC >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `_ s = (r,t)` mp_tac >>
  qpat_x_assum `call_stipend_prefix n A D oa s` mp_tac >>
  qid_spec_tac `t` >> qid_spec_tac `r` >> qid_spec_tac `s` >>
  simp[AND_IMP_INTRO, charge_new_account_def, credit_new_account_def] >>
  ho_match_mp_tac call_stipend_prefix_cp_bind >>
  conj_tac >- simp[] >> gen_tac >> simp[] >>
  ho_match_mp_tac (SRULE [LET_THM] call_stipend_prefix_zero_gas) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ s = (r,t)` mp_tac >>
  qpat_x_assum `call_stipend_prefix n A D oa s` mp_tac >>
  qid_spec_tac `t` >> qid_spec_tac `r` >> qid_spec_tac `s` >>
  simp[AND_IMP_INTRO] >>
  ntac 4 (ho_match_mp_tac call_stipend_prefix_cp_bind >>
    conj_tac >- simp[] >> gen_tac >> simp[]) >>
  IF_CASES_TAC
  >- (rpt strip_tac >>
      irule (INST_TYPE [alpha |-> ``:unit``] cp_preserves_stipend_prefix) >>
      qexistsl_tac [`abort_unuse stipend`, `r`, `s`] >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `proceed_call _ _ _ _ _ _ _ _ _ _ = _`)
    call_stipend_prefix_proceed_zero >> simp[]
QED

Theorem handle_exception_memory_observation[local]:
  s.contexts = (c,saved)::(caller,cb)::rest /\
  c.msgParams.outputTo = Memory mr /\
  handle_exception e s = (INL (),t) ==>
  ?caller'. t = s with <|
    contexts := (caller',cb)::rest;
    rollback := if e = NONE then s.rollback else saved |> /\
    caller'.msgParams = caller.msgParams
Proof
  strip_tac >> Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  Cases_on `c.msgParams.newAccountCharged` >>
  gvs[handle_exception_def, pop_and_incorporate_context_def,
      LET_THM, restore_state_gas_def, forfeit_remaining_gas_def,
      repay_state_gas_spill_def, credit_new_account_def,
      credit_state_gas_refund_def, absorb_state_gas_def,
      repay_state_gas_spill_context_def,
      get_gas_left_def, get_num_contexts_def, get_output_to_def,
      get_return_data_def, get_current_context_def, pop_context_def,
      consume_gas_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
      set_rollback_def, set_current_context_def, set_return_data_def,
      inc_pc_def, push_stack_def, write_memory_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      combinTheory.o_DEF, combinTheory.C_DEF, AllCaseEqs()] >>
  simp[execution_state_component_equality] >> metis_tac[]
QED

Theorem call_stipend_prefix_pop[local]:
  call_stipend_prefix n A D oa s /\
  s.contexts = (callee,saved)::(caller,callerSaved)::rest /\
  caller'.msgParams = caller.msgParams /\
  t = s with <| contexts := (caller',callerSaved)::rest;
    rollback := if success then s.rollback else saved |> ==>
  t.originalAccounts = oa /\
  (n <= LENGTH t.contexts ==> call_stipend_prefix n A D oa t)
Proof
  simp[call_stipend_prefix_def, call_footprint_def] >> strip_tac >>
  strip_tac >> gvs[] >>
  `SUC (SUC (LENGTH rest)) - n = SUC (SUC (LENGTH rest) - n)` by decide_tac >>
  `SUC (SUC (LENGTH rest)) - n + 1 = SUC (SUC (LENGTH rest) - n + 1)` by decide_tac >>
  gvs[] >>
  `SUC (SUC (LENGTH rest)) - (n + 1) = SUC (LENGTH rest) - n` by decide_tac >>
  gvs[] >> Cases_on `SUC (LENGTH rest) - n` >> gvs[] >>
  Cases_on `success` >> simp[]
QED

Theorem call_stipend_prefix_handle_step[local]:
  EVERY (wf_context o FST) s.contexts /\ stack_room_ok s /\ gas_stack_ok s /\
  call_stipend_prefix n A D oa s /\ handle_step e s = (INL (),t) ==>
  t.originalAccounts = oa /\
  (n <= LENGTH t.contexts ==> call_stipend_prefix n A D oa t)
Proof
  strip_tac >>
  drule call_stipend_prefix_head >> strip_tac >>
  `s.contexts <> []` by simp[] >>
  qpat_x_assum `handle_step e s = _` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[call_stipend_prefix_def, call_footprint_def]) >>
  simp[handle_def] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises) >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[reraise_def] >>
  `2 <= LENGTH s.contexts` by
    (fs[call_stipend_prefix_def] >> decide_tac) >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  PairCases_on `h` >> PairCases_on `h'` >> gvs[] >>
  Cases_on `h0.msgParams.outputTo` >> gvs[] >>
  strip_tac >>
  drule_all handle_exception_memory_observation >> strip_tac >>
  irule call_stipend_prefix_pop >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `e = NONE` >> simp[]
QED

Theorem call_stipend_prefix_step_inst[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_inst op s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  Cases_on `op = Call` >- (gvs[step_inst_def] >> metis_tac[call_stipend_prefix_call]) >>
  Cases_on `op = CallCode` >- (gvs[step_inst_def] >> metis_tac[call_stipend_prefix_call]) >>
  Cases_on `op = DelegateCall` >- (gvs[step_inst_def] >> metis_tac[call_stipend_prefix_call]) >>
  Cases_on `op = StaticCall` >- (gvs[step_inst_def] >> metis_tac[call_stipend_prefix_call]) >>
  metis_tac[call_stipend_prefix_noncall_dispatch]
QED

Theorem step_inner_preserves_stipend_prefix[local]:
  !s r t. call_stipend_prefix n A D oa s /\ step_inner s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  rewrite_tac[step_inner_def, ignore_bind_def] >>
  ho_match_mp_tac call_stipend_prefix_cp_bind >>
  conj_tac >- simp[] >> gen_tac >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
  >- (IF_CASES_TAC >> simp[] >> metis_tac[call_stipend_prefix_step_inst]) >>
  rpt strip_tac >>
  qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[bind_def] >> Cases_on `step_inst x s` >>
  rename1 `step_inst x s = (rr,mid)` >>
  `call_stipend_prefix n A D oa mid` by
    metis_tac[call_stipend_prefix_step_inst] >>
  Cases_on `rr` >> simp[] >> strip_tac >> gvs[] >>
  irule (INST_TYPE [alpha |-> ``:unit``] cp_preserves_stipend_prefix) >>
  qexistsl_tac [`inc_pc_or_jump x`, `r`, `mid`] >> simp[]
QED

Theorem step_preserves_stipend_prefix[local]:
  wf_state s /\ call_stipend_prefix n A D oa s /\ step s = (INL (),t) ==>
  wf_state t /\ t.originalAccounts = oa /\
  (n <= LENGTH t.contexts ==> call_stipend_prefix n A D oa t)
Proof
  strip_tac >>
  `wf_state t` by (drule step_preserves_wf_state >> simp[]) >> simp[] >>
  qpat_x_assum `step s = _` mp_tac >>
  rewrite_tac[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> rename1 `step_inner s = (rr,mid)` >>
  `call_stipend_prefix n A D oa mid` by
    metis_tac[step_inner_preserves_stipend_prefix] >>
  Cases_on `rr` >> simp[]
  >- (strip_tac >> gvs[call_stipend_prefix_def, call_footprint_def]) >>
  `stack_room_ok mid /\ gas_stack_ok mid` by
    metis_tac[step_inner_preserves_stack_room_gas_ok] >>
  `EVERY (wf_context o FST) mid.contexts` by
    (mp_tac decreases_gas_cred_step_inner >>
     simp[decreases_gas_cred_def] >>
     disch_then (qspec_then `s` mp_tac) >> simp[] >>
     fs[wf_state_def]) >>
  strip_tac >> drule_all call_stipend_prefix_handle_step >> simp[]
QED

Theorem run_call_reaches_stipend_prefix[local]:
  wf_state es /\ call_stipend_prefix (LENGTH es.contexts) A D oa es /\
  run_call_reaches es t ==>
  t.originalAccounts = oa /\
  (LENGTH es.contexts <= LENGTH t.contexts ==>
    call_stipend_prefix (LENGTH es.contexts) A D oa t)
Proof
  strip_tac >>
  `(\s. wf_state s /\ s.originalAccounts = oa /\
    (LENGTH es.contexts <= LENGTH s.contexts ==>
      call_stipend_prefix (LENGTH es.contexts) A D oa s)) t` suffices_by simp[] >>
  irule run_call_reaches_inv >> qexists_tac `es` >> simp[] >>
  conj_tac >- fs[call_stipend_prefix_def, call_footprint_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all step_preserves_stipend_prefix >> simp[]
QED

Theorem run_call_stipend_originalAccounts[local]:
  wf_state es /\ es.contexts = (callee,saved)::cs /\ 1 <= LENGTH cs /\
  callee.msgParams.gasLimit <= call_stipend /\
  (!a. callee.msgParams.outputTo <> Code a) /\
  run_call es = SOME (INL (),t) ==>
  t.originalAccounts = es.originalAccounts
Proof
  strip_tac >>
  `call_stipend_prefix (LENGTH es.contexts) es.rollback.accounts
    es.rollback.toDelete es.originalAccounts es` by
    (irule call_stipend_prefix_root >> simp[call_footprint_def] >> metis_tac[]) >>
  drule call_return_last_step >> strip_tac >>
  `call_stipend_prefix (LENGTH es.contexts) es.rollback.accounts
    es.rollback.toDelete es.originalAccounts before` by
    metis_tac[run_call_reaches_stipend_prefix] >>
  `wf_state before` by metis_tac[run_call_reaches_wf_state] >>
  drule_all step_preserves_stipend_prefix >> simp[]
QED

Theorem handle_step_noncode_rollback[local]:
  EVERY (wf_context o FST) s.contexts ∧ stack_room_ok s ∧ gas_stack_ok s ∧
  2 ≤ LENGTH s.contexts ∧
  (∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a) ∧
  handle_step e s = (INL (),t) ⇒
  t.rollback = if e = NONE then s.rollback else SND (HD s.contexts)
Proof
  strip_tac >>
  `s.contexts ≠ []` by (Cases_on `s.contexts` >> fs[]) >>
  drule_all call_return_handle_step_noncode >>
  Cases_on `s.contexts` >- fs[] >>
  rename1 `s.contexts = calleePair::cs` >>
  Cases_on `cs` >- fs[] >>
  PairCases_on `calleePair` >> PairCases_on `h` >>
  gvs[] >> Cases_on `calleePair0.msgParams.outputTo` >> gvs[] >>
  strip_tac >> drule_all handle_exception_memory_observation >>
  strip_tac >> gvs[]
QED

Theorem run_call_stipend_footprint:
  wf_state es ∧ es.contexts = (callee,saved)::cs ∧ 1 ≤ LENGTH cs ∧
  callee.msgParams.gasLimit ≤ call_stipend ∧
  (∀a. callee.msgParams.outputTo ≠ Code a) ∧
  run_call es = SOME (INL (),t) ⇒
  ∃n before err mid.
    FUNPOW (step o SND) n (INL (),es) = (INL (),before) ∧
    run_call_reaches es before ∧ wf_state before ∧
    LENGTH before.contexts = LENGTH es.contexts ∧
    TL before.contexts = TL es.contexts ∧ t.txParams = es.txParams ∧
    step before = (INL (),t) ∧ step_inner before = (INR err,mid) ∧
    handle_step err mid = (INL (),t) ∧
    t.originalAccounts = es.originalAccounts ∧
    (if err = NONE then
       t.rollback.accounts = es.rollback.accounts ∧
       t.rollback.toDelete = es.rollback.toDelete
     else t.rollback = saved)
Proof
  strip_tac >>
  `t.originalAccounts = es.originalAccounts` by
    (irule run_call_stipend_originalAccounts >> metis_tac[]) >>
  drule_all call_return_last_pop >> strip_tac >>
  qexistsl_tac [`n`,`before`,`err`,`mid`] >> simp[] >>
  `2 ≤ LENGTH es.contexts` by simp[] >>
  `SND (HD before.contexts) = saved ∧
   (FST (HD before.contexts)).msgParams = callee.msgParams` by
    (drule_all call_return_root_metadata >> simp[]) >>
  `call_stipend_prefix (LENGTH es.contexts) es.rollback.accounts
    es.rollback.toDelete es.originalAccounts es` by
    (irule call_stipend_prefix_root >> simp[call_footprint_def] >> metis_tac[]) >>
  `call_stipend_prefix (LENGTH es.contexts) es.rollback.accounts
    es.rollback.toDelete es.originalAccounts before` by
    (drule_all run_call_reaches_stipend_prefix >> simp[]) >>
  `call_stipend_prefix (LENGTH es.contexts) es.rollback.accounts
    es.rollback.toDelete es.originalAccounts mid` by
    metis_tac[step_inner_preserves_stipend_prefix] >>
  suspend "final_footprint"
QED

Resume run_call_stipend_footprint[final_footprint]:
  `LENGTH t.contexts + 1 = LENGTH es.contexts` by
    metis_tac[run_call_inl_length] >>
  `LENGTH t.contexts + 1 = LENGTH before.contexts` by decide_tac >>
  drule_all call_return_inner_final_frame >> strip_tac >>
  `SND (HD mid.contexts) = saved ∧
   (FST (HD mid.contexts)).msgParams = callee.msgParams` by
    fs[same_frame_rel_def] >>
  `2 ≤ LENGTH mid.contexts` by fs[same_frame_rel_def] >>
  `(∀a. (FST (HD mid.contexts)).msgParams.outputTo ≠ Code a)` by simp[] >>
  drule_all handle_step_noncode_rollback >>
  Cases_on `err = NONE` >> simp[] >>
  strip_tac >> simp[] >>
  fs[call_stipend_prefix_def, call_footprint_def]
QED

Finalise run_call_stipend_footprint


Definition call_abort_context_def:
  call_abort_context charged cg caller =
    let cost = if charged then new_account_state_gas else 0;
        paid = MIN cost caller.stateGasSpilled
    in caller with <|stack := b2w F::caller.stack; returnData := [];
         pc := SUC caller.pc; gasUsed := caller.gasUsed - paid - cg;
         stateGasLeft := caller.stateGasLeft + (cost - paid);
         stateGasSpilled := caller.stateGasSpilled - paid|>
End

Theorem call_abort_context_pair[local]:
  prepared.contexts = (caller,cb)::cs /\
  stateCost = (if charged then new_account_state_gas else 0) /\
  creditBack = MIN stateCost caller.stateGasSpilled /\
  cg <= caller.gasUsed - creditBack /\ LENGTH caller.stack < stack_limit ==>
  ignore_bind (credit_new_account charged) (abort_call_value cg) prepared =
    (INL (),prepared with contexts := (call_abort_context charged cg caller,cb)::cs)
Proof
  strip_tac >> drule_all call_credit_abort_pair >>
  simp[LET_THM, call_abort_context_def]
QED

Theorem call_returns_summary[local]:
  wf_state s /\ s.contexts = (c,cb)::cs /\
  FLOOKUP c.msgParams.parsed c.pc = SOME op /\
  is_call op /\ op <> Create /\ op <> Create2 /\
  prepared = s with <|contexts := (caller,cb)::cs;
                         rollback := saved; msdomain := Collect dd|> /\
  charged = (op = Call /\ 0 < value /\
    account_empty (lookup_account addr saved.accounts)) /\
  stateCost = (if charged then new_account_state_gas else 0) /\
  creditBack = MIN stateCost caller.stateGasSpilled /\
  cg <= caller.gasUsed - creditBack /\ LENGTH caller.stack < stack_limit /\
  ~fIN addr precompile_addresses /\
  step_call op s =
    (if failed then ignore_bind (credit_new_account charged) (abort_call_value cg) prepared
     else ignore_bind (set_return_data [])
       (proceed_call op sender addr value ao az code cg (Memory mr)) prepared) ==>
  ?k t dd' cc err gasLeft out success.
    FUNPOW (\r. if ISR (FST r) then r else step (SND r))
      k (INL (),s) = (INL (),t) /\ wf_state t /\
    t.msdomain = Collect dd' /\ t.txParams = s.txParams /\
    gasLeft <= cg /\ success = (~failed /\ err = NONE) /\
    gasLeft = (if failed then cg else call_return_gas err cc) /\
    out = (if failed then [] else call_return_data err cc) /\
    t.contexts = ((if failed then call_abort_context charged cg caller
      else call_return_context err cc
        (caller with <|returnData := []; stateGasLeft := 0|>) mr),cb)::cs /\
    (~failed ==> cc.msgParams.outputTo = Memory mr /\
                 cc.msgParams.gasLimit = cg /\
                 cc.msgParams.newAccountCharged = charged) /\
    (~success ==> t.rollback = saved) /\
    (cg <= call_stipend ==>
      t.originalAccounts = s.originalAccounts /\
      (success ==>
        t.rollback.accounts =
          (if op <> CallCode /\ 0 < value then
             transfer_value sender addr value saved.accounts else saved.accounts) /\
        t.rollback.toDelete = saved.toDelete))
Proof
  strip_tac >>
  `prepared.contexts = (caller,cb)::cs` by simp[] >>
  Cases_on `failed`
  >- (drule_all call_abort_context_pair >> strip_tac >>
      `step s = (INL (),prepared with contexts :=
        (call_abort_context charged cg caller,cb)::cs)` by
        (irule step_call_success_dispatch >> metis_tac[]) >>
      `wf_state (prepared with contexts :=
        (call_abort_context charged cg caller,cb)::cs)` by
        metis_tac[step_preserves_wf_state, SND] >>
      qexistsl_tac [`1`,`prepared with contexts :=
        (call_abort_context charged cg caller,cb)::cs`,`dd`,
        `caller`,`NONE`,`cg`,`[]`,`F`] >>
      simp[FUNPOW_1]) >>
  suspend "entered"
QED

Resume call_returns_summary[entered]:
  qabbrev_tac `cleared = prepared with contexts :=
    (caller with returnData := [],cb)::cs` >>
  `cleared.contexts = (caller with returnData := [],cb)::cs` by
    simp[Abbr `cleared`] >>
  `set_return_data [] prepared = (INL (),cleared)` by
    simp[set_return_data_def, get_current_context_def,
         set_current_context_def, bind_def, return_def, Abbr `cleared`] >>
  qpat_x_assum `step_call op s = _` mp_tac >>
  pure_rewrite_tac[COND_CLAUSES, ignore_bind_def, bind_def] >>
  qpat_assum `set_return_data [] prepared = _` (fn th => rewrite_tac[th]) >>
  drule_then (fn th => simp[th, LET_THM]) proceed_call_pair >>
  qmatch_goalsub_abbrev_tac `(INL (),entry)` >>
  strip_tac >>
  `step s = (INL (),entry)` by
    (irule step_call_success_dispatch >> metis_tac[]) >>
  `wf_state entry` by metis_tac[step_preserves_wf_state, SND] >>
  qmatch_asmsub_abbrev_tac
    `(callee,cleared.rollback)::(caller with <|returnData := []; stateGasLeft := 0|>,cb)::cs` >>
  `entry.contexts = (callee,saved)::(caller with <|returnData := []; stateGasLeft := 0|>,cb)::cs ∧
   entry.msdomain = Collect dd ∧ callee.msgParams.outputTo = Memory mr ∧
   callee.msgParams.gasLimit = cg ∧ callee.msgParams.newAccountCharged = charged` by
    simp[Abbr `entry`, Abbr `cleared`, Abbr `callee`,
         initial_context_def, initial_msg_params_def] >>
  `entry.txParams = s.txParams ∧ entry.originalAccounts = s.originalAccounts ∧
   entry.rollback.toDelete = saved.toDelete ∧
   entry.rollback.accounts =
     (if op ≠ CallCode ∧ 0 < value then
        transfer_value sender addr value saved.accounts else saved.accounts)` by
    (simp[Abbr `entry`, Abbr `cleared`] >>
     Cases_on `op ≠ CallCode ∧ 0 < value` >> simp[]) >>
  `call_meter_budget (LENGTH entry.contexts) cg entry` by
    simp[call_meter_budget_def, call_meter_prefix_def, call_meter_chain_def,
         vfmCallMeterProbeTheory.call_meter_claim_def, Abbr `callee`, initial_context_def,
         initial_msg_params_def] >>
  `cg <= (caller with <|returnData := []; stateGasLeft := 0|>).gasUsed` by simp[] >>
  drule_all run_call_memory_returns >> strip_tac >>
  qexistsl_tac [`SUC k`,`t`,`dd'`,`cc`,`err`] >>
  qpat_x_assum `Abbrev (entry = _)` kall_tac >>
  qpat_x_assum `Abbrev (cleared = _)` kall_tac >>
  qpat_x_assum `Abbrev (callee = _)` kall_tac >>
  simp[FUNPOW] >> strip_tac >>
  `!a. callee.msgParams.outputTo <> Code a` by simp[] >>
  `callee.msgParams.gasLimit <= call_stipend` by simp[] >>
  `1 <= LENGTH ((caller with <|returnData := []; stateGasLeft := 0|>,cb)::cs)` by simp[] >>
  drule_all run_call_stipend_footprint >> strip_tac >>
  `LENGTH t.contexts + 1 = LENGTH entry.contexts` by
    metis_tac[run_call_inl_length] >>
  drule_all call_memory_final_pop >> strip_tac >>
  `err = NONE <=> err' = NONE` by
    (qpat_x_assum `t.contexts = _` mp_tac >>
     simp[call_return_context_observations, context_component_equality] >>
     strip_tac >>
     Cases_on `err = NONE` >> Cases_on `err' = NONE` >>
     gvs[call_return_context_observations]) >>
  metis_tac[]
QED

Finalise call_returns_summary

Theorem call_entry_prepared[local]:
  wf_state s ∧ s.contexts = (c,cb)::cs ∧
  FLOOKUP c.msgParams.parsed c.pc = SOME op ∧
  is_call op ∧ op ≠ Create ∧ op ≠ Create2 ∧
  s.msdomain = Collect dd ∧ ¬fIN addr precompile_addresses ∧
  6 + v ≤ LENGTH c.stack ∧
  v = (if call_has_value op then 1 else 0) ∧
  w2n (EL 0 c.stack) = gas ∧ w2w (EL 1 c.stack) = addr ∧
  (if 0 < v then w2n (EL 2 c.stack) else 0) = value ∧
  w2n (EL (v+2) c.stack) = ao ∧ w2n (EL (v+3) c.stack) = az ∧
  w2n (EL (v+4) c.stack) = ro ∧ w2n (EL (v+5) c.stack) = rz ∧
  max_expansion_range (ao,az) (ro,rz) = (offset,sz) ∧
  lookup_account addr s.rollback.accounts = ta ∧
  delegate_check ta.code (msdomain_add addr s.msdomain)
    (accesses_add addr s.rollback) dc rb' dom' ∧
  memory_cost c.memory offset sz = mc ∧
  charged = (op = Call /\ 0 < value /\ account_empty ta) /\
  stateCost = (if charged then new_account_state_gas else 0) /\
  (if charged then new_account_state_gas else 0) <= c.stateGasLeft /\
  call_gas value gas
    (c.msgParams.gasLimit - (c.gasUsed + (static_gas op +
      access_cost s.rollback addr + (if 0 < value then call_value_cost else 0) + dc + mc)))
    0 0 = (dg,cg) /\
  c.gasUsed + (static_gas op + access_cost s.rollback addr +
    (if 0 < value then call_value_cost else 0) + dc + mc + dg) <= c.msgParams.gasLimit /\
  creditBack = MIN stateCost c.stateGasSpilled /\
  cg <= c.gasUsed + (static_gas op + access_cost s.rollback addr +
    (if 0 < value then call_value_cost else 0) + dc + mc + dg) - creditBack /\ 
  (0 < value ⇒ ¬c.msgParams.static) ∧
  caller = c with <|stack := DROP (6+v) c.stack;
    gasUsed := c.gasUsed + (static_gas op + access_cost s.rollback addr +
      (if 0 < value then call_value_cost else 0) + dc + mc + dg);
    stateGasLeft := c.stateGasLeft - stateCost;
    memory := expanded_memory c.memory offset sz|> ∧
  prepared = s with <|rollback := rb'; msdomain := dom';
                      contexts := (caller,cb)::cs|> ⇒
  ∃k t dd' cc err gasLeft out success.
    FUNPOW (λr. if ISR (FST r) then r else step (SND r))
      k (INL (),s) = (INL (),t) ∧ wf_state t ∧
    t.msdomain = Collect dd' ∧ t.txParams = s.txParams ∧ gasLeft ≤ cg ∧
    success = (~((lookup_account c.msgParams.callee s.rollback.accounts).balance < value \/
                 LENGTH s.contexts > 1024) /\ err = NONE) /\
    gasLeft = (if (lookup_account c.msgParams.callee s.rollback.accounts).balance < value \/
                 LENGTH s.contexts > 1024 then cg else call_return_gas err cc) /\
    out = (if (lookup_account c.msgParams.callee s.rollback.accounts).balance < value \/
                 LENGTH s.contexts > 1024 then [] else call_return_data err cc) /\
    t.contexts = ((if (lookup_account c.msgParams.callee s.rollback.accounts).balance < value \/
                 LENGTH s.contexts > 1024 then call_abort_context charged cg caller
      else call_return_context err cc
        (caller with <|returnData := []; stateGasLeft := 0|>)
        <|offset := ro; size := rz|>),cb)::cs ∧
    (¬success ⇒ t.rollback = rb') ∧
    (cg ≤ call_stipend ⇒
      t.originalAccounts = s.originalAccounts ∧
      (success ⇒
        t.rollback.accounts =
          (if op ≠ CallCode ∧ 0 < value then
             transfer_value c.msgParams.callee addr value s.rollback.accounts
           else s.rollback.accounts) ∧
        t.rollback.toDelete = s.rollback.toDelete))
Proof
  strip_tac >>
  `access_check s.msdomain addr` by simp[access_check_def] >>
  `step_call op s =
    if (lookup_account c.msgParams.callee s.rollback.accounts).balance < value
    then ignore_bind (credit_new_account charged) (abort_call_value cg) prepared
    else ignore_bind (set_return_data [])
      (if LENGTH s.contexts > 1024 then ignore_bind (credit_new_account charged) (abort_unuse cg)
       else proceed_call op c.msgParams.callee addr value ao az
         (case get_delegate ta.code of NONE => ta.code
          | SOME a => (lookup_account a s.rollback.accounts).code)
         cg (Memory <|offset := ro; size := rz|>)) prepared` by
    suspend "normalize_entry" >>
  suspend "compose_entry"
QED

Resume call_entry_prepared[normalize_entry]:
  `c.gasUsed + (static_gas op + access_cost s.rollback addr +
      (if 0 < value then call_value_cost else 0) + dc + mc) <= c.msgParams.gasLimit`
    by decide_tac >>
  qpat_x_assum `wf_state s` kall_tac >>
  qpat_x_assum `FLOOKUP _ _ = SOME op` kall_tac >>
  qpat_x_assum `is_call op` kall_tac >>
  qpat_x_assum `op ≠ Create` kall_tac >>
  qpat_x_assum `op ≠ Create2` kall_tac >>
  qpat_x_assum `s.msdomain = Collect dd` kall_tac >>
  qpat_x_assum `¬fIN addr precompile_addresses` kall_tac >>
  `v+6 <= LENGTH c.stack /\
   0 < 6+v /\ 1 < 6+v /\ 2 < 6+v /\
   v+2 < 6+v /\ v+3 < 6+v /\ v+4 < 6+v /\ v+5 < 6+v` by decide_tac >>
  `pop_stack (6+v) s =
    (INL (TAKE (6+v) c.stack),
     s with contexts := (c with stack := DROP (6+v) c.stack,cb)::cs)` by
    (qpat_x_assum `v = _` kall_tac >>
     simp[pop_stack_def, get_current_context_def, set_current_context_def,
          assert_def, bind_def, ignore_bind_def, return_def]) >>
  qpat_x_assum `prepared = _` (mk_asm "prepared") >>
  once_rewrite_tac[step_call_def] >>
  qpat_x_assum `v = _` (fn th => rewrite_tac[GSYM th]) >>
  simp_tac std_ss [LET_THM] >>
  once_rewrite_tac[bind_def] >>
  `2+v=v+2 /\ 3+v=v+3 /\ 4+v=v+4 /\ 5+v=v+5` by decide_tac >>
  asm_simp_tac (srw_ss()) [LET_THM, EL_TAKE] >>
  qpat_x_assum `w2n (EL 0 _) = gas`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  asm_simp_tac (srw_ss()) [HD_TAKE] >>
  once_rewrite_tac[bind_def] >>
  asm_simp_tac (srw_ss()) [memory_expansion_info_split] >>
  once_rewrite_tac[bind_def] >>
  asm_simp_tac (srw_ss()) [access_address_split] >>
  once_rewrite_tac[bind_def] >>
  asm_simp_tac (srw_ss()) [get_accounts_def, get_rollback_def,
                          return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `bind _ _ entryState` >>
  `delegate_check ta.code entryState.msdomain entryState.rollback dc rb' dom'`
    by simp[Abbr `entryState`] >>
  drule call_delegate_resolution >>
  simp_tac (srw_ss()) [Abbr `entryState`] >>
  disch_tac >>
  once_rewrite_tac[bind_def] >>
  asm_simp_tac (srw_ss()) [] >>
  ntac 2 (pop_assum kall_tac) >>
  once_rewrite_tac[bind_def] >>
  asm_simp_tac (srw_ss()) [get_gas_left_def, get_current_context_def, return_def] >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def,
    get_current_context_def, consume_gas_def, assert_def, fail_def,
    set_current_context_def, get_callee_def, get_num_contexts_def,
    expand_memory_def, expanded_memory_def, assert_not_static_def,
    LET_THM, get_static_def, GSYM ADD_ASSOC] >>
  fs[GSYM ADD_ASSOC] >>
  qpat_assum `charged = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  Cases_on `charged` >>
  fs[charge_new_account_def, charge_state_gas_def,
    bind_def, return_def, get_current_context_def, set_current_context_def] >>
  Cases_on `op = Call /\ 0 < value` >>
  gvs[] >>
  fs[GSYM ADD_ASSOC] >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def,
    get_current_context_def, get_static_def, assert_def, fail_def,
    set_current_context_def, get_num_contexts_def, LET_THM] >>
  asm_x "prepared" assume_tac >>
  asm_simp_tac (srw_ss()) [expanded_memory_def,
    bind_def, ignore_bind_def, return_def, set_return_data_def,
    get_current_context_def, set_current_context_def, get_num_contexts_def,
    LET_THM] >>
  `!x:num. dg + (dc + x) = dc + (dg + x)` by decide_tac >>
  simp[COND_RATOR, bind_def, ignore_bind_def, return_def, set_return_data_def,
    get_current_context_def, set_current_context_def, get_num_contexts_def] >>
  IF_CASES_TAC >> gvs[] >>
  simp[assert_def, fail_def, COND_RATOR, bind_def, ignore_bind_def, return_def, set_return_data_def,
    get_current_context_def, set_current_context_def, get_num_contexts_def]
QED

Resume call_entry_prepared[compose_entry]:
  `∃dd1. dom' = Collect dd1 ∧ rb'.accounts = s.rollback.accounts ∧
    rb'.toDelete = s.rollback.toDelete` by
    (qpat_x_assum `delegate_check _ _ _ _ _ _` mp_tac >>
     simp[msdomain_add_def] >> strip_tac >>
     drule delegate_check_collect_frame >> simp[accesses_add_def]) >>
  `creditBack = MIN stateCost caller.stateGasSpilled /\
   cg <= caller.gasUsed - creditBack` by (fs[GSYM ADD_ASSOC] >> gvs[]) >>
  `LENGTH c.stack ≤ stack_limit` by fs[wf_state_def, wf_context_def] >>
  `LENGTH (DROP (6+v) c.stack) < stack_limit` by
    (irule call_operand_drop_room >> qpat_x_assum `v = _` kall_tac >> simp[]) >>
  `LENGTH caller.stack < stack_limit` by
    (qpat_x_assum `v = _` kall_tac >> fs[]) >>
  `prepared.contexts = (caller,cb)::cs` by simp[] >>
  drule_all call_entry_failure_normalize >>
  disch_then (fn th =>
    qpat_x_assum `step_call op s = _` (assume_tac o ONCE_REWRITE_RULE [th])) >>
  `prepared = s with <|contexts := (caller,cb)::cs;
    rollback := rb'; msdomain := Collect dd1|>` by simp[] >>
  `charged = (op = Call /\ 0 < value /\
    account_empty (lookup_account addr rb'.accounts))` by simp[] >>
  drule_all call_returns_summary >>
  strip_tac >> qexistsl_tac [`k`,`t`,`dd'`,`cc`,`err`,`gasLeft`,`out`,`success`] >>
  simp[] >> metis_tac[]
QED

Finalise call_entry_prepared

Theorem IMP_EVM_SPEC_FINITE:
  (!s dom. p (evm2set_on dom s) ==>
    ?k t. FUNPOW (\s. if ISR (FST s) then s else step (SND s)) k s = t /\
      q (evm2set_on dom t) /\ evm2set_without dom s = evm2set_without dom t) ==>
  SPEC EVM_MODEL p {} q
Proof
  rewrite_tac[EVM_SPEC_SEMANTICS, rel_sequence_EVM_NEXT_REL_FUNPOW] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `k` >> simp[]
QED

Theorem IMP_EVM_SPEC_FINITE_CODE:
  (!s dom. (p * CODE_POOL EVM_INSTR code) (evm2set_on dom s) ==>
    ?k t. FUNPOW (\s. if ISR (FST s) then s else step (SND s)) k s = t /\
      (q * CODE_POOL EVM_INSTR code) (evm2set_on dom t) /\
      evm2set_without dom s = evm2set_without dom t) ==>
  SPEC EVM_MODEL p code q
Proof
  strip_tac >>
  once_rewrite_tac[GSYM (REWRITE_RULE [GSYM EVM_MODEL_def]
    (SIMP_RULE std_ss [EVM_MODEL_def] (ISPEC ``EVM_MODEL`` SPEC_CODE)))] >>
  irule IMP_EVM_SPEC_FINITE >> simp[STAR_COMM] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `k` >> gvs[]
QED

Theorem caller_observation_frame:
  wf_state (SND r) ∧ wf_state (SND r') ∧
  ctxt = FST (HD (SND r).contexts) ∧
  ctxt' = FST (HD (SND r').contexts) ∧
  (HasException ∉ dom ⇒ FST r' = FST r) ∧
  (HasStack ∉ dom ⇒ ctxt'.stack = ctxt.stack) ∧
  (HasGasUsed ∉ dom ⇒ ctxt'.gasUsed = ctxt.gasUsed) ∧
  (HasStateGasLeft NOTIN dom ==> ctxt'.stateGasLeft = ctxt.stateGasLeft) /\
  (HasStateGasSpilled NOTIN dom ==> ctxt'.stateGasSpilled = ctxt.stateGasSpilled) /\
  (HasStateGasBaseline NOTIN dom ==> ctxt'.stateGasBaseline = ctxt.stateGasBaseline) /\
  (HasStateGasCommitted NOTIN dom ==> ctxt'.stateGasCommitted = ctxt.stateGasCommitted) /\
  (HasMsgParams ∉ dom ⇒ ctxt'.msgParams = ctxt.msgParams) ∧
  (HasLogs ∉ dom ⇒ ctxt'.logs = ctxt.logs) ∧
  (HasSubRefund ∉ dom ⇒ ctxt'.subRefund = ctxt.subRefund) ∧
  (HasAddRefund ∉ dom ⇒ ctxt'.addRefund = ctxt.addRefund) ∧
  (HasReturnData ∉ dom ⇒ ctxt'.returnData = ctxt.returnData) ∧
  (HasJumpDest ∉ dom ⇒ ctxt'.jumpDest = ctxt.jumpDest) ∧
  (HasMemory ∉ dom ⇒ ctxt'.memory = ctxt.memory) ∧
  (HasPC ∉ dom ⇒ ctxt'.pc = ctxt.pc) ∧
  (∀pc. HasParsed pc ∉ dom ⇒
    FLOOKUP ctxt'.msgParams.parsed pc = FLOOKUP ctxt.msgParams.parsed pc) ∧
  (HasContexts ∉ dom ⇒ TL (SND r').contexts = TL (SND r).contexts) ∧
  (HasCachedRB ∉ dom ⇒
    SND (HD (SND r').contexts) = SND (HD (SND r).contexts)) ∧
  (HasTxParams ∉ dom ⇒ (SND r').txParams = (SND r).txParams) ∧
  (HasRollback ∉ dom ⇒ (SND r').rollback = (SND r).rollback) ∧
  (HasOriginalAccounts ∉ dom ⇒
    (SND r').originalAccounts = (SND r).originalAccounts) ∧
  (HasMsdomain ∉ dom ⇒ (SND r').msdomain = (SND r).msdomain)
  ⇒ evm2set_without dom r' = evm2set_without dom r
Proof
  strip_tac >>
  simp[evm2set_without_def, evm2set_def, EXTENSION, evm2set_on_def] >>
  Cases >> simp[COND_RAND, COND_RATOR] >>
  rw[Once EQ_IMP_THM] >> gvs[]
QED

Theorem call_final_context_observations[local]:
  final = (if failed then call_abort_context charged cg caller
    else call_return_context err cc
      (caller with <|returnData := []; stateGasLeft := 0|>) mr) /\
  success = (~failed /\ err = NONE) /\
  out = (if failed then [] else call_return_data err cc) ==>
  final.stack = b2w success::caller.stack /\
  final.pc = SUC caller.pc /\
  final.memory = buffer_write mr.offset (TAKE mr.size out) caller.memory /\
  final.returnData = out /\
  final.msgParams = caller.msgParams /\
  final.jumpDest = caller.jumpDest /\
  final.logs = caller.logs ++ (if success then cc.logs else []) /\
  final.addRefund = caller.addRefund + (if success then cc.addRefund else 0) /\
  final.subRefund = caller.subRefund + (if success then cc.subRefund else 0)
Proof
  Cases_on `failed` >>
  simp[call_abort_context_def, call_return_context_observations] >>
  rpt strip_tac >> gvs[]
QED

val call_spec_entry_tac =
  irule IMP_EVM_SPEC_FINITE_CODE >> rpt gen_tac >>
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
    [STAR_evm2set, STAR_evm_OriginalAccounts, GSYM STAR_ASSOC,
     STAR_CODE_POOL_evm2set, CODE_POOL_evm2set])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `ss = c.stack` >>
  `s = (INL (),SND s)` by
    (Cases_on `s` >> Cases_on `q` >> gvs[]) >>
  `(SND s).contexts ≠ []` by gvs[wf_state_def] >>
  Cases_on `(SND s).contexts` >- gvs[] >>
  PairCases_on `h` >>
  `h0 = c` by simp[Abbr `c`] >>
  qpat_x_assum `Abbrev (c = _)` kall_tac >>
  gvs[] >>
  qpat_assum `Collect dd = _` (assume_tac o SYM) >>
  drule_all (SIMP_RULE (boss_ss()) [] (GEN_ALL call_entry_prepared)) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `t'.contexts = (final,cb)::cs` >>
  qpat_assum `Abbrev (final = _)`
    (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all call_final_context_observations >> strip_tac >>
  `FUNPOW (λr. if ISR (FST r) then r else step (SND r)) k s = (INL (),t')` by
    (qpat_assum `s = (INL (),SND s)` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qexists_tac `k` >>
  qpat_x_assum `FUNPOW _ k s = _` (fn th => rewrite_tac[th]);

val call_spec_post_tac = fn witnesses =>
  once_rewrite_tac[STAR_COMM] >>
  simp[STAR_CODE_POOL_evm2set] >>
  conj_tac >- (qpat_x_assum `_ = {HasParsed c.pc}` mp_tac >> SET_TAC[]) >>
  CONV_TAC (REDEPTH_CONV (HO_REWR_CONV SEP_EXISTS_THM)) >>
  qexistsl_tac witnesses >>
  gvs[] >> Cases_on `success` >>
  simp[STAR_evm2set, STAR_evm_OriginalAccounts, GSYM STAR_ASSOC,
       call_return_context_observations, call_return_context_meter,
       call_abort_context_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `evm2set_on rest _` >>
  `rest = {}` by
    (qunabbrev_tac `rest` >>
     qpat_x_assum `_ = {HasParsed c.pc}` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> SET_TAC[]) >>
  simp[cond_def, evm2set_on_def];

val call_spec_frame_tac =
  sym_tac >> irule caller_observation_frame >> simp[];

(* CALL to any code at a non-precompile, in a Collect domain (the
   default; an Enforce domain can abort the callee).  The precondition is
   SPEC_Call's without the balance and depth checks: when those fail the
   CALL returns 0 at once, which the postcondition covers. The callee's
   CREATEs reset accounts in originalAccounts, so the rule owns it. *)
Theorem SPEC_Call_any:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_OriginalAccounts oa *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, calleeGas) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         ¬fIN addr precompile_addresses ∧
         d = Collect dd))
  {(pc,call_inst)}
  (SEP_EXISTS success out gasLeft calleeLogs calleeAr calleeSr rb' dd' oa'.
   evm_Stack (b2w success :: DROP (6 + vOff) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + gasCost - gasLeft) *
   evm_MsgParams p *
   evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
   evm_Rollback rb' * evm_Msdomain (Collect dd') * evm_ReturnData out *
   evm_Exception (INL ()) *
   evm_AddRefund (ar + if success then calleeAr else 0) *
   evm_SubRefund (sr + if success then calleeSr else 0) *
   evm_Logs (l ++ if success then calleeLogs else []) *
   evm_OriginalAccounts oa' *
   cond (gasLeft ≤ calleeGas ∧ (¬success ⇒ rb' = newRb)))
Proof
  call_spec_entry_tac >>
  conj_tac >- suspend "post" >>
  suspend "frame"
QED

Resume SPEC_Call_any[post]:
  call_spec_post_tac
    [`success`,`out`,`gasLeft`,`cc.logs`,`cc.addRefund`,`cc.subRefund`,
     `t'.rollback`,`dd'`,`t'.originalAccounts`]
QED

Resume SPEC_Call_any[frame]:
  call_spec_frame_tac
QED

Finalise SPEC_Call_any

(* With at most the 2300-gas stipend, no frame of the callee can SSTORE
   (EIP-2200 sentry), CALL with value (9000), SELFDESTRUCT (5000) or CREATE
   (32000), so no account changes apart from the CALL's own value transfer,
   which is undone if the callee fails. *)
Theorem SPEC_Call_stipend:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, calleeGas) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         ¬fIN addr precompile_addresses ∧
         d = Collect dd ∧
         calleeGas ≤ call_stipend))
  {(pc,call_inst)}
  (SEP_EXISTS success out gasLeft calleeLogs calleeAr calleeSr rb' dd'.
   evm_Stack (b2w success :: DROP (6 + vOff) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + gasCost - gasLeft) *
   evm_MsgParams p *
   evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
   evm_Rollback rb' * evm_Msdomain (Collect dd') * evm_ReturnData out *
   evm_Exception (INL ()) *
   evm_AddRefund (ar + if success then calleeAr else 0) *
   evm_SubRefund (sr + if success then calleeSr else 0) *
   evm_Logs (l ++ if success then calleeLogs else []) *
   cond (gasLeft ≤ calleeGas ∧
         (if success then
            rb'.accounts =
              (if call_inst ≠ CallCode ∧ 0 < value
               then transfer_value p.callee addr value rb.accounts
               else rb.accounts) ∧
            rb'.toDelete = rb.toDelete
          else rb' = newRb)))
Proof
  call_spec_entry_tac >>
  conj_tac >- suspend "post" >>
  suspend "frame"
QED

Resume SPEC_Call_stipend[post]:
  call_spec_post_tac
    [`success`,`out`,`gasLeft`,`cc.logs`,`cc.addRefund`,`cc.subRefund`,
     `t'.rollback`,`dd'`]
QED

Resume SPEC_Call_stipend[frame]:
  call_spec_frame_tac
QED

Finalise SPEC_Call_stipend
