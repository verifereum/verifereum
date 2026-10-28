(* CALL to arbitrary code, as one SPEC step for the caller: control comes
   back to the caller's frame with the callee's effects confined to the
   rollback state, logs and refunds. *)
Theory vfmProgCall
Ancestors
  vfmProg vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmDecreasesGas vfmRunCall vfmContextLength vfmAccountFrame vfmStaticCalls
  vfmRunWithinFrame vfmSameFrame vfmDomainCollection vfmStepLength
  vfmTypes vfmBuffer vfmHandleStep
  prog set_sep pred_set pair list arithmetic option finite_map combin

(* ----------------------------------------------------------------------------- *)
(* The contexts below the callee are left alone while it runs                    *)
(* ----------------------------------------------------------------------------- *)

Theorem DROP_TL_eq[local]:
  0 < k ∧ l1 ≠ [] ∧ l2 ≠ [] ∧ TL l1 = TL l2 ⇒ DROP k l1 = DROP k l2
Proof
  Cases_on `k` \\ Cases_on `l1` \\ Cases_on `l2` \\ gvs[]
QED

Theorem DROP_SUC_TL_TL[local]:
  0 < k ∧ 2 ≤ LENGTH l' ∧ l ≠ [] ∧ TL (TL l') = TL l ⇒
  DROP (SUC k) l' = DROP k l
Proof
  Cases_on `k` \\ Cases_on `l` \\ gvs[]
  \\ Cases_on `l'` \\ gvs[] \\ Cases_on `t'` \\ gvs[]
QED

Theorem DROP_pop[local]:
  L ≤ SUC (LENGTH rest) ⇒
  DROP (LENGTH (x::rest) + 1 - L) (x::rest) =
  DROP (LENGTH (a::b::rest) + 1 - L) (a::b::rest)
Proof
  strip_tac
  \\ `LENGTH (a::b::rest) + 1 - L = SUC (SUC (SUC (LENGTH rest) - L)) ∧
      LENGTH (x::rest) + 1 - L = SUC (SUC (LENGTH rest) - L)` by simp[]
  \\ ASM_REWRITE_TAC[] \\ simp[]
QED

Theorem step_push_TL_TL[local]:
  wf_state s ∧ step s = (r,s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  TL (TL s'.contexts) = TL s.contexts
Proof
  strip_tac
  \\ `s.contexts ≠ []` by gvs[wf_state_def]
  \\ drule_all step_push_foreign \\ strip_tac \\ simp[]
  \\ drule_all step_grow_dispatch \\ strip_tac \\ gvs[]
  >- (drule step_call_push_structure \\ simp[])
  \\ drule step_create_reaches_proceed_create \\ simp[] \\ strip_tac
  \\ gvs[cp_rel_def, proceed_create_def, update_accounts_def, get_rollback_def,
         get_original_def, set_original_def, push_context_def,
         ignore_bind_def, bind_def, return_def, fail_def, AllCaseEqs()]
QED

(* While run_call es is still in es's frame or deeper, the contexts below
   es's frame are those of es. *)
Theorem run_call_reaches_outer_contexts:
  wf_state es ∧ run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ⇒
  DROP (LENGTH s.contexts + 1 - LENGTH es.contexts) s.contexts = TL es.contexts
Proof
  strip_tac
  \\ `(λs. wf_state s ∧
        (LENGTH es.contexts ≤ LENGTH s.contexts ⇒
         DROP (LENGTH s.contexts + 1 - LENGTH es.contexts) s.contexts =
         TL es.contexts)) s` suffices_by simp[]
  \\ irule run_call_reaches_inv
  \\ qexists_tac `es` \\ simp[]
  \\ conj_tac
  >- (`es.contexts ≠ []` by gvs[wf_state_def]
      \\ Cases_on `es.contexts` \\ gvs[])
  \\ qx_genl_tac [`t`,`t'`] \\ strip_tac
  \\ `wf_state t'` by metis_tac[step_preserves_wf_state, SND]
  \\ simp[] \\ strip_tac
  \\ `t.contexts ≠ []` by gvs[wf_state_def]
  \\ `DROP (LENGTH t.contexts + 1 - LENGTH es.contexts) t.contexts =
      TL es.contexts` by metis_tac[]
  \\ qpat_x_assum `_ ⇒ _` kall_tac
  \\ Cases_on `LENGTH t'.contexts = LENGTH t.contexts`
  >- (`outputTo_consistent t`
        by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent]
      \\ drule_all step_same_frame \\ rw[same_frame_rel_def]
      \\ `t'.contexts ≠ []` by gvs[wf_state_def]
      \\ qpat_x_assum `DROP _ _ = _` (SUBST1_TAC o SYM)
      \\ irule DROP_TL_eq \\ simp[])
  \\ Cases_on `LENGTH t.contexts < LENGTH t'.contexts`
  >- (drule_all step_push_TL_TL \\ strip_tac
      \\ qpat_x_assum `DROP _ _ = _` (SUBST1_TAC o SYM)
      \\ `LENGTH t'.contexts + 1 - LENGTH es.contexts =
          SUC (LENGTH t.contexts + 1 - LENGTH es.contexts)` by simp[]
      \\ pop_assum SUBST1_TAC
      \\ `0 < LENGTH t.contexts` by (Cases_on `t.contexts` \\ fs[])
      \\ irule DROP_SUC_TL_TL \\ simp[])
  \\ `LENGTH t'.contexts < LENGTH t.contexts` by decide_tac
  \\ `outputTo_consistent_stack t ∧ EVERY (wf_context o FST) t.contexts`
       by gvs[wf_state_def]
  \\ drule_all step_pop_structure \\ strip_tac
  \\ `LENGTH es.contexts ≤ SUC (LENGTH rest)` by gvs[]
  \\ qpat_x_assum `DROP _ _ = _` (SUBST1_TAC o SYM)
  \\ qpat_x_assum `t'.contexts = _` SUBST1_TAC
  \\ qpat_x_assum `t.contexts = _` (fn th => ONCE_REWRITE_TAC[th])
  \\ irule DROP_pop \\ simp[]
QED

Theorem step_preserves_selected_metadata:
  wf_state s ∧ step s = (r,t) ∧ 2 ≤ n ∧
  n ≤ LENGTH s.contexts ∧ n ≤ LENGTH t.contexts ⇒
  (SND (EL (LENGTH t.contexts - n) t.contexts),
   (FST (EL (LENGTH t.contexts - n) t.contexts)).msgParams) =
  (SND (EL (LENGTH s.contexts - n) s.contexts),
   (FST (EL (LENGTH s.contexts - n) s.contexts)).msgParams)
Proof
  strip_tac >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- suspend "same_depth"
  >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- suspend "push_depth"
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac
  >> suspend "pop_depth"
QED

Resume step_preserves_selected_metadata[same_depth]:
  drule_all step_same_frame_foreign >> strip_tac >>
  qpat_x_assum `∀y. _` kall_tac >>
  qpat_x_assum `wf_state _` kall_tac >>
  qpat_x_assum `step _ = _` kall_tac >>
  Cases_on `s.contexts` >- gvs[] >>
  Cases_on `t.contexts` >- gvs[] >>
  gvs[] >> Cases_on `SUC (LENGTH t') - n` >> gvs[]
QED

Resume step_preserves_selected_metadata[push_depth]:
  drule_all step_push_TL_TL >> strip_tac >>
  drule_all step_push_foreign >> strip_tac >>
  `2 ≤ LENGTH s.contexts` by decide_tac >>
  `LENGTH t.contexts - n = SUC (LENGTH s.contexts - n)` by decide_tac >>
  qpat_x_assum `∀y. _` kall_tac >>
  qpat_x_assum `wf_state _` kall_tac >>
  qpat_x_assum `step _ = _` kall_tac >>
  Cases_on `s.contexts` >- gvs[] >>
  Cases_on `t.contexts` >- gvs[] >>
  rename1 `t.contexts = a::tail` >>
  Cases_on `tail` >- gvs[] >> gvs[] >>
  `SUC (SUC (LENGTH t')) - n = SUC (SUC (LENGTH t') - n)`
    by decide_tac >>
  asm_rewrite_tac[] >> Cases_on `SUC (LENGTH t') - n` >> gvs[]
QED

Resume step_preserves_selected_metadata[pop_depth]:
  drule_all step_pop_foreign >> strip_tac >>
  qpat_x_assum `wf_state _` kall_tac >>
  qpat_x_assum `step _ = _` kall_tac >>
  qpat_x_assum `s.contexts = _` (fn th => ONCE_REWRITE_TAC[th]) >>
  `n ≤ SUC (LENGTH rest)` by gvs[] >>
  `SUC (SUC (LENGTH rest)) - n = SUC (SUC (LENGTH rest) - n)`
    by decide_tac >>
  simp[] >> asm_rewrite_tac[] >>
  Cases_on `SUC (LENGTH rest) - n` >> gvs[]
QED

Finalise step_preserves_selected_metadata

Theorem run_call_reaches_selected_metadata:
  wf_state es ∧ run_call_reaches es t ∧
  2 ≤ n ∧ n ≤ LENGTH es.contexts ∧ n ≤ LENGTH t.contexts ⇒
  (SND (EL (LENGTH t.contexts - n) t.contexts),
   (FST (EL (LENGTH t.contexts - n) t.contexts)).msgParams) =
  (SND (EL (LENGTH es.contexts - n) es.contexts),
   (FST (EL (LENGTH es.contexts - n) es.contexts)).msgParams)
Proof
  strip_tac >>
  `(λs. wf_state s ∧
     (n ≤ LENGTH s.contexts ⇒
      (SND (EL (LENGTH s.contexts - n) s.contexts),
       (FST (EL (LENGTH s.contexts - n) s.contexts)).msgParams) =
      (SND (EL (LENGTH es.contexts - n) es.contexts),
       (FST (EL (LENGTH es.contexts - n) es.contexts)).msgParams))) t`
    suffices_by simp[] >>
  irule run_call_reaches_inv >> qexists_tac `es` >> simp[] >>
  qx_genl_tac [`s`,`s'`] >> strip_tac >>
  `wf_state s'` by metis_tac[step_preserves_wf_state, SND] >>
  simp[] >> strip_tac >>
  `n ≤ LENGTH s.contexts` by decide_tac >>
  drule_all step_preserves_selected_metadata >> simp[]
QED

Theorem run_call_reaches_root_metadata:
  wf_state es ∧ 2 ≤ LENGTH es.contexts ∧ run_call_reaches es t ∧
  LENGTH t.contexts = LENGTH es.contexts ⇒
  SND (HD t.contexts) = SND (HD es.contexts) ∧
  (FST (HD t.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  strip_tac >>
  drule (Q.INST [`n` |-> `LENGTH es.contexts`]
    run_call_reaches_selected_metadata) >>
  disch_then (qspec_then `t` mp_tac) >> simp[]
QED

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

Theorem call_entry_failure_normalize[local]:
  prepared.contexts = (caller,cb)::cs ∧ cg ≤ caller.gasUsed ∧
  LENGTH caller.stack < stack_limit ⇒
  (if balanceFail then abort_call_value cg prepared
   else ignore_bind (set_return_data [])
     (if depthFail then abort_unuse cg else proceed) prepared) =
  (if balanceFail ∨ depthFail then abort_call_value cg prepared
   else ignore_bind (set_return_data []) proceed prepared)
Proof
  strip_tac >> drule_all call_abort_pair >>
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
      (op = StaticCall \/ c.msgParams.static) output tx,s.rollback)::(c,cb)::cs;
    rollback := s.rollback with accounts updated_by
      (if op <> CallCode /\ 0 < value then transfer_value sender addr value else I)
  |>)
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value` >>
  simp[proceed_call_def, get_rollback_def, read_memory_def,
       get_current_context_def, update_accounts_def,
       get_caller_def, get_value_def, get_static_def, push_context_def,
       bind_def, ignore_bind_def, return_def] >>
  simp[execution_state_component_equality, rollback_state_component_equality]
QED


(* The return boundary retains every unmentioned state and context field. *)
Theorem pop_and_incorporate_context_pair[local]:
  s.contexts = (callee, saved)::(caller, callerSaved)::rest /\
  callee.msgParams.gasLimit - callee.gasUsed <= caller.gasUsed ==>
  pop_and_incorporate_context success s =
    (INL (), s with <|
      contexts :=
        (caller with <|
          gasUsed := caller.gasUsed -
            (callee.msgParams.gasLimit - callee.gasUsed);
          logs := caller.logs ++ (if success then callee.logs else []);
          addRefund := caller.addRefund + (if success then callee.addRefund else 0);
          subRefund := caller.subRefund + (if success then callee.subRefund else 0)
        |>, callerSaved)::rest;
      rollback := if success then s.rollback else saved
    |>)
Proof
  strip_tac >> Cases_on `success` >>
  simp[pop_and_incorporate_context_def, get_gas_left_def,
       get_current_context_def, pop_context_def, unuse_gas_def,
       push_logs_def, update_gas_refund_def, set_rollback_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def, combinTheory.o_DEF, combinTheory.C_DEF,
       vfmContextTheory.context_component_equality] >>
  cong_tac (SOME 4) >> simp[context_component_equality]
QED

Theorem handle_exception_memory_return[local]:
  s.contexts = (callee, saved)::(caller, callerSaved)::rest /\
  callee.msgParams.outputTo = Memory r /\
  callee.gasUsed <= callee.msgParams.gasLimit /\
  callee.msgParams.gasLimit - callee.gasUsed <= caller.gasUsed /\
  LENGTH caller.stack < stack_limit ==>
  handle_exception e s =
  let success = (e = NONE);
      gasLeft = if e = NONE \/ e = SOME Reverted then
                  callee.msgParams.gasLimit - callee.gasUsed else 0;
      out = if e = NONE \/ e = SOME Reverted then callee.returnData else []
  in (INL (), s with <|
    contexts := (caller with <|
      stack := b2w success :: caller.stack;
      pc := SUC caller.pc;
      gasUsed := caller.gasUsed - gasLeft;
      memory := buffer_write r.offset (TAKE r.size out) caller.memory;
      returnData := out;
      logs := caller.logs ++ (if success then callee.logs else []);
      addRefund := caller.addRefund + (if success then callee.addRefund else 0);
      subRefund := caller.subRefund + (if success then callee.subRefund else 0)
    |>, callerSaved)::rest;
    rollback := if success then s.rollback else saved
  |>)
Proof
  strip_tac >> Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, pop_and_incorporate_context_def,
      get_gas_left_def, get_num_contexts_def, get_output_to_def,
      get_return_data_def, get_current_context_def, pop_context_def,
      consume_gas_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
      set_rollback_def, set_current_context_def, set_return_data_def,
      inc_pc_def, push_stack_def, write_memory_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      combinTheory.o_DEF, combinTheory.C_DEF] >>
  cong_tac (SOME 4) >> simp[context_component_equality, ADD_COMM]
QED

Theorem step_collect_not_outside[local]:
  s.msdomain = Collect dd /\ step s = (r,s') ==>
  r <> INR (SOME (OutsideDomain x))
Proof
  strip_tac >>
  mp_tac step_computes_minimal_domain >>
  rewrite_tac[computes_minimal_domain_def] >>
  disch_then drule >> simp[]
QED

Theorem run_call_preserves_collect[local]:
  es.msdomain = Collect dd /\ run_call es = SOME (r,es') ==>
  ?dd'. es'.msdomain = Collect dd'
Proof
  strip_tac >>
  `(\p. ?d. (SND p).msdomain = Collect d) (r,es')` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  qexists_tac `\(r,s). ISL r /\ LENGTH es.contexts <= LENGTH s.contexts` >>
  qexists_tac `step o SND` >>
  qexists_tac `(INL () : unit + exception option,es)` >>
  simp[] >>
  reverse conj_tac >- fs[run_call_def, GREATER_EQ, UNCURRY] >>
  qx_gen_tac `st` >> PairCases_on `st` >> simp[] >> strip_tac >>
  Cases_on `step st1` >> simp[] >>
  irule step_preserves_collect >> metis_tac[]
QED

Definition call_exn_safe_def:
  call_exn_safe P m Q <=>
    !s r t. P s /\ m s = (r,t) ==>
      Q t /\ (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
End

Theorem call_exn_safe_consequence[local]:
  (!s. P' s ==> P s) /\ call_exn_safe P m Q /\ (!s. Q s ==> Q' s) ==>
  call_exn_safe P' m Q'
Proof
  simp[call_exn_safe_def] >> metis_tac[]
QED

Theorem call_exn_safe_bind[local]:
  call_exn_safe P g R /\ (!x. call_exn_safe R (f x) Q) /\
  (!s. R s ==> Q s) ==> call_exn_safe P (bind g f) Q
Proof
  rw[call_exn_safe_def, bind_def] >>
  Cases_on `g s` >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem call_exn_safe_bind_invariant[local]:
  call_exn_safe P g Inv /\ (!x. call_exn_safe Inv (f x) Inv) ==>
  call_exn_safe P (bind g f) Inv
Proof
  strip_tac >> irule call_exn_safe_bind >> metis_tac[]
QED

Theorem call_exn_safe_return[local]:
  call_exn_safe P (return x) P
Proof
  simp[call_exn_safe_def, return_def]
QED

Theorem call_exn_safe_fail[local]:
  e <> Impossible /\ e <> Unimplemented ==> call_exn_safe P (fail e) P
Proof
  simp[call_exn_safe_def, fail_def]
QED

Theorem call_exn_safe_assert[local]:
  e <> Impossible /\ e <> Unimplemented ==>
  call_exn_safe P (assert b e) P
Proof
  Cases_on `b` >> simp[call_exn_safe_def, assert_def]
QED

Theorem call_exn_safe_reraise[local]:
  e <> SOME Impossible /\ e <> SOME Unimplemented ==>
  call_exn_safe P (reraise e) P
Proof
  simp[call_exn_safe_def, reraise_def]
QED

Theorem call_exn_safe_finish[local]:
  call_exn_safe P finish P /\ call_exn_safe P revert P
Proof
  simp[call_exn_safe_def, finish_def, revert_def]
QED

Theorem call_exn_safe_get_current_context[local]:
  call_exn_safe (\s. s.contexts <> []) get_current_context
    (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >> gvs[get_current_context_def, return_def]
QED

Theorem call_exn_safe_set_current_context[local]:
  call_exn_safe (\s. s.contexts <> []) (set_current_context c)
    (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >> gvs[set_current_context_def, return_def]
QED

Theorem call_exn_safe_original[local]:
  call_exn_safe (\s. s.contexts <> []) get_original
    (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (set_original a)
    (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >> gvs[get_original_def, set_original_def, return_def]
QED

Theorem call_exn_safe_state_readers[local]:
  call_exn_safe P get_num_contexts P /\
  call_exn_safe P get_tx_params P /\
  call_exn_safe P get_accounts P /\
  call_exn_safe P get_tStorage P /\
  call_exn_safe P get_rollback P
Proof
  simp[call_exn_safe_def, get_num_contexts_def, get_tx_params_def,
       get_accounts_def, get_tStorage_def, get_rollback_def, return_def]
QED

Theorem call_exn_safe_state_updates[local]:
  call_exn_safe (\s. s.contexts <> []) (update_accounts f) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (set_tStorage ts) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (set_rollback rb) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (set_domain d) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (add_to_delete a) (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >>
  gvs[update_accounts_def, set_tStorage_def, set_rollback_def,
      set_domain_def, add_to_delete_def, return_def]
QED

Theorem call_exn_safe_context_readers[local]:
  call_exn_safe (\s. s.contexts <> []) get_gas_left (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_callee (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_caller (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_value (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_output_to (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_return_data (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_static (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_current_code (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) get_call_data (\s. s.contexts <> [])
Proof
  rewrite_tac[get_gas_left_def, get_callee_def, get_caller_def, get_value_def,
    get_output_to_def, get_return_data_def, get_static_def,
    get_current_code_def, get_call_data_def] >>
  rpt conj_tac >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_get_current_context, call_exn_safe_return]
QED

Theorem call_exn_safe_context_updates[local]:
  call_exn_safe (\s. s.contexts <> []) (set_return_data rd) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (set_jump_dest jd) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (push_logs ls) (\s. s.contexts <> [])
Proof
  rewrite_tac[set_return_data_def, set_jump_dest_def, push_logs_def] >>
  rpt conj_tac >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_get_current_context, call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_consume_gas[local]:
  call_exn_safe (\s. s.contexts <> []) (consume_gas n) (\s. s.contexts <> [])
Proof
  rewrite_tac[consume_gas_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_get_current_context] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_assert, call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_stack[local]:
  call_exn_safe (\s. s.contexts <> []) (pop_stack n) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (push_stack v) (\s. s.contexts <> [])
Proof
  rewrite_tac[pop_stack_def, push_stack_def, ignore_bind_def] >>
  conj_tac >> irule call_exn_safe_bind_invariant >>
  (reverse conj_tac >- simp[call_exn_safe_get_current_context]) >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  (reverse conj_tac >- simp[call_exn_safe_assert]) >>
  gen_tac >> simp[]
  >- (irule call_exn_safe_bind_invariant >>
      simp[call_exn_safe_set_current_context, call_exn_safe_return]) >>
  simp[call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_inc_pc_or_jump[local]:
  call_exn_safe (\s. s.contexts <> []) (inc_pc_or_jump op) (\s. s.contexts <> [])
Proof
  rewrite_tac[inc_pc_or_jump_def] >>
  Cases_on `is_call op` >- simp[call_exn_safe_return] >>
  simp[] >> irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_get_current_context] >>
  qx_gen_tac `ctx` >> simp[] >>
  Cases_on `ctx.jumpDest` >- simp[call_exn_safe_set_current_context] >>
  simp[ignore_bind_def] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_assert, call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_step_binop[local]:
  call_exn_safe (\s. s.contexts <> []) (step_binop op f) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_binop_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_stack] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_consume_gas, call_exn_safe_stack]
QED

Theorem call_exn_safe_step_monop[local]:
  call_exn_safe (\s. s.contexts <> []) (step_monop op f) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_monop_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_stack] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_consume_gas, call_exn_safe_stack]
QED

Theorem call_exn_safe_step_modop[local]:
  call_exn_safe (\s. s.contexts <> []) (step_modop op f) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_modop_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_stack] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_consume_gas, call_exn_safe_stack]
QED

Theorem call_exn_safe_step_context[local]:
  call_exn_safe (\s. s.contexts <> []) (step_context op f) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_context_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_consume_gas] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_get_current_context, call_exn_safe_stack]
QED

Theorem call_exn_safe_step_txParams[local]:
  call_exn_safe (\s. s.contexts <> []) (step_txParams op f) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_txParams_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_consume_gas] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_state_readers, call_exn_safe_stack]
QED

Theorem call_exn_safe_domain_check[local]:
  call_exn_safe (\s. s.contexts <> []) cont (\s. s.contexts <> []) ==>
  call_exn_safe (\s. s.contexts <> []) (domain_check err check dom_add cont)
    (\s. s.contexts <> [])
Proof
  pure_rewrite_tac[call_exn_safe_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `s.msdomain`
  >- (gvs[domain_check_def] >> Cases_on `check d` >>
      gvs[fail_def] >> metis_tac[]) >>
  gvs[domain_check_def, ignore_bind_def, bind_def, set_domain_def, return_def] >>
  first_x_assum (qspec_then `s with msdomain := Collect (dom_add d)` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem call_exn_safe_memory[local]:
  call_exn_safe (\s. s.contexts <> []) (memory_expansion_info offset sz)
    (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (expand_memory n) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (read_memory offset sz) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (write_memory offset bytes) (\s. s.contexts <> [])
Proof
  rewrite_tac[memory_expansion_info_def, expand_memory_def,
    read_memory_def, write_memory_def] >>
  rpt conj_tac >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_get_current_context, call_exn_safe_return,
    call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_access[local]:
  call_exn_safe (\s. s.contexts <> []) (access_address a) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (access_slot x) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (ensure_storage_in_domain a) (\s. s.contexts <> [])
Proof
  rewrite_tac[access_address_def, access_slot_def, ensure_storage_in_domain_def] >>
  rpt conj_tac >> irule call_exn_safe_domain_check >>
  rw[call_exn_safe_def] >> gvs[return_def]
QED

Theorem call_exn_safe_get_code[local]:
  call_exn_safe P (get_code a) P
Proof
  rewrite_tac[get_code_def] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_state_readers, call_exn_safe_return]
QED

Theorem call_exn_safe_storage_updates[local]:
  call_exn_safe (\s. s.contexts <> []) (write_storage a k v) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (write_transient_storage a k v) (\s. s.contexts <> [])
Proof
  rewrite_tac[write_storage_def, write_transient_storage_def] >>
  conj_tac >- simp[call_exn_safe_state_updates] >>
  irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_state_readers, call_exn_safe_state_updates]
QED

Theorem call_exn_safe_get_return_data_check[local]:
  call_exn_safe (\s. s.contexts <> []) (get_return_data_check off sz) (\s. s.contexts <> [])
Proof
  rewrite_tac[get_return_data_check_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_context_readers] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_assert, call_exn_safe_return]
QED

Theorem call_exn_safe_update_gas_refund[local]:
  call_exn_safe (\s. s.contexts <> []) (update_gas_refund deltas) (\s. s.contexts <> [])
Proof
  Cases_on `deltas` >> rewrite_tac[update_gas_refund_def] >>
  irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_get_current_context, call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_assert_not_static[local]:
  call_exn_safe (\s. s.contexts <> []) assert_not_static (\s. s.contexts <> [])
Proof
  rewrite_tac[assert_not_static_def] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_context_readers, call_exn_safe_assert]
QED

Theorem call_exn_safe_simple_opcodes[local]:
  call_exn_safe (\s. s.contexts <> []) step_exp (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_balance (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_call_data_load (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_ext_code_size (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_ext_code_hash (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_keccak256 (\s. s.contexts <> [])
Proof
  rewrite_tac[step_exp_def, step_balance_def, step_call_data_load_def,
    step_ext_code_size_def, step_ext_code_hash_def, step_keccak256_def, ignore_bind_def] >>
  rpt conj_tac >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_consume_gas,
         call_exn_safe_state_readers, call_exn_safe_access,
         call_exn_safe_context_readers, call_exn_safe_memory] >>
       gen_tac >> simp[]) >>
  simp[call_exn_safe_stack]
QED

Theorem call_exn_safe_environment_memory_stack[local]:
  call_exn_safe (\s. s.contexts <> []) step_block_hash (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_blob_hash (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_self_balance (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_mload (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (step_mstore op) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_jump (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_jumpi (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (step_push n ws) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) step_pop (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (step_dup n) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (step_swap n) (\s. s.contexts <> []) /\
  call_exn_safe (\s. s.contexts <> []) (step_log n) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_block_hash_def, step_blob_hash_def, step_self_balance_def,
    step_mload_def, step_mstore_def, step_jump_def, step_jumpi_def, step_push_def,
    step_pop_def, step_dup_def, step_swap_def, step_log_def, ignore_bind_def] >>
  rpt conj_tac >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_consume_gas,
         call_exn_safe_state_readers, call_exn_safe_context_readers,
         call_exn_safe_memory, call_exn_safe_get_current_context,
         call_exn_safe_assert, call_exn_safe_assert_not_static] >>
       gen_tac >> simp[]) >>
  simp[call_exn_safe_stack, call_exn_safe_consume_gas, call_exn_safe_memory,
    call_exn_safe_context_updates, call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_step_return[local]:
  call_exn_safe (\s. s.contexts <> []) (step_return b) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_return_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_consume_gas,
         call_exn_safe_memory, call_exn_safe_context_updates] >>
       gen_tac >> simp[]) >>
  Cases_on `b` >> simp[call_exn_safe_finish]
QED

Theorem call_exn_safe_copy_to_memory[local]:
  (!reader. src = SOME reader ==>
    call_exn_safe (\s. s.contexts <> []) reader (\s. s.contexts <> [])) ==>
  call_exn_safe (\s. s.contexts <> []) (copy_to_memory gas off srcOff sz src)
    (\s. s.contexts <> [])
Proof
  strip_tac >> Cases_on `src`
  >- (Cases_on `max_expansion_range (off,sz) (srcOff,sz)` >>
      simp[copy_to_memory_def, ignore_bind_def] >>
      rpt (irule call_exn_safe_bind_invariant >>
           reverse conj_tac >- simp[call_exn_safe_memory, call_exn_safe_consume_gas] >>
           gen_tac >> simp[]) >> simp[call_exn_safe_memory]) >>
  gvs[] >> simp[copy_to_memory_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_memory, call_exn_safe_consume_gas] >>
       gen_tac >> simp[]) >>
  simp[call_exn_safe_memory]
QED

Theorem call_exn_safe_step_copy_to_memory[local]:
  (!reader. src = SOME reader ==>
    call_exn_safe (\s. s.contexts <> []) reader (\s. s.contexts <> [])) ==>
  call_exn_safe (\s. s.contexts <> []) (step_copy_to_memory op src) (\s. s.contexts <> [])
Proof
  strip_tac >> rewrite_tac[step_copy_to_memory_def] >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac >- simp[call_exn_safe_stack] >>
  gen_tac >> simp[] >> irule call_exn_safe_copy_to_memory >> simp[]
QED

Theorem call_exn_safe_step_return_data_copy[local]:
  call_exn_safe (\s. s.contexts <> []) step_return_data_copy (\s. s.contexts <> [])
Proof
  rewrite_tac[step_return_data_copy_def] >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac >- simp[call_exn_safe_stack] >>
  gen_tac >> simp[] >> irule call_exn_safe_copy_to_memory >>
  simp[call_exn_safe_get_return_data_check]
QED

Theorem call_exn_safe_step_ext_code_copy[local]:
  call_exn_safe (\s. s.contexts <> []) step_ext_code_copy (\s. s.contexts <> [])
Proof
  rewrite_tac[step_ext_code_copy_def] >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac >- simp[call_exn_safe_stack] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_access] >>
  gen_tac >> simp[] >> irule call_exn_safe_copy_to_memory >> simp[call_exn_safe_get_code]
QED

Theorem call_exn_safe_step_sstore_gas_consumption[local]:
  call_exn_safe (\s. s.contexts <> []) (step_sstore_gas_consumption a k v)
    (\s. s.contexts <> [])
Proof
  rewrite_tac[step_sstore_gas_consumption_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_context_readers, call_exn_safe_assert,
         call_exn_safe_state_readers, call_exn_safe_original, call_exn_safe_access,
         call_exn_safe_update_gas_refund] >> gen_tac >> simp[]) >>
  simp[call_exn_safe_consume_gas]
QED

Theorem call_exn_safe_step_sstore[local]:
  call_exn_safe (\s. s.contexts <> []) (step_sstore transient) (\s. s.contexts <> [])
Proof
  Cases_on `transient` >> rewrite_tac[step_sstore_def, ignore_bind_def] >> simp[] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_context_readers,
         call_exn_safe_consume_gas, call_exn_safe_step_sstore_gas_consumption,
         call_exn_safe_assert_not_static] >> gen_tac >> simp[]) >>
  simp[call_exn_safe_storage_updates]
QED

Theorem call_exn_safe_step_sload[local]:
  call_exn_safe (\s. s.contexts <> []) (step_sload transient) (\s. s.contexts <> [])
Proof
  Cases_on `transient` >> rewrite_tac[step_sload_def, ignore_bind_def] >> simp[] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_context_readers,
         call_exn_safe_return, call_exn_safe_access, call_exn_safe_consume_gas,
         call_exn_safe_state_readers] >> gen_tac >> simp[]) >>
  simp[call_exn_safe_stack]
QED

Theorem call_exn_safe_step_self_destruct[local]:
  call_exn_safe (\s. s.contexts <> []) step_self_destruct (\s. s.contexts <> [])
Proof
  rewrite_tac[step_self_destruct_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_access,
         call_exn_safe_context_readers, call_exn_safe_context_updates,
         call_exn_safe_state_readers, call_exn_safe_consume_gas,
         call_exn_safe_assert_not_static, call_exn_safe_state_updates,
         call_exn_safe_original] >> gen_tac >> simp[]) >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[call_exn_safe_return] >>
      irule call_exn_safe_bind_invariant >>
      simp[call_exn_safe_state_updates]) >>
  simp[call_exn_safe_finish]
QED

Theorem call_exn_safe_step_inst_noncall[local]:
  ~is_call op ==>
  call_exn_safe (\s. s.contexts <> []) (step_inst op) (\s. s.contexts <> [])
Proof
  Cases_on `op` >> simp[is_call_def, step_inst_def, step_msgParams_def,
    call_exn_safe_step_binop, call_exn_safe_step_monop, call_exn_safe_step_modop,
    call_exn_safe_step_context, call_exn_safe_step_txParams, call_exn_safe_simple_opcodes,
    call_exn_safe_environment_memory_stack, call_exn_safe_step_return,
    call_exn_safe_step_return_data_copy, call_exn_safe_step_ext_code_copy,
    call_exn_safe_step_sstore, call_exn_safe_step_sload, call_exn_safe_step_self_destruct,
    call_exn_safe_fail, call_exn_safe_consume_gas] >>
  rpt strip_tac
  >- (rewrite_tac[ignore_bind_def] >> irule call_exn_safe_bind_invariant >>
      simp[call_exn_safe_context_updates, call_exn_safe_finish]) >>
  irule call_exn_safe_step_copy_to_memory >> simp[call_exn_safe_context_readers]
QED

Theorem call_exn_safe_unuse_gas[local]:
  call_exn_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (unuse_gas n) (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >>
  gvs[unuse_gas_def, get_current_context_def, bind_def, return_def,
      ignore_bind_def, assert_def, set_current_context_def]
QED

Theorem call_exn_safe_inc_pc[local]:
  call_exn_safe (\s. s.contexts <> []) inc_pc (\s. s.contexts <> [])
Proof
  rewrite_tac[inc_pc_def] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_get_current_context, call_exn_safe_set_current_context]
QED

Theorem call_exn_safe_abort_unuse[local]:
  call_exn_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (abort_unuse n) (\s. s.contexts <> [])
Proof
  rewrite_tac[abort_unuse_def, ignore_bind_def] >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac
  >- simp[call_exn_safe_unuse_gas] >>
  gen_tac >> simp[] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_stack, call_exn_safe_inc_pc]
QED

Theorem call_exn_safe_push_context[local]:
  call_exn_safe P (push_context crb) (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >> gvs[push_context_def, return_def]
QED

Theorem call_exn_safe_abort_create_exists[local]:
  call_exn_safe (\s. s.contexts <> []) (abort_create_exists a) (\s. s.contexts <> [])
Proof
  rewrite_tac[abort_create_exists_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_state_updates, call_exn_safe_stack] >>
       gen_tac >> simp[]) >> simp[call_exn_safe_inc_pc]
QED

Theorem call_exn_safe_proceed_create[local]:
  call_exn_safe (\s. s.contexts <> []) (proceed_create sender addr value code gas)
    (\s. s.contexts <> [])
Proof
  rewrite_tac[proceed_create_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_state_updates, call_exn_safe_state_readers,
         call_exn_safe_original] >> gen_tac >> simp[]) >>
  simp[call_exn_safe_push_context]
QED

Theorem call_exn_safe_abort_call_value[local]:
  call_exn_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (abort_call_value n) (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def] >>
  gvs[abort_call_value_def, push_stack_def, set_return_data_def,
    unuse_gas_def, inc_pc_def, get_current_context_def, set_current_context_def,
    bind_def, ignore_bind_def, return_def, assert_def, AllCaseEqs()]
QED

Theorem call_exn_safe_dispatch_precompiles[local]:
  fIN a precompile_addresses ==>
  call_exn_safe (\s. s.contexts <> []) (dispatch_precompiles a) (\s. s.contexts <> [])
Proof
  rw[call_exn_safe_def]
  >- metis_tac[dispatch_precompiles_preserves_nonempty_contexts, SND] >>
  drule_all dispatch_precompiles_inr_not_reverted_not_abort >>
  Cases_on `e` >> simp[vfm_abort_def] >> Cases_on `x` >> simp[vfm_abort_def]
QED

Theorem call_exn_safe_proceed_call[local]:
  call_exn_safe (\s. s.contexts <> [])
    (proceed_call op sender addr value argsOff argsSz code gas output)
    (\s. s.contexts <> [])
Proof
  rewrite_tac[proceed_call_def, ignore_bind_def] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_state_readers, call_exn_safe_memory] >>
       gen_tac >> simp[]) >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[call_exn_safe_state_updates, call_exn_safe_return]) >>
  gen_tac >> simp[] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_context_readers, call_exn_safe_push_context] >>
       gen_tac >> simp[]) >>
  IF_CASES_TAC >> simp[call_exn_safe_dispatch_precompiles, call_exn_safe_return]
QED

Definition call_success_safe_def:
  call_success_safe P m Q <=>
    call_exn_safe P m (\s. s.contexts <> []) /\
    (!s x t. P s /\ m s = (INL x,t) ==> Q x t)
End

Theorem call_success_safe_forget[local]:
  call_success_safe P m Q ==> call_exn_safe P m (\s. s.contexts <> [])
Proof
  simp[call_success_safe_def]
QED

Theorem call_success_safe_lift[local]:
  call_exn_safe P m R /\ (!s. R s ==> s.contexts <> []) ==>
  call_success_safe P m (\x s. R s)
Proof
  simp[call_success_safe_def, call_exn_safe_def] >> metis_tac[]
QED

Theorem call_success_safe_consequence[local]:
  (!s. P' s ==> P s) /\ call_success_safe P m Q /\
  (!x s. Q x s ==> Q' x s) ==> call_success_safe P' m Q'
Proof
  simp[call_success_safe_def, call_exn_safe_def] >> metis_tac[]
QED

Theorem call_success_safe_return[local]:
  (!s. P s ==> s.contexts <> []) ==>
  call_success_safe P (return v) (\x s. x = v /\ P s)
Proof
  simp[call_success_safe_def, call_exn_safe_def, return_def]
QED

Theorem call_success_safe_bind[local]:
  call_success_safe P m R /\ (!x. call_success_safe (R x) (f x) Q) ==>
  call_success_safe P (bind m f) Q
Proof
  rw[call_success_safe_def, call_exn_safe_def, bind_def] >>
  Cases_on `m s` >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem call_success_safe_bind_exn[local]:
  call_success_safe P m R /\
  (!x. call_exn_safe (R x) (f x) (\s. s.contexts <> [])) ==>
  call_exn_safe P (bind m f) (\s. s.contexts <> [])
Proof
  rw[call_success_safe_def, call_exn_safe_def, bind_def] >>
  Cases_on `m s` >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem call_success_safe_consume_gas[local]:
  call_success_safe (\s. s.contexts <> []) (consume_gas n)
    (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
Proof
  rewrite_tac[call_success_safe_def] >>
  conj_tac >- simp[call_exn_safe_consume_gas] >>
  rw[] >> gvs[consume_gas_def, bind_def, ignore_bind_def, assert_def,
    get_current_context_def, set_current_context_def, return_def, AllCaseEqs()]
QED

Theorem call_success_safe_credit_assert[local]:
  e <> Impossible /\ e <> Unimplemented ==>
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (assert b e) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
Proof
  strip_tac >> ho_match_mp_tac call_success_safe_lift >>
  simp[call_exn_safe_assert]
QED

Theorem call_success_safe_credit_readers[local]:
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    get_accounts (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed) /\
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    get_num_contexts (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
Proof
  conj_tac >> ho_match_mp_tac call_success_safe_lift >> simp[call_exn_safe_state_readers]
QED

Theorem call_success_safe_credit_return[local]:
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (return v) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
Proof
  ho_match_mp_tac call_success_safe_lift >> simp[call_exn_safe_return]
QED

Theorem call_success_safe_credit_context_effects[local]:
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    assert_not_static (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed) /\
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (expand_memory amount) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed) /\
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (read_memory off sz) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed) /\
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    get_callee (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed) /\
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (set_return_data rd) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
Proof
  rpt conj_tac >> ho_match_mp_tac call_success_safe_lift >>
  (conj_tac >- (rw[call_exn_safe_def] >>
    gvs[assert_not_static_def, get_static_def, expand_memory_def, read_memory_def,
      get_callee_def, set_return_data_def, bind_def, ignore_bind_def,
      get_current_context_def, set_current_context_def, assert_def,
      return_def, AllCaseEqs()]) >> simp[])
QED

Theorem call_success_safe_credit_access[local]:
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (access_address a) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed) /\
  call_success_safe (\s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
    (ensure_storage_in_domain a) (\x s. s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed)
Proof
  conj_tac >> ho_match_mp_tac call_success_safe_lift >>
  (conj_tac >- (rw[call_exn_safe_def] >>
    Cases_on `s.msdomain` >>
    gvs[access_address_def, ensure_storage_in_domain_def, domain_check_def,
      bind_def, ignore_bind_def, set_domain_def, return_def, fail_def, AllCaseEqs()]) >>
  simp[])
QED

Theorem call_gas_refund_credit[local]:
  call_gas value gas gasLeft memoryCost
    (accessCost + (if 0 < value then call_value_cost else 0) + createCost + delegateCost) =
      (dynamicGas,stipend) ==>
  stipend <= static_gas op + dynamicGas + memoryCost
Proof
  strip_tac >>
  `stipend <= dynamicGas + memoryCost` suffices_by simp[] >>
  irule call_gas_stipend_le_consumed >>
  goal_assum (drule_at Any) >>
  Cases_on `0 < value` >> simp[call_stipend_def, call_value_cost_def]
QED

Theorem call_exn_safe_step_create[local]:
  call_exn_safe (\s. s.contexts <> []) (step_create two) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_create_def, ignore_bind_def] >> simp[] >>
  ntac 9 (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_memory,
         call_exn_safe_consume_gas, call_exn_safe_context_readers,
         call_exn_safe_state_readers, call_exn_safe_assert] >> gen_tac >> simp[]) >>
  qmatch_goalsub_abbrev_tac `consume_gas credit` >>
  irule call_success_safe_bind_exn >>
  qexists_tac `\x s. s.contexts <> [] /\ credit <= (FST (HD s.contexts)).gasUsed` >>
  reverse conj_tac >- irule call_success_safe_consume_gas >>
  gen_tac >> simp[] >>
  rpt (irule call_success_safe_bind_exn >>
       qexists_tac `\x s. s.contexts <> [] /\ credit <= (FST (HD s.contexts)).gasUsed` >>
       reverse conj_tac >- simp[call_success_safe_credit_context_effects,
         call_success_safe_credit_readers] >> gen_tac >> simp[]) >>
  IF_CASES_TAC >- simp[call_exn_safe_abort_unuse] >>
  irule call_exn_safe_consequence >>
  qexistsl_tac [`\s. s.contexts <> []`, `\s. s.contexts <> []`] >>
  simp[] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_access] >> gen_tac >> simp[]) >>
  IF_CASES_TAC >> simp[call_exn_safe_abort_create_exists, call_exn_safe_proceed_create]
QED

Theorem call_exn_safe_step_call[local]:
  call_exn_safe (\s. s.contexts <> []) (step_call op) (\s. s.contexts <> [])
Proof
  rewrite_tac[step_call_def, ignore_bind_def] >> simp[] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_stack, call_exn_safe_memory,
         call_exn_safe_access, call_exn_safe_context_readers,
         call_exn_safe_state_readers] >> gen_tac >> simp[]) >>
  pairarg_tac >> simp[] >>
  rpt (irule call_exn_safe_bind_invariant >>
       reverse conj_tac >- simp[call_exn_safe_memory, call_exn_safe_access,
         call_exn_safe_state_readers] >> gen_tac >> simp[]) >>
  pop_assum kall_tac >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[call_exn_safe_return] >>
      irule call_exn_safe_bind_invariant >>
      simp[call_exn_safe_access, call_exn_safe_return]) >>
  qx_gen_tac `code_cost` >> PairCases_on `code_cost` >> simp[] >>
  irule call_exn_safe_bind_invariant >> reverse conj_tac
  >- simp[call_exn_safe_context_readers] >>
  gen_tac >> simp[] >> pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `call_gas value gas available mem_cost costs` >>
  qmatch_goalsub_abbrev_tac `consume_gas charge` >>
  `stipend <= charge` by
    (`stipend <= dynamicGas + mem_cost` suffices_by simp[Abbr `charge`] >>
     irule call_gas_stipend_le_consumed >>
     goal_assum (drule_at Any) >>
     Cases_on `0 < value` >>
     simp[Abbr `costs`, call_stipend_def, call_value_cost_def] >>
     IF_CASES_TAC >> simp[] >> decide_tac) >>
  irule call_success_safe_bind_exn >>
  qexists_tac `\x s. s.contexts <> [] /\ stipend <= (FST (HD s.contexts)).gasUsed` >>
  reverse conj_tac
  >- (irule call_success_safe_consequence >>
      qexistsl_tac [`\s. s.contexts <> []`,
        `\x s. s.contexts <> [] /\ charge <= (FST (HD s.contexts)).gasUsed`] >>
      simp[call_success_safe_consume_gas] >> rpt strip_tac >> decide_tac) >>
  gen_tac >> simp[] >>
  irule call_success_safe_bind_exn >>
  qexists_tac `\x s. s.contexts <> [] /\ stipend <= (FST (HD s.contexts)).gasUsed` >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[call_success_safe_credit_context_effects,
         call_success_safe_credit_return]) >>
  gen_tac >> simp[] >>
  rpt (irule call_success_safe_bind_exn >>
       qexists_tac `\x s. s.contexts <> [] /\ stipend <= (FST (HD s.contexts)).gasUsed` >>
       reverse conj_tac >- simp[call_success_safe_credit_context_effects,
         call_success_safe_credit_readers] >> gen_tac >> simp[]) >>
  IF_CASES_TAC >- simp[call_exn_safe_abort_call_value] >>
  rpt (irule call_success_safe_bind_exn >>
       qexists_tac `\x s. s.contexts <> [] /\ stipend <= (FST (HD s.contexts)).gasUsed` >>
       reverse conj_tac >- simp[call_success_safe_credit_context_effects,
         call_success_safe_credit_readers] >> gen_tac >> simp[]) >>
  IF_CASES_TAC >- simp[call_exn_safe_abort_unuse] >>
  irule call_exn_safe_consequence >>
  qexistsl_tac [`\s. s.contexts <> []`, `\s. s.contexts <> []`] >>
  simp[call_exn_safe_proceed_call]
QED

Theorem call_exn_safe_step_inst[local]:
  call_exn_safe (\s. s.contexts <> []) (step_inst op) (\s. s.contexts <> [])
Proof
  Cases_on `is_call op` >- (Cases_on `op` >>
    gvs[is_call_def, step_inst_def, call_exn_safe_step_call, call_exn_safe_step_create]) >>
  simp[call_exn_safe_step_inst_noncall]
QED

Theorem call_exn_safe_step_inner[local]:
  call_exn_safe (\s. s.contexts <> []) step_inner (\s. s.contexts <> [])
Proof
  rewrite_tac[step_inner_def] >> irule call_exn_safe_bind_invariant >>
  reverse conj_tac >- simp[call_exn_safe_get_current_context] >>
  gen_tac >> simp[] >> BasicProvers.TOP_CASE_TAC
  >- (IF_CASES_TAC >> simp[call_exn_safe_step_inst]) >>
  rewrite_tac[ignore_bind_def] >> irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_step_inst, call_exn_safe_inc_pc_or_jump]
QED

Theorem step_inner_not_impossible_unimplemented[local]:
  s.contexts <> [] /\ step_inner s = (INR e,t) ==>
  e <> SOME Impossible /\ e <> SOME Unimplemented
Proof
  mp_tac call_exn_safe_step_inner >> simp[call_exn_safe_def] >> metis_tac[]
QED

Theorem step_inner_handler_state[local]:
  wf_state s /\ 2 <= LENGTH s.contexts /\ step_inner s = (r,t) ==>
  2 <= LENGTH t.contexts /\ EVERY (wf_context o FST) t.contexts /\
  stack_room_ok t /\ gas_stack_ok t
Proof
  rpt strip_tac
  >- (`s.contexts <> []` by (strip_tac >> gvs[]) >>
      `LENGTH s.contexts <= LENGTH t.contexts` by
        (`same_frame_or_grow step_inner` by simp[] >>
         drule_all same_frame_or_grow_length >> simp[]) >> decide_tac)
  >- (mp_tac decreases_gas_cred_step_inner >>
      simp[decreases_gas_cred_def] >>
      disch_then (qspec_then `s` mp_tac) >> gvs[wf_state_def])
  >- metis_tac[step_inner_preserves_stack_room_gas_ok]
  >> metis_tac[step_inner_preserves_stack_room_gas_ok]
QED

Theorem step_collect_ge2_inl[local]:
  wf_state s /\ s.msdomain = Collect dd /\ 2 <= LENGTH s.contexts /\
  step s = (r,t) ==> ISL r
Proof
  strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  `!x. r <> INR (SOME (OutsideDomain x))` by
    metis_tac[step_collect_not_outside] >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> gvs[] >>
  rename1 `step_inner s = (INR err, mid)` >> strip_tac >>
  `err <> SOME Impossible /\ err <> SOME Unimplemented` by
    metis_tac[step_inner_not_impossible_unimplemented] >>
  Cases_on `vfm_abort err`
  >- (gvs[handle_step_def, reraise_def] >>
      Cases_on `err` >> gvs[vfm_abort_def] >>
      Cases_on `x` >> gvs[vfm_abort_def] >> metis_tac[]) >>
  drule_all step_inner_handler_state >> strip_tac >>
  irule handle_step_not_abort_returns_inl >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem step_collect_ge2_not_abort[local]:
  wf_state s /\ s.msdomain = Collect dd /\ 2 <= LENGTH s.contexts /\
  step s = (r,t) ==> !e. r = INR e ==> ~vfm_abort e
Proof
  strip_tac >> drule_all step_collect_ge2_inl >> Cases_on `r` >> simp[]
QED

Theorem run_call_collect_inl[local]:
  wf_state es /\ es.msdomain = Collect dd /\ 2 <= LENGTH es.contexts /\
  run_call es = SOME (r,t) ==> ISL r
Proof
  strip_tac >>
  `(\p. ISL (FST p) /\ wf_state (SND p) /\
      ?d. (SND p).msdomain = Collect d) (r,t)` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  qexists_tac `\(r,s). ISL r /\ LENGTH es.contexts <= LENGTH s.contexts` >>
  qexists_tac `step o SND` >>
  qexists_tac `(INL () : unit + exception option,es)` >> simp[] >>
  reverse conj_tac >- fs[run_call_def, GREATER_EQ, UNCURRY] >>
  qx_gen_tac `st` >> PairCases_on `st` >> simp[] >> strip_tac >>
  Cases_on `step st1` >> simp[] >>
  `2 <= LENGTH st1.contexts` by decide_tac >>
  conj_tac >- metis_tac[step_collect_ge2_inl] >>
  conj_tac >- (drule step_preserves_wf_state >> simp[]) >>
  irule step_preserves_collect >> metis_tac[]
QED

Theorem run_call_collect_returns[local]:
  wf_state es /\ es.msdomain = Collect dd /\ 2 <= LENGTH es.contexts ==>
  ?es' dd'. run_call es = SOME (INL (),es') /\
    LENGTH es'.contexts + 1 = LENGTH es.contexts /\ es'.msdomain = Collect dd'
Proof
  strip_tac >>
  Cases_on `run_call_tr (LENGTH es.contexts) (step es)` >>
  `run_call es = SOME (q,r)` by simp[run_call_eq_tr] >>
  `ISL q` by metis_tac[run_call_collect_inl] >>
  Cases_on `q` >> gvs[] >>
  drule_all run_call_inl_length >>
  drule_all run_call_preserves_collect >> metis_tac[]
QED

(* run_call_finite_trace already provides the reusable finite-steps interface. *)
Theorem run_call_last_step[local]:
  run_call es = SOME (INL (),t) ==>
  ?n before. FUNPOW (step o SND) n (INL (),es) = (INL (),before) /\
    run_call_reaches es before /\ LENGTH es.contexts <= LENGTH before.contexts /\
    step before = (INL (),t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  Cases_on `n`
  >- gvs[] >>
  rename1 `FUNPOW (step o SND) (SUC n) _ = _` >>
  `ISL (FST (FUNPOW (step o SND) n (INL (),es))) /\
    LENGTH es.contexts <= LENGTH (SND (FUNPOW (step o SND) n (INL (),es))).contexts`
    by (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `run_call_reaches es (SND (FUNPOW (step o SND) n (INL (),es)))` by
    (irule run_call_trace_reaches >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`n`, `SND (FUNPOW (step o SND) n (INL (),es))`] >>
  gvs[FUNPOW_SUC] >>
  Cases_on `FUNPOW (step o SND) n (INL (),es)` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem run_call_last_pop[local]:
  wf_state es /\ run_call es = SOME (INL (),t) ==>
  ?n before err mid.
    FUNPOW (step o SND) n (INL (),es) = (INL (),before) /\
    run_call_reaches es before /\ wf_state before /\
    LENGTH before.contexts = LENGTH es.contexts /\
    TL before.contexts = TL es.contexts /\
    t.txParams = es.txParams /\ step before = (INL (),t) /\
    step_inner before = (INR err,mid) /\ handle_step err mid = (INL (),t)
Proof
  strip_tac >> drule run_call_last_step >> strip_tac >>
  `wf_state before` by metis_tac[run_call_reaches_wf_state] >>
  `LENGTH t.contexts + 1 = LENGTH es.contexts` by
    metis_tac[run_call_inl_length] >>
  `LENGTH before.contexts <= LENGTH t.contexts + 1` by
    metis_tac[step_length_not_drop_more_than_one] >>
  `LENGTH before.contexts = LENGTH es.contexts` by decide_tac >>
  `TL before.contexts = TL es.contexts` by
    (drule_all run_call_reaches_outer_contexts >> simp[] >>
     Cases_on `before.contexts` >> gvs[]) >>
  `before.txParams = es.txParams` by
    (`(\s. s.txParams = es.txParams) before` suffices_by simp[] >>
     irule run_call_reaches_inv >> qexists_tac `es` >> simp[] >>
     rpt strip_tac >>
     metis_tac[vfmTxParamsTheory.step_preserves_txParams, SND]) >>
  `t.txParams = es.txParams` by
    metis_tac[vfmTxParamsTheory.step_preserves_txParams, SND] >>
  qpat_x_assum `step before = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner before` >> Cases_on `q` >> simp[]
  >- (strip_tac >> gvs[] >>
      `same_frame_or_grow step_inner` by simp[] >>
      `before.contexts <> []` by gvs[wf_state_def] >>
      drule_all same_frame_or_grow_length >> simp[]) >>
  strip_tac >> qexistsl_tac [`n`, `before`, `y`, `r`] >>
  simp[GSYM step_eq_handle_step_inner]
QED

Theorem handle_step_noncode_inl[local]:
  s.contexts ≠ [] ∧
  (∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a) ∧
  handle_step e s = (INL (),t) ⇒
  handle_exception e s = (INL (),t)
Proof
  strip_tac >> qpat_x_assum `handle_step e s = _` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC >- simp[reraise_def] >>
  simp[handle_def] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises) >>
  disch_then (fn th => rewrite_tac[th]) >> simp[reraise_def]
QED

Theorem step_inner_final_pop_frame[local]:
  wf_state s ∧ step_inner s = (INR err,mid) ∧
  handle_step err mid = (INL (),t) ∧
  LENGTH t.contexts + 1 = LENGTH s.contexts ⇒
  same_frame_rel s mid ∧ EVERY (wf_context o FST) mid.contexts ∧
  stack_room_ok mid ∧ gas_stack_ok mid
Proof
  strip_tac >>
  `s.contexts ≠ []` by fs[wf_state_def] >>
  `same_frame_or_grow step_inner` by simp[] >>
  `LENGTH s.contexts ≤ LENGTH mid.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `mid.contexts ≠ []` by
    (Cases_on `mid.contexts` >> simp[] >>
     qpat_x_assum `LENGTH s.contexts ≤ _` mp_tac >> simp[] >>
     Cases_on `s.contexts` >> fs[]) >>
  `LENGTH mid.contexts = LENGTH s.contexts` by
    (drule_all handle_step_shrinks_by_one >> strip_tac >> decide_tac) >>
  conj_tac >- (drule_all same_frame_or_grow_eq_length >> simp[]) >>
  conj_tac
  >- (mp_tac decreases_gas_cred_step_inner >>
      simp[decreases_gas_cred_def] >>
      disch_then (qspec_then `s` mp_tac) >> simp[] >> fs[wf_state_def]) >>
  metis_tac[step_inner_preserves_stack_room_gas_ok]
QED

Theorem call_memory_final_pop[local]:
  wf_state es ∧ es.contexts = (callee,saved)::(caller,cb)::rest ∧
  callee.msgParams.outputTo = Memory mr ∧ run_call_reaches es before ∧
  LENGTH before.contexts = LENGTH es.contexts ∧
  TL before.contexts = TL es.contexts ∧
  step_inner before = (INR err,mid) ∧ handle_step err mid = (INL (),t) ∧
  LENGTH t.contexts + 1 = LENGTH es.contexts ⇒
  ∃cc gasLeft out.
    mid.contexts = (cc,saved)::(caller,cb)::rest ∧
    cc.msgParams = callee.msgParams ∧
    gasLeft = (if err = NONE ∨ err = SOME Reverted then
      cc.msgParams.gasLimit - cc.gasUsed else 0) ∧
    out = (if err = NONE ∨ err = SOME Reverted then cc.returnData else []) ∧
    gasLeft ≤ callee.msgParams.gasLimit ∧
    t.contexts = (caller with <|
      stack := b2w (err = NONE) :: caller.stack;
      pc := SUC caller.pc; gasUsed := caller.gasUsed - gasLeft;
      memory := buffer_write mr.offset (TAKE mr.size out) caller.memory;
      returnData := out;
      logs := caller.logs ++ (if err = NONE then cc.logs else []);
      addRefund := caller.addRefund + (if err = NONE then cc.addRefund else 0);
      subRefund := caller.subRefund + (if err = NONE then cc.subRefund else 0)
    |>,cb)::rest ∧
    t.rollback = (if err = NONE then mid.rollback else saved)
Proof
  strip_tac >>
  `2 ≤ LENGTH es.contexts` by simp[] >>
  `wf_state before` by metis_tac[run_call_reaches_wf_state] >>
  `LENGTH t.contexts + 1 = LENGTH before.contexts` by decide_tac >>
  drule_all step_inner_final_pop_frame >> strip_tac >>
  `SND (HD before.contexts) = saved ∧
   (FST (HD before.contexts)).msgParams = callee.msgParams` by
    (drule_all run_call_reaches_root_metadata >> simp[]) >>
  `SND (HD mid.contexts) = saved ∧
   (FST (HD mid.contexts)).msgParams = callee.msgParams ∧
   TL mid.contexts = (caller,cb)::rest ∧ mid.contexts ≠ []` by
    (fs[same_frame_rel_def] >> Cases_on `mid.contexts` >> fs[]) >>
  `mid.contexts = (FST (HD mid.contexts),saved)::(caller,cb)::rest` by
    (Cases_on `mid.contexts` >- fs[] >> PairCases_on `h` >> fs[]) >>
  suspend "memory_equation"
QED

Resume call_memory_final_pop[memory_equation]:
  qmatch_asmsub_abbrev_tac `mid.contexts = (cc,saved)::(caller,cb)::rest` >>
  `cc.msgParams = callee.msgParams` by simp[Abbr `cc`] >>
  `cc.gasUsed ≤ cc.msgParams.gasLimit ∧ LENGTH caller.stack < stack_limit` by
    fs[wf_context_def, stack_room_ok_def] >>
  `cc.msgParams.gasLimit - cc.gasUsed ≤ caller.gasUsed` by
    (fs[gas_stack_ok_def] >> first_x_assum (qspec_then `0` mp_tac) >>
     simp[unused_gas_def]) >>
  `(∀a. (FST (HD mid.contexts)).msgParams.outputTo ≠ Code a)` by simp[] >>
  `cc.msgParams.outputTo = Memory mr` by simp[] >>
  drule_all handle_step_noncode_inl >>
  drule_all handle_exception_memory_return >>
  disch_then (fn th => rewrite_tac[th]) >> simp[LET_THM] >> strip_tac >>
  qpat_x_assum `_ = t` (SUBST1_TAC o SYM) >>
  Cases_on `err = NONE ∨ err = SOME Reverted` >> simp[]
QED

Finalise call_memory_final_pop

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
  simp[proceed_call_def, get_rollback_def, read_memory_def,
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
     irule call_stipend_prefix_push >> simp[Abbr `child`, initial_context_def, initial_msg_params_def]) >>
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
  (0 < value ==> call_value_cost <= oc) /\
  (!cg s r t. value = 0 /\ cg <= call_stipend /\
    call_stipend_prefix n A D oa s /\ suffix cg s = (r,t) ==>
    call_stipend_prefix n A D oa t) ==>
  !s r t. call_stipend_prefix n A D oa s /\
    bind get_gas_left (\left.
      let (dg,cg) = call_gas value gas left mc oc in
        bind (consume_gas (sc + dg + mc)) (\u. suffix cg)) s = (r,t) ==>
    call_stipend_prefix n A D oa t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule call_stipend_prefix_head >> strip_tac >>
  qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[get_gas_left_def, get_current_context_def, bind_def, return_def] >>
  Cases_on `call_gas value gas
    ((FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed) mc oc` >>
  rename1 `call_gas value gas _ mc oc = (dg,cg)` >>
  simp[bind_def] >>
  Cases_on `consume_gas (dg + (mc + sc)) s` >>
  rename1 `consume_gas _ s = (res,mid)` >>
  `call_stipend_prefix n A D oa mid` by
    (irule (INST_TYPE [alpha |-> ``:unit``] cp_preserves_stipend_prefix) >>
     qexistsl_tac [`consume_gas (dg + (mc + sc))`, `res`, `s`] >> simp[]) >>
  Cases_on `res` >> simp[]
  >- (Cases_on `x` >>
      drule_all consume_gas_affordable >> strip_tac >>
      `value = 0 /\ cg <= call_stipend` by
        (`value = 0 /\ cg <=
          (FST (HD s.contexts)).msgParams.gasLimit -
          (FST (HD s.contexts)).gasUsed` suffices_by simp[] >>
         irule call_gas_stipend_budget >>
         conj_tac >- decide_tac >>
         qexistsl_tac [`dg`, `gas`, `mc`, `oc`, `sc`] >> simp[] >> decide_tac) >>
      strip_tac >> metis_tac[]) >>
  strip_tac >> gvs[]
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
  ho_match_mp_tac (SRULE [LET_THM, AC ADD_ASSOC ADD_COMM] call_stipend_prefix_call_charge) >>
  conj_tac >- (strip_tac >> simp[] >> IF_CASES_TAC >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
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

Theorem handle_exception_memory_footprint[local]:
  call_footprint A D oa s /\
  s.contexts = (callee,saved)::(caller,callerSaved)::rest /\
  callee.msgParams.outputTo = Memory r /\
  callee.gasUsed <= callee.msgParams.gasLimit /\
  callee.msgParams.gasLimit - callee.gasUsed <= caller.gasUsed /\
  LENGTH caller.stack < stack_limit /\ handle_exception e s = (res,t) ==>
  t.originalAccounts = oa /\
  (e = NONE ==> t.rollback.accounts = A /\ t.rollback.toDelete = D) /\
  (e <> NONE ==> t.rollback = saved)
Proof
  strip_tac >> drule_all handle_exception_memory_return >>
  Cases_on `e = NONE` >> simp[LET_THM] >> strip_tac >> gvs[call_footprint_def]
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
  call_stipend_prefix n A D oa s /\ handle_step e s = (res,t) ==>
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
  `h0.gasUsed <= h0.msgParams.gasLimit /\ LENGTH h'0.stack < stack_limit` by
    (fs[wf_context_def, stack_room_ok_def]) >>
  `h0.msgParams.gasLimit - h0.gasUsed <= h'0.gasUsed` by
    (fs[gas_stack_ok_def] >> first_x_assum (qspec_then `0` mp_tac) >>
     simp[unused_gas_def]) >>
  drule_all handle_exception_memory_return >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[LET_THM] >> strip_tac >>
  irule call_stipend_prefix_pop >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `_ = t` (assume_tac o SYM) >>
  goal_assum (drule_at Any) >> simp[]
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

Theorem step_inner_preserves_stipend_prefix:
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

Theorem step_preserves_stipend_prefix:
  wf_state s /\ call_stipend_prefix n A D oa s /\ step s = (r,t) ==>
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

Theorem run_call_stipend_originalAccounts:
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
  drule run_call_last_step >> strip_tac >>
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
  drule_all handle_step_noncode_inl >>
  Cases_on `s.contexts` >- fs[] >>
  rename1 `s.contexts = calleePair::cs` >>
  Cases_on `cs` >- fs[] >>
  PairCases_on `calleePair` >> PairCases_on `h` >>
  gvs[] >> Cases_on `calleePair0.msgParams.outputTo` >> gvs[] >>
  `calleePair0.gasUsed ≤ calleePair0.msgParams.gasLimit ∧
   LENGTH h0.stack < stack_limit` by
    (fs[wf_context_def, stack_room_ok_def]) >>
  `calleePair0.msgParams.gasLimit - calleePair0.gasUsed ≤ h0.gasUsed` by
    (fs[gas_stack_ok_def] >> first_x_assum (qspec_then `0` mp_tac) >>
     simp[unused_gas_def]) >>
  drule_all handle_exception_memory_return >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[LET_THM] >> strip_tac >> gvs[]
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
  drule_all run_call_last_pop >> strip_tac >>
  qexistsl_tac [`n`,`before`,`err`,`mid`] >> simp[] >>
  `2 ≤ LENGTH es.contexts` by simp[] >>
  `SND (HD before.contexts) = saved ∧
   (FST (HD before.contexts)).msgParams = callee.msgParams` by
    (drule_all run_call_reaches_root_metadata >> simp[]) >>
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
  drule_all step_inner_final_pop_frame >> strip_tac >>
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

Theorem FUNPOW_guarded_prefix:
  ∀stop f n x. (∀i. i < n ⇒ ¬stop (FUNPOW f i x)) ⇒
  FUNPOW (λx. if stop x then x else f x) n x = FUNPOW f n x
Proof
  Induct_on `n` >- simp[] >> rpt gen_tac >> strip_tac >>
  `∀i. i < n ⇒ ¬stop (FUNPOW f i x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `¬stop (FUNPOW f n x)` by
    (qpat_x_assum `∀i. i < SUC n ⇒ _` (qspec_then `n` mp_tac) >> simp[]) >>
  simp[FUNPOW_SUC]
QED

Theorem guarded_steps_preserve_wf:
  ∀n r. wf_state (SND r) ⇒
  wf_state (SND (FUNPOW
    (λr. if ISR (FST r) then r else step (SND r)) n r))
Proof
  Induct_on `n` >- simp[] >> gen_tac >> strip_tac >>
  simp[FUNPOW_SUC] >> IF_CASES_TAC >> simp[] >>
  metis_tac[step_preserves_wf_state]
QED

Theorem run_call_guarded_trace[local]:
  wf_state es ∧ run_call es = SOME (INL (),t) ⇒
  ∃k. FUNPOW (λr. if ISR (FST r) then r else step (SND r))
    k (INL (),es) = (INL (),t) ∧ wf_state t
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  `∀i. i < n ⇒ ¬ISR (FST (FUNPOW (step o SND) i (INL (),es)))` by
    (gen_tac >> disch_tac >> first_x_assum drule >>
     Cases_on `FST (FUNPOW (step o SND) i (INL (),es))` >> simp[]) >>
  `FUNPOW (λr. if ISR (FST r) then r else step (SND r)) n (INL (),es) =
    FUNPOW (step o SND) n (INL (),es)` by
    (qspecl_then [`ISR o FST`, `step o SND`, `n`, `(INL (),es)`]
       mp_tac FUNPOW_guarded_prefix >> simp[]) >>
  qexists_tac `n` >> simp[] >>
  qspecl_then [`n`, `(INL (),es)`] mp_tac guarded_steps_preserve_wf >> simp[]
QED

(* Shared entered-CALL return interface, including the conditional stipend frame. *)
Theorem run_call_memory_returns[local]:
  wf_state es ∧ es.contexts = (callee,saved)::(caller,cb)::rest ∧
  es.msdomain = Collect dd ∧ callee.msgParams.outputTo = Memory mr ⇒
  ∃k t dd' cc gasLeft out success.
    FUNPOW (λr. if ISR (FST r) then r else step (SND r))
      k (INL (),es) = (INL (),t) ∧ wf_state t ∧
    t.msdomain = Collect dd' ∧ t.txParams = es.txParams ∧
    gasLeft ≤ callee.msgParams.gasLimit ∧
    t.contexts = (caller with <|
      stack := b2w success :: caller.stack;
      pc := SUC caller.pc; gasUsed := caller.gasUsed - gasLeft;
      memory := buffer_write mr.offset (TAKE mr.size out) caller.memory;
      returnData := out;
      logs := caller.logs ++ (if success then cc.logs else []);
      addRefund := caller.addRefund + (if success then cc.addRefund else 0);
      subRefund := caller.subRefund + (if success then cc.subRefund else 0)
    |>,cb)::rest ∧
    (¬success ⇒ t.rollback = saved) ∧
    (callee.msgParams.gasLimit ≤ call_stipend ⇒
      t.originalAccounts = es.originalAccounts ∧
      (success ⇒ t.rollback.accounts = es.rollback.accounts ∧
                  t.rollback.toDelete = es.rollback.toDelete))
Proof
  strip_tac >>
  `2 ≤ LENGTH es.contexts` by simp[] >>
  drule_all run_call_collect_returns >> strip_tac >>
  `∃n before err mid.
    FUNPOW (step o SND) n (INL (),es) = (INL (),before) ∧
    run_call_reaches es before ∧ wf_state before ∧
    LENGTH before.contexts = LENGTH es.contexts ∧
    TL before.contexts = TL es.contexts ∧ es'.txParams = es.txParams ∧
    step before = (INL (),es') ∧ step_inner before = (INR err,mid) ∧
    handle_step err mid = (INL (),es') ∧
    (callee.msgParams.gasLimit ≤ call_stipend ⇒
      es'.originalAccounts = es.originalAccounts ∧
      (err = NONE ⇒ es'.rollback.accounts = es.rollback.accounts ∧
                     es'.rollback.toDelete = es.rollback.toDelete))` by
    (Cases_on `callee.msgParams.gasLimit ≤ call_stipend`
     >- (drule run_call_stipend_footprint >>
         disch_then (qspecl_then [`es'`,`saved`,`(caller,cb)::rest`,`callee`] mp_tac) >>
         simp[] >> strip_tac >>
         qexistsl_tac [`n`,`before`,`err`,`mid`] >> simp[] >>
         Cases_on `err = NONE` >> gvs[])
     >> drule_all run_call_last_pop >> metis_tac[]) >>
  drule_all call_memory_final_pop >> strip_tac >>
  drule_all run_call_guarded_trace >> strip_tac >>
  qexistsl_tac [`k`,`es'`,`dd'`,`cc`,`gasLeft`,`out`,`err = NONE`] >>
  simp[] >> metis_tac[]
QED

(* The entry normalization is supplied by call_entry_prepared; caller is the
   charged, expanded, argument-popped caller.  Both entry failures have the
   same abort_call_value result, so they share a single branch here. *)
Theorem call_returns_summary[local]:
  wf_state s ∧ s.contexts = (c,cb)::cs ∧
  FLOOKUP c.msgParams.parsed c.pc = SOME op ∧
  is_call op ∧ op ≠ Create ∧ op ≠ Create2 ∧
  prepared = s with <|contexts := (caller,cb)::cs;
                         rollback := saved; msdomain := Collect dd|> ∧
  cg ≤ caller.gasUsed ∧ LENGTH caller.stack < stack_limit ∧
  ¬fIN addr precompile_addresses ∧
  step_call op s =
    (if failed then abort_call_value cg prepared
     else ignore_bind (set_return_data [])
       (proceed_call op sender addr value ao az code cg (Memory mr)) prepared) ⇒
  ∃k t dd' cc gasLeft out success.
    FUNPOW (λr. if ISR (FST r) then r else step (SND r))
      k (INL (),s) = (INL (),t) ∧ wf_state t ∧
    t.msdomain = Collect dd' ∧ t.txParams = s.txParams ∧
    gasLeft ≤ cg ∧
    t.contexts = (caller with <|
      stack := b2w success :: caller.stack;
      pc := SUC caller.pc; gasUsed := caller.gasUsed - gasLeft;
      memory := buffer_write mr.offset (TAKE mr.size out) caller.memory;
      returnData := out;
      logs := caller.logs ++ (if success then cc.logs else []);
      addRefund := caller.addRefund + (if success then cc.addRefund else 0);
      subRefund := caller.subRefund + (if success then cc.subRefund else 0)
    |>,cb)::cs ∧
    (¬success ⇒ t.rollback = saved) ∧
    (cg ≤ call_stipend ⇒
      t.originalAccounts = s.originalAccounts ∧
      (success ⇒
        t.rollback.accounts =
          (if op ≠ CallCode ∧ 0 < value then
             transfer_value sender addr value saved.accounts else saved.accounts) ∧
        t.rollback.toDelete = saved.toDelete))
Proof
  strip_tac >>
  `prepared.contexts = (caller,cb)::cs` by simp[] >>
  Cases_on `failed`
  >- (drule_all call_abort_pair >> simp[LET_THM] >> strip_tac >>
      `step s = abort_call_value cg prepared` by
        (simp[] >> irule step_call_success_dispatch >> metis_tac[]) >>
      `wf_state (SND (abort_call_value cg prepared))` by
        metis_tac[step_preserves_wf_state] >>
      qexistsl_tac [`1`,`SND (abort_call_value cg prepared)`,`dd`,
                    `caller`,`cg`,`[]`,`F`] >>
      simp[FUNPOW_1, context_component_equality]) >>
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
    `(callee,cleared.rollback)::(caller with returnData := [],cb)::cs` >>
  `entry.contexts = (callee,saved)::(caller with returnData := [],cb)::cs ∧
   entry.msdomain = Collect dd ∧ callee.msgParams.outputTo = Memory mr ∧
   callee.msgParams.gasLimit = cg` by
    simp[Abbr `entry`, Abbr `cleared`, Abbr `callee`,
         initial_context_def, initial_msg_params_def] >>
  `entry.txParams = s.txParams ∧ entry.originalAccounts = s.originalAccounts ∧
   entry.rollback.toDelete = saved.toDelete ∧
   entry.rollback.accounts =
     (if op ≠ CallCode ∧ 0 < value then
        transfer_value sender addr value saved.accounts else saved.accounts)` by
    (simp[Abbr `entry`, Abbr `cleared`] >>
     Cases_on `op ≠ CallCode ∧ 0 < value` >> simp[]) >>
  drule_all run_call_memory_returns >> strip_tac >>
  qexistsl_tac [`SUC k`,`t`,`dd'`,`cc`,`gasLeft`,`out`,`success`] >>
  qpat_x_assum `Abbrev (entry = _)` kall_tac >>
  qpat_x_assum `Abbrev (cleared = _)` kall_tac >>
  qpat_x_assum `Abbrev (callee = _)` kall_tac >>
  simp[FUNPOW, context_component_equality] >>
  metis_tac[]
QED

Finalise call_returns_summary

(* Strengthened in place: the pure entry interface now returns the caller.
   The implementation-level entry equation is proved only in the suspended
   normalization block, not re-unfolded by either SPEC consumer. *)
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
  call_gas value gas (c.msgParams.gasLimit-c.gasUsed) mc
    (access_cost s.rollback addr + (if 0 < value then call_value_cost else 0) +
     (if op = Call ∧ 0 < value ∧ account_empty ta then new_account_cost else 0) + dc)
    = (dg,cg) ∧
  c.gasUsed + (static_gas op + dg + mc) ≤ c.msgParams.gasLimit ∧
  (0 < value ⇒ ¬c.msgParams.static) ∧
  caller = c with <|stack := DROP (6+v) c.stack;
    gasUsed := c.gasUsed + (static_gas op + dg + mc);
    memory := expanded_memory c.memory offset sz|> ∧
  prepared = s with <|rollback := rb'; msdomain := dom';
                      contexts := (caller,cb)::cs|> ⇒
  ∃k t dd' cc gasLeft out success.
    FUNPOW (λr. if ISR (FST r) then r else step (SND r))
      k (INL (),s) = (INL (),t) ∧ wf_state t ∧
    t.msdomain = Collect dd' ∧ t.txParams = s.txParams ∧ gasLeft ≤ cg ∧
    t.contexts = (caller with <|
      stack := b2w success :: caller.stack;
      pc := SUC caller.pc; gasUsed := caller.gasUsed - gasLeft;
      memory := buffer_write ro (TAKE rz out) caller.memory; returnData := out;
      logs := caller.logs ++ (if success then cc.logs else []);
      addRefund := caller.addRefund + (if success then cc.addRefund else 0);
      subRefund := caller.subRefund + (if success then cc.subRefund else 0)
    |>,cb)::cs ∧
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
    then abort_call_value cg prepared
    else ignore_bind (set_return_data [])
      (if LENGTH s.contexts > 1024 then abort_unuse cg
       else proceed_call op c.msgParams.callee addr value ao az
         (case get_delegate ta.code of NONE => ta.code
          | SOME a => (lookup_account a s.rollback.accounts).code)
         cg (Memory <|offset := ro; size := rz|>)) prepared` by
    suspend "normalize_entry" >>
  suspend "compose_entry"
QED

Resume call_entry_prepared[normalize_entry]:
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
    LET_THM, get_static_def] >>
  Cases_on `op = Call /\ 0 < value` >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def,
    get_current_context_def, get_static_def, assert_def, fail_def,
    set_current_context_def, get_num_contexts_def, LET_THM] >>
  asm_x "prepared" assume_tac >>
  asm_simp_tac (srw_ss()) [expanded_memory_def,
    bind_def, ignore_bind_def, return_def, set_return_data_def,
    get_current_context_def, set_current_context_def, get_num_contexts_def,
    LET_THM] >>
  Cases_on `(lookup_account c.msgParams.callee s.rollback.accounts).balance < value` >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, return_def,
    get_current_context_def, set_current_context_def, get_num_contexts_def]
QED

Resume call_entry_prepared[compose_entry]:
  `∃dd1. dom' = Collect dd1 ∧ rb'.accounts = s.rollback.accounts ∧
    rb'.toDelete = s.rollback.toDelete` by
    (qpat_x_assum `delegate_check _ _ _ _ _ _` mp_tac >>
     simp[msdomain_add_def] >> strip_tac >>
     drule delegate_check_collect_frame >> simp[accesses_add_def]) >>
  `cg ≤ dg + mc` by (drule call_gas_charged_bound >> simp[]) >>
  `cg ≤ caller.gasUsed` by simp[] >>
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
  drule_all call_returns_summary >>
  strip_tac >> qexistsl_tac [`k`,`t`,`dd'`,`cc`,`gasLeft`,`out`,`success`] >>
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

(* Why SPEC_Call_any holds (notes for the proof; ignore freely):
   - EVM_SPEC_SEMANTICS checks the frame only at the state it picks, so
     the proof may pick the state right after the callee's frame pops
     (contexts back to the caller's length), FUNPOW steps after the
     start; vfmProg's one-step IMP_EVM_SPEC_LEMMA needs a many-step twin.
   - The CALL step itself ends in one of three states, already pinned
     down by SPEC_Call_fail_balance, SPEC_Call_fail_depth and SPEC_Call
     in vfmProg: the two fail states are already the final state
     (success = F, out = [], gasLeft = calleeGas).
   - From the callee's entry state, run_call always terminates
     (run_call_eq_tr).  An INR result there would be an abort
     (run_call_inr_requires_abort_ge2); under Collect no step aborts:
     OutsideDomain needs Enforce, Unimplemented is never raised, and
     Impossible needs empty contexts, an unuse_gas overrun (ruled out by
     gas_stack_ok in wf_state) or the dispatch_precompiles fallback.
     The domain stays Collect (set_domain only adds to a Collect set).
   - So run_call ends INL at the caller's depth, and the last step is the
     callee's pop: handle_exception / pop_and_incorporate_context with
     outputTo = Memory, which writes the caller's stack, pc, memory,
     return data, gas, logs and refunds as in the postcondition.  The
     contexts below are untouched (run_call_reaches_outer_contexts),
     and txParams too (run_call_preserves_txParams).
   - gasLeft ≤ calleeGas: the callee's gasLimit is calleeGas and its
     gasUsed only grows.
   For SPEC_Call_stipend, the extra fact is an invariant over the
   callee's run in the style of run_call_static_frame in
   vfmAccountFrame: every frame above the caller has gas left ≤
   call_stipend and outputTo = Memory, and rollback.accounts and
   toDelete stay at their value just after the CALL's transfer.  An
   SSTORE fails its sentry (call_stipend < gas left), a CALL/CALLCODE
   with value needs call_value_cost = 9000, SELFDESTRUCT 5000 and CREATE
   32000 static gas, all charged before any account write; nested
   calls get at most the parent's gas left. *)

(* CALL to any code at a non-precompile, in a Collect domain (the
   default; an Enforce domain can abort the callee).  The precondition is
   SPEC_Call's without the balance and depth checks: when those fail the
   CALL returns 0 at once, which the postcondition covers. The callee's
   CREATEs reset accounts in originalAccounts, so the rule owns it. *)
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
  simp[STAR_evm2set, STAR_evm_OriginalAccounts, GSYM STAR_ASSOC] >>
  qmatch_goalsub_abbrev_tac `evm2set_on rest _` >>
  `rest = {}` by
    (qunabbrev_tac `rest` >>
     qpat_x_assum `_ = {HasParsed c.pc}` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> SET_TAC[]) >>
  simp[cond_def, evm2set_on_def];

val call_spec_frame_tac =
  sym_tac >> irule caller_observation_frame >> simp[];

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
