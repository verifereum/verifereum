(* CALL to arbitrary code, as one SPEC step for the caller: control comes
   back to the caller's frame with the callee's effects confined to the
   rollback state, logs and refunds. *)
Theory vfmProgCall
Ancestors
  vfmProg vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmDecreasesGas vfmRunCall vfmContextLength vfmAccountFrame vfmStaticCalls
  vfmRunWithinFrame vfmSameFrame vfmDomainCollection
  vfmTypes vfmBuffer
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

Theorem call_entry_prepared[local]:
  s.contexts = (c,cb)::cs /\
  6 + v <= LENGTH c.stack /\
  v = (if call_has_value op then 1 else 0) /\
  w2n (EL 0 c.stack) = gas /\ w2w (EL 1 c.stack) = addr /\
  (if 0 < v then w2n (EL 2 c.stack) else 0) = value /\
  w2n (EL (v+2) c.stack) = ao /\ w2n (EL (v+3) c.stack) = az /\
  w2n (EL (v+4) c.stack) = ro /\ w2n (EL (v+5) c.stack) = rz /\
  max_expansion_range (ao,az) (ro,rz) = (offset,sz) /\
  lookup_account addr s.rollback.accounts = ta /\
  access_check s.msdomain addr /\
  delegate_check ta.code (msdomain_add addr s.msdomain)
    (accesses_add addr s.rollback) dc rb' dom' /\
  memory_cost c.memory offset sz = mc /\
  call_gas value gas (c.msgParams.gasLimit-c.gasUsed) mc
    (access_cost s.rollback addr + (if 0 < value then call_value_cost else 0) +
     (if op = Call /\ 0 < value /\ account_empty ta then new_account_cost else 0) + dc)
    = (dg,cg) /\
  c.gasUsed + (static_gas op + dg + mc) <= c.msgParams.gasLimit /\
  (0 < value ==> ~c.msgParams.static) /\
  prepared = s with <|rollback := rb'; msdomain := dom'; contexts :=
    (c with <|stack := DROP (6+v) c.stack;
      gasUsed := c.gasUsed + (static_gas op + dg + mc);
      memory := expanded_memory c.memory offset sz|>,cb)::cs|> ==>
  step_call op s =
    if (lookup_account c.msgParams.callee s.rollback.accounts).balance < value
    then abort_call_value cg prepared
    else ignore_bind (set_return_data [])
      (if LENGTH s.contexts > 1024 then abort_unuse cg
       else proceed_call op c.msgParams.callee addr value ao az
         (case get_delegate ta.code of NONE => ta.code
          | SOME a => (lookup_account a s.rollback.accounts).code)
         cg (Memory <|offset := ro; size := rz|>)) prepared
Proof
  strip_tac >>
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

Theorem call_exn_safe_bind_probe[local]:
  call_exn_safe (\s:execution_state. T) (fail Reverted : execution_state -> unit execution_result)
    (\s. T) /\
  (!x:unit. call_exn_safe (\s:execution_state. T)
    (\s. (INL (),s with contexts := [])) (\s. s.contexts = [])) /\
  ~call_exn_safe (\s:execution_state. T)
    (bind (fail Reverted : execution_state -> unit execution_result)
      (\x:unit. \s. (INL (),s with contexts := [])))
    (\s. s.contexts = [])
Proof
  simp[call_exn_safe_def, fail_def, bind_def] >>
  qexists_tac `ARB with contexts := [(ARB,ARB)]` >> simp[]
QED

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

Theorem call_exn_safe_bind_positive_probe[local]:
  call_exn_safe P (bind (fail Reverted) (\x:unit. return x)) P
Proof
  irule call_exn_safe_bind_invariant >>
  simp[call_exn_safe_fail, call_exn_safe_return]
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
  cheat
QED

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
  cheat
QED
