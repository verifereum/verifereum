(* CALL to arbitrary code, as one SPEC step for the caller: control comes
   back to the caller's frame with the callee's effects confined to the
   rollback state, logs and refunds. *)
Theory vfmProgCall
Ancestors
  vfmProg vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmDecreasesGas vfmRunCall vfmContextLength vfmAccountFrame vfmStaticCalls
  vfmRunWithinFrame vfmSameFrame
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
