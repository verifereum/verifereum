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
