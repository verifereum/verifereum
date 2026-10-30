(*
 * Handle-step layer lemmas.
 *
 * `handle_step` wraps `handle_create` and `handle_exception`, and is
 * invoked by `step` when the inner monad returns an exception. This
 * theory collects:
 *
 *   - `psf_handle_create`: under `outputTo_consistent`, handle_create
 *     stays in-frame.
 *   - `handle_exception_same_frame`: when handle_exception preserves
 *     the contexts-stack length (i.e. takes the n ≤ 1 reraise branch,
 *     not a pop), its result is `same_frame_rel`-related to the
 *     input.
 *   - `handle_step_same_frame`: the combined result for handle_step.
 *   - tiny state-effect lemmas for `set_rollback`, `pop_context`,
 *     `push_context`.
 *   - `pop_and_incorporate_context_failure_effect`: exact state
 *     shape after the failure pop.
 *   - `handle_exception_pop_{success,failure}_memory_effect[_gen]`
 *     and the corresponding `handle_step_pop_*` lemmas: the state-
 *     shape conclusions used by downstream INR-grow-then-pop
 *     reasoning (specialised and generalised variants).
 *
 * The pop-effect lemmas deliberately do not mention `msdomain`;
 * msdomain preservation is handled separately in
 * `vfmMsdomainPreserved`.
 *)
Theory vfmHandleStep
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmStoragePredicates vfmSameFrame vfmDecreasesGas
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

(* ---------------- handle_create ---------------- *)

(* Under outputTo_consistent, handle_create's code-install branch
   writes at the callee (because outputTo = Code address implies
   callee = address), which is a callee-local change permitted by
   same_frame_rel. *)
Theorem psf_handle_create:
  psf outputTo_consistent (handle_create e)
Proof
  rw[psf_def, handle_create_def, bind_def,
     get_return_data_def, get_output_to_def,
     get_current_context_def, return_def, charge_state_gas_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `e`
  >- (
    (* e = NONE *)
    Cases_on `h0.msgParams.outputTo` \\ gvs[reraise_def]
    >- (
      (* outputTo = Memory — reraise *)
      irule same_frame_rel_refl \\ simp[])
    >- (
      (* outputTo = Code c — install code at c *)
      gvs[ignore_bind_def, bind_def, assert_def, return_def,
          fail_def, AllCaseEqs(), consume_gas_def,
          get_current_context_def, charge_state_gas_def,
          set_current_context_def, update_accounts_def,
          reraise_def]
      (* Each branch: either fail (refl), or consume_gas + update_accounts.
         The update is at address = c, which equals the head's callee by
         outputTo_consistent. *)
      \\ gvs[outputTo_consistent_def]
      \\ rw[same_frame_rel_def, callee_local_changes_def,
            lookup_account_def, update_account_def,
            APPLY_UPDATE_THM]
      \\ rw[]
      (* EIP-8037: the creation charge's branch sits inside a hypothesis,
         where nothing splits its `if`, so its output survives to the end as
         the variable `s''`.  Bring the equation into the goal, take the
         branch, and each branch reduces to a concrete state. *)
      \\ TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
              \\ rpt IF_CASES_TAC
              \\ gvs[consume_gas_def, get_current_context_def,
                     set_current_context_def, assert_def, bind_def,
                     ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                     pairTheory.PAIR_FST_SND_EQ]
              \\ rw[]
              \\ simp[APPLY_UPDATE_THM])))
  \\ (* e = SOME _ — reraise *)
    gvs[reraise_def]
  \\ Cases_on `h0.msgParams.outputTo` \\ gvs[reraise_def]
  \\ irule same_frame_rel_refl \\ simp[]
QED

Theorem pop_and_incorporate_context_length:
  1 < LENGTH s.contexts ==>
  LENGTH (SND (pop_and_incorporate_context success s)).contexts + 1 =
    LENGTH s.contexts
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  Cases_on `t` >> simp[] >> PairCases_on `h` >>
  simp[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
       credit_new_account_def, credit_state_gas_refund_def,
       get_gas_left_def, get_current_context_def, pop_context_def,
       return_def, unuse_gas_def, set_current_context_def,
       absorb_state_gas_def, push_logs_def, update_gas_refund_def,
       repay_state_gas_spill_def, repay_state_gas_spill_context_def,
       set_rollback_def, assert_def, fail_def] >> rw[] >>
  simp[bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, set_rollback_def]
QED

Theorem handle_ex_helper_length:
  s.contexts <> [] /\ handle_ex_helper e s = (r, s') ==>
  LENGTH s'.contexts =
    if LENGTH s.contexts <= 1 then LENGTH s.contexts
    else LENGTH s.contexts - 1
Proof
  Cases_on `LENGTH s.contexts <= 1`
  >- (simp[handle_ex_helper_def, bind_def, get_num_contexts_def,
           return_def, reraise_def]) >>
  simp[handle_ex_helper_def, bind_def, get_num_contexts_def,
       get_return_data_def, get_output_to_def, get_current_context_def,
       return_def, ignore_bind_def] >> strip_tac >> gvs[] >>
  Cases_on `pop_and_incorporate_context (e = NONE) s` >>
  `LENGTH r'.contexts + 1 = LENGTH s.contexts` by
    (mp_tac (Q.INST [`s` |-> `s`, `success` |-> `e = (NONE:exception option)`]
       pop_and_incorporate_context_length) >> simp[]) >>
  qhdtm_x_assum `pop_and_incorporate_context` kall_tac >>
  Cases_on `q` >> gvs[] >>
  drule_at Any cp_imp_length_contexts_preserved >> simp[] >>
  impl_tac >- (Cases_on `r' .contexts` >> gvs[]) >> simp[]
QED

Theorem handle_exception_prefix_same_frame:
  s.contexts <> [] ==>
  same_frame_rel (zero_head_refunds s)
    (SND ((if e <> NONE /\ e <> SOME Reverted then
       do restore_state_gas; gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else if e = SOME Reverted then restore_state_gas else return ()) s))
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  simp[restore_state_gas_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, return_def,
       get_gas_left_def, consume_gas_def, assert_def, fail_def,
       set_return_data_def, zero_head_refunds_def, same_frame_rel_def] >>
  rw[]
QED

(* handle_exception either reraises (n ≤ 1) or pops (n > 1). When the
   length is preserved, the reraise branch was taken. The prefix
   (consume_gas + set_return_data in non-Revert error cases) is
   preserves_same_frame. *)
Theorem handle_exception_same_frame:
  s.contexts ≠ [] ∧
  handle_exception e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel
    (s with contexts := (FST (HD s.contexts) with <|addRefund := 0; subRefund := 0|>,
                         SND (HD s.contexts)) :: TL s.contexts)
    s'
Proof
  strip_tac >> pure_once_rewrite_tac[GSYM zero_head_refunds_def] >>
  qabbrev_tac `prefix = (if e <> NONE /\ e <> SOME Reverted then
       do restore_state_gas; gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else if e = SOME Reverted then restore_state_gas else return ())` >>
  `cp prefix` by
    simp[Abbr `prefix`, cp_state_gas_meter, cp_bind, cp_ignore_bind] >>
  `same_frame_rel (zero_head_refunds s) (SND (prefix s))` by
    (simp[Abbr `prefix`, handle_exception_prefix_same_frame]) >>
  `handle_exception e s = bind prefix (\u. handle_ex_helper e) s` by
    simp[NoAsms, Abbr `prefix`, handle_exception_decomp] >>
  Cases_on `prefix s` >> Cases_on `q` >>
  gvs[bind_def] >- (
    rename1 `handle_ex_helper e sp = (r,s')` >>
    `LENGTH sp.contexts = LENGTH s.contexts` by
      (drule_all cp_imp_length_contexts_preserved >> simp[]) >>
    `sp.contexts <> []` by (Cases_on `sp.contexts` >> gvs[]) >>
    drule_all handle_ex_helper_length >>
    Cases_on `LENGTH sp.contexts <= 1` >> simp[] >>
    gvs[handle_ex_helper_def, bind_def, get_num_contexts_def,
        return_def, reraise_def]) >>
  gvs[]
QED

(* ---------------- handle_step under length preservation --------- *)

(* handle_step = if vfm_abort e then reraise e
                 else handle (handle_create e) handle_exception.
   The reraise case is trivial. In the handle case, handle_create always
   returns INR, so handle_exception is always invoked; we compose
   psf_handle_create with the same-length version of
   handle_exception_same_frame. *)
(* EIP-8037: the failure path's `restore_state_gas` zeroes the failing frame's
   refund counters (`restore_state_gas_def`), so `same_frame_rel` does not hold
   of the frame as it entered.  The statement pins the input's refund counters
   at 0 instead, which is the relation's refund clause with the loss removed;
   it reduces to the old statement when the frame had no accrued refunds. *)
Theorem handle_step_same_frame:
  outputTo_consistent s ∧
  handle_step e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel
    (s with contexts := (FST (HD s.contexts) with <|addRefund := 0; subRefund := 0|>,
                         SND (HD s.contexts)) :: TL s.contexts)
    s'
Proof
  rw[handle_step_def]
  >- (
    (* vfm_abort e: reraise, state unchanged *)
    gvs[reraise_def]
    \\ pure_once_rewrite_tac[GSYM zero_head_refunds_def]
    \\ irule same_frame_rel_zero_head_refunds_refl
    \\ gvs[outputTo_consistent_def])
  \\ (* handle (handle_create e) handle_exception s *)
    gvs[handle_def]
  \\ `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  \\ qspec_then`e`mp_tac(Q.GEN`e`(INST_TYPE[alpha |-> ``:unit``]handle_create_INR))
  \\ rw[] >> gvs[]
  \\ rename1`handle_create _ s = (_,s1)`
  \\ qmatch_asmsub_abbrev_tac`hce s = _`
  \\ `psf outputTo_consistent hce` by metis_tac[psf_handle_create]
  \\ `same_frame_rel s s1` by (
       gvs[psf_def,Abbr`hce`]
       \\ first_x_assum irule
       \\ simp[] \\ metis_tac[])
  \\ `LENGTH s1.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  \\ `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  \\ `LENGTH s'.contexts = LENGTH s1.contexts` by simp[]
  \\ `same_frame_rel (zero_head_refunds s1) s'`
     by (pure_once_rewrite_tac[zero_head_refunds_def] >>
         irule handle_exception_same_frame >> metis_tac[])
  \\ pure_once_rewrite_tac[GSYM zero_head_refunds_def]
  \\ metis_tac[same_frame_rel_zero_head_refunds_weaken,
                same_frame_rel_zero_head_refunds_trans]
QED

(* ================================================================ *)
(* Case (b) decomposition: push-fail-pop.                            *)
(*                                                                   *)
(* In step_same_frame's case (b), the inner monad grew (pushed a     *)
(* child context via proceed_call) and handle_step pops it back.     *)
(* The final state is `same_frame_rel`-related to the original       *)
(* because:                                                          *)
(*   - set_rollback during pop restores rollback to the snapshot     *)
(*     that proceed_call captured (i.e. the rollback at the start    *)
(*     of proceed_call, before any transfer).                        *)
(*   - The parent's head context accumulates only                    *)
(*     preserves_same_frame changes from step_call's prefix and      *)
(*     handle_exception's finalisation (inc_pc, set_return_data,     *)
(*     push_stack, write_memory).                                    *)
(*                                                                   *)
(* Decomposition into small lemmas, bottom-up.                       *)
(* ================================================================ *)

(* ---- Tiny state-effect lemmas for specific primitives ---------- *)

(* set_rollback sets `rollback`, leaves everything else alone. *)
Theorem set_rollback_effect:
  set_rollback r s = (q, s') ⇒
    q = INL () ∧ s' = s with rollback := r
Proof
  rw[set_rollback_def, return_def]
QED

(* pop_context removes the head of contexts, returns it, leaves
   everything else alone. *)
Theorem pop_context_effect:
  s.contexts ≠ [] ⇒
  pop_context s = (q, s') ⇒
    q = INL (HD s.contexts) ∧ s' = s with contexts := TL s.contexts
Proof
  rw[pop_context_def, return_def, fail_def] >>
  rw[execution_state_component_equality]
QED

(* push_context adds to the head. *)
Theorem push_context_effect:
  push_context crb s = (q, s') ⇒
    q = INL () ∧ s' = s with contexts := crb :: s.contexts
Proof
  rw[push_context_def, return_def] >>
  rw[execution_state_component_equality]
QED

(* ---- Behaviour of pop_and_incorporate_context on failure ------- *)

(* When called with success = F on a non-empty context stack with at
   least 2 entries, pop_and_incorporate_context pops the head,
   restores rollback from the popped head's saved rb, and unuse_gas's
   on the new head.

   Concretely: if s.contexts = (callee, callee_rb) :: rest and
   rest ≠ [], and we call with success=F, then:
     - s'.contexts has `rest`'s head with gasUsed possibly reduced,
       same SND (HD rest), same msgParams/logs/refunds/stack/memory
       /pc/jumpDest/returnData.
     - s'.rollback = callee_rb.
     - Other fields preserved. *)
(* Only describes the effect when the pop succeeded (q = INL ()). The
   failure case (q = INR (SOME Impossible)) happens when the callee
   consumed more gas than the parent had — possible if wf_state is
   not enforced. Callers rule this out separately. *)
Theorem pop_and_incorporate_context_failure_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  pop_and_incorporate_context F s = (INL (), s') ⇒
    s'.rollback = callee_rb ∧
    s'.txParams = s.txParams ∧
    s'.msdomain = s.msdomain ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       new_parent_ctx.logs = (FST parent).logs ∧
       new_parent_ctx.addRefund = (FST parent).addRefund ∧
       new_parent_ctx.subRefund = (FST parent).subRefund ∧
       new_parent_ctx.stack = (FST parent).stack ∧
       new_parent_ctx.memory = (FST parent).memory ∧
       new_parent_ctx.pc = (FST parent).pc ∧
       new_parent_ctx.jumpDest = (FST parent).jumpDest ∧
       new_parent_ctx.returnData = (FST parent).returnData)
Proof
  strip_tac
  >> gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
         credit_new_account_def, credit_state_gas_refund_def]
  >> gvs[get_gas_left_def, get_current_context_def, return_def,
         pop_context_def]
  >> gvs[unuse_gas_def, bind_def, get_current_context_def, return_def,
         assert_def, set_current_context_def, set_rollback_def,
         fail_def, ignore_bind_def]
  >> Cases_on `parent` >> gvs[]
  >> qmatch_asmsub_abbrev_tac `if cond then _ else _`
  >> Cases_on `cond` >> gvs[absorb_state_gas_def]
  (* EIP-8037: the credit that the pop's failure branch wraps in its own
     `if` is not the one the abbreviation above took, so its branch is
     still inside a hypothesis.  Take it into the goal and split it. *)
  >> TRY (qpat_x_assum `chgeq = (res,s')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[credit_new_account_def, credit_state_gas_refund_def,
                 get_current_context_def, set_current_context_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM])
QED

(* ---- Behaviour of handle_exception's pop-failure branch -------- *)

(* When e ≠ NONE and e ≠ SOME Reverted and the context stack has at
   least 2 entries (child + parent + rest), and the child's outputTo
   is Memory mr, then handle_exception e on this state ends with:
   - rollback = child's saved rb (restored by set_rollback).
   - contexts = new-parent-with-finalisation :: rest.
   - msdomain possibly grown from various Collect additions.
   - Specifically, the new-parent's head gets:
     - pc incremented;
     - returnData set to output (which after prefix consume_gas is []);
     - stack pushed with b2w F;
     - memory: write_memory r.offset [] = no-op. *)
(* Requires e ≠ NONE (for e = NONE the success pop path is taken which
   keeps rollback) and handle_exception result = INL (q = INL ()):
   gas/stack assertions may fail, giving INR.
   The typical caller (step_call failing via precompile with OutOfGas
   etc.) has e ≠ NONE and establishes q = INL () from pop's success. *)
Theorem handle_exception_pop_failure_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  callee.msgParams.outputTo = Memory mr ∧
  e ≠ NONE ∧
  handle_exception e s = (INL (), s') ⇒
    s'.rollback = callee_rb ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       new_parent_ctx.logs = (FST parent).logs ∧
       new_parent_ctx.addRefund = (FST parent).addRefund ∧
       new_parent_ctx.subRefund = (FST parent).subRefund)
Proof
  strip_tac
  >> Cases_on `parent`
  >> Cases_on `e = SOME Reverted` >> gvs[]
  >> gvs[handle_exception_def, restore_state_gas_def, forfeit_remaining_gas_def,
         absorb_state_gas_def, repay_state_gas_spill_def,
         repay_state_gas_spill_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, credit_new_account_def,
         credit_state_gas_refund_def, pop_context_def,
         set_rollback_def, unuse_gas_def, AllCaseEqs()]
  (* EIP-8037: the credit's `if` is left in a hypothesis, so its output is
     still the variable `s''`; take the branch in the goal and reduce it. *)
  >> TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[credit_new_account_def, credit_state_gas_refund_def,
                 get_current_context_def, set_current_context_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM])
QED

(* Variant for the success path (e = NONE): pop_and_incorporate_context T
   keeps rollback as-is. No set_rollback call. *)
Theorem handle_exception_pop_success_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  callee.msgParams.outputTo = Memory mr ∧
  handle_exception NONE s = (INL (), s') ⇒
    s'.rollback = s.rollback ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> Cases_on `parent`
  >> gvs[handle_exception_def, restore_state_gas_def, forfeit_remaining_gas_def,
         absorb_state_gas_def, repay_state_gas_spill_def,
         repay_state_gas_spill_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, credit_new_account_def,
         credit_state_gas_refund_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
QED

(* Generalised variant: drops `= (INL (), s')` requirement. Even if
   handle_exception returns INR (due to unuse_gas failing Impossible,
   or push_stack failing StackOverflow), the structural conclusions
   still hold. This is because:
   - unuse_gas Impossible fails BEFORE any state modification, so s' = s
     after pop_context only (head = parent, not updated);
   - push_stack StackOverflow fails AFTER inc_pc, set_return_data, so
     the parent head has been modified but stack not updated;
   - rollback is NEVER modified in the success path (no set_rollback).
*)
Theorem handle_exception_pop_success_memory_effect_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  callee.msgParams.outputTo = Memory mr ∧
  handle_exception NONE s = (q, s') ⇒
    s'.rollback = s.rollback ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> Cases_on `parent`
  >> gvs[handle_exception_def, restore_state_gas_def, forfeit_remaining_gas_def,
         absorb_state_gas_def, repay_state_gas_spill_def,
         repay_state_gas_spill_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, credit_new_account_def,
         credit_state_gas_refund_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
QED

(* Generalised variant for failure path: drops INL () requirement.
   Uses precondition s.rollback = callee_rb so that in INR cases
   (when unuse_gas fails Impossible, before set_rollback runs),
   s'.rollback still equals callee_rb.

   This is the failure pop path (e ≠ NONE, e ≠ Reverted, or Reverted
   which skips consume_gas). In all INL and INR outcomes, the
   structural conclusions hold. *)
(* Note: this generalised variant requires e ≠ SOME Reverted, which
   rules out the pathological unuse_gas-failure subcase. In that
   remaining path (e is OOG, InvalidParameter, etc.), consume_gas
   sets callee.gasUsed = gasLimit, making calleeGasLeft = 0 and
   unuse_gas 0 always succeed. So set_rollback always runs,
   restoring s'.rollback = callee_rb regardless of s.rollback.
   Precompile failures (which is when this lemma is used in
   step_call_handle_step_inr_grow_same_frame) never raise Reverted,
   so this restriction is always satisfied. *)
Theorem handle_exception_pop_failure_memory_effect_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  callee.msgParams.outputTo = Memory mr ∧
  e ≠ NONE ∧
  e ≠ SOME Reverted ∧
  handle_exception e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    s'.rollback = callee_rb ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> Cases_on `parent`
  >> gvs[handle_exception_def, restore_state_gas_def, forfeit_remaining_gas_def,
         absorb_state_gas_def, repay_state_gas_spill_def,
         repay_state_gas_spill_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, credit_new_account_def,
         credit_state_gas_refund_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
  (* EIP-8037: the credit's `if` is left in a hypothesis, so its output is
     still the variable `s''`; take the branch in the goal and reduce it. *)
  >> TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[credit_new_account_def, credit_state_gas_refund_def,
                 get_current_context_def, set_current_context_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM]
          >> rewrite_tac[execution_state_component_equality]
          >> qpat_x_assum `x.contexts = []` (fn th => rewrite_tac [th])
          >> simp[APPLY_UPDATE_THM])
QED

(* ---- Behaviour of handle_step when the pushed frame has Memory
        outputTo and e is not a vfm_abort -------------------------- *)

(* Variant for success: handle_step NONE with Memory outputTo.
   Rollback is KEPT (no set_rollback), logs/refunds grow. *)
Theorem handle_step_pop_success_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  (∃mr. callee.msgParams.outputTo = Memory mr) ∧
  handle_step NONE s = (INL (), s') ⇒
    s'.rollback = s.rollback ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> `s.contexts ≠ []` by simp[]
  >> `∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a` by simp[]
  >> drule (INST_TYPE [alpha |-> ``:unit``]
             vfmStaticCallsTheory.handle_create_reraises)
  >> simp[reraise_def]
  >> strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def, vfm_abort_def]
  >> strip_tac
  >> drule_all handle_exception_pop_success_memory_effect
  >> simp[]
QED

(* Generalised handle_step pop success: drops q = INL () requirement.
   Same proof strategy, uses handle_exception_pop_success_memory_effect_gen. *)
Theorem handle_step_pop_success_memory_effect_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  (∃mr. callee.msgParams.outputTo = Memory mr) ∧
  handle_step NONE s = (q, s') ⇒
    s'.rollback = s.rollback ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> `s.contexts ≠ []` by simp[]
  >> `∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a` by simp[]
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def, vfm_abort_def, handle_create_def,
          bind_def, get_return_data_def, get_output_to_def,
          get_current_context_def, return_def, reraise_def,
          charge_state_gas_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> strip_tac
  >> drule_all handle_exception_pop_success_memory_effect_gen
  >> simp[]
QED

(* Combines handle_create_reraises (for Memory outputTo) with
   handle_exception_pop_failure_memory_effect. *)
Theorem handle_step_pop_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  (∃mr. callee.msgParams.outputTo = Memory mr) ∧
  ¬ vfm_abort e ∧
  e ≠ NONE ∧
  handle_step e s = (INL (), s') ⇒
    s'.rollback = callee_rb ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       new_parent_ctx.logs = (FST parent).logs ∧
       new_parent_ctx.addRefund = (FST parent).addRefund ∧
       new_parent_ctx.subRefund = (FST parent).subRefund)
Proof
  strip_tac
  >> `s.contexts ≠ []` by simp[]
  >> `∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a` by simp[]
  >> drule (INST_TYPE [alpha |-> ``:unit``]
             vfmStaticCallsTheory.handle_create_reraises)
  >> simp[reraise_def]
  >> strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def]
  >> strip_tac
  >> drule_all handle_exception_pop_failure_memory_effect
  >> simp[]
QED

(* Generalised handle_step pop failure: drops q = INL () requirement.
   Extra hypothesis: LENGTH s'.contexts < LENGTH s.contexts (pop
   actually happened). *)
Theorem handle_step_pop_memory_effect_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  (∃mr. callee.msgParams.outputTo = Memory mr) ∧
  ¬ vfm_abort e ∧
  e ≠ NONE ∧
  e ≠ SOME Reverted ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    s'.rollback = callee_rb ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> `s.contexts ≠ []` by simp[]
  >> `∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a` by simp[]
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def, handle_create_def,
          bind_def, get_return_data_def, get_output_to_def,
          get_current_context_def, return_def, reraise_def,
          charge_state_gas_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> simp[AllCaseEqs()]
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s.contexts` by simp[]
  >> drule_all handle_exception_pop_failure_memory_effect_gen
  >> simp[]
QED

(* Rollback-only version of handle_exception_pop_failure_memory_effect_gen.
   Drops the Memory precondition because rollback after a failure pop
   is always callee_rb regardless of outputTo. *)
Theorem handle_exception_pop_failure_rollback_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  e ≠ NONE ∧
  e ≠ SOME Reverted ∧
  handle_exception e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    s'.rollback = callee_rb
Proof
  strip_tac
  >> Cases_on `parent`
  >> Cases_on `callee.msgParams.outputTo`
  >> gvs[handle_exception_def, restore_state_gas_def, forfeit_remaining_gas_def,
         absorb_state_gas_def, repay_state_gas_spill_def,
         repay_state_gas_spill_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, credit_new_account_def,
         credit_state_gas_refund_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
  (* EIP-8037: the credit's `if` is left in a hypothesis, so its output is
     still the variable `s''`; take the branch in the goal and reduce it. *)
  >> TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[credit_new_account_def, credit_state_gas_refund_def,
                 get_current_context_def, set_current_context_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM])
QED

(* When e <> NONE, handle_create always reraises regardless of outputTo.
   The Code+NONE branch is the only non-reraise path, and e <> NONE
   rules it out. *)
Theorem handle_create_reraises_when_some:
  e <> NONE /\ s.contexts <> [] ==> handle_create e s = reraise e s
Proof
  strip_tac
  >> Cases_on `e` >> gvs[]
  >> simp[handle_create_def, bind_def, get_return_data_def, get_output_to_def,
          get_current_context_def, return_def, reraise_def, AllCaseEqs()]
  >> Cases_on `(FST (HD s.contexts)).msgParams.outputTo` >> gvs[reraise_def]
QED



(* =====================================================================
 * Handle-step structural, length, rollback, and storage lemmas.
 *
 * Structural characterizations of handle_exception, handle_create,
 * and handle_step: length effects, rollback preservation, TL/SND-HD
 * preservation, storage preservation, and pop structure.
 * ===================================================================== *)

Theorem preserves_rollback_handle_exception_prefix:
  preserves_rollback
    (if b then
       ignore_bind (bind get_gas_left (λgasLeft. consume_gas gasLeft))
                   (set_return_data [])
     else return ())
Proof
  Cases_on `b` >> rw[]
  >> irule preserves_rollback_ignore_bind >> rw[]
QED

(* handle_exception with num_contexts ≤ 1 preserves rollback:
   only the reraise branch runs (after consume_gas + set_return_data
   which are preserves_rollback). *)
(* handle_exception when LENGTH is preserved: rollback is preserved.
   Because handle_exception's structure takes the n ≤ 1 branch when
   length is preserved (n > 1 would pop). In the n ≤ 1 branch only
   preserves_rollback primitives run. *)
Theorem handle_exception_same_length_preserves_rollback:
  handle_exception e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  s'.rollback = s.rollback
Proof
  simp[handle_exception_decomp] >>
  qmatch_goalsub_abbrev_tac`bind prefix _` >>
  simp[bind_def] >>
  TOP_CASE_TAC >>
  `r'.rollback = s.rollback ∧ LENGTH r'.contexts = LENGTH s.contexts` by (
    gvs[Abbr`prefix`,restore_state_gas_def, forfeit_remaining_gas_def,
        return_def,AllCaseEqs(),COND_RATOR,
        bind_def,ignore_bind_def,get_gas_left_def,
        get_current_context_def,fail_def,return_def,
        consume_gas_def,set_current_context_def,
        set_return_data_def,assert_def] >>
    Cases_on`s.contexts` >> gvs[] ) >>
  reverse TOP_CASE_TAC >- (rw[] >> gvs[]) >>
  Cases_on `r'.contexts = []`
  >- (simp[handle_ex_helper_def, bind_def, get_num_contexts_def,
           return_def, reraise_def] >> rpt strip_tac >> gvs[reraise_def]) >>
  strip_tac >>
  drule_all handle_ex_helper_length >>
  Cases_on `LENGTH r'.contexts <= 1` >> simp[] >>
  gvs[handle_ex_helper_def, bind_def, get_num_contexts_def,
      return_def, reraise_def]
QED

(* handle_step preserves storage when it preserves length.
   Under same_frame_rel (from handle_step_same_frame), storage at
   non-callee is preserved by callee_local_changes. At callee,
   no SSTORE runs in handle_step (handle_create only touches .code,
   handle_exception doesn't touch .storage). *)

Theorem handle_step_preserves_storage_same_length:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  handle_step y s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rw[handle_step_def, reraise_def, handle_def]
  >> gvs[AllCaseEqs()]
  >- (
    (* handle_create returned INL — impossible by handle_create_INR. *)
    rename1 `handle_create e`
    >> strip_assume_tac(INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
    >> gvs[] )
  (* handle_create returned INR eout; handle_exception eout s'' = (r, s'). *)
  >> rename1 `handle_create y s = (INR eout, s'')`
  >> mp_tac (INST_TYPE [alpha |-> ``:unit``]
              (GEN_ALL preserves_storage_handle_create))
  >> simp[preserves_storage_def]
  >> disch_then drule >> rw[]
  >> `same_frame_rel s s''` by (
       mp_tac (Q.SPEC `y`
                (Q.GEN `e`
                  (SIMP_RULE std_ss [psf_def]
                    (INST_TYPE [alpha |-> ``:unit``] psf_handle_create))))
       >> disch_then drule
       >> simp[])
  >> `s''.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> `LENGTH s''.contexts = LENGTH s.contexts` by fs[same_frame_rel_def]
  >> `LENGTH s'.contexts = LENGTH s''.contexts` by simp[]
  >> `s'.rollback = s''.rollback`
       by metis_tac[handle_exception_same_length_preserves_rollback]
  >> simp[]
QED

(* =====================================================================
 * Helpers for step_push_structure / step_pop_structure.
 * ===================================================================== *)

(* handle_exception: pop_and_incorporate_context is the only place that
   reduces contexts. It reduces by one. So handle_exception shrinks by at
   most one. *)
Theorem handle_exception_shrinks_by_one:
  handle_exception e s = (q, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts + 1 ≥ LENGTH s.contexts ∧
  LENGTH s'.contexts ≤ LENGTH s.contexts
Proof
  simp[handle_exception_decomp] >>
  qmatch_goalsub_abbrev_tac `bind prefix _` >>
  `cp prefix` by simp[Abbr `prefix`, cp_state_gas_meter, cp_bind, cp_ignore_bind] >>
  Cases_on `prefix s` >> rename1 `prefix s = (res,sp)` >>
  simp[bind_def] >> strip_tac >>
  `LENGTH sp.contexts = LENGTH s.contexts` by
    (drule_all cp_imp_length_contexts_preserved >> simp[]) >>
  Cases_on `res` >> gvs[] >>
  `sp.contexts <> []` by (Cases_on `sp.contexts` >> gvs[]) >>
  drule_all handle_ex_helper_length >>
  Cases_on `LENGTH sp.contexts <= 1` >> simp[]
QED

Theorem handle_exception_preserves_length_1:
  handle_exception e s = (q,s') /\ LENGTH s.contexts = 1 ==>
  LENGTH s'.contexts = 1
Proof
  simp[handle_exception_decomp] >>
  qmatch_goalsub_abbrev_tac `bind prefix _` >>
  `cp prefix` by simp[Abbr `prefix`, cp_state_gas_meter, cp_bind, cp_ignore_bind] >>
  Cases_on `prefix s` >> rename1 `prefix s = (res,sp)` >>
  simp[bind_def] >> strip_tac >>
  `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  `LENGTH sp.contexts = LENGTH s.contexts` by
    (drule_all cp_imp_length_contexts_preserved >> simp[]) >>
  Cases_on `res` >> gvs[] >>
  `sp.contexts <> []` by (Cases_on `sp.contexts` >> gvs[]) >>
  drule_all handle_ex_helper_length >> simp[]
QED

(* When LENGTH ≥ 2 and wf_state, handle_exception takes the pop branch and
   shrinks by exactly 1. The n ≤ 1 reraise branch is not taken, and the
   prefix (consume_gas) succeeds because wf_state ensures gasUsed ≤ gasLimit. *)
Theorem handle_exception_ge_2_pops:
  EVERY (wf_context o FST) s.contexts ∧ LENGTH s.contexts ≥ 2 ∧ handle_exception e s = (q, s') ⇒
  LENGTH s'.contexts + 1 = LENGTH s.contexts (* ∧ ISL q *)
Proof
  strip_tac >>
  `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  `wf_context (FST (HD s.contexts))` by
    (Cases_on `s.contexts` >> gvs[]) >>
  `(FST (HD s.contexts)).gasUsed <= (FST (HD s.contexts)).msgParams.gasLimit`
    by gvs[wf_context_def] >>
  qabbrev_tac `prefix = (if e <> NONE /\ e <> SOME Reverted then
       do restore_state_gas; gasLeft <- get_gas_left; consume_gas gasLeft;
          set_return_data [] od
     else if e = SOME Reverted then restore_state_gas else return ())` >>
  `?sp. prefix s = (INL (),sp) /\ LENGTH sp.contexts = LENGTH s.contexts` by
    (Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
     Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
     simp[Abbr `prefix`, restore_state_gas_def, bind_def, ignore_bind_def,
          get_current_context_def, set_current_context_def, get_gas_left_def,
          consume_gas_def, set_return_data_def, assert_def, fail_def,
          return_def]) >>
  `handle_exception e s = bind prefix (\u. handle_ex_helper e) s` by
    simp[NoAsms, Abbr `prefix`, handle_exception_decomp] >>
  gvs[bind_def] >>
  `sp.contexts <> []` by (Cases_on `sp.contexts` >> gvs[]) >>
  drule_all handle_ex_helper_length >> simp[]
QED

(* handle_create doesn't change contexts length (it may modify
   account.code for Code outputTo success but doesn't touch contexts). *)
Theorem handle_create_preserves_length:
  handle_create e s = (q, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> gvs[AllCaseEqs()]
  >> Cases_on `s.contexts` >> fs[]
  (* EIP-8037: the charge's branch sits in a hypothesis, so its output is
     still the variable `s''`; take the branch in the goal and reduce it. *)
  >> TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, assert_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM])
QED

(* handle_create preserves wf_state: it doesn't modify stack, gasUsed, or
   msgParams - only return_data/output_to/accounts. *)
Theorem handle_create_preserves_wf_state:
  wf_state s ∧ handle_create e s = (q, s') ⇒
  wf_state s'
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     charge_state_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     wf_state_def, all_accounts_def, wf_context_def]
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def, wf_state_def, all_accounts_def, wf_context_def,
         return_destination_CASE_rator, vfmTypesTheory.option_CASE_rator]
  (* EIP-8037: the charge's branch sits in a hypothesis, where nothing splits
     its `if`, so its output stays the variable `s''`; take the branch in the
     goal and reduce it to a concrete state before the obligations below are
     read off the state. *)
  >> TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, assert_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM])
  >> Cases_on `s.contexts` >> gvs[wf_context_def]
  >> gvs[update_account_def, lookup_account_def, APPLY_UPDATE_THM,
         wf_accounts_def] >> rw[] >>
     gvs[wf_account_state_def, EVAL``max_code_size``]
  >> gvs[stack_room_ok_def, gas_stack_ok_def,
         outputTo_consistent_ctx_def,
         outputTo_consistent_stack_def]
  >> Cases_on`t` >> gvs[unused_gas_def, frame_unused_gas_def]
  >> TRY (
    Cases >> gvs[]
    >> TRY ( first_x_assum(qspec_then`0`mp_tac) >> simp[] >> NO_TAC)
    >> first_x_assum(qspec_then`SUC n`mp_tac) >> simp[] )
QED

Theorem handle_create_preserves_wf_contexts:
  EVERY (wf_context o FST) s.contexts ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s') ⇒
  EVERY (wf_context o FST) s'.contexts
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     charge_state_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     wf_context_def]
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def, wf_context_def,
         return_destination_CASE_rator, vfmTypesTheory.option_CASE_rator]
  (* EIP-8037: the charge's branch sits in a hypothesis, where nothing splits
     its `if`, so its output stays the variable `s''`; take the branch in the
     goal and reduce it to a concrete state first. *)
  >> TRY (qpat_x_assum `chgeq = (res,s'')` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, assert_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ]
          >> rw[]
          >> simp[APPLY_UPDATE_THM]
          >> rw[wf_context_def]
          >> fs[APPLY_UPDATE_THM])
  >> Cases_on `s.contexts` >> gvs[wf_context_def]
QED

(* EIP-8037: a pop moves execution gas twice, so the bound carries the
   repayment term.  `pop_and_incorporate_context` reads the child's leftover
   execution gas and gives it back with `unuse_gas` (`gasUsed := gasUsed - n`,
   `spec/vfmExecutionScript.sml`), then `absorb_state_gas` (`:578`) adds the
   child's reservoir and spill to the parent's three meter fields and leaves
   `gasUsed` alone, and then on the success branch `repay_state_gas_spill_context`
   (`:599`) removes `MIN stateGasLeft stateGasSpilled` from `gasUsed` as well.
   So the parent's `gasUsed` after a pop is
     parent.gasUsed - calleeGasLeft
       - MIN (parent.stateGasLeft + child.stateGasLeft)
             (parent.stateGasSpilled + child.stateGasSpilled).

   The child's leftover execution gas at the pop is not
   `callee.msgParams.gasLimit - callee.gasUsed` in general: `handle_exception`
   touches the child's `gasUsed` before popping it.  `leftAfter` names that
   quantity, in the three cases `e` can be:
     - `e = NONE`: nothing has run, so it is
       `callee.msgParams.gasLimit - callee.gasUsed`;
     - `e = SOME Reverted`: `restore_state_gas` credits the child's spill back
       into its execution gas (`gasUsed := gasUsed - stateGasSpilled`,
       saturating), so its leftover grows by `MIN callee.stateGasSpilled
       callee.gasUsed` and the parent gives up that much more through
       `unuse_gas`;
     - `e ≠ NONE ∧ e ≠ SOME Reverted`: `forfeit_remaining_gas` leaves the child
       no execution gas, so the leftover is 0.
   The repayment term is as derived from `absorb_state_gas` and
   `repay_state_gas_spill_context` above, and it applies on the success branch
   only:
   - `e = NONE`: the prefix is `return ()`, so the child's meter at the pop is
     the one the statement names and the term above is exact.
   - `e = SOME Reverted`: `restore_state_gas` moves the child's reservoir to its
     baseline and its spill to 0, and `success = F` skips the repayment, so the
     parent loses no extra gas and the term only weakens the bound.
   - `e ≠ NONE` and `e ≠ SOME Reverted`: `forfeit_remaining_gas` leaves the child
     no execution gas and the repayment is skipped, so the term only weakens
     the bound. *)
(* Generic handle_exception pop structure: when it shrinks, the contexts
   take the form (new_head, SND parent) :: rest with msgParams preserved,
   and the rollback is either s.rollback (success) or callee_rb (failure). *)


Theorem handle_exception_pop_generic_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_exception e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ∧
  leftAfter = (if e = NONE then callee.msgParams.gasLimit - callee.gasUsed
               else if e = SOME Reverted then
                 callee.msgParams.gasLimit -
                 (callee.gasUsed - MIN callee.stateGasSpilled callee.gasUsed)
               else 0) ⇒
    (s'.rollback = s.rollback ∨ s'.rollback = callee_rb) ∧
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
      new_parent_ctx.gasUsed ≥
        (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled) -
        MIN new_account_state_gas (FST parent).stateGasSpilled
Proof
  strip_tac
  >> Cases_on `parent`
  >> Cases_on `callee.msgParams.outputTo`
  >> Cases_on `e = NONE`
  >> Cases_on `e = SOME Reverted`
  >> gvs[handle_exception_def, restore_state_gas_def, forfeit_remaining_gas_def,
         absorb_state_gas_def, repay_state_gas_spill_def,
         repay_state_gas_spill_context_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def]
  (* Split off the datatype case analysis: with it in the same step the
     unfolding and the splits together run over the per-step budget. *)
  >> gvs[AllCaseEqs()]
  (* EIP-8037: the credit is left opaque by the blast above, so its output is
     the variable `s''` and nothing can split the branch inside it.  Replace
     `s''` by the credit's second component, unfold the credit in the goal,
     take its branch, and reduce it to a concrete state. *)
  >> (qpat_x_assum `chgeq = (INL (),s'')`
        (fn th => SUBST_ALL_TAC
          (SYM (CONJUNCT2 (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th))))
      ORELSE all_tac)
  >> (qpat_x_assum `chgeq = (INR err,s')`
        (fn th => SUBST_ALL_TAC
          (SYM (CONJUNCT2 (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th))))
      ORELSE all_tac)
  (* EIP-8037: the credit's branch sits in a hypothesis, where nothing splits
     its `if`, so its output stays the variable `s''` (or `s'` when the credit
     fails).  With the charge flag known, the credit collapses once it is
     unfolded; replace its output by the projection the equation bounds, so
     the reductions above and the frame lemmas can read it. *)
  >> Cases_on `callee.msgParams.newAccountCharged`
  >> (qpat_x_assum `chgeq = (INL (),s'')`
        (fn th => SUBST_ALL_TAC
          (SYM (CONJUNCT2 (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th))))
      ORELSE all_tac)
  >> (qpat_x_assum `chgeq = (INR err,s')`
        (fn th => SUBST_ALL_TAC
          (SYM (CONJUNCT2 (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th))))
      ORELSE all_tac)
  >> gvs[credit_new_account_def, credit_state_gas_refund_def,
         get_current_context_def, set_current_context_def, bind_def,
         ignore_bind_def, return_def, fail_def, APPLY_UPDATE_THM] >>
  rw[] >>
  pure_rewrite_tac[MIN_DEF] >> rpt IF_CASES_TAC >> decide_tac
QED

(* handle_create preserves TL(contexts) and SND(HD contexts).
   For Code+NONE case it modifies HD(contexts) gasUsed; for other
   cases it's an exact reraise. In both sub-cases TL and SND-of-HD
   are unchanged. *)
Theorem handle_create_preserves_tl_and_snd_hd:
  handle_create e s = (q, s') ∧ s.contexts ≠ [] ⇒
    s'.contexts ≠ [] ∧
    TL s'.contexts = TL s.contexts ∧
    SND (HD s'.contexts) = SND (HD s.contexts) ∧
    (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
    (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> gvs[AllCaseEqs()]
  >> Cases_on `s.contexts` >> fs[]
  (* EIP-8037: the creation charge's branch sits inside a hypothesis, where
     nothing splits its `if`, so its output survives to the end as the
     variable `s''`.  Bring the equation into the goal, take the branch, and
     each branch reduces to a concrete state. *)
  >> TRY (qpat_x_assum `chgeq = (INL (),sv)` mp_tac
          >> rpt IF_CASES_TAC
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, assert_def, bind_def,
                 ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[]
          >> simp[APPLY_UPDATE_THM])
  (* Where the charge's equation did not match that shape, take every
     hypothesis into the goal and split the conditionals there, which is the
     only place a tactic can. *)
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def, assert_def,
                 bind_def, ignore_bind_def, return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[] >> NO_TAC)
QED

(* handle_create preserves rollback (it only modifies .code via
   update_accounts which writes into rollback.accounts). Actually
   update_accounts DOES modify rollback.accounts, so this is FALSE
   in the Code+NONE case. Instead provide a weaker lemma: in the
   cases where handle_create doesn't go into Code+NONE, rollback
   is unchanged. *)
Theorem handle_create_non_code_success_preserves_rollback:
  handle_create e s = (q, s') ∧ s.contexts ≠ [] ∧
  (e ≠ NONE ∨ ∃mr. (FST (HD s.contexts)).msgParams.outputTo = Memory mr) ⇒
  s'.rollback = s.rollback
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
QED

(* handle_create preserves .accesses: all primitives within
   handle_create are either reads, preserves_rollback, or update_accounts
   with a function touching only .accounts (not .accesses). *)
Theorem handle_create_preserves_accesses:
  handle_create e s = (q, s') ⇒
  s'.rollback.accesses = s.rollback.accesses
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  (* EIP-8037: where a charge's branch is left inside a hypothesis, nothing
     splits its `if`; take the hypotheses into the goal, split there, and
     reduce each branch to a concrete state. *)
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def,
                 charge_new_account_def, assert_def, bind_def, ignore_bind_def,
                 return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[] >> NO_TAC)
QED

(* EIP-8037: the code deposit charges state gas, so `handle_create` is no
   longer meter-neutral.  What the charge does to the head frame's meter is
   what every state charge does -- take from the reservoir first and spill
   the remainder into the frame's execution gas -- so the reservoir only
   falls, the spill only rises, and the spill rises by no more than the
   execution gas that leaves.  Only the `(NONE, Code address)` input
   reaches the charge; every other input takes `reraise e`, which moves
   nothing, so all three hold with equality there.  The leftover bound is
   the one the pop's repayment reads. *)
Theorem handle_create_effective_leftover:
  handle_create e s = (INR e', s1) /\ s.contexts <> [] ==>
  (FST (HD s1.contexts)).stateGasLeft <= (FST (HD s.contexts)).stateGasLeft /\
  (FST (HD s.contexts)).stateGasSpilled <= (FST (HD s1.contexts)).stateGasSpilled /\
  (FST (HD s1.contexts)).stateGasSpilled - (FST (HD s.contexts)).stateGasSpilled <=
    (FST (HD s1.contexts)).gasUsed - (FST (HD s.contexts)).gasUsed /\
  (if e' = NONE then
     (FST (HD s1.contexts)).msgParams.gasLimit - (FST (HD s1.contexts)).gasUsed
   else if e' = SOME Reverted then
     (FST (HD s1.contexts)).msgParams.gasLimit -
       ((FST (HD s1.contexts)).gasUsed -
        MIN (FST (HD s1.contexts)).stateGasSpilled (FST (HD s1.contexts)).gasUsed)
   else 0) <=
  (if e = NONE then
     (FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed
   else if e = SOME Reverted then
     (FST (HD s.contexts)).msgParams.gasLimit -
       ((FST (HD s.contexts)).gasUsed -
        MIN (FST (HD s.contexts)).stateGasSpilled (FST (HD s.contexts)).gasUsed)
   else 0)
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> Cases_on `s.contexts` >> gvs[]
  (* EIP-8037: where a charge's branch is left inside a hypothesis, nothing
     splits its `if`; take the hypotheses into the goal, split there, and
     reduce each branch to a concrete state. *)
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def,
                 charge_new_account_def, assert_def, bind_def, ignore_bind_def,
                 return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[])
  >> decide_tac
QED

(* EIP-8037: the code deposit's charge keeps the frame's meter inside its
   own grant.  `consume_gas` guards the hash cost and the spill's assertion
   guards the rest, so a charge that succeeded leaves `gasUsed` at most the
   frame's `gasLimit` -- and every other input leaves the meter alone.  This
   is what makes the pop's repayment term read `limit - gasUsed` as a
   leftover that cannot go negative. *)
Theorem handle_create_gasUsed_le_limit[local]:
  handle_create e s = (INR e', s1) /\ s.contexts <> [] ==>
  (FST (HD s1.contexts)).gasUsed <=
    (FST (HD s.contexts)).msgParams.gasLimit \/
  (FST (HD s1.contexts)).gasUsed <= (FST (HD s.contexts)).gasUsed
Proof
  rw[handle_create_def, bind_def, ignore_bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, return_def, fail_def,
     reraise_def, consume_gas_def, update_accounts_def, assert_def,
     set_current_context_def, charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def,
                 charge_new_account_def, assert_def, bind_def, ignore_bind_def,
                 return_def, fail_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[])
  >> decide_tac
QED

(* EIP-8037: `handle_create` either re-raises the exception it was given (the
   non-deposit inputs and the deposit's own success) or fails one of the
   deposit's two assertions, so its result can be a revert only if its input
   was.  The pop's repayment reads the leftover differently for a revert than
   for anything else, and without this the branch on the result is free to
   pair a frame the deposit charged with the revert form, where the leftover
   inequality the repayment needs does not hold. *)
(* EIP-8037: a create that returns `SOME Reverted` is the `reraise e` path,
   which hands its own exception straight back, so an unreverted input can
   never come out reverted.  The pop's leftover terms are read off both the
   frame before the deposit charge and the frame after it, and this is what
   ties the two to the same exception. *)
Theorem handle_create_reverted_iff[local]:
  handle_create e s = (INR e', s1) /\ s.contexts <> [] ==>
  (e' = SOME Reverted <=> e = SOME Reverted)
Proof
  rw[handle_create_def, bind_def, ignore_bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, return_def, fail_def,
     reraise_def, consume_gas_def, update_accounts_def, assert_def,
     set_current_context_def, charge_state_gas_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def, consume_gas_def,
         charge_state_gas_def, APPLY_UPDATE_THM]
  >> Cases_on `s.contexts` >> gvs[]
  (* EIP-8037: the charge's branch sits in a hypothesis, where nothing splits
     its `if`; take the hypotheses into the goal, split there, and read the
     result off each branch. *)
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def,
                 charge_new_account_def, assert_def, bind_def, ignore_bind_def,
                 return_def, fail_def, update_accounts_def, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[] >> NO_TAC)
QED

(* A state charge that lowers a reservoir by `l` and raises a spill by `sp`
   lowers `MIN (p + reservoir) (q + spill)` by at most the execution gas it
   spends: the `MIN` can only have followed the reservoir down, or the
   spill up, by that much.  The pop's repayment term below is the instance
   with `p` and `q` the parent's two meter fields, and `d` the execution
   gas the charge spent. *)
(* The charge's leftover terms are differences against the same limit, so the
   limit cancels; `decide_tac` alone does not see through the nested
   subtraction. *)
Theorem sub_left_cancel[local]:
  (b:num) <= c /\ c <= a ==> a - b - (a - c) = c - b
Proof
  rpt strip_tac >> rewrite_tac[arithmeticTheory.SUB_LEFT_SUB]
  >> rpt IF_CASES_TAC >> decide_tac
QED

Theorem MIN_add_le_of_spill_move[local]:
  l' <= l /\ sp' - sp <= d ==>
  MIN (p + l') (q + sp') <= MIN (l + p) (sp + q) + d
Proof
  strip_tac >> `sp' <= sp + d` by decide_tac
  >> rewrite_tac[MIN_DEF] >> rpt IF_CASES_TAC >> decide_tac
QED

(* Generic handle_step pop structure — storage-aware.

   When handle_step shrinks contexts, the contexts structure is
   (new_head, SND parent) :: rest, and the storage of s'.rollback.accounts
   equals the storage of either s.rollback.accounts (success pop) OR
   callee_rb.accounts (failure pop) — at every address.

   For Code+NONE+success case, handle_create deposits bytecode before
   pop. This changes .code but not .storage. So the storage equality
   still holds. *)
Theorem handle_step_pop_generic_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ∧
  leftAfter = (if e = NONE then callee.msgParams.gasLimit - callee.gasUsed
               else if e = SOME Reverted then
                 callee.msgParams.gasLimit -
                 (callee.gasUsed - MIN callee.stateGasSpilled callee.gasUsed)
               else 0) ⇒
    ((∀a. (lookup_account a s'.rollback.accounts).storage =
          (lookup_account a s.rollback.accounts).storage) ∨
     (∀a. (lookup_account a s'.rollback.accounts).storage =
          (lookup_account a callee_rb.accounts).storage)) ∧
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
      new_parent_ctx.gasUsed ≥
        (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled) -
        MIN new_account_state_gas (FST parent).stateGasSpilled
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[handle_def]
  >> `s.contexts ≠ []` by simp[]
  >> strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_tl_and_snd_hd
  >> strip_tac
  >> `s1.contexts = (FST (HD s1.contexts), callee_rb) :: parent :: rest` by (
       Cases_on `s1.contexts` >> fs[]
       >> PairCases_on `h` >> fs[])
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s1.contexts` by decide_tac
  >> TRY (drule_all handle_create_reverted_iff >> strip_tac)
  >> drule_all handle_create_effective_leftover >> strip_tac
  >> drule handle_create_gasUsed_le_limit >> strip_tac
  >> drule_at (Pat `handle_exception _ _ = _`) handle_exception_pop_generic_gen
  >> simp[] >> strip_tac >> first_x_assum drule >> strip_tac >> fs[]
  >> mp_tac (INST_TYPE[alpha|->``:unit``]preserves_storage_handle_create)
  >> rewrite_tac[preserves_storage_def]
  >> disch_then drule
  >> strip_tac
  (* EIP-8037: the storage disjunct needs only the pointwise hypothesis from
     `preserves_storage_handle_create`: unfold `lookup_storage` in it and
     extensionality settles the disjunct.  `gvs` with these same rewrites has
     to generalise and strip on top of that, which blows the tactic timeout on
     the gas arithmetic in the goal and its hypotheses; `fs` does the same
     simplification without it. *)
  >> fs[lookup_storage_def, FUN_EQ_THM]
  >> qpat_x_assum `(if _ then _ else _) <= _` mp_tac
  (* EIP-8037: that leftover inequality is stated about `FST (HD s.contexts)`
     and the gas bound about `callee`; the two are the same frame only up to
     the head of `s.contexts`.  Rewrite the gas bound into the inequality's
     form, so the two abbreviations below name matching occurrences and the
     `MIN_add_le_of_spill_move` premises are stated the way the hypotheses
     `handle_create_effective_leftover` left them. *)
  >> `callee = FST (HD s.contexts)` by simp[]
  >> pop_assum (fn th => rewrite_tac[th])
  (* EIP-8037: the pop's own bound reads its leftover through `e'`, while the
     leftover inequality it hands back reads its two sides through `e'` and
     `e`; the create lemma's iff identifies those two `Reverted` guards, so
     after this rewrite all three leftover terms are the one term the
     abbreviations below name.  The pop's bound comes into the goal first, so
     its copies of the repayment term and the leftover are named with the
     rest; the repayment term reads the head frame's reservoir and spill, so
     keeping it a single variable is what leaves the arithmetic linear. *)
  >> qpat_x_assum `new_parent_ctx.gasUsed >= _` mp_tac
  >> qabbrev_tac `repay1 =
       MIN ((FST parent).stateGasLeft + (FST (HD s1.contexts)).stateGasLeft)
           ((FST parent).stateGasSpilled + (FST (HD s1.contexts)).stateGasSpilled)`
  >> `e = SOME Reverted <=> e' = SOME Reverted` by simp[]
  >> pop_assum (fn th => rewrite_tac[th])
  >> qmatch_goalsub_abbrev_tac `newLeft <= oldLeft`
  >> qmatch_goalsub_abbrev_tac `_ >= used - oldLeft - repayment - newAcctMin`
  >> `repay1 <= repayment + (oldLeft - newLeft)`
       by (qunabbrev_tac `repay1` >> qunabbrev_tac `repayment`
           >> qunabbrev_tac `oldLeft` >> qunabbrev_tac `newLeft`
           (* EIP-8037: the deposit's charge and the account update it is
              followed by each leave their output in an opaque variable, and
              these goals read the head frame off that variable.  Replace
              each output by the state its equation bounds, so that unfolding
              the charge below lands the frame's gas fields on concrete
              records -- left as it is, the simplifier reads them off the
              variable and the branch's assertion never reaches the
              arithmetic. *)
           >> TRY (qpat_x_assum `update_accounts _ _ = (INL (), sv)`
                     (fn th => SUBST_ALL_TAC
                        (SYM (CONJUNCT2
                          (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th)))))
           >> TRY (qpat_x_assum `(if _ then _ else _) _ = (INL (), sv)`
                     (fn th => SUBST_ALL_TAC
                        (SYM (CONJUNCT2
                          (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th)))))
           >> irule MIN_add_le_of_spill_move >> conj_tac
           >> TRY (qpat_x_assum
                     `(FST (HD s1.contexts)).stateGasLeft ≤
                      (FST (HD s.contexts)).stateGasLeft` ACCEPT_TAC)
           >> Cases_on `callee.msgParams.outputTo`
           (* EIP-8037: a create that did not reach the deposit takes the
              `reraise e` path, which leaves the meter alone; taking `e`'s
              two shapes here lets that path show itself instead of staying
              a `case`. *)
           >> Cases_on `e`
           >> rpt IF_CASES_TAC
           >> gvs[handle_create_def, bind_def, ignore_bind_def,
                  get_return_data_def, get_output_to_def,
                  get_current_context_def, return_def, reraise_def,
                  charge_state_gas_def, consume_gas_def,
                  charge_new_account_def, assert_def,
                  set_current_context_def, AllCaseEqs(),
                  sub_left_cancel, APPLY_UPDATE_THM]
           (* EIP-8037: the deposit charge's branch is left inside a
              hypothesis, where nothing splits its `if`, and the arithmetic
              needs what the taken branch asserts -- that the gas the charge
              spilled still fits the frame's grant.  Take those two
              hypotheses into the goal and split there, carrying nothing else
              along: the whole hypothesis list is far too big to generalise
              and strip inside the time a step gets. *)
           >> TRY (qpat_x_assum `update_accounts _ _ = (INL (), _)` mp_tac
                   >> qpat_x_assum `(if _ then _ else _) _ = (INL (), _)` mp_tac
                   >> rpt IF_CASES_TAC >> rpt disch_tac
                   >> gvs[consume_gas_def, get_current_context_def,
                          set_current_context_def, charge_state_gas_def,
                          charge_new_account_def, assert_def, bind_def,
                          ignore_bind_def, return_def, fail_def,
                          update_accounts_def, AllCaseEqs(),
                          sub_left_cancel, APPLY_UPDATE_THM]
                   >> rw[])
           (* EIP-8037: the repayment terms are `MIN`s, and the arithmetic
              has to see which way each one falls; `decide_tac` does not
              look through `MIN`. *)
           >> TRY (pure_rewrite_tac[MIN_DEF] >> rpt IF_CASES_TAC)
           >> decide_tac)
  (* EIP-8037: with the leftover terms named and the two exceptions' guards
     identified, the pop's bound, the leftover inequality and the `repay1`
     fact are all stated about the same terms, so what is left is linear. *)
  >> decide_tac
QED

(* Strengthening of handle_step_pop_generic_gen that pairs each
   storage disjunct with the matching accesses subset. *)
Theorem handle_step_pop_generic_gen_paired:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ∧
  leftAfter = (if e = NONE then callee.msgParams.gasLimit - callee.gasUsed
               else if e = SOME Reverted then
                 callee.msgParams.gasLimit -
                 (callee.gasUsed - MIN callee.stateGasSpilled callee.gasUsed)
               else 0) ⇒
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
      new_parent_ctx.gasUsed ≥
        (FST parent).gasUsed - leftAfter -
        MIN ((FST parent).stateGasLeft + callee.stateGasLeft)
            ((FST parent).stateGasSpilled + callee.stateGasSpilled) -
        MIN new_account_state_gas (FST parent).stateGasSpilled ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet callee_rb.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a callee_rb.accounts).storage)))
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[handle_def]
  >> `s.contexts ≠ []` by simp[]
  >> strip_assume_tac
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_tl_and_snd_hd
  >> strip_tac
  >> `s1.contexts = (FST (HD s1.contexts), callee_rb) :: parent :: rest` by (
       Cases_on `s1.contexts` >> fs[]
       >> PairCases_on `h` >> fs[])
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s1.contexts` by decide_tac
  >> TRY (drule_all handle_create_reverted_iff >> strip_tac)
  >> drule_all handle_create_effective_leftover >> strip_tac
  >> drule handle_create_gasUsed_le_limit >> strip_tac
  >> drule_at (Pat `handle_exception _ _ = _`) handle_exception_pop_generic_gen
  >> simp[] >> strip_tac >> first_x_assum drule >> strip_tac >> fs[]
  >> drule handle_create_preserves_accesses
  >> mp_tac (INST_TYPE[alpha|->``:unit``]preserves_storage_handle_create)
  >> rewrite_tac[preserves_storage_def]
  >> disch_then drule
  >> fs[lookup_storage_def, FUN_EQ_THM]
  >> rpt strip_tac
  >> qpat_x_assum `(if _ then _ else _) <= _` mp_tac
  (* EIP-8037: the gas bound is stated about `callee` and the leftover
     inequality about `FST (HD s.contexts)`; the two are the same frame only
     up to the head of `s.contexts`, so rewriting the bound into the
     inequality's form lets the abbreviations below name both.  The pop's own
     bound reads its leftover through `e'` while the inequality reads its two
     sides through `e'` and `e`; the create lemma's iff identifies those two
     `Reverted` guards, so after the rewrite all three leftover terms are one
     term.  The pop's bound comes into the goal first so its copies of the
     repayment term and the leftover are named with the rest. *)
  >> `callee = FST (HD s.contexts)` by simp[]
  >> pop_assum (fn th => rewrite_tac[th])
  >> qpat_x_assum `new_parent_ctx.gasUsed >= _` mp_tac
  >> qabbrev_tac `repay1 =
       MIN ((FST parent).stateGasLeft + (FST (HD s1.contexts)).stateGasLeft)
           ((FST parent).stateGasSpilled + (FST (HD s1.contexts)).stateGasSpilled)`
  >> `e = SOME Reverted <=> e' = SOME Reverted` by simp[]
  >> pop_assum (fn th => rewrite_tac[th])
  >> qmatch_goalsub_abbrev_tac `newLeft <= oldLeft`
  >> qmatch_goalsub_abbrev_tac `_ >= used - oldLeft - repayment - newAcctMin`
  >> `repay1 <= repayment + (oldLeft - newLeft)`
       by (qunabbrev_tac `repay1` >> qunabbrev_tac `repayment`
           >> qunabbrev_tac `oldLeft` >> qunabbrev_tac `newLeft`
           (* EIP-8037: the deposit's charge and the account update it is
              followed by each leave their output in an opaque variable, and
              these goals read the head frame off that variable.  Replace
              each output by the state its equation bounds, so that unfolding
              the charge below lands the frame's gas fields on concrete
              records -- left as it is, the simplifier reads them off the
              variable and the branch's assertion never reaches the
              arithmetic. *)
           >> TRY (qpat_x_assum `update_accounts _ _ = (INL (), sv)`
                     (fn th => SUBST_ALL_TAC
                        (SYM (CONJUNCT2
                          (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th)))))
           >> TRY (qpat_x_assum `(if _ then _ else _) _ = (INL (), sv)`
                     (fn th => SUBST_ALL_TAC
                        (SYM (CONJUNCT2
                          (REWRITE_RULE [pairTheory.PAIR_FST_SND_EQ] th)))))
           >> irule MIN_add_le_of_spill_move >> conj_tac
           >> TRY (qpat_x_assum
                     `(FST (HD s1.contexts)).stateGasLeft ≤
                      (FST (HD s.contexts)).stateGasLeft` ACCEPT_TAC)
           >> Cases_on `callee.msgParams.outputTo`
           (* EIP-8037: a create that did not reach the deposit takes the
              `reraise e` path, which leaves the meter alone; taking `e`'s
              two shapes here lets that path show itself instead of staying
              a `case`. *)
           >> Cases_on `e`
           >> rpt IF_CASES_TAC
           >> gvs[handle_create_def, bind_def, ignore_bind_def,
                  get_return_data_def, get_output_to_def,
                  get_current_context_def, return_def, reraise_def,
                  charge_state_gas_def, consume_gas_def,
                  charge_new_account_def, assert_def,
                  set_current_context_def, AllCaseEqs(),
                  sub_left_cancel, APPLY_UPDATE_THM]
           (* EIP-8037: the deposit charge's branch is left inside a
              hypothesis, where nothing splits its `if`, and the arithmetic
              needs what the taken branch asserts -- that the gas the charge
              spilled still fits the frame's grant.  Take those two
              hypotheses into the goal and split there, carrying nothing else
              along: the whole hypothesis list is far too big to generalise
              and strip inside the time a step gets. *)
           >> TRY (qpat_x_assum `update_accounts _ _ = (INL (), _)` mp_tac
                   >> qpat_x_assum `(if _ then _ else _) _ = (INL (), _)` mp_tac
                   >> rpt IF_CASES_TAC >> rpt disch_tac
                   >> gvs[consume_gas_def, get_current_context_def,
                          set_current_context_def, charge_state_gas_def,
                          charge_new_account_def, assert_def, bind_def,
                          ignore_bind_def, return_def, fail_def,
                          update_accounts_def, AllCaseEqs(),
                          sub_left_cancel, APPLY_UPDATE_THM]
                   >> rw[])
           (* EIP-8037: the repayment terms are `MIN`s, and the arithmetic
              has to see which way each one falls; `decide_tac` does not
              look through `MIN`. *)
           >> TRY (pure_rewrite_tac[MIN_DEF] >> rpt IF_CASES_TAC)
           >> decide_tac)
  (* EIP-8037: with the leftover terms named and the two exceptions' guards
     identified, the pop's bound, the leftover inequality and the `repay1`
     fact are all stated about the same terms, so what is left is linear. *)
  >> decide_tac
QED

(* Saved rollback's accesses are in s'.rollback's accesses, regardless
   of which pop branch handle_step took.
   Requires the hypothesis callee_rb.accesses ⊆ s.rollback.accesses
   (a structural invariant: at push_context time the saved rollback
   equals current, and accesses only grow). This invariant needs to
   be added to run_call_inv as:
     EVERY (λrb. toSet rb.accesses.storageKeys ⊆
                 toSet s.rollback.accesses.storageKeys)
           (MAP SND s.contexts)
   and maintained by run_call_inv_step. *)
Theorem handle_step_pop_accesses_bound:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ∧
  toSet callee_rb.accesses.storageKeys ⊆
    toSet s.rollback.accesses.storageKeys ⇒
  toSet callee_rb.accesses.storageKeys ⊆
    toSet s'.rollback.accesses.storageKeys
Proof
  rw[] >>
  drule_then drule handle_step_pop_generic_gen_paired >>
  rw[] >>
  gvs[SUBSET_DEF]
QED

Theorem handle_step_preserves_length_1:
  handle_step e s = (q, s') ∧ LENGTH s.contexts = 1 ⇒
  LENGTH s'.contexts = 1
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> reverse IF_CASES_TAC >> simp[]
  >> TRY (simp[reraise_def] >> strip_tac >> gvs[] >> NO_TAC)
  >> simp[handle_def]
  >> `s.contexts ≠ []` by (Cases_on `s.contexts` >> fs[])
  >> strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> `LENGTH s1.contexts = 1` by simp[]
  >> strip_tac
  >> drule_all handle_exception_preserves_length_1 >> simp[]
QED

(* handle_step reduces contexts by at most one. *)
Theorem handle_step_shrinks_by_one:
  handle_step e s = (q, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts + 1 ≥ LENGTH s.contexts ∧
  LENGTH s'.contexts ≤ LENGTH s.contexts
Proof
  strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def]
  >> reverse IF_CASES_TAC >> simp[]
  >> TRY (strip_tac >> gvs[reraise_def] >> NO_TAC)
  >> simp[handle_def]
  >> strip_assume_tac
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> simp[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> `s1.contexts ≠ []` by (Cases_on `s1.contexts` >> fs[])
  >> strip_tac
  >> imp_res_tac handle_exception_shrinks_by_one
  >> fs[]
QED

(* When ¬vfm_abort e, wf_context on all contexts, and LENGTH ≥ 2,
   handle_step shrinks by exactly 1. *)
Theorem handle_step_not_abort_pops:
  EVERY (wf_context o FST) s.contexts ∧ ¬vfm_abort e ∧ LENGTH s.contexts ≥ 2 ∧
  handle_step e s = (q, s') ⇒
  LENGTH s'.contexts + 1 = LENGTH s.contexts
Proof
  strip_tac
  >> gvs[handle_step_def, handle_def]
  >> `s.contexts ≠ []` by (Cases_on `s.contexts` >> fs[])
  >> strip_assume_tac
       (INST_TYPE [alpha |-> ``:unit``] handle_create_INR)
  >> gvs[]
  >> qmatch_asmsub_rename_tac `handle_create e s = (INR e', s1)`
  >> drule_all handle_create_preserves_length
  >> strip_tac
  >> `LENGTH s1.contexts ≥ 2` by simp[]
  (* Need EVERY (wf_context o FST) s1 to apply handle_exception_ge_2_pops *)
  >> `EVERY (wf_context o FST) s1.contexts` by metis_tac[handle_create_preserves_wf_contexts]
  >> drule_all handle_exception_ge_2_pops
  >> simp[]
QED


(* ================================================================== *)
(* Stack-room and gas-allocation invariant preservation               *)
(*                                                                    *)
(* stack_room_ok: saved parent contexts have stacks strictly shorter  *)
(*   than stack_limit. Gas_stack_ok: each parent can absorb its       *)
(*   child's remaining gas. Both follow from three structural cases:  *)
(*   1. Same-frame (TL unchanged, gasUsed monotone)                   *)
(*   2. Push (old head enters TL with pop_stack-shrunk stack and      *)
(*      consume_gas-increased gasUsed ≥ child.gasLimit)               *)
(*   3. Pop (handle_exception removes callee, parent.gasUsed grows)   *)
(* ================================================================== *)

(* --- Case 1: same_frame_rel preserves stack_room_ok --- *)

Theorem same_frame_rel_preserves_stack_room_ok:
  same_frame_rel s s' ∧ stack_room_ok s ⇒ stack_room_ok s'
Proof
  rw[stack_room_ok_def, same_frame_rel_def]
QED

(* --- Case 1: same_frame_rel preserves gas_stack_ok when the head's *)
(* frame_unused_gas does not grow.                                    *)
(*                                                                    *)
(* EIP-8037: the head's share of `unused_gas` is its                  *)
(* `frame_unused_gas`, `gasLimit - gasUsed + stateGasSpilled`, and    *)
(* `same_frame_rel` pins no meter field at all -- so gasUsed           *)
(* monotonicity alone was not enough: a head whose spill grows with   *)
(* its `gasUsed` unchanged has a larger `frame_unused_gas`, and       *)
(* `gas_stack_ok`, at the frames below it, whose `EL (SUC i)` is the  *)
(* same frame in both states, fails.  Checked witness:                *)
(* `spec/prop/vfmGasStackProbeScript.sml`                             *)
(* `same_frame_rel_preserves_gas_stack_ok_counterexample`.            *)
(*                                                                    *)
(* The hypothesis is the measure itself rather than a pair of meter   *)
(* fields: `charge_state_gas`'s spill branch raises `gasUsed` and the *)
(* spill by the same amount, so a step that spills state gas leaves   *)
(* `frame_unused_gas` alone while a spill-down conjunct would be      *)
(* false there.  The measure is spill-invariant on purpose, as its    *)
(* definition's comment says, and it is both the quantity this bound  *)
(* needs and the one the step rules can be argued about.              *)

Theorem same_frame_rel_preserves_gas_stack_ok:
  same_frame_rel s s' ∧ gas_stack_ok s ∧
  frame_unused_gas (FST (HD s'.contexts)) ≤
  frame_unused_gas (FST (HD s.contexts))
  ⇒ gas_stack_ok s'
Proof
  rw[gas_stack_ok_def, same_frame_rel_def] >>
  Cases_on`s.contexts` >- gvs[] >> fs[] >> BasicProvers.VAR_EQ_TAC >>
  Cases_on`s'.contexts` >- gvs[] >> fs[unused_gas_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  Cases_on`i` >> simp[]
QED

(* --- handle_create preserves both invariants (contexts structure    *)
(* unchanged, only head.gasUsed/accounts modified) --- *)

Theorem handle_create_preserves_stack_room_ok:
  stack_room_ok s ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s')
  ⇒ stack_room_ok s'
Proof
  (* EIP-8037: `stack_room_ok` reads the frames below the head only, and the
     creation charge -- the part of `handle_create` the phase 3 deposit
     added -- touches the head frame's meters alone, so the tail the
     invariant reads is the one `handle_create_preserves_tl_and_snd_hd`
     already pins. *)
  rw[stack_room_ok_def]
  >> drule_all handle_create_preserves_tl_and_snd_hd
  >> strip_tac
  >> simp[]
QED

(* EIP-8037: an operation that leaves the frames below the head alone and
   does not raise the head frame's `frame_unused_gas` keeps `gas_stack_ok`:
   every bound the invariant states is read off a tail frame -- the same
   frame in both states -- and the unused gas of the frames above it, of
   which only the head's moved, in the safe direction.  The hypothesis is
   the head frame's measure rather than a pair of meter fields, for the
   reason the comment on `same_frame_rel_preserves_gas_stack_ok` gives. *)
Theorem gas_stack_ok_same_tail_transfer:
  gas_stack_ok s ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧
  TL s'.contexts = TL s.contexts ∧
  frame_unused_gas (FST (HD s'.contexts)) ≤
  frame_unused_gas (FST (HD s.contexts))
  ⇒ gas_stack_ok s'
Proof
  rw[gas_stack_ok_def] >>
  Cases_on`s.contexts` >- gvs[] >> fs[] >> BasicProvers.VAR_EQ_TAC >>
  Cases_on`s'.contexts` >- gvs[] >> fs[unused_gas_def] >>
  first_x_assum(qspec_then`i`mp_tac) >>
  Cases_on`i` >> simp[]
QED

(* EIP-8037: the creation charge's lemmas are stated about the `INR` result,
   so the `INL` arm of a case split on that result is the arm that cannot
   happen.  The result is polymorphic in the success type and impossible at
   every instance of it, not only at `unit`, so `handle_create_INR` is
   instantiated at this statement's own type variable. *)
Theorem handle_create_not_inl[local]:
  handle_create e s = (INL (x:'a), s') ⇒ F
Proof
  strip_tac
  >> qspec_then`e`mp_tac(Q.GEN`e`(INST_TYPE[alpha |-> ``:'a``]handle_create_INR))
  >> gvs[]
QED

Theorem handle_create_preserves_gas_stack_ok:
  gas_stack_ok s ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s')
  ⇒ gas_stack_ok s'
Proof
  strip_tac
  >> Cases_on `q`
  (* EIP-8037: `handle_create` never returns a success, so the `INL` case of
     the input equation's result contradicts `handle_create_not_inl`; the
     `INR` case names the exception and leaves the state the input equation
     gave, which is the state the charge's lemmas below are stated about. *)
  >- (drule_all handle_create_not_inl >> gvs[])
  >> drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac
  >> drule_all handle_create_effective_leftover >> strip_tac
  >> drule_all handle_create_gasUsed_le_limit >> strip_tac
  (* EIP-8037: the creation charge takes execution gas out of the head frame
     and puts at most the same amount back into its spill, so the frame's
     unused gas does not rise; and it leaves the frames below the head alone.
     With that, the transfer above applies. *)
  >> `frame_unused_gas (FST (HD s'.contexts)) ≤
      frame_unused_gas (FST (HD s.contexts))` by
       (rw[frame_unused_gas_def] >> decide_tac)
  >> match_mp_tac gas_stack_ok_same_tail_transfer
  >> rw[]
QED

(* --- Linchpin: handle_exception at depth ≥ 2 returns INL under     *)
(* wf_state.                                                          *)
(*                                                                    *)
(* Every sub-operation succeeds:                                      *)
(*   - prefix (consume_gas gasLeft): gasLeft = callee.gasLimit -      *)
(*     callee.gasUsed ≤ callee.gasLimit (from wf_context) ✓          *)
(*   - n > 1: depth ≥ 2 ✓                                           *)
(*   - pop_and_incorporate_context → unuse_gas calleeGasLeft:         *)
(*     calleeGasLeft = callee.gasLimit - callee.gasUsed ≤             *)
(*     parent.gasUsed (from gas_stack_ok) ✓                          *)
(*   - push_stack: parent.stack < stack_limit (from stack_room_ok) ✓ *)
(*   - inc_pc, set_return_data, write_memory: always succeed ✓       *)

Theorem gas_stack_ok_parent_has_child_unused:
  gas_stack_ok s ∧ LENGTH s.contexts ≥ 2 ⇒
    (FST (EL 1 s.contexts)).gasUsed ≥
    (FST (HD s.contexts)).msgParams.gasLimit -
    (FST (HD s.contexts)).gasUsed
Proof
  rw[gas_stack_ok_def]
  >> first_x_assum(qspec_then `0` mp_tac)
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[unused_gas_def, frame_unused_gas_def]
QED

Theorem stack_room_ok_parent_stack:
  stack_room_ok s ∧ LENGTH s.contexts ≥ 2 ⇒
    LENGTH (FST (EL 1 s.contexts)).stack < stack_limit
Proof
  rw[stack_room_ok_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[]
QED

Theorem handle_exception_prefix_budget:
  s.contexts <> [] /\
  (FST (HD s.contexts)).gasUsed <= (FST (HD s.contexts)).msgParams.gasLimit ==>
  ?sp. (if ~(e = NONE) /\ e <> SOME Reverted then
          do restore_state_gas; gasLeft <- get_gas_left; consume_gas gasLeft;
             set_return_data [] od
        else if e = SOME Reverted then restore_state_gas else return ()) s = (INL (),sp) /\
       TL sp.contexts = TL s.contexts /\
       LENGTH sp.contexts = LENGTH s.contexts /\
       sp.contexts <> [] /\
       (FST (HD sp.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
       (FST (HD sp.contexts)).msgParams.gasLimit -
         (FST (HD sp.contexts)).gasUsed <= frame_unused_gas (FST (HD s.contexts))
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[restore_state_gas_def, forfeit_remaining_gas_def,
      set_return_data_def, ignore_bind_def, bind_def,
      get_current_context_def, set_current_context_def, return_def,
      frame_unused_gas_def, get_gas_left_def, consume_gas_def, assert_def]
QED

Theorem pop_and_incorporate_context_success_stack:
  s.contexts = (c,rb)::(p,rp)::tail /\
  c.msgParams.gasLimit - c.gasUsed <= p.gasUsed ==>
  ?sp. pop_and_incorporate_context b s = (INL (),sp) /\
       LENGTH sp.contexts = SUC (LENGTH tail) /\
       (FST (HD sp.contexts)).stack = p.stack
Proof
  strip_tac >>
  simp[pop_and_incorporate_context_def, credit_new_account_def,
       credit_state_gas_refund_def, get_gas_left_def,
       pop_context_def, unuse_gas_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, return_def,
       assert_def, absorb_state_gas_def] >>
  Cases_on `b` >>
  (* EIP-8037: the new-account credit is the one step of the pop that the
     state's shape does not settle -- it is the popped frame's flag, which
     the merge below no longer reads -- so it has to be taken here; in
     either branch the repayment reduces to a concrete state. *)
  Cases_on `c.msgParams.newAccountCharged` >>
  simp[push_logs_def, update_gas_refund_def, repay_state_gas_spill_def,
       repay_state_gas_spill_context_def, credit_new_account_def,
       credit_state_gas_refund_def, set_rollback_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def]
QED

Theorem handle_exception_ge_2_inl:
  EVERY (wf_context o FST) s.contexts ∧ stack_room_ok s ∧ gas_stack_ok s ∧
  LENGTH s.contexts ≥ 2 ∧ handle_exception e s = (q, s') ⇒
    ISL q
Proof
  strip_tac >>
  `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  `(FST (HD s.contexts)).gasUsed <=
     (FST (HD s.contexts)).msgParams.gasLimit` by
    (Cases_on `s.contexts` >> gvs[wf_context_def]) >>
  drule_all handle_exception_prefix_budget >>
  disch_then (qspec_then `e` strip_assume_tac) >>
  `frame_unused_gas (FST (HD s.contexts)) <=
     (FST (EL 1 s.contexts)).gasUsed` by
    (qhdtm_x_assum `gas_stack_ok` mp_tac >>
     simp[gas_stack_ok_def] >>
     disch_then (qspec_then `0` mp_tac) >>
     Cases_on `s.contexts` >> gvs[unused_gas_def]) >>
  `LENGTH (FST (EL 1 s.contexts)).stack < stack_limit` by
    metis_tac[stack_room_ok_parent_stack] >>
  qhdtm_x_assum `handle_exception` mp_tac >>
  simp[handle_exception_decomp, bind_def] >>
  simp[handle_ex_helper_def, get_num_contexts_def, bind_def, return_def] >>
  Cases_on `sp.contexts` >> fs[] >>
  rename1 `sp.contexts = child::rest` >>
  Cases_on `rest` >> fs[] >>
  rename1 `sp.contexts = child::parent::tail` >>
  PairCases_on `child` >> PairCases_on `parent` >> gvs[] >>
  `child0.msgParams.gasLimit - child0.gasUsed <= parent0.gasUsed` by
    (Cases_on `s.contexts` >> gvs[] >> decide_tac) >>
  `sp.contexts = (child0,child1)::(parent0,parent1)::tail` by metis_tac[] >>
  drule_all pop_and_incorporate_context_success_stack >>
  disch_then (qspec_then `e = NONE` strip_assume_tac) >>
  simp[get_return_data_def, get_output_to_def, get_current_context_def,
       bind_def, return_def, ignore_bind_def] >>
  `LENGTH parent0.stack < stack_limit` by
    (Cases_on `s.contexts` >> gvs[]) >>
  Cases_on `sp'.contexts` >> gvs[] >>
  simp[after_pop_def, inc_pc_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, return_def] >>
  Cases_on `(FST (HD s.contexts)).msgParams.outputTo` >>
  Cases_on `e = NONE` >>
  gvs[set_return_data_def, push_stack_def, write_memory_def,
      bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, assert_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[]
QED
