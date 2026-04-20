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
  vfmStaticCalls vfmSameFrame
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
     get_current_context_def, ok_state_def, return_def]
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
          get_current_context_def, ok_state_def,
          set_current_context_def, update_accounts_def,
          reraise_def]
      (* Each branch: either fail (refl), or consume_gas + update_accounts.
         The update is at address = c, which equals the head's callee by
         outputTo_consistent. *)
      \\ gvs[outputTo_consistent_def]
      \\ rw[same_frame_rel_def, callee_local_changes_def,
            lookup_account_def, update_account_def,
            APPLY_UPDATE_THM]
      \\ rw[]))
  \\ (* e = SOME _ — reraise *)
    gvs[reraise_def]
  \\ Cases_on `h0.msgParams.outputTo` \\ gvs[reraise_def]
  \\ irule same_frame_rel_refl \\ simp[]
QED

(* handle_exception either reraises (n ≤ 1) or pops (n > 1). When the
   length is preserved, the reraise branch was taken. The prefix
   (consume_gas + set_return_data in non-Revert error cases) is
   preserves_same_frame. *)
Theorem handle_exception_same_frame:
  s.contexts ≠ [] ∧
  handle_exception e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  simp[handle_exception_def, bind_def, ignore_bind_def]
  \\ strip_tac
  \\ reverse (Cases_on`LENGTH s.contexts ≤ 1`)
  >- (
    gvs[AllCaseEqs(), COND_RATOR, get_num_contexts_def,
        return_def, reraise_def] >>
    TRY (
      gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def,
          set_return_data_def, consume_gas_def, get_gas_left_def,
          assert_def, set_current_context_def, fail_def,
          get_current_context_def, same_frame_rel_def] >> NO_TAC ) >>
    rename1`_ s1 = (_,s')` >>
    TRY (
      rename1`_ s = (_,s1)` >>
      `LENGTH s1.contexts = LENGTH s.contexts` by 
        gvs[bind_def, ignore_bind_def, AllCaseEqs(),
            get_gas_left_def, consume_gas_def, assert_def,
            set_return_data_def, fail_def, return_def,
            set_current_context_def, get_current_context_def]) >>
     `LENGTH s'.contexts <> LENGTH s1.contexts` suffices_by gvs[] >>
     qpat_x_assum`_ = (_,s')`mp_tac >>
     pop_assum kall_tac >>
     simp[bind_def] >>
     simp[get_return_data_def, bind_def,
          return_def, get_current_context_def] >>
     TRY IF_CASES_TAC >> gvs[return_def, fail_def] >>
     simp[get_output_to_def, bind_def, get_current_context_def] >>
     gvs[return_def] >>
     simp[pop_and_incorporate_context_def,bind_def] >>
     simp[get_gas_left_def, bind_def, get_current_context_def, return_def] >>
     simp[pop_context_def, return_def] >>
     simp[ignore_bind_def, bind_def] >>
     CASE_TAC >>
     drule_at Any cp_imp_length_contexts_preserved >>
     simp[] >>
     Cases_on`s1.contexts` >> gvs[] >>
     Cases_on`t` >> gvs[] >> strip_tac >>
     BasicProvers.TOP_CASE_TAC >> (
     reverse BasicProvers.TOP_CASE_TAC >- (
       rw[] >> gvs[AllCaseEqs(),set_rollback_def,return_def] >>
       drule_at Any psf_imp_length_contexts_preserved >> rw[] >>
       gvs[push_logs_def, bind_def, get_current_context_def, AllCaseEqs(),
           return_def, set_current_context_def]
     ) ) >>
     BasicProvers.TOP_CASE_TAC >>
     drule_at Any psf_imp_length_contexts_preserved >>
     (impl_tac >- (simp[] >> gvs[AllCaseEqs(), set_rollback_def, return_def] >>
                   strip_tac >> gvs[] >>
                   qhdtm_x_assum`update_gas_refund`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] >>
                   qhdtm_x_assum`push_logs`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] 
     )) >> strip_tac >> (
     reverse BasicProvers.TOP_CASE_TAC >- (
       rw[] >>
       strip_tac >>  gvs[AllCaseEqs(),set_rollback_def,return_def] >>
                   qhdtm_x_assum`update_gas_refund`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] >>
                   qhdtm_x_assum`push_logs`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[]
     ) ) >>
     simp[AllCaseEqs(),return_destination_CASE_rator,bind_def] >>
     rw[] >> gvs[push_stack_def, set_return_data_def, get_current_context_def,
                 set_current_context_def, bind_def, return_def, assert_def,
                 fail_def,AllCaseEqs(),ignore_bind_def] >>
     strip_tac >> gvs[set_rollback_def, return_def] >>
     gvs[write_memory_def, bind_def, ignore_bind_def,
         get_current_context_def, set_current_context_def, assert_def,
         fail_def,return_def] >>
                   qhdtm_x_assum`update_gas_refund`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] >>
                   qhdtm_x_assum`push_logs`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[]
  )
  \\ gvs[AllCaseEqs(), COND_RATOR]
  (* Various branches: the prefix may be a consume_gas + set_return_data
     block or just return (); then n <- get_num_contexts; if n ≤ 1
     reraise else pop. The length hypothesis rules out the pop branch. *)
  \\ gvs[get_gas_left_def, get_current_context_def, ok_state_def,
         return_def, get_num_contexts_def, reraise_def, fail_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_return_data_def, get_output_to_def]
  \\ gvs[bind_def, ignore_bind_def, AllCaseEqs(), get_current_context_def,
         assert_def, fail_def, return_def, set_current_context_def,
         inc_pc_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ (* In each remaining branch, s' equals s with possibly modified
        head context (gasUsed up, returnData cleared). *)
    PairCases_on `h` \\ gvs[]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  \\ gvs[AllCaseEqs(), rich_listTheory.IS_PREFIX_REFL]
QED

(* ---------------- handle_step under length preservation --------- *)

(* handle_step = if vfm_abort e then reraise e
                 else handle (handle_create e) handle_exception.
   The reraise case is trivial. In the handle case, handle_create always
   returns INR, so handle_exception is always invoked; we compose
   psf_handle_create with the same-length version of
   handle_exception_same_frame. *)
Theorem handle_step_same_frame:
  outputTo_consistent s ∧
  handle_step e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  rw[handle_step_def]
  >- (
    (* vfm_abort e: reraise, state unchanged *)
    gvs[reraise_def]
    \\ irule same_frame_rel_refl
    \\ gvs[outputTo_consistent_def])
  \\ (* handle (handle_create e) handle_exception s *)
    gvs[handle_def]
  \\ `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  \\ drule_then(qspec_then`e`mp_tac) (INST_TYPE[alpha |-> ``:unit``]handle_create_INR)
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
  \\ `same_frame_rel s1 s'`
     by (irule handle_exception_same_frame \\ metis_tac[])
  \\ metis_tac[same_frame_rel_trans]
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
   consumed more gas than the parent had — possible if ok_state is
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
  >> gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def]
  >> gvs[get_gas_left_def, get_current_context_def, return_def,
         pop_context_def]
  >> gvs[unuse_gas_def, bind_def, get_current_context_def, return_def,
         assert_def, set_current_context_def, set_rollback_def,
         fail_def, ignore_bind_def]
  >> Cases_on `parent` >> gvs[]
  >> qmatch_asmsub_abbrev_tac `if cond then _ else _`
  >> Cases_on `cond` >> gvs[]
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
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
         set_rollback_def, unuse_gas_def, AllCaseEqs()]
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
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
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
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
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
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
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
          get_current_context_def, return_def, reraise_def]
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
          get_current_context_def, return_def, reraise_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> simp[AllCaseEqs()]
  >> strip_tac
  >> `LENGTH s'.contexts < LENGTH s.contexts` by simp[]
  >> drule_all handle_exception_pop_failure_memory_effect_gen
  >> simp[]
QED
