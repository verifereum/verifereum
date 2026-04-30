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
  vfmStaticCalls vfmStoragePredicates vfmSameFrame
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
     get_current_context_def, return_def]
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
          get_current_context_def,
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
  \\ gvs[get_gas_left_def, get_current_context_def,
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
  simp[handle_exception_def] >>
  qmatch_goalsub_abbrev_tac`ignore_bind prefix _` >>
  simp[ignore_bind_def, bind_def] >>
  TOP_CASE_TAC >>
  `r'.rollback = s.rollback ∧ LENGTH r'.contexts = LENGTH s.contexts` by (
    gvs[Abbr`prefix`,return_def,AllCaseEqs(),COND_RATOR,
        bind_def,ignore_bind_def,get_gas_left_def,
        get_current_context_def,fail_def,return_def,
        consume_gas_def,set_current_context_def,
        set_return_data_def,assert_def] >>
    Cases_on`s.contexts` >> gvs[] ) >>
  reverse TOP_CASE_TAC >- (rw[] >> gvs[]) >>
  simp[get_num_contexts_def, return_def] >>
  IF_CASES_TAC >- (rw[reraise_def] >> gvs[]) >>
  simp[bind_def, get_return_data_def, get_output_to_def, return_def,
       get_current_context_def] >>
  IF_CASES_TAC >> gvs[] >>
  TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac`pop_and_incorporate_context _ s1 = (r2, s2)` >>
  `s2.contexts <> [] ∧ (ISR r2 ⇒ s2.rollback = s1.rollback)
   ∧ (ISL r2 ⇒ LENGTH s2.contexts < LENGTH s1.contexts)` by (
    gvs[pop_and_incorporate_context_def] >>
    gvs[bind_def, AllCaseEqs(),ignore_bind_def,get_gas_left_def,return_def,
        pop_context_def,fail_def,get_current_context_def,unuse_gas_def,
        assert_def,set_current_context_def,COND_RATOR,
        update_gas_refund_def,push_logs_def,set_rollback_def] >>
    Cases_on`s1.contexts` >> gvs[] ) >>
  reverse TOP_CASE_TAC >- (rw[] >> gvs[]) >>
  gvs[] >>
  simp[inc_pc_def, get_current_context_def, return_def, bind_def,
       ignore_bind_def,set_current_context_def] >>
  simp[AllCaseEqs(), return_destination_CASE_rator, bind_def,
       ignore_bind_def, set_return_data_def, get_current_context_def,
       return_def, push_stack_def, assert_def, COND_RATOR, fail_def] >>
  rw[] >> gvs[set_current_context_def, return_def] >>
  qmatch_asmsub_abbrev_tac`write_memory i bs` >>
  mp_tac preserves_same_frame_write_memory >>
  rewrite_tac[preserves_same_frame_def] >>
  disch_then drule >>
  simp[same_frame_rel_def]
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
  strip_tac
  >> qhdtm_x_assum `handle_exception` mp_tac
  >> simp[handle_exception_def]
  >> simp[ignore_bind_def, Once bind_def]
  >> qmatch_goalsub_abbrev_tac `prefix s`
  >> `preserves_same_frame prefix` by (
       simp[Abbr`prefix`] >> IF_CASES_TAC >> simp[])
  >> Cases_on `prefix s`
  >> qmatch_asmsub_rename_tac `prefix s = (res, sp)`
  >> `same_frame_rel s sp` by metis_tac[preserves_same_frame_def]
  >> `LENGTH sp.contexts = LENGTH s.contexts` by fs[same_frame_rel_def]
  >> `sp.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> reverse (Cases_on `res`) >> simp[]
  >- (strip_tac >> gvs[])
  >> simp[Once bind_def, get_num_contexts_def, return_def]
  >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[])
  >> simp[Once bind_def]
  >> simp[get_return_data_def, bind_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `sp.contexts` >> fs[]
  >> simp[get_output_to_def, bind_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `pop_and_incorporate_context (e = NONE) sp` >> simp[]
  >> Cases_on `q'` >> simp[]
  >- ((* INL case: pop succeeded, shrinks by exactly 1. *)
      `LENGTH r.contexts + 1 = LENGTH sp.contexts` by (
        qhdtm_x_assum `pop_and_incorporate_context` mp_tac
        >> gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
               get_gas_left_def, return_def, pop_context_def, fail_def,
               unuse_gas_def, get_current_context_def,
               set_current_context_def, push_logs_def,
               update_gas_refund_def, set_rollback_def, assert_def,
               AllCaseEqs()]
        >> strip_tac >> gvs[] >> pop_assum mp_tac
        >> IF_CASES_TAC
        >> gvs[bind_def, get_current_context_def, set_current_context_def,
               return_def, fail_def, set_rollback_def, AllCaseEqs()]
        >> strip_tac >> gvs[])
      >> simp[inc_pc_def, bind_def, get_current_context_def,
              ignore_bind_def, set_current_context_def]
      >> IF_CASES_TAC >> gvs[return_def, return_destination_CASE_rator]
      >> rw[] >> gvs[AllCaseEqs(),bind_def,COND_RATOR]
      >> gvs[set_return_data_def,push_stack_def,write_memory_def,
             get_current_context_def,bind_def,return_def,fail_def,
             assert_def,pop_and_incorporate_context_def,AllCaseEqs(),
             ignore_bind_def,set_current_context_def])
  (* INR case: pop failed. *)
  >> strip_tac >> gvs[]
  >> gvs[set_return_data_def,push_stack_def,write_memory_def,
         get_current_context_def,bind_def,return_def,fail_def,
         assert_def,pop_and_incorporate_context_def,AllCaseEqs(),
         ignore_bind_def,set_current_context_def,COND_RATOR,
         pop_context_def,unuse_gas_def,push_logs_def,update_gas_refund_def,
         get_gas_left_def,set_rollback_def]
QED

(* When LENGTH ≥ 2 and wf_state, handle_exception takes the pop branch and
   shrinks by exactly 1. The n ≤ 1 reraise branch is not taken, and the
   prefix (consume_gas) succeeds because wf_state ensures gasUsed ≤ gasLimit. *)
Theorem handle_exception_ge_2_pops:
  EVERY (wf_context o FST) s.contexts ∧ LENGTH s.contexts ≥ 2 ∧ handle_exception e s = (q, s') ⇒
  LENGTH s'.contexts + 1 = LENGTH s.contexts (* ∧ ISL q *)
Proof
  strip_tac
  >> `s.contexts ≠ []` by (Cases_on `s.contexts` >> fs[])
  >> `wf_context (FST (HD s.contexts))` by (
       Cases_on `s.contexts` >> gvs[EVERY_MEM])
  >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s.contexts)).msgParams.gasLimit`
       by gvs[wf_context_def]
  >> qhdtm_x_assum `handle_exception` mp_tac
  >> simp[handle_exception_def]
  >> simp[ignore_bind_def, Once bind_def]
  >> qmatch_goalsub_abbrev_tac `prefix s`
  (* prefix always succeeds (INL) when gasUsed ≤ gasLimit *)
  >> `∃r sp. prefix s = (INL r, sp) ∧ LENGTH sp.contexts = LENGTH s.contexts` by (
       simp[Abbr`prefix`]
       >> IF_CASES_TAC >> simp[return_def]
       >> simp[bind_def, get_gas_left_def, get_current_context_def, return_def]
       >> simp[consume_gas_def, bind_def, assert_def, return_def, ignore_bind_def,
               get_current_context_def, set_current_context_def]
       >> simp[ignore_bind_def, set_return_data_def, bind_def,
               get_current_context_def, set_current_context_def, return_def])
  >> gvs[]
  >> simp[Once bind_def, get_num_contexts_def, return_def]
  (* The key: LENGTH sp.contexts ≥ 2 means ¬(n ≤ 1), so pop branch taken *)
  >> `¬(LENGTH sp.contexts ≤ 1)` by simp[]
  >> simp[]
  >> simp[Once bind_def]
  >> simp[get_return_data_def, bind_def, get_current_context_def,
          return_def, fail_def]
  >> `sp.contexts ≠ []` by (Cases_on `sp.contexts` >> gvs[])
  >> Cases_on `sp.contexts` >> fs[]
  >> simp[get_output_to_def, bind_def, get_current_context_def,
          return_def, fail_def]
  >> Cases_on `pop_and_incorporate_context (e = NONE) sp` >> simp[]
  >> `EVERY (wf_context o FST) sp.contexts`
  by (
    gvs[Abbr`prefix`,COND_RATOR,AllCaseEqs(),return_def] >>
    gvs[bind_def,ignore_bind_def,AllCaseEqs()] >>
    gvs[EVERY_MEM,consume_gas_def,get_gas_left_def,set_return_data_def,
        get_current_context_def,set_current_context_def,bind_def,
        return_def,fail_def,AllCaseEqs(),ignore_bind_def,assert_def] >>
    Cases_on`s.contexts` >> gvs[] >>
    gvs[wf_context_def] )
  >> Cases_on `q'` >> simp[]
  >- ((* INL case: pop succeeded, shrinks by exactly 1. *)
      `LENGTH r.contexts + 1 = LENGTH sp.contexts` by (
        qhdtm_x_assum `pop_and_incorporate_context` mp_tac
        >> gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def,
               get_gas_left_def, return_def, pop_context_def, fail_def,
               unuse_gas_def, get_current_context_def,
               set_current_context_def, push_logs_def,
               update_gas_refund_def, set_rollback_def, assert_def,
               AllCaseEqs()]
        >> strip_tac >> gvs[] >> pop_assum mp_tac
        >> IF_CASES_TAC
        >> gvs[bind_def, get_current_context_def, set_current_context_def,
               return_def, fail_def, set_rollback_def, AllCaseEqs()]
        >> strip_tac >> gvs[])
      >> simp[inc_pc_def, bind_def, get_current_context_def,
              ignore_bind_def, set_current_context_def]
      >> IF_CASES_TAC >> gvs[return_def, return_destination_CASE_rator]
      >> strip_tac
      >> gvs[set_return_data_def,push_stack_def,write_memory_def,
             get_current_context_def,bind_def,return_def,fail_def,
             assert_def,pop_and_incorporate_context_def,AllCaseEqs(),
             bind_def,ignore_bind_def,set_current_context_def, COND_RATOR,
             push_logs_def, unuse_gas_def, update_gas_refund_def,
             get_gas_left_def, pop_context_def, set_rollback_def]
      >> Cases_on`t` >> gvs[]
      >> gvs[EVERY_MEM, wf_context_def]
  )
  (* INR case: pop failed. *)
  >> strip_tac >> gvs[]
  >> gvs[set_return_data_def,push_stack_def,write_memory_def,
         get_current_context_def,bind_def,return_def,fail_def,
         assert_def,pop_and_incorporate_context_def,AllCaseEqs(),
         ignore_bind_def,set_current_context_def,COND_RATOR,
         pop_context_def,unuse_gas_def,push_logs_def,update_gas_refund_def,
         get_gas_left_def,set_rollback_def]
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
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> gvs[AllCaseEqs()]
  >> Cases_on `s.contexts` >> fs[]
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
     update_accounts_def, assert_def, set_current_context_def,
     wf_state_def, all_accounts_def, wf_context_def]
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def, wf_state_def, all_accounts_def, wf_context_def,
         return_destination_CASE_rator, vfmTypesTheory.option_CASE_rator]
  >> Cases_on `s.contexts` >> gvs[wf_context_def]
  >> gvs[update_account_def, lookup_account_def, APPLY_UPDATE_THM,
         wf_accounts_def] >> rw[] >>
     gvs[wf_account_state_def, EVAL``max_code_size``]
QED

Theorem handle_create_preserves_wf_contexts:
  EVERY (wf_context o FST) s.contexts ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s') ⇒
  EVERY (wf_context o FST) s'.contexts
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def,
     wf_context_def]
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def, wf_context_def,
         return_destination_CASE_rator, vfmTypesTheory.option_CASE_rator]
  >> Cases_on `s.contexts` >> gvs[wf_context_def]
QED

(* Generic handle_exception pop structure: when it shrinks, the contexts
   take the form (new_head, SND parent) :: rest with msgParams preserved,
   and the rollback is either s.rollback (success) or callee_rb (failure). *)
Theorem handle_exception_pop_generic_gen:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_exception e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    (s'.rollback = s.rollback ∨ s'.rollback = callee_rb) ∧
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams
Proof
  strip_tac
  >> Cases_on `parent`
  >> Cases_on `callee.msgParams.outputTo`
  >> Cases_on `e = NONE`
  >> Cases_on `e = SOME Reverted`
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

(* handle_create preserves TL(contexts) and SND(HD contexts).
   For Code+NONE case it modifies HD(contexts) gasUsed; for other
   cases it's an exact reraise. In both sub-cases TL and SND-of-HD
   are unchanged. *)
Theorem handle_create_preserves_tl_and_snd_hd:
  handle_create e s = (q, s') ∧ s.contexts ≠ [] ⇒
    s'.contexts ≠ [] ∧
    TL s'.contexts = TL s.contexts ∧
    SND (HD s'.contexts) = SND (HD s.contexts) ∧
    (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  rw[handle_create_def, bind_def, ignore_bind_def,
     get_return_data_def, get_output_to_def, get_current_context_def,
     return_def, fail_def, reraise_def, consume_gas_def,
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
  >> gvs[AllCaseEqs()]
  >> Cases_on `s.contexts` >> fs[]
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
     update_accounts_def, assert_def, set_current_context_def]
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
     update_accounts_def, assert_def, set_current_context_def]
  >> BasicProvers.every_case_tac
  >> gvs[AllCaseEqs(), reraise_def, fail_def, bind_def, ignore_bind_def,
         assert_def, get_current_context_def, set_current_context_def,
         update_accounts_def, return_def]
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
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    ((∀a. (lookup_account a s'.rollback.accounts).storage =
          (lookup_account a s.rollback.accounts).storage) ∨
     (∀a. (lookup_account a s'.rollback.accounts).storage =
          (lookup_account a callee_rb.accounts).storage)) ∧
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams
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
  >> drule_all handle_exception_pop_generic_gen
  >> strip_tac >> gvs[]
  >> mp_tac (INST_TYPE[alpha|->``:unit``]preserves_storage_handle_create)
  >> rewrite_tac[preserves_storage_def]
  >> disch_then drule
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

(* Strengthening of handle_step_pop_generic_gen that pairs each
   storage disjunct with the matching accesses subset. *)
Theorem handle_step_pop_generic_gen_paired:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  handle_step e s = (q, s') ∧
  LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_parent_ctx.
      s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
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
  >> drule_all handle_exception_pop_generic_gen
  >> strip_tac >> gvs[]
  >> drule handle_create_preserves_accesses
  >> mp_tac (INST_TYPE[alpha|->``:unit``]preserves_storage_handle_create)
  >> rewrite_tac[preserves_storage_def]
  >> disch_then drule
  >> gvs[lookup_storage_def, FUN_EQ_THM]
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
  >> simp[Once handle_exception_def]
  >> simp[ignore_bind_def, Once bind_def]
  >> qmatch_goalsub_abbrev_tac `pair_CASE (prefix s1)`
  >> `preserves_same_frame prefix` by (
       simp[Abbr`prefix`]
       >> IF_CASES_TAC >> simp[]
       >> irule preserves_same_frame_ignore_bind >> simp[]
       >> irule preserves_same_frame_bind >> simp[])
  >> Cases_on `prefix s1`
  >> qmatch_asmsub_rename_tac `prefix s1 = (res, sp)`
  >> `s1.contexts ≠ []` by (Cases_on `s1.contexts` >> fs[])
  >> `same_frame_rel s1 sp` by (
       Cases_on `res` >> metis_tac[preserves_same_frame_def])
  >> `LENGTH sp.contexts = 1` by fs[same_frame_rel_def]
  >> reverse (Cases_on `res`) >> simp[]
  >- (strip_tac >> gvs[])
  >> simp[Once bind_def, get_num_contexts_def, return_def]
  >> simp[reraise_def]
  >> strip_tac >> gvs[]
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

