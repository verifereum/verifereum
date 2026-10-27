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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* pop_context removes the head of contexts, returns it, leaves
   everything else alone. *)
Theorem pop_context_effect:
  s.contexts ≠ [] ⇒
  pop_context s = (q, s') ⇒
    q = INL (HD s.contexts) ∧ s' = s with contexts := TL s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* push_context adds to the head. *)
Theorem push_context_effect:
  push_context crb s = (q, s') ⇒
    q = INL () ∧ s' = s with contexts := crb :: s.contexts
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* When e <> NONE, handle_create always reraises regardless of outputTo.
   The Code+NONE branch is the only non-reraise path, and e <> NONE
   rules it out. *)
Theorem handle_create_reraises_when_some:
  e <> NONE /\ s.contexts <> [] ==> handle_create e s = reraise e s
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* When LENGTH ≥ 2 and wf_state, handle_exception takes the pop branch and
   shrinks by exactly 1. The n ≤ 1 reraise branch is not taken, and the
   prefix (consume_gas) succeeds because wf_state ensures gasUsed ≤ gasLimit. *)
Theorem handle_exception_ge_2_pops:
  EVERY (wf_context o FST) s.contexts ∧ LENGTH s.contexts ≥ 2 ∧ handle_exception e s = (q, s') ⇒
  LENGTH s'.contexts + 1 = LENGTH s.contexts (* ∧ ISL q *)
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_create doesn't change contexts length (it may modify
   account.code for Code outputTo success but doesn't touch contexts). *)
Theorem handle_create_preserves_length:
  handle_create e s = (q, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_create preserves wf_state: it doesn't modify stack, gasUsed, or
   msgParams - only return_data/output_to/accounts. *)
Theorem handle_create_preserves_wf_state:
  wf_state s ∧ handle_create e s = (q, s') ⇒
  wf_state s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_preserves_wf_contexts:
  EVERY (wf_context o FST) s.contexts ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s') ⇒
  EVERY (wf_context o FST) s'.contexts
Proof
  cheat  (* SCAFFOLD *)
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
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
      new_parent_ctx.gasUsed ≥
        (FST parent).gasUsed -
        (callee.msgParams.gasLimit - callee.gasUsed)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* handle_create preserves .accesses: all primitives within
   handle_create are either reads, preserves_rollback, or update_accounts
   with a function touching only .accounts (not .accesses). *)
Theorem handle_create_preserves_accesses:
  handle_create e s = (q, s') ⇒
  s'.rollback.accesses = s.rollback.accesses
Proof
  cheat  (* SCAFFOLD *)
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
      new_parent_ctx.msgParams = (FST parent).msgParams ∧
      new_parent_ctx.gasUsed ≥
        (FST parent).gasUsed -
        (callee.msgParams.gasLimit - callee.gasUsed)
Proof
  cheat  (* SCAFFOLD *)
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
      new_parent_ctx.gasUsed ≥
        (FST parent).gasUsed -
        (callee.msgParams.gasLimit - callee.gasUsed) ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet callee_rb.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a callee_rb.accounts).storage)))
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_preserves_length_1:
  handle_step e s = (q, s') ∧ LENGTH s.contexts = 1 ⇒
  LENGTH s'.contexts = 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_step reduces contexts by at most one. *)
Theorem handle_step_shrinks_by_one:
  handle_step e s = (q, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts + 1 ≥ LENGTH s.contexts ∧
  LENGTH s'.contexts ≤ LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* When ¬vfm_abort e, wf_context on all contexts, and LENGTH ≥ 2,
   handle_step shrinks by exactly 1. *)
Theorem handle_step_not_abort_pops:
  EVERY (wf_context o FST) s.contexts ∧ ¬vfm_abort e ∧ LENGTH s.contexts ≥ 2 ∧
  handle_step e s = (q, s') ⇒
  LENGTH s'.contexts + 1 = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* --- Case 1: same_frame_rel preserves gas_stack_ok under           *)
(* gasUsed monotonicity.                                              *)
(*                                                                    *)
(* Key: head's gasUsed never decreases in a same-frame step.         *)
(* consume_gas always increases it; unuse_gas decreases it, but only  *)
(* after consume_gas increased it by more (net positive). All other   *)
(* same-frame ops leave gasUsed unchanged. Since gasLimit =          *)
(* msgParams.gasLimit is preserved by same_frame_rel, the bound      *)
(* gasLimit - gasUsed can only shrink, preserving the inequality.    *)

Theorem same_frame_rel_preserves_gas_stack_ok:
  same_frame_rel s s' ∧ gas_stack_ok s ∧
  (FST (HD s'.contexts)).gasUsed ≥ (FST (HD s.contexts)).gasUsed
  ⇒ gas_stack_ok s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- handle_create preserves both invariants (contexts structure    *)
(* unchanged, only head.gasUsed/accounts modified) --- *)

Theorem handle_create_preserves_stack_room_ok:
  stack_room_ok s ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s')
  ⇒ stack_room_ok s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_preserves_gas_stack_ok:
  gas_stack_ok s ∧ s.contexts ≠ [] ∧ handle_create e s = (q, s')
  ⇒ gas_stack_ok s'
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem stack_room_ok_parent_stack:
  stack_room_ok s ∧ LENGTH s.contexts ≥ 2 ⇒
    LENGTH (FST (EL 1 s.contexts)).stack < stack_limit
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_ge_2_inl:
  EVERY (wf_context o FST) s.contexts ∧ stack_room_ok s ∧ gas_stack_ok s ∧
  LENGTH s.contexts ≥ 2 ∧ handle_exception e s = (q, s') ⇒
    ISL q
Proof
  cheat  (* SCAFFOLD *)
QED
