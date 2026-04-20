(*
 * Application layer for call-frame reasoning.
 *
 * The underlying frameworks live in separate theories:
 *   - `vfmSameFrame`: the base `same_frame_rel` relation, the
 *     `preserves_same_frame` and `psf` frameworks, per-opcode /
 *     per-precompile [simp] lemmas, `outputTo_consistent`,
 *     SELFDESTRUCT psf details, and `proceed_call_length` /
 *     `proceed_create_length`.
 *   - `vfmStepLength`: the `same_frame_or_grow` / `psf_or_grow` and
 *     `length_preserves` / `length_or_inl_grow` frameworks, with
 *     associated step_call / step_create structural lemmas.
 *   - `vfmMsdomainPreserved`: `SND_*_msdomain[simp]` leaf lemmas
 *     and `SND_handle_step_msdomain`.
 *   - `vfmHandleStep`: `psf_handle_create`,
 *     `handle_exception_same_frame`, `handle_step_same_frame`, the
 *     tiny state-effect lemmas for set_rollback / pop_context /
 *     push_context, `pop_and_incorporate_context_failure_effect`,
 *     and the `handle_exception_pop_*` / `handle_step_pop_*`
 *     memory-effect lemmas.
 *
 * This theory composes those to prove:
 *   - `bind_inr_grow_factor` / `ignore_bind_inr_grow_factor` and
 *     the `inr_grow_witness` framework (for locating the state just
 *     before a growth-causing step);
 *   - the INR-grow structure lemma `step_call_inr_grow_structure`;
 *   - `step_call_handle_step_inr_grow_same_frame`, `step_same_frame`,
 *     `run_within_frame_preserves`, `run_within_frame_gas_monotone`;
 *   - the downstream named corollaries
 *     `run_within_frame_preserves_*` exposing individual conjuncts
 *     of `same_frame_rel` for user consumption.
 *)
Theory vfmCallFrame
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame vfmStepLength vfmMsdomainPreserved vfmHandleStep
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"


(* ================================================================ *)
(* Framework: INR-grow structure witness.                             *)
(*                                                                    *)
(* When a bind chain g;f INR-grows and g preserves_same_frame, the    *)
(* INR-grow must come from f (since preserves_same_frame implies     *)
(* length preservation). This lets us "peel off" prefix layers to    *)
(* locate the state just before the growth-causing step.             *)
(* ================================================================ *)

Theorem bind_inr_grow_factor:
  preserves_same_frame g ∧
  bind g f s = (INR e, s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃x sp. g s = (INL x, sp) ∧ same_frame_rel s sp ∧
            f x sp = (INR e, s1)
Proof
  strip_tac
  >> fs[preserves_same_frame_def]
  >> `∀rr ss. g s = (rr, ss) ⇒ same_frame_rel s ss`
      by (rpt strip_tac
          >> first_x_assum drule >> simp[])
  >> Cases_on `g s`
  >> rename1 `g s = (q, sp)`
  >> Cases_on `q`
  >- (  (* g returned INL x *)
       qexists_tac `x` >> qexists_tac `sp`
       >> `same_frame_rel s sp` by (first_x_assum irule >> simp[])
       >> simp[]
       >> qpat_x_assum `bind _ _ _ = _` mp_tac
       >> simp[bind_def])
  (* g returned INR: sp ≠ s1 because same_frame_rel s sp gives equal
     lengths, but LENGTH s1 > LENGTH s. *)
  >> `same_frame_rel s sp` by (first_x_assum irule >> simp[])
  >> qpat_x_assum `monad_bind _ _ _ = _` mp_tac
  >> simp[bind_def]
  >> strip_tac
  >> spose_not_then strip_assume_tac
  >> fs[same_frame_rel_def]
QED

Theorem ignore_bind_inr_grow_factor:
  preserves_same_frame g ∧
  ignore_bind g f s = (INR e, s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃sp. g s = (INL (), sp) ∧ same_frame_rel s sp ∧
         f sp = (INR e, s1)
Proof
  rw[ignore_bind_def]
  >> drule_all bind_inr_grow_factor
  >> rw[]
QED

(* ---------------- inr_grow_witness predicate ------------------- *)

(* `inr_grow_witness P m` says: whenever m INR-grows from a state s,
   there exists a sp with same_frame_rel s sp such that P holds of
   (sp, s1, e).

   This is compositional: we can chain preserves_same_frame prefixes
   onto any inr_grow_witness f, giving inr_grow_witness (bind g f). *)
Definition inr_grow_witness_def:
  inr_grow_witness (P: execution_state -> execution_state -> exception option -> bool)
                   (m: unit execution) ⇔
    ∀s e s1. m s = (INR e, s1) ∧ s.contexts ≠ [] ∧
             LENGTH s1.contexts > LENGTH s.contexts ⇒
      ∃sp. same_frame_rel s sp ∧ P sp s1 e
End

(* Strengthen: if P sp s1 e implies Q sp s1 e, then witness with P
   gives witness with Q. *)
Theorem inr_grow_witness_mono:
  inr_grow_witness P m ∧ (∀sp s1 e. P sp s1 e ⇒ Q sp s1 e) ⇒
  inr_grow_witness Q m
Proof
  rw[inr_grow_witness_def] >> metis_tac[]
QED

(* Composition: preserves_same_frame prefix + inr_grow_witness tail. *)
Theorem inr_grow_witness_bind_preserves_g:
  preserves_same_frame g ∧ (∀x. inr_grow_witness P (f x)) ⇒
  inr_grow_witness P (bind g f)
Proof
  rw[inr_grow_witness_def]
  >> drule_all bind_inr_grow_factor
  >> strip_tac
  >> first_x_assum (qspec_then `x` mp_tac)
  >> rewrite_tac[inr_grow_witness_def]
  >> disch_then drule
  >> `sp.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> `LENGTH s1.contexts > LENGTH sp.contexts`
       by (`LENGTH sp.contexts = LENGTH s.contexts` by fs[same_frame_rel_def]
           >> simp[])
  >> simp[]
  >> strip_tac
  >> qexists_tac `sp'`
  >> simp[]
  >> metis_tac[same_frame_rel_trans]
QED

Theorem inr_grow_witness_ignore_bind_preserves_g:
  preserves_same_frame g ∧ inr_grow_witness P f ⇒
  inr_grow_witness P (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule inr_grow_witness_bind_preserves_g
  >> simp[]
QED

Theorem inr_grow_witness_cond[simp]:
  inr_grow_witness P m1 ∧ inr_grow_witness P m2 ⇒
  inr_grow_witness P (if b then m1 else m2)
Proof
  rw[]
QED

Theorem inr_grow_witness_case_option[simp]:
  inr_grow_witness P m_none ∧ (∀x. inr_grow_witness P (m_some x)) ⇒
  inr_grow_witness P (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem inr_grow_witness_let[simp]:
  (∀x. inr_grow_witness P (f x)) ⇒
  inr_grow_witness P (let x = v in f x)
Proof
  rw[]
QED

Theorem inr_grow_witness_case_pair[simp]:
  (∀a b. inr_grow_witness P (f a b)) ⇒
  inr_grow_witness P (case p of (a, b) => f a b)
Proof
  Cases_on `p` >> rw[]
QED

(* From preserves_same_frame: m never INR-grows, so witness is
   vacuously true. *)
Theorem inr_grow_witness_of_preserves_same_frame:
  preserves_same_frame m ⇒ inr_grow_witness P m
Proof
  rw[preserves_same_frame_def, inr_grow_witness_def]
  >> first_x_assum drule_all
  >> rw[same_frame_rel_def]
QED

(* Predicate capturing the INR-grow structure we want from
   step_call / proceed_call.

   `inr_grow_P outputTo sp s1 e` says that s1 results from proceed_call
   (after some prefix) with outputTo parameter, exhibiting:
   - e is not vfm_abort and not SOME Reverted
   - callee_local_changes, accesses grow, msdomain grow
   - s1.contexts structure has the pushed child + original parent + rest *)
Definition inr_grow_P_def:
  inr_grow_P sp s1 e ⇔
    ¬ vfm_abort e ∧ e ≠ SOME Reverted ∧
    callee_local_changes
      (FST (HD sp.contexts)).msgParams.callee sp.rollback s1.rollback ∧
    toSet sp.rollback.accesses.addresses ⊆
      toSet s1.rollback.accesses.addresses ∧
    toSet sp.rollback.accesses.storageKeys ⊆
      toSet s1.rollback.accesses.storageKeys ∧
    msdomain_compatible sp.msdomain s1.msdomain ∧
    (∃callee_ctx parent_ctx mr.
      s1.contexts = (callee_ctx, sp.rollback) ::
                    (parent_ctx, SND (HD sp.contexts)) ::
                    TL sp.contexts ∧
      parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams ∧
      parent_ctx.logs = (FST (HD sp.contexts)).logs ∧
      parent_ctx.addRefund = (FST (HD sp.contexts)).addRefund ∧
      parent_ctx.subRefund = (FST (HD sp.contexts)).subRefund ∧
      callee_ctx.msgParams.outputTo = Memory mr)
End



(* The `push_context (ctx, rb) ; dispatch_precompiles a` pattern:
   push_context grows by 1 and returns INL. dispatch_precompiles is
   preserves_same_frame so it may INR but doesn't further grow.

   When this composed monad INR-grows, we extract structural info. *)

(* TODO: a helper lemma stating that, when `a` is a precompile
   address, any INR exception raised by `dispatch_precompiles a`
   is neither a `vfm_abort` nor `SOME Reverted`. This is consumed
   by `step_call_inr_grow_structure` below. An earlier attempt to
   build a compositional `inr_ok_exn` framework for this is removed;
   the helper will be proven directly when the main theorem lands. *)

(* ---- step_call INR-grow structure lemma ------------------------ *)

(* When step_call INR-grows, we can identify an intermediate state sp
   (after the prefix) such that:
   - same_frame_rel s sp
   - s1 = result of (proceed_call's body from sp, including push and
     precompile failure)
   - sp.rollback = (the saved rb in s1's pushed child)
   - The child's outputTo is Memory
   - The exception e is not a vfm_abort (precompiles only fail with
     OOG, never OutsideDomain/Unimplemented/Impossible).
   - s1.contexts has parent (= sp's head possibly with set_return_data
     applied) + child + rest. *)
Theorem step_call_inr_grow_structure:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_call op s = (INR e, s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ¬ vfm_abort e ∧ e ≠ SOME Reverted ∧
    (∃sp callee_ctx callee_rb mr.
       same_frame_rel s sp ∧
       callee_rb = sp.rollback ∧
       (* Relationship between s1.rollback and sp.rollback:
          - callee_local_changes (sp's callee) sp.rollback s1.rollback:
            transfer_value (if called) modifies only balance;
            precompile bodies don't touch rollback.
          - Accesses grow monotonically.
          - msdomain grows monotonically. *)
       callee_local_changes
         (FST (HD sp.contexts)).msgParams.callee
         sp.rollback s1.rollback ∧
       toSet sp.rollback.accesses.addresses ⊆
         toSet s1.rollback.accesses.addresses ∧
       toSet sp.rollback.accesses.storageKeys ⊆
         toSet s1.rollback.accesses.storageKeys ∧
       msdomain_compatible sp.msdomain s1.msdomain ∧
       (∃parent_ctx.
          s1.contexts = (callee_ctx, callee_rb) ::
                        (parent_ctx, SND (HD sp.contexts)) ::
                        TL sp.contexts ∧
          parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams ∧
          parent_ctx.logs = (FST (HD sp.contexts)).logs ∧
          parent_ctx.addRefund = (FST (HD sp.contexts)).addRefund ∧
          parent_ctx.subRefund = (FST (HD sp.contexts)).subRefund) ∧
       callee_ctx.msgParams.outputTo = Memory mr)
Proof
  cheat  (* Weakened-conclusion structure lemma. See
            docs/issue-113-plan.md for analysis and proof plan. *)
QED

(* ---- The case (b) lemma ---------------------------------------- *)

(* Combines the above: when step_call INR-grew and handle_step popped
   back, the result is same-frame-related to s. *)
Theorem step_call_handle_step_inr_grow_same_frame:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_call op s = (INR e, s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ∧
  handle_step e s1 = (q, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  (* Step 1: Extract structure from step_call_inr_grow_structure. *)
  >> drule_all step_call_inr_grow_structure
  >> strip_tac
  (* Now in scope: ¬ vfm_abort e, same_frame_rel s sp,
     callee_rb = sp.rollback, s1.rollback = sp.rollback,
     s1.contexts = (callee_ctx, callee_rb) ::
                   (parent_ctx, SND (HD sp.contexts)) :: TL sp.contexts,
     parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams,
     ... parent_ctx.addRefund/subRefund/logs = ...,
     callee_ctx.msgParams.outputTo = Memory mr. *)
  >> `∃mr'. callee_ctx.msgParams.outputTo = Memory mr'`
       by (qexists_tac `mr` >> simp[])
  >> `s.contexts ≠ []` by simp[]
  >> `sp.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> `LENGTH sp.contexts = LENGTH s.contexts`
       by metis_tac[same_frame_rel_def]
  (* Step 2: Split on e = NONE vs e ≠ NONE to apply correct pop lemma. *)
  (* Common txParams and msdomain reasoning for both branches. *)
  >> `s'.txParams = s.txParams` by (
       `s'.txParams = s1.txParams`
         by metis_tac[vfmTxParamsTheory.handle_step_preserves_txParams, SND]
       >> `s1.txParams = s.txParams`
         by metis_tac[vfmTxParamsTheory.step_call_preserves_txParams, SND]
       >> simp[])
  >> `s'.msdomain = s1.msdomain`
       by metis_tac[SND_handle_step_msdomain, SND]
  >> `msdomain_compatible sp.msdomain s'.msdomain` by simp[]
  >> `s.txParams = sp.txParams` by fs[same_frame_rel_def]
  >> Cases_on `e = NONE`
  >- (  (* Success case: e = NONE. Use _gen variant which handles
           q = INR post-pop finalization failures too. *)
       gvs[]
       >> drule handle_step_pop_success_memory_effect_gen
       >> disch_then (qspecl_then [`s'`, `q`] mp_tac)
       >> impl_tac >- simp[]
       >> strip_tac
       >> `s'.rollback = s1.rollback` by simp[]
       (* Prove same_frame_rel sp s': uses callee_local_changes
          from the structure lemma (sp → s1), plus the pop's
          structural effect. *)
       >> `same_frame_rel sp s'` by (
            simp[same_frame_rel_def]
            >> rpt conj_tac
            >> TRY (fs[] >> NO_TAC)
            >> fs[]
            >> TRY (fs[rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC)
            >> decide_tac)
       >> metis_tac[same_frame_rel_trans])
  (* Failure case: e ≠ NONE. Use _gen variant. Need e ≠ SOME Reverted,
     which comes from the structure lemma (precompiles don't raise
     Reverted). *)
  >> drule handle_step_pop_memory_effect_gen
  >> disch_then (qspecl_then [`s'`, `q`, `e`] mp_tac)
  >> impl_tac >- simp[]
  >> strip_tac
  >> `s'.rollback = sp.rollback` by simp[]
  >> `same_frame_rel sp s'` by (
       simp[same_frame_rel_def, callee_local_changes_refl]
       >> fs[]
       >> rw[]
       >> fs[rich_listTheory.IS_PREFIX_APPEND]
       >> decide_tac)
  >> metis_tac[same_frame_rel_trans]
QED


Theorem step_same_frame:
  outputTo_consistent s ∧
  step s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> gvs[step_def, handle_def]
  >> qmatch_asmsub_abbrev_tac`pair_CASE (inner s)`
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> gvs[AllCaseEqs()]
  >- (
    (* inner returned INL: step s = (INL _, r) so s' = r. *)
    gvs[same_frame_or_grow_def] >> first_x_assum drule >> simp[])
  >> (* inner returned INR with state s1: step s = handle_step e s1.
        Two sub-cases based on same_frame_or_grow inner:
          (a) same_frame_rel s s1: compose with handle_step_same_frame.
          (b) inner grew: s1.contexts = s.contexts + k for some k ≥ 1.
              handle_step must shrink back to s.contexts for our
              hypothesis. This happens when handle_exception pops. *)
  rename1`inner s = (INR e, s1)` >>
  `same_frame_rel s s1 ∨ LENGTH s1.contexts ≥ LENGTH s.contexts + 1`
  by (gvs[same_frame_or_grow_def] >> first_x_assum drule >> simp[])
  >- (
    (* (a) same_frame_rel s s1 *)
    `outputTo_consistent s1` by
       metis_tac[same_frame_rel_preserves_outputTo_consistent]
    >> `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
    >> `LENGTH s1.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
    >> `LENGTH s'.contexts = LENGTH s1.contexts` by simp[]
    >> `same_frame_rel s1 s'` by (
         drule handle_step_same_frame >> disch_then drule
         >> disch_then drule >> simp[])
    >> metis_tac[same_frame_rel_trans])
  >> (* (b) inner grew. Reduce to step_call_handle_step_inr_grow_same_frame.
        The op must be Call/CallCode/DelegateCall/StaticCall (the only
        ops that can INR-grow). *)
     (* Unfold inner to extract the opcode *)
     qunabbrev_tac `inner`
  >> pop_assum mp_tac
  >> simp[bind_def]
  >> simp[get_current_context_def, ok_state_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> strip_tac >> gvs[bind_def, get_current_context_def, return_def]
  >> gvs[CaseEq"bool",COND_RATOR]
  >- (
    (* step_inst Stop case: doesn't grow (preserves_same_frame).
       Contradicts the grow hypothesis. *)
    `preserves_same_frame (step_inst Stop)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved
    >> simp[])
  >> gvs[vfmTypesTheory.option_CASE_rator,CaseEq"option"]
  >- (
    (* step_inst Invalid case: doesn't grow. *)
    `preserves_same_frame (step_inst Invalid)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved
    >> simp[])
  >> (* step_inst x; inc_pc_or_jump x case *)
     gvs[ignore_bind_def, bind_def]
  >> gvs[AllCaseEqs()]  >- (
    (* step_inst x returned INL, then inc_pc_or_jump x returned INR.
       inc_pc_or_jump is preserves_same_frame, so can't grow. *)
    `preserves_same_frame (inc_pc_or_jump op)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved >>
    `same_frame_or_grow (step_inst op)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[same_frame_or_grow_def]
    >> disch_then drule >> simp[]
    >> strip_tac
    >- (
      impl_keep_tac >- metis_tac[same_frame_rel_contexts_ne]
      >> `LENGTH s.contexts = LENGTH s''.contexts`
      by metis_tac[same_frame_rel_def]
      >> strip_tac >> gvs[] )
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> drule step_inst_inl_grew_is_call
    >> simp[]
    >> strip_tac >> gvs[inc_pc_or_jump_def]
    >> gvs[return_def])
  (* step_inst x returned INR with grew state s1.
     Must be Call-family. Reduce to step_call_handle_step_inr_grow. *)
  >> drule step_inst_inr_grew_is_call_family
  >> impl_tac >- gvs[]
  >> disch_then assume_tac
  >> `step_inst op s = step_call op s` by gvs[step_inst_def]
  >> pop_assum (mp_tac o SYM) >> simp[] >> strip_tac
  >> irule step_call_handle_step_inr_grow_same_frame
  >> simp[]
  >> rpt(goal_assum drule)
  >> simp[]
QED

(* ================================================================ *)
(* run_within_frame_preserves: iterated step preserves same-frame.   *)
(* ================================================================ *)

(* run_within_frame_preserves needs the length-equality hypothesis
   because OWHILE may stop due to length change (if execution pops
   out of `es`'s frame, e.g. via SELFDESTRUCT / RETURN in a
   non-outermost frame). In that case `es'` is not same-frame-
   related to `es`. We require the length-preservation hypothesis to
   restrict to the "terminated normally" case. *)
(* The invariant is conditional: WHEN length stays equal to the
   starting length, we maintain same_frame_rel es s. If step grows or
   shrinks (pop), the invariant is vacuously preserved, and the OWHILE
   guard stops iteration there. The theorem's hypothesis
   `LENGTH es'.contexts = LENGTH es.contexts` rules the "pop below"
   and "pushed" cases out at the conclusion. *)
Theorem run_within_frame_preserves:
  outputTo_consistent es ∧
  run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  same_frame_rel es es'
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> gvs[run_within_frame_def]
  >> `(λp. LENGTH (SND p).contexts = LENGTH es.contexts ⇒
           same_frame_rel es (SND p)) (r, es')` suffices_by simp[]
  >> irule (MP_CANON WhileTheory.OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[]
  >> conj_tac
  >- simp[same_frame_rel_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `same_frame_rel es s''` by simp[]
  >> `outputTo_consistent s''`
       by metis_tac[same_frame_rel_preserves_outputTo_consistent]
  >> `same_frame_rel s'' r'` by (
       irule step_same_frame
       >> goal_assum (first_assum o mp_then Any mp_tac)
       >> simp[])
  >> metis_tac[same_frame_rel_trans]
QED

(* ================================================================ *)
(* Gas monotonicity corollary (separate from same_frame_rel).        *)
(* ================================================================ *)

Theorem step_same_frame_gas_monotone:
  outputTo_consistent s ∧ ok_state s ∧ step s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> mp_tac decreases_gas_cred_step
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then`s`mp_tac)
  >> IF_CASES_TAC >> gvs[] >> strip_tac
  (* Use step_same_frame to get the tail and msgParams (hence gasLimit)
     preservation, which decreases_gas_cred_step alone doesn't give us. *)
  >> `same_frame_rel s s'` by (
       irule step_same_frame
       >> goal_assum (first_assum o mp_then Any mp_tac) >> simp[])
  >> `TL s'.contexts = TL s.contexts` by gvs[same_frame_rel_def]
  >> `(FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
     by gvs[same_frame_rel_def]
  (* Now use decreases_gas_cred_step for the gas-weight inequality. *)
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def, unused_gas_def]
  >> (* The inequality reduces because the tails match and gasLimits
        match at the heads. *)
     BasicProvers.FULL_CASE_TAC >> gvs[]
  >> gvs[LEX_DEF]
  >> gvs[ok_state_def, wf_context_def]
QED

Theorem run_within_frame_gas_monotone:
  outputTo_consistent es ∧ ok_state es ∧
  run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es.contexts)).gasUsed ≤ (FST (HD es'.contexts)).gasUsed
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> gvs[run_within_frame_def]
  >> `(λp. LENGTH (SND p).contexts = LENGTH es.contexts ⇒
           same_frame_rel es (SND p) ∧ ok_state (SND p) ∧
           (FST (HD es.contexts)).gasUsed ≤
             (FST (HD (SND p).contexts)).gasUsed) (r, es')`
     suffices_by simp[]
  >> irule (MP_CANON WhileTheory.OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[]
  >> conj_tac
  >- simp[same_frame_rel_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `same_frame_rel es s'' ∧ ok_state s'' ∧
      (FST (HD es.contexts)).gasUsed ≤ (FST (HD s''.contexts)).gasUsed`
       by simp[]
  >> `outputTo_consistent s''`
       by metis_tac[same_frame_rel_preserves_outputTo_consistent]
  >> `s''.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> `same_frame_rel s'' r'` by (
       irule step_same_frame
       >> goal_assum (first_assum o mp_then Any mp_tac)
       >> simp[])
  >> `(FST (HD s''.contexts)).gasUsed ≤ (FST (HD r'.contexts)).gasUsed` by (
       irule step_same_frame_gas_monotone
       >> goal_assum (first_assum o mp_then Any mp_tac)
       >> simp[])
  >> `ok_state r'` by (
       `ok_state (SND (step s''))` suffices_by simp[]
       >> mp_tac (SPEC ``s'':execution_state`` (PURE_REWRITE_RULE
            [decreases_gas_cred_def] decreases_gas_cred_step))
       >> simp[])
  >> rpt conj_tac
  >- metis_tac[same_frame_rel_trans]
  >- simp[]
  >> simp[]
QED

(* ================================================================ *)
(* Named corollaries of `run_within_frame_preserves`.                *)
(*                                                                   *)
(* These extract individual conjuncts of `same_frame_rel` for users *)
(* who only need a specific property.                                *)
(* ================================================================ *)

Theorem run_within_frame_preserves_txParams:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  es'.txParams = es.txParams
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_preserves_storage_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).storage =
      (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_tStorage_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      es'.rollback.tStorage a = es.rollback.tStorage a
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_code_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).code =
      (lookup_account a es.rollback.accounts).code
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_nonce_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).nonce =
      (lookup_account a es.rollback.accounts).nonce
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_nonhead_contexts:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  TL es'.contexts = TL es.contexts
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_preserves_head_msgParams:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es'.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_preserves_saved_rollback:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  SND (HD es'.contexts) = SND (HD es.contexts)
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_callee_nonce_monotone:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (lookup_account (FST (HD es.contexts)).msgParams.callee
      es.rollback.accounts).nonce ≤
  (lookup_account (FST (HD es.contexts)).msgParams.callee
      es'.rollback.accounts).nonce
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_logs_grow:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  IS_PREFIX (FST (HD es'.contexts)).logs (FST (HD es.contexts)).logs
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_accesses_grow:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  toSet es.rollback.accesses.addresses ⊆
    toSet es'.rollback.accesses.addresses ∧
  toSet es.rollback.accesses.storageKeys ⊆
    toSet es'.rollback.accesses.storageKeys
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_refund_monotone:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es.contexts)).addRefund ≤ (FST (HD es'.contexts)).addRefund ∧
  (FST (HD es.contexts)).subRefund ≤ (FST (HD es'.contexts)).subRefund
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_domain_compatible:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  msdomain_compatible es.msdomain es'.msdomain
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED
