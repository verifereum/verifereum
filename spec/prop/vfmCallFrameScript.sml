(*
 * Call-frame boundary reasoning on top of `same_frame_rel`.
 *
 * The base `same_frame_rel` relation, the `preserves_same_frame`
 * framework, the `psf` framework, per-opcode / per-precompile [simp]
 * lemmas, `outputTo_consistent`, SELFDESTRUCT psf details and
 * `proceed_call_length` / `proceed_create_length` all live in
 * `vfmSameFrame`.
 *
 * This theory adds:
 *   - `psf_handle_create`, `handle_exception_same_frame`,
 *     `handle_step_same_frame` — the handle-layer lemmas that lift
 *     same-frame preservation across `handle_step` on the length-
 *     preserving branch;
 *   - `same_frame_or_grow` and `psf_or_grow` frameworks for monads
 *     that either stay in the current frame or push a new context
 *     (used to reason about step_call / step_create);
 *   - `length_preserves` and `length_or_inl_grow` frameworks for
 *     reasoning about the CREATE family's push behaviour;
 *   - `pop_and_incorporate_context_failure_effect` and related
 *     pop-effect lemmas;
 *   - `SND_*_msdomain` leaf lemmas and `SND_handle_step_msdomain`
 *     showing msdomain is preserved exactly through handle_step;
 *   - `bind_inr_grow_factor` / `ignore_bind_inr_grow_factor` and the
 *     `inr_grow_witness` framework;
 *   - the INR-grow structure + same-frame lemmas for step_call and
 *     step_create, `step_same_frame`, and the downstream
 *     `run_within_frame_preserves_*` named corollaries.
 *)
Theory vfmCallFrame
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame
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
(* same_frame_or_grow: a monadic property for computations whose     *)
(* effect on the call stack is either "stay in the current frame"   *)
(* or "push (grow by at least one)". Needed for step_call and       *)
(* step_create, whose push branches violate preserves_same_frame    *)
(* but can be ruled out by a length hypothesis.                     *)
(* ================================================================ *)

Definition same_frame_or_grow_def:
  same_frame_or_grow (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      same_frame_rel s s' ∨
      LENGTH s'.contexts ≥ LENGTH s.contexts + 1
End

(* ---------------- Bridge from preserves_same_frame -------------- *)

Theorem same_frame_or_grow_of_preserves[simp]:
  preserves_same_frame m ⇒ same_frame_or_grow m
Proof
  rw[preserves_same_frame_def, same_frame_or_grow_def]
  >> disj1_tac >> first_x_assum irule >> metis_tac[]
QED

(* ---------------- Composition rules ----------------------------- *)

Theorem same_frame_or_grow_bind[simp]:
  same_frame_or_grow g ∧ (∀x. same_frame_or_grow (f x)) ⇒
  same_frame_or_grow (bind g f)
Proof
  rw[same_frame_or_grow_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> first_x_assum drule
  >> first_x_assum drule
  >> simp[]
  >> disch_then assume_tac
  >> impl_keep_tac
  >- (
    gvs[] >> imp_res_tac same_frame_rel_contexts_ne >>
    strip_tac >> gvs[] )
  >> strip_tac >> gvs[]
  >> metis_tac[same_frame_rel_trans, same_frame_rel_def]
QED

Theorem same_frame_or_grow_ignore_bind[simp]:
  same_frame_or_grow g ∧ same_frame_or_grow f ⇒
  same_frame_or_grow (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule same_frame_or_grow_bind >> simp[]
QED

Theorem same_frame_or_grow_handle[simp]:
  same_frame_or_grow f ∧ (∀e. same_frame_or_grow (h e)) ⇒
  same_frame_or_grow (handle f h)
Proof
  rw[same_frame_or_grow_def, handle_def]
  >> gvs[AllCaseEqs()]
  >> first_x_assum drule
  >> first_x_assum drule
  >> simp[]
  >> disch_then assume_tac
  >> impl_keep_tac
  >- (
    gvs[] >> imp_res_tac same_frame_rel_contexts_ne >>
    strip_tac >> gvs[] )
  >> strip_tac >> gvs[]
  >> metis_tac[same_frame_rel_trans, same_frame_rel_def]
QED

Theorem same_frame_or_grow_cond[simp]:
  same_frame_or_grow m1 ∧ same_frame_or_grow m2 ⇒
  same_frame_or_grow (if b then m1 else m2)
Proof
  rw[]
QED

Theorem same_frame_or_grow_case_option[simp]:
  same_frame_or_grow m_none ∧ (∀x. same_frame_or_grow (m_some x)) ⇒
  same_frame_or_grow
    (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem same_frame_or_grow_case_sum[simp]:
  (∀x. same_frame_or_grow (f x)) ∧ (∀y. same_frame_or_grow (g y)) ⇒
  same_frame_or_grow
    (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` >> rw[]
QED

Theorem same_frame_or_grow_case_pair[simp]:
  (∀x y. same_frame_or_grow (f x y)) ⇒
  same_frame_or_grow (case pr of (x, y) => f x y)
Proof
  Cases_on `pr` >> rw[]
QED

Theorem same_frame_or_grow_let[simp]:
  (∀x. same_frame_or_grow (f x)) ⇒
  same_frame_or_grow (let x = v in f x)
Proof
  rw[]
QED

Theorem same_frame_or_grow_uncurry[simp]:
  (∀x y. same_frame_or_grow (f x y)) ⇒
  same_frame_or_grow (UNCURRY f pr)
Proof
  Cases_on `pr` >> rw[]
QED

(* ---------------- proceed_call / proceed_create grow ------------ *)

Theorem same_frame_or_grow_proceed_call[simp]:
  same_frame_or_grow
    (proceed_call op sender addr value aOff aSz code stipend outTo)
Proof
  rw[same_frame_or_grow_def]
  >> disj2_tac
  >> drule_then drule proceed_call_length >> simp[]
QED

Theorem same_frame_or_grow_proceed_create[simp]:
  same_frame_or_grow
    (proceed_create senderAddr addr value code gas)
Proof
  rw[same_frame_or_grow_def]
  >> disj2_tac
  >> drule_then drule proceed_create_length >> simp[]
QED

(* ================================================================ *)
(* psf_or_grow: state-indexed variant of same_frame_or_grow.         *)
(*                                                                   *)
(* Same-shape predicate as `psf`, but with the or-grow disjunct     *)
(* baked in. Used for `step_create` where the push branch only     *)
(* same-frames under a value-level precondition from `get_callee`. *)
(* ================================================================ *)

Definition psf_or_grow_def:
  psf_or_grow p (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
      same_frame_rel s s' ∨
      LENGTH s'.contexts ≥ LENGTH s.contexts + 1
End

(* ---------------- Bridges ------------------- *)

Theorem psf_or_grow_of_same_frame_or_grow[simp]:
  same_frame_or_grow m ⇒ psf_or_grow p m
Proof
  rw[same_frame_or_grow_def, psf_or_grow_def]
  >> first_x_assum irule >> metis_tac[]
QED

Theorem same_frame_or_grow_eq_psf_or_grow_T:
  same_frame_or_grow m ⇔ psf_or_grow (λs. T) m
Proof
  rw[same_frame_or_grow_def, psf_or_grow_def]
QED

(* ---------------- Composition rules ------------------- *)

Theorem psf_or_grow_bind:
  psf_or_grow p g ∧
  (∀x. psf_or_grow (p_cont x) (f x)) ∧
  (∀x s s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒
            p_cont x s') ⇒
  psf_or_grow p (bind g f)
Proof
  rw[psf_or_grow_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> first_x_assum drule
  >> first_x_assum drule
  >> first_x_assum drule
  >> rw[] >> gvs[]
  >> imp_res_tac same_frame_rel_contexts_ne >> gvs[]
  >- metis_tac[same_frame_rel_trans, same_frame_rel_def]
  >- metis_tac[same_frame_rel_trans, same_frame_rel_def]
  >> qmatch_asmsub_abbrev_tac`xxx ⇒ _`
  >> `xxx` by (simp[Abbr`xxx`] >> strip_tac >> gvs[])
  >> gvs[Abbr`xxx`]
  >- metis_tac[same_frame_rel_trans, same_frame_rel_def]
QED

Theorem psf_or_grow_ignore_bind:
  psf_or_grow p g ∧
  psf_or_grow p_cont f ∧
  (∀s x s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒ p_cont s') ⇒
  psf_or_grow p (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λu s. p_cont s`
  >> simp[] >> metis_tac[]
QED

Theorem psf_or_grow_cond[simp]:
  psf_or_grow p m1 ∧ psf_or_grow p m2 ⇒
  psf_or_grow p (if b then m1 else m2)
Proof
  rw[]
QED

Theorem psf_or_grow_case_option[simp]:
  psf_or_grow p m_none ∧ (∀x. psf_or_grow p (m_some x)) ⇒
  psf_or_grow p (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem psf_or_grow_let[simp]:
  (∀x. psf_or_grow p (f x)) ⇒
  psf_or_grow p (let x = v in f x)
Proof
  rw[]
QED

(* ---------------- Specialised getter-bind for get_callee -------- *)

Theorem psf_or_grow_bind_get_callee:
  (∀x. psf_or_grow (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.callee)
                    (f x)) ⇒
  psf_or_grow p (bind get_callee f)
Proof
  rw[psf_or_grow_def, bind_def, get_callee_def,
     get_current_context_def, ok_state_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> first_x_assum (qspec_then `s` mp_tac)
  >> rw[psf_or_grow_def]
QED

(* ---------------- Leaf for abort_create_exists with callee ------ *)

(* Under the precondition that the argument equals the head's callee,
   abort_create_exists preserves same_frame (and therefore trivially
   same-frame-or-grows). *)
Theorem psf_or_grow_abort_create_exists_callee:
  psf_or_grow
    (λs. senderAddress = (FST (HD s.contexts)).msgParams.callee)
    (abort_create_exists senderAddress)
Proof
  rw[psf_or_grow_def]
  >> disj1_tac
  >> drule_at Any abort_create_exists_same_frame >> simp[]
  >> disch_then (qspec_then `senderAddress` mp_tac) >> simp[]
  >> Cases_on `abort_create_exists senderAddress s` >> gvs[]
QED

(* ---------------- step_call and step_create -------------------- *)

Theorem same_frame_or_grow_step_call[simp]:
  same_frame_or_grow (step_call op)
Proof
  simp[step_call_def]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_cond >> simp[]
QED

Theorem same_frame_or_grow_step_create[simp]:
  same_frame_or_grow (step_create two)
Proof
  simp[same_frame_or_grow_eq_psf_or_grow_T, step_create_def]
  (* Peel the prefix before get_callee using psf_or_grow_bind with
     trivially-transferred precondition. Then use psf_or_grow_bind_get_callee
     to strengthen to "senderAddress = callee" and continue. *)
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. T` >> simp[] >> gen_tac
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. T` >> simp[] >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `λs. T` >> simp[]
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `λs. T` >> simp[]
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. T` >> simp[] >> gen_tac
  >> irule psf_or_grow_bind_get_callee >> simp[] >> gen_tac
  (* From here `x'` (the senderAddress) is known to equal the head's
     callee. Continue peeling while threading this precondition. *)
  >> qmatch_goalsub_abbrev_tac`psf_or_grow pco`
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. pco s` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame get_accounts` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `pco` >> simp[]
  >> conj_tac >- simp[assert_def]
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `pco` >> simp[]
  >> conj_tac >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac`access_address addr`
    >> `preserves_same_frame (access_address addr)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_bind >> simp[] >>
  qexists_tac `λx s. pco s` >> simp[] >>
  conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame get_gas_left` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[] >> qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac`consume_gas n`
    >> `preserves_same_frame (consume_gas n)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_ignore_bind >> simp[] >>
  qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame assert_not_static` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_ignore_bind >> simp[] >> qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame (set_return_data [])` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_bind >> simp[] >>
  qexists_tac `λx s. pco s` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame get_num_contexts` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[] >>
  qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac`ensure_storage_in_domain n`
    >> `preserves_same_frame (ensure_storage_in_domain n)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_cond >> conj_tac
  >- (
    (* abort_unuse branch: preserves_same_frame, trivially psf_or_grow *)
    simp[])
  >> irule psf_or_grow_cond >> conj_tac
  >- (
    (* abort_create_exists senderAddress: where senderAddress = head's callee *)
    qunabbrev_tac`pco` >>
    irule psf_or_grow_abort_create_exists_callee)
  (* proceed_create: grows *)
  >> simp[]
QED

(* ---------------- Final same-frame theorems -------------------- *)

Theorem step_call_same_frame:
  outputTo_consistent s ∧
  step_call op s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> `same_frame_or_grow (step_call op)` by simp[]
  >> pop_assum mp_tac >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> rw[]
QED

Theorem step_create_same_frame:
  outputTo_consistent s ∧
  step_create two s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> `same_frame_or_grow (step_create two)` by simp[]
  >> pop_assum mp_tac >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> rw[]
QED

(* ================================================================ *)
(* step_same_frame: the main Pass D theorem.                         *)
(*                                                                   *)
(* Combines:                                                         *)
(*  - per-opcode preserves_same_frame lemmas (Pass B) for Group 1;  *)
(*  - step_call_same_frame / step_create_same_frame for CALL/CREATE; *)
(*  - handle_step_same_frame (Pass C) for the handle layer.         *)
(* ================================================================ *)

(* Helper: same_frame_or_grow (step_inst op). Covers all opcodes     *)
(* uniformly: Group 1 ops lift from preserves_same_frame, CALL and  *)
(* CREATE are same_frame_or_grow via our helpers.                   *)
Theorem same_frame_or_grow_step_inst[simp]:
  same_frame_or_grow (step_inst op)
Proof
  Cases_on `op` >> simp[]
  >> simp[step_inst_def]
QED

(* The inner monad of step (before the outer handle) is composed of
   preserves_same_frame prefixes followed by a step_inst and
   inc_pc_or_jump. It satisfies same_frame_or_grow. *)
Theorem same_frame_or_grow_step_inner[simp]:
  same_frame_or_grow
    (do
       context <- get_current_context;
       if LENGTH context.msgParams.code ≤ context.pc
       then step_inst Stop
       else case FLOOKUP context.msgParams.parsed context.pc of
              NONE => step_inst Invalid
            | SOME op => do step_inst op; inc_pc_or_jump op od
     od)
Proof
  irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> Cases_on `LENGTH x.msgParams.code ≤ x.pc` >> simp[]
  >> CASE_TAC >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
QED

(* If step_inst returned INL with strictly larger contexts, the only
   opcodes that could have done this are the push ops: Call, CallCode,
   DelegateCall, StaticCall, Create, Create2. All of these satisfy
   `is_call`. For every other opcode, step_inst is preserves_same_frame
   (from Pass B), which preserves contexts length. *)
(* If step_inst returned INL with strictly larger contexts, op must
   be one of the 6 push ops (is_call is T). All other ops are
   preserves_same_frame (Pass B), which preserves length. *)
Theorem step_inst_inl_grew_is_call:
  step_inst op s = (INL (), s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ∧
  s.contexts ≠ [] ⇒
  is_call op
Proof
  strip_tac
  >> CCONTR_TAC
  >> `LENGTH s'.contexts = LENGTH s.contexts` suffices_by simp[]
  >> Cases_on `op` >> gvs[is_call_def]
  >> imp_res_tac psf_imp_length_contexts_preserved
  >> fs[]
QED

(* If step_inst returned INR with strictly larger contexts, op must be
   a Call-family opcode specifically (Create/Create2 never INR-grow
   because proceed_create always returns INL). *)
(* Helper: step_create never INR-grows. Only proceed_create pushes,
   and proceed_create returns INL. All abort branches are
   preserves_same_frame. *)
(* proceed_create always returns INL (push_context is the final
   primitive and it returns INL). *)
Theorem proceed_create_returns_inl:
  s.contexts ≠ [] ∧
  proceed_create senderAddr addr value code gas s = (r, s') ⇒
  ISL r
Proof
  strip_tac
  >> gvs[proceed_create_def, bind_def, ignore_bind_def,
         get_rollback_def, get_original_def, set_original_def,
         update_accounts_def, push_context_def, return_def,
         AllCaseEqs()]
QED

(* step_create never INR-grows. Use same_frame_or_grow_step_create:
   either same-frame (length preserved), or grew ≥ 1. In the grow case,
   all non-proceed_create branches don't grow, so we must have reached
   proceed_create. proceed_create returns INL, so the outer result is
   INL too, contradicting our INR hypothesis.

   We formalise this as: step_create, in the grow case, returns INL. *)
(* step_create grown result must be INL: every primitive in step_create's
   bind chain either preserves_same_frame (no grow) or is
   proceed_create (returns INL). So grown + INR is impossible.
   Formalised below as `length_or_inl_grow` predicate with
   composition rules. *)
(* Helper: abort_unuse/abort_create_exists both preserve length.
   They are each a sequence of primitive effects none of which push
   or pop contexts. *)
Theorem abort_unuse_length:
  s.contexts ≠ [] ∧ abort_unuse n s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  (* abort_unuse uses push_stack, set_return_data, unuse_gas, inc_pc
     which are all preserves_same_frame. Either it returns INL or INR
     with state where length is preserved. *)
  strip_tac
  >> `preserves_same_frame (abort_unuse n)` by simp[]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule >> rw[]
  >> metis_tac[same_frame_rel_def]
QED

Theorem abort_create_exists_length:
  s.contexts ≠ [] ∧ abort_create_exists a s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  strip_tac
  >> gvs[abort_create_exists_def, bind_def, ignore_bind_def,
         update_accounts_def, push_stack_def, inc_pc_def, return_def,
         fail_def, get_current_context_def, set_current_context_def,
         assert_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

(* ================================================================ *)
(* grown_is_inl: if a monad grows the context stack, the result is
   INL. This property composes nicely through bind because it's
   "monotone" (once grown, INL is determined).

   Key insight: we need a *combined* property with length preservation
   too. The predicate length_or_inl_grow tracks: the monad either
   strictly preserves length, or grows length and returns INL. *)
(* ================================================================ *)

(* Precondition-free length preservation: m preserves contexts length
   whenever the input contexts are non-empty. (For empty contexts,
   many primitives fail with Impossible, which we can treat as a
   special case if needed.) *)
Definition length_preserves_def:
  length_preserves (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
             LENGTH s'.contexts = LENGTH s.contexts
End

Definition length_or_inl_grow_def:
  length_or_inl_grow (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      LENGTH s'.contexts = LENGTH s.contexts ∨
      (LENGTH s'.contexts > LENGTH s.contexts ∧ ISL r)
End

Theorem length_preserves_imp_length_or_inl_grow:
  length_preserves m ⇒ length_or_inl_grow m
Proof
  rw[length_preserves_def, length_or_inl_grow_def]
  >> metis_tac[]
QED

Theorem length_preserves_of_preserves_same_frame[simp]:
  preserves_same_frame m ⇒ length_preserves m
Proof
  rw[preserves_same_frame_def, length_preserves_def]
  >> first_x_assum drule_all
  >> rw[same_frame_rel_def]
QED

Theorem length_or_inl_grow_of_length_preserves[simp]:
  length_preserves m ⇒ length_or_inl_grow m
Proof
  metis_tac[length_preserves_imp_length_or_inl_grow]
QED

(* Composition through bind: g.length_preserves ensures f runs on
   state with same length as start; then f can either preserve or
   grow+INL, giving length_or_inl_grow for the bind. *)
Theorem length_or_inl_grow_bind_preserves_g:
  length_preserves g ∧
  (∀x. length_or_inl_grow (f x)) ⇒
  length_or_inl_grow (bind g f)
Proof
  rw[length_preserves_def, length_or_inl_grow_def, bind_def]
  >> Cases_on `g s` >> gvs[AllCaseEqs()]
  >- (  (* g INL x, s''. f x runs. *)
       rename1 `f x s'' = _`
       >> `LENGTH s''.contexts = LENGTH s.contexts` by metis_tac[]
       >> `s''.contexts ≠ []` by (
            strip_tac
            >> `LENGTH s''.contexts = 0` by simp[]
            >> `LENGTH s.contexts = 0` by decide_tac
            >> gvs[])
       >> first_x_assum (qspec_then `x` mp_tac)
       >> disch_then drule_all
       >> rw[] >> simp[])
  (* g INR: no f. *)
  >> first_x_assum drule_all >> rw[]
QED

Theorem length_or_inl_grow_ignore_bind_preserves_g:
  length_preserves g ∧
  length_or_inl_grow f ⇒
  length_or_inl_grow (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule length_or_inl_grow_bind_preserves_g >> simp[]
QED

Theorem length_or_inl_grow_cond[simp]:
  length_or_inl_grow m1 ∧ length_or_inl_grow m2 ⇒
  length_or_inl_grow (if b then m1 else m2)
Proof
  rw[]
QED

Theorem length_or_inl_grow_let[simp]:
  (∀x. length_or_inl_grow (f x)) ⇒
  length_or_inl_grow (let x = v in f x)
Proof
  rw[]
QED

Theorem length_or_inl_grow_case_option[simp]:
  length_or_inl_grow m_none ∧ (∀x. length_or_inl_grow (m_some x)) ⇒
  length_or_inl_grow (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem length_preserves_case_sum[simp]:
  (∀x. length_preserves (m_inl x)) ∧ (∀y. length_preserves (m_inr y)) ⇒
  length_preserves (case v of INL x => m_inl x | INR y => m_inr y)
Proof
  Cases_on `v` >> rw[]
QED

Theorem length_or_inl_grow_case_sum[simp]:
  (∀x. length_or_inl_grow (m_inl x)) ∧
  (∀y. length_or_inl_grow (m_inr y)) ⇒
  length_or_inl_grow (case v of INL x => m_inl x | INR y => m_inr y)
Proof
  Cases_on `v` >> rw[]
QED

Theorem length_or_inl_grow_case_pair[simp]:
  (∀x y. length_or_inl_grow (m x y)) ⇒
  length_or_inl_grow (case p of (x, y) => m x y)
Proof
  Cases_on `p` >> rw[]
QED

Theorem length_preserves_case_pair[simp]:
  (∀x y. length_preserves (m x y)) ⇒
  length_preserves (case p of (x, y) => m x y)
Proof
  Cases_on `p` >> rw[]
QED

(* Composition for length_preserves *)
Theorem length_preserves_bind:
  length_preserves g ∧
  (∀x. length_preserves (f x)) ⇒
  length_preserves (bind g f)
Proof
  rw[length_preserves_def, bind_def]
  >> Cases_on `g s` >> gvs[AllCaseEqs()]
  >- (rename1 `f x s'' = _`
      >> `LENGTH s''.contexts = LENGTH s.contexts` by metis_tac[]
      >> `s''.contexts ≠ []` by (
           strip_tac
           >> `LENGTH s''.contexts = 0` by simp[]
           >> `LENGTH s.contexts = 0` by decide_tac
           >> gvs[])
      >> metis_tac[])
  >> metis_tac[]
QED

Theorem length_preserves_ignore_bind:
  length_preserves g ∧ length_preserves f ⇒
  length_preserves (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule length_preserves_bind >> simp[]
QED

Theorem length_preserves_cond[simp]:
  length_preserves m1 ∧ length_preserves m2 ⇒
  length_preserves (if b then m1 else m2)
Proof
  rw[]
QED

Theorem length_preserves_case_option[simp]:
  length_preserves m_none ∧ (∀x. length_preserves (m_some x)) ⇒
  length_preserves (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem length_preserves_let[simp]:
  (∀x. length_preserves (f x)) ⇒
  length_preserves (let x = v in f x)
Proof
  rw[]
QED

(* proceed_create grows by 1 and returns INL. *)
Theorem length_or_inl_grow_proceed_create[simp]:
  length_or_inl_grow (proceed_create sa a v c g)
Proof
  rw[length_or_inl_grow_def]
  >> Cases_on `r`
  >- (  (* INL *)
       `LENGTH s'.contexts = LENGTH s.contexts + 1`
         by (drule_all proceed_create_length >> simp[])
       >> simp[])
  (* INR: contradict proceed_create_returns_inl *)
  >> drule_all proceed_create_returns_inl
  >> simp[]
QED

(* abort_unuse and abort_create_exists are length_preserves. *)
Theorem length_preserves_abort_unuse[simp]:
  length_preserves (abort_unuse n)
Proof
  rw[length_preserves_def]
  >> drule_all abort_unuse_length >> simp[]
QED

Theorem length_preserves_abort_create_exists[simp]:
  length_preserves (abort_create_exists a)
Proof
  rw[length_preserves_def]
  >> drule_all abort_create_exists_length >> simp[]
QED

Theorem length_or_inl_grow_step_create[simp]:
  length_or_inl_grow (step_create two)
Proof
  simp[step_create_def]
  (* Peel through prefix primitives which are all length_preserves
     (via preserves_same_frame lifts). The final
     if-cond-cond-else ends in abort_unuse (length_preserves),
     abort_create_exists (length_preserves), or proceed_create
     (length_or_inl_grow). *)
  >> rpt (
       (irule length_or_inl_grow_bind_preserves_g >> simp[] >> gen_tac)
       ORELSE
       (irule length_or_inl_grow_ignore_bind_preserves_g >> simp[])
       ORELSE
       (irule length_or_inl_grow_cond >> simp[]))
QED

Theorem step_create_grown_returns_inl:
  s.contexts ≠ [] ∧
  step_create two s = (r, s') ∧
  LENGTH s'.contexts ≥ LENGTH s.contexts + 1 ⇒
  ISL r
Proof
  strip_tac
  >> `length_or_inl_grow (step_create two)` by simp[]
  >> pop_assum mp_tac
  >> rewrite_tac[length_or_inl_grow_def]
  >> disch_then drule_all
  >> rw[]
QED

Theorem step_create_inr_no_grow:
  s.contexts ≠ [] ∧ step_create two s = (INR e, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  strip_tac
  >> mp_tac same_frame_or_grow_step_create
  >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> simp[]
  >> strip_tac
  >- gvs[same_frame_rel_def]
  (* Grow case: step_create_grown_returns_inl gives ISL r, but r = INR e. *)
  >> drule_all step_create_grown_returns_inl
  >> simp[]
QED

Theorem step_inst_inr_grew_is_call_family:
  step_inst op s = (INR e, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ∧
  s.contexts ≠ [] ⇒
  op = Call ∨ op = CallCode ∨ op = DelegateCall ∨ op = StaticCall
Proof
  strip_tac
  >> CCONTR_TAC
  >> `LENGTH s'.contexts = LENGTH s.contexts` suffices_by simp[]
  >> Cases_on `op` >> gvs[]
  >> TRY (imp_res_tac psf_imp_length_contexts_preserved >> fs[] >> NO_TAC)
  >> gvs[step_inst_def]
  >> imp_res_tac step_create_inr_no_grow
  >> fs[]
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

(* handle_step does not modify msdomain. All its primitives
   (consume_gas, set_return_data, pop/push context, unuse_gas,
   push_logs, update_gas_refund, set_rollback, inc_pc, push_stack,
   write_memory, update_accounts) leave msdomain unchanged. *)
Theorem SND_reraise_msdomain[simp]:
  ∀e s. (SND (reraise e s)).msdomain = s.msdomain
Proof
  rw[reraise_def, return_def, fail_def] >> rw[]
QED

Theorem SND_get_current_context_msdomain[simp]:
  (SND (get_current_context s)).msdomain = s.msdomain
Proof
  rw[get_current_context_def, return_def, fail_def] >> rw[]
QED

Theorem SND_get_num_contexts_msdomain[simp]:
  (SND (get_num_contexts s)).msdomain = s.msdomain
Proof
  rw[get_num_contexts_def, return_def]
QED

Theorem SND_get_gas_left_msdomain[simp]:
  (SND (get_gas_left s)).msdomain = s.msdomain
Proof
  rw[get_gas_left_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_get_return_data_msdomain[simp]:
  (SND (get_return_data s)).msdomain = s.msdomain
Proof
  rw[get_return_data_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_get_output_to_msdomain[simp]:
  (SND (get_output_to s)).msdomain = s.msdomain
Proof
  rw[get_output_to_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_pop_context_msdomain[simp]:
  (SND (pop_context s)).msdomain = s.msdomain
Proof
  rw[pop_context_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_num_contexts_def, get_current_context_def]
  >> rw[]
QED

Theorem SND_unuse_gas_msdomain[simp]:
  ∀n s. (SND (unuse_gas n s)).msdomain = s.msdomain
Proof
  rw[unuse_gas_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_current_context_def, set_current_context_def]
  >> rw[]
QED

Theorem SND_push_logs_msdomain[simp]:
  ∀ls s. (SND (push_logs ls s)).msdomain = s.msdomain
Proof
  rw[push_logs_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_update_gas_refund_msdomain[simp]:
  ∀p s. (SND (update_gas_refund p s)).msdomain = s.msdomain
Proof
  Cases_on `p`
  >> rw[update_gas_refund_def, bind_def, return_def, get_current_context_def,
        set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_set_rollback_msdomain[simp]:
  ∀r s. (SND (set_rollback r s)).msdomain = s.msdomain
Proof
  rw[set_rollback_def, return_def]
QED

Theorem SND_pop_and_incorporate_context_msdomain[simp]:
  ∀b s. (SND (pop_and_incorporate_context b s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[pop_and_incorporate_context_def, bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

Theorem SND_inc_pc_msdomain[simp]:
  (SND (inc_pc s)).msdomain = s.msdomain
Proof
  rw[inc_pc_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_push_stack_msdomain[simp]:
  ∀v s. (SND (push_stack v s)).msdomain = s.msdomain
Proof
  rw[push_stack_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_current_context_def, set_current_context_def]
  >> rw[]
QED

Theorem SND_write_memory_msdomain[simp]:
  ∀a bs s. (SND (write_memory a bs s)).msdomain = s.msdomain
Proof
  rw[write_memory_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_handle_exception_msdomain[simp]:
  ∀e s. (SND (handle_exception e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[handle_exception_def, bind_def, ignore_bind_def, return_def,
          fail_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

Theorem SND_handle_create_msdomain[simp]:
  ∀e s. (SND (handle_create e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[handle_create_def, bind_def, ignore_bind_def, return_def,
          fail_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

(* handle_step does not modify msdomain. *)
Theorem SND_handle_step_msdomain[simp]:
  ∀e s. (SND (handle_step e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> rw[handle_step_def, handle_def, bind_def, return_def, fail_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
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
