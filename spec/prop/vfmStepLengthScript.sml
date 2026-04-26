(*
 * Frameworks for reasoning about how monadic execution changes the
 * length of the context stack.
 *
 * The push / pop boundaries of a call frame violate
 * `preserves_same_frame` (they grow or shrink the stack). This theory
 * introduces two complementary frameworks — `same_frame_or_grow` /
 * `psf_or_grow` and `length_preserves` / `length_or_inl_grow` — that
 * track stack-length behaviour compositionally, and culminates in
 * structural lemmas about step_call / step_create:
 *
 *   - `same_frame_or_grow_step_call[simp]`,
 *     `same_frame_or_grow_step_create[simp]`,
 *     `step_call_same_frame`, `step_create_same_frame`;
 *   - `same_frame_or_grow_step_inst[simp]`,
 *     `same_frame_or_grow_step_inner[simp]`,
 *     `step_inst_inl_grew_is_call`;
 *   - `proceed_create_returns_inl`, `abort_unuse_length`,
 *     `abort_create_exists_length`;
 *   - the CREATE-family length framework: `length_or_inl_grow_*`
 *     primitives and composition lemmas;
 *   - `step_create_grown_returns_inl`, `step_create_inr_no_grow`,
 *     `step_inst_inr_grew_is_call_family`.
 *
 * Downstream theories use these to rule out the push / pop branches
 * via a length hypothesis when working inside a fixed frame.
 *)
Theory vfmStepLength
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

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

Theorem proceed_call_returns_inl:
  s.contexts ≠ [] ∧ ¬fIN c precompile_addresses ∧
  proceed_call a b c d e f g h i s = (r, s') ⇒
  ISL r
Proof
  strip_tac
  >> gvs[proceed_call_def, bind_def, ignore_bind_def, fail_def,
         get_rollback_def, read_memory_def, get_caller_def, COND_RATOR,
         return_def, get_caller_def, get_value_def, get_static_def,
         get_current_context_def, push_context_def, AllCaseEqs(),
         update_accounts_def]
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

Theorem bind_length_preserves_imp_grow:
  length_preserves m ∧
  (∀x s r. f x s = (r,s') ∧ s.contexts ≠ [] ∧
           LENGTH s'.contexts > LENGTH s.contexts
     ⇒ LENGTH s'.contexts = LENGTH s.contexts + 1) ∧
  bind m f s = (r,s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts
  ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  rw[length_preserves_def, bind_def, AllCaseEqs()] >>
  first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >>
  Cases_on`s''.contexts` >> gvs[]
QED

(* When step_call grows, it grows by exactly 1 (via proceed_call). *)
Theorem step_call_grows_by_exactly_one:
  s.contexts ≠ [] ∧ step_call op s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  simp[step_call_def] >> strip_tac >>
  qpat_x_assum`_ = (_,_)`mp_tac >>
  simp[bind_def] >> TOP_CASE_TAC >>
  reverse TOP_CASE_TAC >- (
    rw[] >> gvs[pop_stack_def, bind_def, AllCaseEqs(),
                get_current_context_def, return_def] >>
    gvs[ignore_bind_def,bind_def,assert_def,
        set_current_context_def,return_def,fail_def,
        AllCaseEqs()] ) >>
  pairarg_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac`pop_stack n s` >>
  `length_preserves (pop_stack n)` by simp[] >>
  pop_assum mp_tac >> rewrite_tac[length_preserves_def] >>
  disch_then drule >> impl_tac >- rw[] >> strip_tac >>
  pop_assum(assume_tac o SYM) >> gvs[] >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  reverse conj_asm2_tac >- (strip_tac >> gvs[]) >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  gvs[ignore_bind_def] >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum`_ = (r'',_)`kall_tac >>
  gvs[COND_RATOR,CaseEq"bool"]
  >- (
    drule_at(Pat`_ = (_,_)`)psf_imp_length_contexts_preserved >>
    simp[] ) >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  gvs[COND_RATOR,CaseEq"bool"]
  >- (
    drule_at(Pat`_ = (_,_)`)psf_imp_length_contexts_preserved >>
    simp[] ) >>
  drule_all proceed_call_length >> gvs[]
QED

(* When step_create grows, it grows by exactly 1 (via proceed_create). *)
Theorem step_create_grows_by_exactly_one:
  s.contexts ≠ [] ∧ step_create two s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  simp[step_create_def, ignore_bind_def] >> strip_tac >>
  (* Peel away length-preserving prefixes *)
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  gvs[ignore_bind_def] >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  drule_at(Pat`bind`)bind_length_preserves_imp_grow >>
  disch_then irule >> simp[] >>
  qpat_x_assum`_ = (_,_)`kall_tac >> rpt gen_tac >> strip_tac >>
  gvs[COND_RATOR,CaseEq"bool"]
  (* abort_unuse path: preserves_same_frame, can't grow *)
  >> TRY (
    drule_at(Pat`_ = (_,_)`)psf_imp_length_contexts_preserved >>
    simp[] >> NO_TAC ) >>
  TRY (
    drule(REWRITE_RULE[length_preserves_def]
      length_preserves_abort_create_exists) >> gvs[] >> NO_TAC) >>
  drule_all proceed_create_length >> gvs[]
QED

(* When the inner computation of step grows, it grows by exactly 1.
   This is because all growth paths go through step_call or step_create,
   which grow by exactly 1 via proceed_call/proceed_create. *)
Theorem step_inner_grows_by_exactly_one:
  s.contexts ≠ [] ∧
  (do
     context <- get_current_context;
     if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
     else case FLOOKUP context.msgParams.parsed context.pc of
            NONE => step_inst Invalid
          | SOME op => do step_inst op; inc_pc_or_jump op od
   od) s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  strip_tac
  >> gvs[bind_def, get_current_context_def, return_def, fail_def,
         COND_RATOR, vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
         ignore_bind_def]
  (* Stop case: preserves_same_frame, can't grow *)
  >- (`preserves_same_frame (step_inst Stop)` by simp[]
      >> imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  (* Invalid case: preserves_same_frame, can't grow *)
  >- (`preserves_same_frame (step_inst Invalid)` by simp[]
      >> imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  (* SOME op case *)
  >> rename1 `step_inst op s = _`
  >> Cases_on `step_inst op s` >> gvs[AllCaseEqs()]
  (* step_inst INL: inc_pc_or_jump ran. inc_pc_or_jump is psf, so growth from step_inst *)
  >- (
    `preserves_same_frame (inc_pc_or_jump op)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved
    >> impl_keep_tac
    >- (
      strip_tac >> gvs[inc_pc_or_jump_def,COND_RATOR,AllCaseEqs(),return_def] >>
      gvs[bind_def,get_current_context_def,return_def,AllCaseEqs(),fail_def] )
    >> strip_tac >> gvs[]
    >> drule_all step_inst_inl_grew_is_call
    >> Cases_on`step_inst op s = step_call op s` >> gvs[]
    >- ( drule_then drule step_call_grows_by_exactly_one >> rw[] )
    >> strip_tac
    >> `∃two. step_inst op s = step_create two s` by (
      Cases_on`op` >> gvs[step_inst_def,is_call_def] >> metis_tac[])
    >> irule step_create_grows_by_exactly_one >> simp[]
    >> metis_tac[] )
  (* step_inst INR: s' is from step_inst directly *)
  >> rename1 `step_inst op s = (INR e, s')`
  >> `op = Call ∨ op = CallCode ∨ op = DelegateCall ∨ op = StaticCall`
       by metis_tac[step_inst_inr_grew_is_call_family]
  >> gvs[step_inst_def]
  >> irule step_call_grows_by_exactly_one >> simp[]
  >> metis_tac[]
QED

(* ================================================================ *)
(* length_or_inl_grow for step_call (mirrors step_create framework) *)
(* ================================================================ *)

Theorem length_or_inl_grow_proceed_call[simp]:
  length_or_inl_grow (proceed_call a b c d e f g h x)
Proof
  rw[length_or_inl_grow_def]
  >> Cases_on `r`
  >- (  (* INL *)
       `LENGTH s'.contexts = LENGTH s.contexts + 1`
         by (drule_all proceed_call_length >> simp[])
       >> simp[])
  (* INR: contradict proceed_call_returns_inl *)
  >> Cases_on`fIN c precompile_addresses` >- cheat
  >> drule_all proceed_call_returns_inl
  >> simp[]
QED

Theorem length_or_inl_grow_step_call[simp]:
  length_or_inl_grow (step_call op)
Proof
  simp[step_call_def]
  (* Peel through prefix primitives which are all length_preserves
     (via preserves_same_frame lifts). The final branches end in
     abort_unuse (length_preserves), abort_call_value (length_preserves),
     or proceed_call (length_or_inl_grow). Also handles case_option for
     get_delegate and case_pair for tuple destructuring. *)
  >> rpt (
       (irule length_or_inl_grow_bind_preserves_g >> simp[] >> gen_tac)
       ORELSE
       (irule length_or_inl_grow_ignore_bind_preserves_g >> simp[])
       ORELSE
       (irule length_or_inl_grow_cond >> simp[])
       ORELSE
       (irule length_or_inl_grow_case_option >> simp[])
       ORELSE
       (irule length_or_inl_grow_case_pair >> simp[])
       ORELSE
       (irule length_or_inl_grow_case_sum >> simp[])
  ORELSE (pairarg_tac >> gvs[]))
QED

Theorem step_call_grown_returns_inl:
  s.contexts ≠ [] ∧
  step_call op s = (r, s') ∧
  LENGTH s'.contexts ≥ LENGTH s.contexts + 1 ⇒
  ISL r
Proof
  strip_tac
  >> `length_or_inl_grow (step_call op)` by simp[]
  >> pop_assum mp_tac
  >> rewrite_tac[length_or_inl_grow_def]
  >> disch_then drule_all
  >> rw[]
QED

Theorem step_call_inr_no_grow:
  s.contexts ≠ [] ∧ step_call op s = (INR e, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  strip_tac
  >> mp_tac same_frame_or_grow_step_call
  >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> simp[]
  >> strip_tac
  >- gvs[same_frame_rel_def]
  (* Grow case: step_call_grown_returns_inl gives ISL r, but r = INR e. *)
  >> drule_all step_call_grown_returns_inl
  >> simp[]
QED
