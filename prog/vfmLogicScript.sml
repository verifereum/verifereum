open HolKernel boolLib bossLib Parse
     vfmContextTheory vfmExecutionTheory;

val () = new_theory "vfmLogic";

Definition valid_def:
  valid P f Q =
  ∀s: execution_state.
    P s ⇒ case f s : α execution_result
          of (r, t) => Q r t
End

Definition valid_result_def:
  valid_result P f Q =
  valid P f (λr s. ISL r ∧ Q (OUTL r) s)
End

Definition valid_result_fn_def:
  valid_result_fn P f Q g =
  valid_result P f (λr s. Q s ∧ r = g s)
End

Definition valid_result_eq_def:
  valid_result_eq P f Q x =
  valid_result_fn P f Q (K x)
End

Theorem valid_strengthen:
  valid P f Q1 ∧
  (∀r s. Q1 r s ⇒ Q r s)
  ⇒
  valid P f Q
Proof
  rw[valid_def]
  \\ last_x_assum drule \\ gvs[]
  \\ CASE_TAC \\ rw[]
QED

Theorem valid_weaken:
  valid P1 f1 Q ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  valid P f Q
Proof
  rw[valid_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem valid_result_weaken:
  valid_result P1 f1 Q ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  valid_result P f Q
Proof
  rw[valid_result_def]
  \\ metis_tac[valid_weaken]
QED

Theorem valid_result_fn_weaken:
  valid_result_fn P1 f1 Q g ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  valid_result_fn P f Q g
Proof
  rw[valid_result_fn_def]
  \\ metis_tac[valid_result_weaken]
QED

Theorem valid_result_eq_weaken:
  valid_result_eq P1 f1 Q g ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  valid_result_eq P f Q g
Proof
  rw[valid_result_eq_def]
  \\ metis_tac[valid_result_fn_weaken]
QED

Theorem valid_result_valid:
  valid_result P f Q1 ∧
  (∀r s. ISL r ∧ Q1 (OUTL r) s ⇒ Q r s)
  ⇒
  valid P f Q
Proof
  rw[valid_result_def]
  \\ irule valid_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_result_eq_valid_result:
  valid_result_eq P f Q1 x ∧
  (∀s. Q1 s ⇒ Q x s)
  ⇒
  valid_result P f Q
Proof
  rw[valid_result_fn_def, valid_result_eq_def, valid_result_def]
  \\ irule valid_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_bind:
  valid_result P g Q1 ∧
  (∀x. valid (Q1 x) (f x) Q)
  ⇒
  valid P (monad_bind g f) Q
Proof
  rw[valid_result_def, valid_def, bind_def]
  \\ CASE_TAC \\ gvs[]
  \\ last_x_assum drule \\ rw[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem valid_ignore_bind:
  valid_result P r Q1 ∧
  (∀x. valid (Q1 x) f Q)
  ⇒
  valid P (ignore_bind r f) Q
Proof
  rw[valid_def, valid_result_def, ignore_bind_def, bind_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ gvs[] \\ strip_tac
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem valid_result_bind:
  valid_result P g Q1 ∧
  (∀x. valid_result (Q1 x) (f x) Q)
  ⇒
  valid_result P (monad_bind g f) Q
Proof
  rw[]
  \\ rw[valid_result_def]
  \\ irule valid_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule valid_result_valid
  \\ qexists_tac`Q` \\ rw[]
QED

Theorem valid_result_ignore_bind:
  valid_result P r Q1 ∧
  (∀x. valid_result (Q1 x) f Q)
  ⇒
  valid_result P (ignore_bind r f) Q
Proof
  rw[]
  \\ rw[valid_result_def]
  \\ irule valid_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule valid_result_valid
  \\ qexists_tac`Q` \\ rw[]
QED

Theorem valid_result_fn_bind:
  valid_result P g Q1 ∧
  (∀x. valid_result_fn (Q1 x) (f x) Q h)
  ⇒
  valid_result_fn P (monad_bind g f) Q h
Proof
  rw[]
  \\ rw[valid_result_fn_def]
  \\ irule valid_result_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ fs[valid_result_fn_def]
QED

Theorem valid_result_eq_bind:
  valid_result P g Q1 ∧
  (∀x. valid_result_eq (Q1 x) (f x) Q y)
  ⇒
  valid_result_eq P (monad_bind g f) Q y
Proof
  rw[valid_result_eq_def]
  \\ irule valid_result_fn_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_result_fn_ignore_bind:
  valid_result P g Q1 ∧
  (∀x. valid_result_fn (Q1 x) f Q h)
  ⇒
  valid_result_fn P (ignore_bind g f) Q h
Proof
  rw[]
  \\ rw[valid_result_fn_def]
  \\ irule valid_result_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ fs[valid_result_fn_def]
QED

Theorem valid_result_eq_ignore_bind:
  valid_result P g Q1 ∧
  (∀x. valid_result_eq (Q1 x) f Q y)
  ⇒
  valid_result_eq P (ignore_bind g f) Q y
Proof
  rw[valid_result_eq_def]
  \\ irule valid_result_fn_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_result_eq_eq_ignore_bind:
  valid_result_eq P g Q1 z ∧
  valid_result_eq Q1 f Q y
  ⇒
  valid_result_eq P (ignore_bind g f) Q y
Proof
  rw[valid_result_eq_def]
  \\ irule valid_result_fn_ignore_bind
  \\ gs[valid_result_fn_def]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule valid_result_weaken
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem valid_result_get_current_context:
  (∀s. P s ⇒ ¬NULL s.contexts) ∧
  (∀s. P s ⇒ Q (HD s.contexts) s)
  ⇒
  valid_result P get_current_context Q
Proof
  rw[valid_result_def, valid_def, get_current_context_def]
  \\ rw[fail_def, return_def]
  \\ rpt(first_x_assum drule)
  \\ rw[]
QED

Theorem valid_result_eq_assert:
  (∀s. P s ⇒ b ∧ Q s)
  ⇒
  valid_result_eq P (assert b e) Q ()
Proof
  rw[valid_result_eq_def, valid_result_fn_def, valid_result_def, valid_def, assert_def]
QED

Theorem valid_result_eq_set_current_context:
  (∀s. P s ⇒ ¬NULL s.contexts) ∧
  (∀s. P s ⇒ Q (s with contexts updated_by λls. c :: TL ls))
  ⇒
  valid_result_eq P (set_current_context c) Q ()
Proof
  rw[valid_result_eq_def, valid_result_def, valid_def,
     valid_result_fn_def, set_current_context_def]
  \\ last_x_assum drule \\ rw[return_def]
  \\ last_x_assum drule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`Q s1`
  \\ qmatch_asmsub_abbrev_tac`Q s2`
  \\ `s1 = s2` by rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality]
  \\ rw[]
QED

Theorem valid_result_handle:
  valid_result P f Q
  ⇒
  valid_result P (handle f g) Q
Proof
  rw[valid_result_def, valid_def, handle_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ gvs[]
QED

Theorem valid_result_fn_handle:
  valid_result_fn P f Q k
  ⇒
  valid_result_fn P (handle f g) Q k
Proof
  rw[valid_result_fn_def, valid_result_handle]
QED

Theorem valid_result_eq_handle:
  valid_result_eq P f Q ()
  ⇒
  valid_result_eq P (handle f g) Q ()
Proof
  rw[valid_result_eq_def, valid_result_fn_handle]
QED

Definition has_cc_def:
  has_cc P s =
  ∃c t. s.contexts = c :: t ∧ P c
End

Definition update_cc_def:
  update_cc f s =
  s with contexts updated_by (λls. (f (HD ls))::(TL ls))
End

Theorem mp_rand:
  Q s1 ∧ s1 = s2 ⇒ Q s2
Proof
  rw[] \\ rw[]
QED

Theorem valid_result_eq_consume_gas:
  (∀s. P s ⇒ has_cc (λc. c.gasUsed + n ≤ c.msgParams.gasLimit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with gasUsed updated_by $+ n) s))
  ⇒
  valid_result_eq P (consume_gas n) Q ()
Proof
  rw[consume_gas_def]
  \\ irule valid_result_eq_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_get_current_context
    \\ rw[] \\ res_tac \\ fs[has_cc_def])
  \\ irule valid_result_eq_ignore_bind
  \\ qexists_tac`λr s. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_eq_valid_result \\ rw[]
    \\ qexists_tac`λs. P s ∧ x = HD s.contexts` \\ rw[]
    \\ irule valid_result_eq_assert
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule valid_result_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem valid_result_eq_push_stack:
  (∀s. P s ⇒ has_cc (λc. LENGTH c.stack < stack_limit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with stack updated_by CONS w) s))
  ⇒
  valid_result_eq P (push_stack w) Q ()
Proof
  (* TODO: mostly repeated from previous proof - abstract or automate? *)
  rw[push_stack_def]
  \\ irule valid_result_eq_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_get_current_context
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule valid_result_eq_ignore_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule valid_result_eq_valid_result \\ rw[]
    \\ qexists_tac`λs. P s ∧ x = HD s.contexts` \\ rw[]
    \\ irule valid_result_eq_assert
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule valid_result_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem valid_result_eq_step_push:
  g = static_gas (Push n ws) ∧
  w = word_of_bytes F 0w (REVERSE ws) ∧
  (∀s. P s ⇒ has_cc (λc.
         c.gasUsed + g ≤ c.msgParams.gasLimit ∧
         LENGTH c.stack < stack_limit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with <|
                  stack updated_by CONS w
                ; gasUsed updated_by $+ g |>) s))
  ⇒
  valid_result_eq P (step_push n ws) Q ()
Proof
  rw[step_push_def, Excl"static_gas_def"]
  \\ qmatch_goalsub_abbrev_tac`consume_gas g`
  \\ qmatch_goalsub_abbrev_tac`push_stack w`
  \\ irule valid_result_eq_ignore_bind \\ rw[]
  \\ qexists_tac`λr s. has_cc (λc. LENGTH c.stack < stack_limit) s ∧
                       Q (update_cc (λc. c with stack updated_by CONS w) s)`
  \\ reverse (rw[])
  >- (
    irule valid_result_eq_valid_result
    \\ qmatch_goalsub_abbrev_tac`_ ⇒ Q1 _ _`
    \\ qexists_tac`λs. Q1 () s`
    \\ rw[Abbr`Q1`]
    \\ irule valid_result_eq_consume_gas
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[update_cc_def]
    \\ last_x_assum drule \\ rw[update_cc_def]
    \\ irule mp_rand \\ goal_assum drule
    \\ rw[execution_state_component_equality,
         context_component_equality, update_cc_def])
  \\ irule valid_result_eq_push_stack
  \\ rw[]
QED

Theorem valid_result_eq_inc_pc_or_jump_inc:
  n = LENGTH (opcode i) ∧ ¬is_call i ∧
  (∀s. P s ⇒ has_cc (λc. c.jumpDest = NONE) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with pc updated_by $+ n) s))
  ⇒
  valid_result_eq P (inc_pc_or_jump i) Q ()
Proof
  rw[inc_pc_or_jump_def]
  \\ irule valid_result_eq_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse conj_tac
  >- (
    irule valid_result_get_current_context
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ rw[]
  \\ reverse(Cases_on`x.jumpDest`)
  >- (
    rw[valid_result_eq_def, valid_result_fn_def, valid_result_def, valid_def]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ gs[] )
  \\ rw[]
  \\ irule valid_result_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem valid_result_eq_step:
  (∀s. P s ⇒ has_cc (λc.
    c.pc < LENGTH c.msgParams.code ∧
    FLOOKUP c.msgParams.parsed c.pc = SOME op) s) ∧
  valid_result_eq P (do step_inst op; inc_pc_or_jump op od) Q ()
  ⇒
  valid_result_eq P step Q ()
Proof
  rw[step_def]
  \\ irule valid_result_eq_handle
  \\ irule valid_result_eq_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ rw[]
  >- (
    rw[valid_result_eq_def, valid_result_fn_def, valid_result_def, valid_def]
    \\ first_x_assum drule
    \\ rw[has_cc_def]
    \\ gvs[] )
  \\ TRY (
    irule valid_result_get_current_context
    \\ rw[]
    \\ first_x_assum drule
    \\ rw[has_cc_def]
    \\ rw[] )
  \\ CASE_TAC
  >- (
    rw[valid_result_eq_def, valid_result_fn_def, valid_result_def, valid_def]
    \\ first_x_assum drule \\ rw[has_cc_def]
    \\ gvs[] )
  \\ irule valid_result_eq_weaken
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ first_x_assum drule
  \\ rw[has_cc_def]
  \\ gvs[]
QED

Theorem valid_imp:
  valid P f Q ∧ P s
  ⇒
  ∃r t. f s = (r, t) ∧ Q r t
Proof
  rw[valid_def]
  \\ last_x_assum drule
  \\ CASE_TAC \\ rw[]
QED

Theorem valid_result_imp:
  valid_result P f Q ∧ P s ⇒
  ∃r t. f s = (INL r, t) ∧ Q r t
Proof
  rw[valid_result_def]
  \\ drule valid_imp
  \\ disch_then drule
  \\ rw[] \\ gvs[]
  \\ Cases_on`r` \\ gvs[]
QED

Theorem valid_result_eq_imp:
  valid_result_eq P f Q x ∧ P s ⇒
  ∃t. f s = (INL x, t) ∧ Q t
Proof
  rw[valid_result_eq_def, valid_result_fn_def]
  \\ drule valid_result_imp
  \\ disch_then drule
  \\ rw[]
QED

val () = export_theory();
