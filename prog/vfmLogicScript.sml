open HolKernel boolLib bossLib Parse
     vfmContextTheory vfmExecutionTheory;

val () = new_theory "vfmLogic";

Definition spec_def:
  spec P f Q =
  ∀s: execution_state.
    P s ⇒ case f s : α execution_result
          of (r, t) => Q r t
End

Definition spec_total_def:
  spec_total P f Q =
  spec P f (λr s. ISL r ∧ Q (OUTL r) s)
End

Definition spec_total_fn_def:
  spec_total_fn P f Q g =
  spec_total P f (λr s. Q s ∧ r = g s)
End

Definition spec_total_eq_def:
  spec_total_eq P f Q x =
  spec_total_fn P f Q (K x)
End

(* TODO: need a version that specifies which exceptions are allowed? *)

Definition spec_partial_def:
  spec_partial P f Q =
  spec P f (λr s. ISL r ⇒ Q (OUTL r) s)
End

Definition spec_partial_unit_def:
  spec_partial_unit P f Q =
  spec_partial P f (λ(r:unit) s. Q s)
End

Theorem spec_strengthen:
  spec P f Q1 ∧
  (∀r s. Q1 r s ⇒ Q r s)
  ⇒
  spec P f Q
Proof
  rw[spec_def]
  \\ last_x_assum drule \\ gvs[]
  \\ CASE_TAC \\ rw[]
QED

Theorem spec_weaken:
  spec P1 f1 Q ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec P f Q
Proof
  rw[spec_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem spec_total_weaken:
  spec_total P1 f1 Q ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_total P f Q
Proof
  rw[spec_total_def]
  \\ metis_tac[spec_weaken]
QED

Theorem spec_total_fn_weaken:
  spec_total_fn P1 f1 Q g ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_total_fn P f Q g
Proof
  rw[spec_total_fn_def]
  \\ metis_tac[spec_total_weaken]
QED

Theorem spec_total_eq_weaken:
  spec_total_eq P1 f1 Q g ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_total_eq P f Q g
Proof
  rw[spec_total_eq_def]
  \\ metis_tac[spec_total_fn_weaken]
QED

Theorem spec_partial_weaken:
  spec_partial P1 f1 Q ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_partial P f Q
Proof
  rw[spec_partial_def]
  \\ metis_tac[spec_weaken]
QED

Theorem spec_partial_unit_weaken:
  spec_partial_unit P1 f1 Q ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_partial_unit P f Q
Proof
  rw[spec_partial_unit_def]
  \\ metis_tac[spec_partial_weaken]
QED

Theorem spec_total_spec:
  spec_total P f Q1 ∧
  (∀r s. ISL r ∧ Q1 (OUTL r) s ⇒ Q r s)
  ⇒
  spec P f Q
Proof
  rw[spec_total_def]
  \\ irule spec_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem spec_total_eq_spec_total:
  spec_total_eq P f Q1 x ∧
  (∀s. Q1 s ⇒ Q x s)
  ⇒
  spec_total P f Q
Proof
  rw[spec_total_fn_def, spec_total_eq_def, spec_total_def]
  \\ irule spec_strengthen
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem spec_bind_total:
  spec_total P g Q1 ∧
  (∀x. spec (Q1 x) (f x) Q)
  ⇒
  spec P (monad_bind g f) Q
Proof
  rw[spec_total_def, spec_def, bind_def]
  \\ CASE_TAC \\ gvs[]
  \\ last_x_assum drule \\ rw[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem spec_ignore_bind_total:
  spec_total P r Q1 ∧
  (∀x. spec (Q1 x) f Q)
  ⇒
  spec P (ignore_bind r f) Q
Proof
  rw[spec_def, spec_total_def, ignore_bind_def, bind_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ gvs[] \\ strip_tac
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem spec_partial_bind:
  spec_partial P g Q1 ∧
  (∀x. spec_partial (Q1 x) (f x) Q)
  ⇒
  spec_partial P (monad_bind g f) Q
Proof
  rw[spec_partial_def, spec_def, bind_def]
  \\ last_x_assum drule \\ rw[]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem spec_partial_ignore_bind:
  spec_partial P g Q1 ∧
  (∀x. spec_partial (Q1 x) f Q)
  ⇒
  spec_partial P (ignore_bind g f) Q
Proof
  rw[spec_partial_def, spec_def, ignore_bind_def, bind_def]
  \\ last_x_assum drule
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
  \\ last_x_assum drule \\ rw[]
QED

Theorem spec_partial_unit_bind:
  spec_partial P g Q1 ∧
  (∀x. spec_partial_unit (Q1 x) (f x) Q)
  ⇒
  spec_partial_unit P (monad_bind g f) Q
Proof
  rw[spec_partial_unit_def]
  \\ irule spec_partial_bind
  \\ goal_assum drule \\ rw[]
QED

Theorem spec_partial_unit_ignore_bind:
  spec_partial P g Q1 ∧
  (∀x. spec_partial_unit (Q1 x) f Q)
  ⇒
  spec_partial_unit P (ignore_bind g f) Q
Proof
  rw[spec_partial_unit_def]
  \\ irule spec_partial_ignore_bind
  \\ goal_assum drule \\ rw[]
QED

Theorem spec_partial_unit_unit_ignore_bind:
  spec_partial_unit P g Q1 ∧
  spec_partial_unit Q1 f Q
  ⇒
  spec_partial_unit P (ignore_bind g f) Q
Proof
  rw[spec_partial_unit_def]
  \\ irule spec_partial_ignore_bind
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ gvs[ETA_AX]
QED

Theorem spec_total_bind:
  spec_total P g Q1 ∧
  (∀x. spec_total (Q1 x) (f x) Q)
  ⇒
  spec_total P (monad_bind g f) Q
Proof
  rw[]
  \\ rw[spec_total_def]
  \\ irule spec_bind_total
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule spec_total_spec
  \\ qexists_tac`Q` \\ rw[]
QED

Theorem spec_total_ignore_bind:
  spec_total P r Q1 ∧
  (∀x. spec_total (Q1 x) f Q)
  ⇒
  spec_total P (ignore_bind r f) Q
Proof
  rw[]
  \\ rw[spec_total_def]
  \\ irule spec_ignore_bind_total
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule spec_total_spec
  \\ qexists_tac`Q` \\ rw[]
QED

Theorem spec_total_fn_bind:
  spec_total P g Q1 ∧
  (∀x. spec_total_fn (Q1 x) (f x) Q h)
  ⇒
  spec_total_fn P (monad_bind g f) Q h
Proof
  rw[]
  \\ rw[spec_total_fn_def]
  \\ irule spec_total_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ fs[spec_total_fn_def]
QED

Theorem spec_total_eq_bind:
  spec_total P g Q1 ∧
  (∀x. spec_total_eq (Q1 x) (f x) Q y)
  ⇒
  spec_total_eq P (monad_bind g f) Q y
Proof
  rw[spec_total_eq_def]
  \\ irule spec_total_fn_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem spec_total_fn_ignore_bind:
  spec_total P g Q1 ∧
  (∀x. spec_total_fn (Q1 x) f Q h)
  ⇒
  spec_total_fn P (ignore_bind g f) Q h
Proof
  rw[]
  \\ rw[spec_total_fn_def]
  \\ irule spec_total_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ fs[spec_total_fn_def]
QED

Theorem spec_total_eq_ignore_bind:
  spec_total P g Q1 ∧
  (∀x. spec_total_eq (Q1 x) f Q y)
  ⇒
  spec_total_eq P (ignore_bind g f) Q y
Proof
  rw[spec_total_eq_def]
  \\ irule spec_total_fn_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem spec_total_eq_eq_ignore_bind:
  spec_total_eq P g Q1 z ∧
  spec_total_eq Q1 f Q y
  ⇒
  spec_total_eq P (ignore_bind g f) Q y
Proof
  rw[spec_total_eq_def]
  \\ irule spec_total_fn_ignore_bind
  \\ gs[spec_total_fn_def]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ irule spec_total_weaken
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

(* TODO: clean up naming esp. of total specs *)
(* TODO: move specs of vfmExecution to another theory *)
(* TODO: move pure monad specs to another theory? *)
(* TODO: split theories for total and partial specs? *)

Theorem spec_partial_get_current_context:
  (∀s. P s ∧ s.contexts ≠ [] ⇒ Q (HD s.contexts) s)
  ⇒
  spec_partial P get_current_context Q
Proof
  rw[spec_partial_def, spec_def, get_current_context_def]
  \\ rw[fail_def, return_def]
QED

Theorem spec_total_get_current_context:
  (∀s. P s ⇒ ¬NULL s.contexts) ∧
  (∀s. P s ⇒ Q (HD s.contexts) s)
  ⇒
  spec_total P get_current_context Q
Proof
  rw[spec_total_def, spec_def, get_current_context_def]
  \\ rw[fail_def, return_def]
  \\ rpt(first_x_assum drule)
  \\ rw[]
QED

Theorem spec_total_eq_assert:
  (∀s. P s ⇒ b ∧ Q s)
  ⇒
  spec_total_eq P (assert b e) Q ()
Proof
  rw[spec_total_eq_def, spec_total_fn_def, spec_total_def, spec_def, assert_def]
QED

Theorem spec_partial_unit_assert:
  (∀s. P s ⇒ Q s)
  ⇒
  spec_partial_unit P (assert b e) Q
Proof
  rw[spec_partial_unit_def, spec_partial_def, spec_def, assert_def]
QED

Theorem spec_total_eq_set_current_context:
  (∀s. P s ⇒ ¬NULL s.contexts) ∧
  (∀s. P s ⇒ Q (s with contexts updated_by λls. c :: TL ls))
  ⇒
  spec_total_eq P (set_current_context c) Q ()
Proof
  rw[spec_total_eq_def, spec_total_def, spec_def,
     spec_total_fn_def, set_current_context_def]
  \\ last_x_assum drule \\ rw[return_def]
  \\ last_x_assum drule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`Q s1`
  \\ qmatch_asmsub_abbrev_tac`Q s2`
  \\ `s1 = s2` by rw[Abbr`s1`, Abbr`s2`, execution_state_component_equality]
  \\ rw[]
QED

Theorem spec_total_handle:
  spec_total P f Q
  ⇒
  spec_total P (handle f g) Q
Proof
  rw[spec_total_def, spec_def, handle_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ gvs[]
QED

Theorem spec_total_fn_handle:
  spec_total_fn P f Q k
  ⇒
  spec_total_fn P (handle f g) Q k
Proof
  rw[spec_total_fn_def, spec_total_handle]
QED

Theorem spec_total_eq_handle:
  spec_total_eq P f Q ()
  ⇒
  spec_total_eq P (handle f g) Q ()
Proof
  rw[spec_total_eq_def, spec_total_fn_handle]
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

Theorem spec_total_eq_consume_gas:
  (∀s. P s ⇒ has_cc (λc. c.gasUsed + n ≤ c.msgParams.gasLimit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with gasUsed updated_by $+ n) s))
  ⇒
  spec_total_eq P (consume_gas n) Q ()
Proof
  rw[consume_gas_def]
  \\ irule spec_total_eq_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule spec_total_get_current_context
    \\ rw[] \\ res_tac \\ fs[has_cc_def])
  \\ irule spec_total_eq_ignore_bind
  \\ qexists_tac`λr s. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule spec_total_eq_spec_total \\ rw[]
    \\ qexists_tac`λs. P s ∧ x = HD s.contexts` \\ rw[]
    \\ irule spec_total_eq_assert
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule spec_total_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem spec_total_eq_push_stack:
  (∀s. P s ⇒ has_cc (λc. LENGTH c.stack < stack_limit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with stack updated_by CONS w) s))
  ⇒
  spec_total_eq P (push_stack w) Q ()
Proof
  (* TODO: mostly repeated from previous proof - abstract or automate? *)
  rw[push_stack_def]
  \\ irule spec_total_eq_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule spec_total_get_current_context
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule spec_total_eq_ignore_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule spec_total_eq_spec_total \\ rw[]
    \\ qexists_tac`λs. P s ∧ x = HD s.contexts` \\ rw[]
    \\ irule spec_total_eq_assert
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ irule spec_total_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem spec_total_eq_step_push:
  g = static_gas (Push n ws) ∧
  w = word_of_bytes F 0w (REVERSE ws) ∧
  (∀s. P s ⇒ has_cc (λc.
         c.gasUsed + g ≤ c.msgParams.gasLimit ∧
         LENGTH c.stack < stack_limit) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with <|
                  stack updated_by CONS w
                ; gasUsed updated_by $+ g |>) s))
  ⇒
  spec_total_eq P (step_push n ws) Q ()
Proof
  rw[step_push_def, Excl"static_gas_def"]
  \\ qmatch_goalsub_abbrev_tac`consume_gas g`
  \\ qmatch_goalsub_abbrev_tac`push_stack w`
  \\ irule spec_total_eq_ignore_bind \\ rw[]
  \\ qexists_tac`λr s. has_cc (λc. LENGTH c.stack < stack_limit) s ∧
                       Q (update_cc (λc. c with stack updated_by CONS w) s)`
  \\ reverse (rw[])
  >- (
    irule spec_total_eq_spec_total
    \\ qmatch_goalsub_abbrev_tac`_ ⇒ Q1 _ _`
    \\ qexists_tac`λs. Q1 () s`
    \\ rw[Abbr`Q1`]
    \\ irule spec_total_eq_consume_gas
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[update_cc_def]
    \\ last_x_assum drule \\ rw[update_cc_def]
    \\ irule mp_rand \\ goal_assum drule
    \\ rw[execution_state_component_equality,
         context_component_equality, update_cc_def])
  \\ irule spec_total_eq_push_stack
  \\ rw[]
QED

Theorem spec_total_eq_inc_pc_or_jump_inc:
  n = LENGTH (opcode i) ∧ ¬is_call i ∧
  (∀s. P s ⇒ has_cc (λc. c.jumpDest = NONE) s) ∧
  (∀s. P s ⇒ Q (update_cc (λc. c with pc updated_by $+ n) s))
  ⇒
  spec_total_eq P (inc_pc_or_jump i) Q ()
Proof
  rw[inc_pc_or_jump_def]
  \\ irule spec_total_eq_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse conj_tac
  >- (
    irule spec_total_get_current_context
    \\ rw[]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ rw[] )
  \\ rw[]
  \\ reverse(Cases_on`x.jumpDest`)
  >- (
    rw[spec_total_eq_def, spec_total_fn_def, spec_total_def, spec_def]
    \\ last_x_assum drule \\ rw[has_cc_def]
    \\ gs[] )
  \\ rw[]
  \\ irule spec_total_eq_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ last_x_assum drule \\ rw[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem spec_total_eq_step:
  (∀s. P s ⇒ has_cc (λc.
    c.pc < LENGTH c.msgParams.code ∧
    FLOOKUP c.msgParams.parsed c.pc = SOME op) s) ∧
  spec_total_eq P (do step_inst op; inc_pc_or_jump op od) Q ()
  ⇒
  spec_total_eq P step Q ()
Proof
  rw[step_def]
  \\ irule spec_total_eq_handle
  \\ irule spec_total_eq_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ rw[]
  >- (
    rw[spec_total_eq_def, spec_total_fn_def, spec_total_def, spec_def]
    \\ first_x_assum drule
    \\ rw[has_cc_def]
    \\ gvs[] )
  \\ TRY (
    irule spec_total_get_current_context
    \\ rw[]
    \\ first_x_assum drule
    \\ rw[has_cc_def]
    \\ rw[] )
  \\ CASE_TAC
  >- (
    rw[spec_total_eq_def, spec_total_fn_def, spec_total_def, spec_def]
    \\ first_x_assum drule \\ rw[has_cc_def]
    \\ gvs[] )
  \\ irule spec_total_eq_weaken
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ first_x_assum drule
  \\ rw[has_cc_def]
  \\ gvs[]
QED

Theorem spec_imp:
  spec P f Q ∧ P s
  ⇒
  ∃r t. f s = (r, t) ∧ Q r t
Proof
  rw[spec_def]
  \\ last_x_assum drule
  \\ CASE_TAC \\ rw[]
QED

Theorem spec_total_imp:
  spec_total P f Q ∧ P s ⇒
  ∃r t. f s = (INL r, t) ∧ Q r t
Proof
  rw[spec_total_def]
  \\ drule spec_imp
  \\ disch_then drule
  \\ rw[] \\ gvs[]
  \\ Cases_on`r` \\ gvs[]
QED

Theorem spec_total_eq_imp:
  spec_total_eq P f Q x ∧ P s ⇒
  ∃t. f s = (INL x, t) ∧ Q t
Proof
  rw[spec_total_eq_def, spec_total_fn_def]
  \\ drule spec_total_imp
  \\ disch_then drule
  \\ rw[]
QED

val () = export_theory();
