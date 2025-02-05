open HolKernel boolLib bossLib Parse
     pred_setTheory
     vfmContextTheory vfmExecutionTheory;

val () = new_theory "vfmLogic";

Definition spec_def:
  spec P f Q =
  ∀s: execution_state.
    P s ⇒ case f s : α execution_result
          of (r, t) => Q r t
End

Definition spec_exc_def:
  spec_exc P f Q R =
  spec P f (λr s. case r of INL x => Q x s | INR e => R e s)
End

Definition spec_excl_def:
  spec_excl P f Q G =
  spec_exc P f Q (λe s. e ∈ G)
End

Definition spec_excl_unit_def:
  spec_excl_unit P f Q G =
  spec_excl P f (λ(r:unit). Q) G
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

Theorem spec_exc_strengthen:
  spec_exc P f Q1 R1 ∧
  (∀r s. Q1 r s ⇒ Q r s) ∧
  (∀e s. R1 e s ⇒ R e s)
  ⇒
  spec_exc P f Q R
Proof
  rw[spec_exc_def]
  \\ irule spec_strengthen
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[] \\ CASE_TAC \\ gvs[]
QED

Theorem spec_excl_strengthen:
  spec_excl P f Q1 G1 ∧
  (∀r s. Q1 r s ⇒ Q r s) ∧
  G1 ⊆ G
  ⇒
  spec_excl P f Q G
Proof
  rw[spec_excl_def]
  \\ irule spec_exc_strengthen
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[] \\ gvs[SUBSET_DEF]
QED

Theorem spec_excl_unit_strengthen:
  spec_excl_unit P f Q1 G1 ∧
  (∀s. Q1 s ⇒ Q s) ∧
  G1 ⊆ G
  ⇒
  spec_excl_unit P f Q G
Proof
  rw[spec_excl_unit_def]
  \\ irule spec_excl_strengthen
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem spec_exc_weaken:
  spec_exc P1 f1 Q R ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_exc P f Q R
Proof
  rw[spec_exc_def]
  \\ metis_tac[spec_weaken]
QED

Theorem spec_excl_weaken:
  spec_excl P1 f1 Q G ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_excl P f Q G
Proof
  rw[spec_excl_def]
  \\ metis_tac[spec_exc_weaken]
QED

Theorem spec_excl_unit_weaken:
  spec_excl_unit P1 f1 Q G ∧ (∀s. P s ⇒ P1 s ∧ f1 = f) ⇒
  spec_excl_unit P f Q G
Proof
  rw[spec_excl_unit_def]
  \\ metis_tac[spec_excl_weaken]
QED

Theorem spec_excl_bind:
  spec_excl P g Q1 G ∧
  (∀x. spec_excl (Q1 x) (f x) Q G)
  ⇒
  spec_excl P (monad_bind g f) Q G
Proof
  rw[spec_excl_def, spec_exc_def, spec_def, bind_def]
  \\ CASE_TAC \\ gvs[]
  \\ last_x_assum drule \\ rw[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem spec_excl_unit_bind:
  spec_excl P g Q1 G ∧
  (∀x. spec_excl_unit (Q1 x) (f x) Q G)
  ⇒
  spec_excl_unit P (monad_bind g f) Q G
Proof
  rw[spec_excl_unit_def]
  \\ irule spec_excl_bind
  \\ metis_tac[]
QED

Theorem spec_excl_ignore_bind:
  spec_excl P r Q1 G ∧
  (∀x. spec_excl (Q1 x) f Q G)
  ⇒
  spec_excl P (ignore_bind r f) Q G
Proof
  rw[spec_def, spec_exc_def, spec_excl_def, ignore_bind_def, bind_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ gvs[] \\ strip_tac
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem spec_excl_unit_ignore_bind:
  spec_excl P g Q1 G ∧
  (∀x. spec_excl_unit (Q1 x) f Q G)
  ⇒
  spec_excl_unit P (ignore_bind g f) Q G
Proof
  rw[spec_excl_unit_def]
  \\ irule spec_excl_ignore_bind
  \\ goal_assum drule \\ rw[]
QED

Theorem spec_excl_unit_unit:
  spec_excl_unit P g Q1 G ∧
  spec_excl_unit Q1 f Q G
  ⇒
  spec_excl_unit P (ignore_bind g f) Q G
Proof
  rw[spec_excl_unit_def]
  \\ irule spec_excl_ignore_bind
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ gvs[]
QED

Theorem mp_rand:
  Q s1 ∧ s1 = s2 ⇒ Q s2
Proof
  rw[] \\ rw[]
QED

(* TODO: move specs of vfmExecution to another theory *)
(* TODO: move pure monad specs to another theory? *)

Definition has_cc_def:
  has_cc P s =
  ∃c t. s.contexts = c :: t ∧ P c
End

Definition update_cc_def:
  update_cc f s =
  s with contexts updated_by (λls. (f (HD ls))::(TL ls))
End

Theorem spec_excl_get_current_context:
  (∀s. P s ∧ s.contexts ≠ [] ⇒ Q (HD s.contexts) s) ∧
  (∀s. P s ∧ SOME Impossible ∉ G ⇒ s.contexts ≠ [])
  ⇒
  spec_excl P get_current_context Q G
Proof
  rw[spec_excl_def, spec_exc_def, spec_def, get_current_context_def]
  \\ rw[fail_def, return_def]
  \\ metis_tac[]
QED

Theorem spec_excl_unit_assert:
  (∀s. P s ∧ b ⇒ Q s) ∧
  (SOME e ∉ G ⇒ ∀s. P s ⇒ b)
  ⇒
  spec_excl_unit P (assert b e) Q G
Proof
  rw[spec_excl_unit_def, spec_excl_def, spec_exc_def, spec_def, assert_def]
  \\ metis_tac[]
QED

Theorem spec_excl_unit_set_current_context:
  (∀s. P s ∧ s.contexts ≠ [] ⇒ Q (update_cc (K c) s)) ∧
  (SOME Impossible ∉ G ⇒ ∀s. P s ⇒ s.contexts ≠ [])
  ⇒
  spec_excl_unit P (set_current_context c) Q G
Proof
  rw[spec_excl_unit_def, spec_excl_def,
     spec_exc_def, spec_def, set_current_context_def]
  \\ rw[fail_def] >- metis_tac[]
  \\ last_x_assum drule \\ rw[return_def, update_cc_def]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality]
QED

Theorem spec_exc_handle:
  spec_exc P f Q R1 ∧
  (∀e. spec_exc (R1 e) (g e) Q R)
  ⇒
  spec_exc P (handle f g) Q R
Proof
  rw[spec_exc_def, spec_def, handle_def]
  \\ first_x_assum drule
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ gvs[]
QED

(*

Theorem spec_excl_unit_consume_gas:
  (∀s. P s ∧ SOME Impossible ∉ G ⇒ s.contexts ≠ []) ∧
  (∀s. P s ∧ SOME OutOfGas ∉ G ∧ s.contexts ≠ [] ⇒
       let c = HD s.contexts in
       c.gasUsed + n ≤ c.msgParams.gasLimit) ∧
  (∀s. P s ∧ has_cc (λc. c.gasUsed + n ≤ c.msgParams.gasLimit) s
       ⇒ Q (update_cc (λc. c with gasUsed updated_by $+ n) s))
  ⇒
  spec_excl_unit P (consume_gas n) Q G
Proof
  rw[consume_gas_def]
  \\ irule spec_excl_unit_bind
  \\ qexists_tac`λr s. P s ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- ( irule spec_excl_get_current_context \\ rw[] )
  \\ irule spec_excl_unit_unit
  \\ qexists_tac`λs. P s ∧ x = HD s.contexts`
  \\ reverse(rw[])
  >- (
    irule spec_excl_unit_set_current_context \\ rw[]

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

*)

val () = export_theory();
