open HolKernel boolLib bossLib Parse
     arithmeticTheory listTheory sumTheory relationTheory pairTheory pred_setTheory
     vfmConstantsTheory vfmContextTheory vfmExecutionTheory;

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

Theorem spec_excl_unit_handle:
  spec_exc P f (λr. Q) R1 ∧
  (∀e. spec_excl_unit (R1 e) (g e) Q G)
  ⇒
  spec_excl_unit P (handle f g) Q G
Proof
  rw[spec_excl_unit_def, spec_excl_def]
  \\ irule spec_exc_handle
  \\ goal_assum drule
  \\ gvs[]
QED

Definition has_gas_def:
  has_gas n c = (c.gasUsed + n ≤ c.msgParams.gasLimit)
End

Theorem spec_excl_unit_consume_gas:
  (∀s. P s ∧ SOME Impossible ∉ G ⇒ s.contexts ≠ []) ∧
  (∀s. P s ∧ SOME OutOfGas ∉ G ∧ s.contexts ≠ []
       ⇒ has_gas n (HD s.contexts)) ∧
  (∀s. P s ∧ has_cc (has_gas n) s
       ⇒ Q (update_cc (λc. c with gasUsed updated_by $+ n) s))
  ⇒
  spec_excl_unit P (consume_gas n) Q G
Proof
  rw[consume_gas_def]
  \\ irule spec_excl_unit_bind
  \\ qexists_tac`λr s. P s ∧ s.contexts ≠ [] ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- ( irule spec_excl_get_current_context \\ rw[] )
  \\ irule spec_excl_unit_unit
  \\ qmatch_goalsub_abbrev_tac`assert b`
  \\ qexists_tac`λs. P s ∧ s.contexts ≠ [] ∧ x = HD s.contexts ∧ b`
  \\ rw[]
  >- ( irule spec_excl_unit_assert \\ rw[Abbr`b`] \\ gs[has_gas_def] )
  \\ irule spec_excl_unit_set_current_context
  \\ rw[]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ first_x_assum drule
  \\ rw[has_cc_def, has_gas_def]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem spec_excl_unit_push_stack:
  (∀s. P s ∧ SOME Impossible ∉ G ⇒ s.contexts ≠ []) ∧
  (∀s. P s ∧ SOME StackOverflow ∉ G ∧ s.contexts ≠ []
       ⇒ LENGTH (HD s.contexts).stack < stack_limit) ∧
  (∀s. P s ∧ has_cc (λc. LENGTH c.stack < stack_limit) s
       ⇒ Q (update_cc (λc. c with stack updated_by CONS w) s))
  ⇒
  spec_excl_unit P (push_stack w) Q G
Proof
  (* TODO: mostly repeated from previous proof - abstract or automate? *)
  rw[push_stack_def]
  \\ irule spec_excl_unit_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ s.contexts ≠ [] ∧ r = HD s.contexts`
  \\ reverse(rw[])
  >- ( irule spec_excl_get_current_context \\ rw[] )
  \\ irule spec_excl_unit_unit \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`assert b`
  \\ qexists_tac`λs. P s ∧ s.contexts ≠ [] ∧ x = HD s.contexts ∧ b`
  \\ rw[]
  >- ( irule spec_excl_unit_assert \\ rw[Abbr`b`] \\ gs[has_gas_def] )
  \\ irule spec_excl_unit_set_current_context
  \\ rw[]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ first_x_assum drule
  \\ rw[has_cc_def]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

Theorem spec_excl_unit_step_push:
  g = static_gas (Push n ws) ∧
  w = word_of_bytes F 0w (REVERSE ws) ∧
  (∀s. P s ∧ SOME Impossible ∉ G ⇒ s.contexts ≠ []) ∧
  (∀s. P s ∧ SOME StackOverflow ∉ G ∧ s.contexts ≠ []
       ⇒ LENGTH (HD s.contexts).stack < stack_limit) ∧
  (∀s. P s ∧ SOME OutOfGas ∉ G ∧ s.contexts ≠ []
       ⇒ has_gas g (HD s.contexts)) ∧
  (∀s. P s ∧ has_cc (λc. has_gas g c ∧ LENGTH c.stack < stack_limit) s
       ⇒ Q (update_cc (λc. c with <|
                  stack updated_by CONS w
                ; gasUsed updated_by $+ g |>) s))
  ⇒
  spec_excl_unit P (step_push n ws) Q G
Proof
  rw[step_push_def, Excl"static_gas_def"]
  \\ qmatch_goalsub_abbrev_tac`consume_gas g`
  \\ qmatch_goalsub_abbrev_tac`push_stack w`
  \\ irule spec_excl_unit_ignore_bind \\ rw[]
  (* TODO: need to derive/match this automatically *)
  \\ qexists_tac`λr s.
       (SOME Impossible ∉ G ⇒ s.contexts ≠ []) ∧
       (SOME StackOverflow ∉ G ∧ s.contexts ≠ [] ⇒
        LENGTH (HD s.contexts).stack < stack_limit) ∧
       (has_cc (λc. LENGTH c.stack < stack_limit) s ⇒
        Q (update_cc (λc. c with stack updated_by CONS w) s))`
  \\ reverse (rw[])
  >- (
    irule (iffLR spec_excl_unit_def)
    \\ irule spec_excl_unit_consume_gas
    \\ rw[]
    \\ rpt(first_x_assum drule)
    \\ gvs[has_cc_def, update_cc_def]
    \\ strip_tac
    \\ irule mp_rand \\ goal_assum drule
    \\ rw[execution_state_component_equality,
         context_component_equality])
  \\ irule spec_excl_unit_push_stack
  \\ rw[]
QED

Theorem spec_excl_unit_inc_pc_or_jump_inc:
  n = LENGTH (opcode i) ∧ ¬is_call i ∧
  (∀s. P s ∧ SOME Impossible ∉ G ⇒ s.contexts ≠ []) ∧
  (∀s. P s ∧ s.contexts ≠ [] ⇒ (HD s.contexts).jumpDest = NONE) ∧
  (∀s. P s ∧ has_cc (λc. c.jumpDest = NONE) s
       ⇒ Q (update_cc (λc. c with pc updated_by $+ n) s))
  ⇒
  spec_excl_unit P (inc_pc_or_jump i) Q G
Proof
  rw[inc_pc_or_jump_def]
  \\ irule spec_excl_unit_bind \\ rw[]
  \\ qexists_tac`λr s. P s ∧ s.contexts ≠ [] ∧ r = HD s.contexts`
  \\ reverse conj_tac
  >- ( irule spec_excl_get_current_context \\ rw[])
  \\ rw[]
  \\ reverse(Cases_on`x.jumpDest`)
  >- (
    rw[spec_excl_unit_def, spec_excl_def, spec_exc_def, spec_def]
    \\ rpt(last_x_assum drule)
    \\ rw[has_cc_def])
  \\ rw[]
  \\ irule spec_excl_unit_set_current_context
  \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ last_x_assum drule \\ rw[has_cc_def]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ irule mp_rand \\ goal_assum drule
  \\ rw[execution_state_component_equality,
        context_component_equality, update_cc_def]
QED

(*
Theorem spec_excl_unit_step:
  (∀s. P s ⇒ has_cc (λc.
    c.pc < LENGTH c.msgParams.code ∧
    FLOOKUP c.msgParams.parsed c.pc = SOME op) s) ∧
  spec_excl_unit P (do step_inst op; inc_pc_or_jump op od) Q G
  ⇒
  spec_excl_unit P step Q G
Proof
  rw[step_def]
  \\ irule spec_excl_unit_handle

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
*)

Theorem spec_imp:
  spec P f Q ∧ P s
  ⇒
  ∃r t. f s = (r, t) ∧ Q r t
Proof
  rw[spec_def]
  \\ last_x_assum drule
  \\ CASE_TAC \\ rw[]
QED

Theorem spec_excl_imp:
  spec_excl P f Q G ∧ P s ⇒
  case f s of (INR e, t) => e ∈ G | (INL r, t) => Q r t
Proof
  rw[spec_excl_def, spec_exc_def]
  \\ drule spec_imp
  \\ disch_then drule
  \\ rw[] \\ gvs[]
QED

Definition decreases_gas_def:
  decreases_gas strict (m: execution_state -> α execution_result) =
    ∀s c cs. s.contexts = c::cs ∧ c.gasUsed ≤ c.msgParams.gasLimit ⇒
    ∃c'.
      (SND (m s)).contexts = c'::cs ∧
      c'.gasUsed ≤ c'.msgParams.gasLimit ∧
      c'.msgParams.gasLimit = c.msgParams.gasLimit ∧
      if strict ∧ ISL (FST (m s))
      then c.gasUsed < c'.gasUsed
      else c.gasUsed ≤ c'.gasUsed
End

Theorem decreases_gas_mono:
  (s' ⇒ s) ∧
  decreases_gas s m ⇒ decreases_gas s' m
Proof
  rw [decreases_gas_def] \\ first_x_assum drule \\ rw []
  \\ qhdtm_x_assum `COND` mp_tac \\ Cases_on `s` \\ rw []
QED

Theorem decreases_gas_return[simp]:
  decreases_gas F (return a)
Proof
  simp [decreases_gas_def, return_def]
QED

Theorem decreases_gas_bind_pred:
  decreases_gas sg g ∧
  (∀s a. FST (g s) = INL a ⇒ p a) ∧
  (∀x. p x ⇒ decreases_gas sf (f x)) ⇒
  decreases_gas (sf ∨ sg) (monad_bind g f)
Proof
  rw [decreases_gas_def, bind_def]
  \\ last_x_assum drule \\ rw []
  \\ CASE_TAC \\ CASE_TAC \\ gvs []
  \\ last_x_assum (qspecl_then [`s`,`x`] mp_tac) \\ rw []
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum (drule_then mp_tac) \\ rw []
  \\ Cases_on `sf` \\ simp []
  \\ rpt (qhdtm_x_assum `COND` mp_tac) \\ rw []
QED

Theorem decreases_gas_bind:
  decreases_gas sg g ∧ (∀x. decreases_gas sf (f x)) ⇒
  decreases_gas (sf ∨ sg) (bind g f)
Proof
  rw [] \\ irule decreases_gas_bind_pred \\ rw []
  \\ qexists_tac `λ_.T` \\ rw []
QED

Theorem decreases_gas_bind_mono:
  decreases_gas sg g ∧ (∀x. decreases_gas sf (f x)) ∧
  (sgf ⇒ sf ∨ sg) ⇒
  decreases_gas sgf (bind g f)
Proof
  rw [] \\ drule_then drule decreases_gas_bind \\ strip_tac
  \\ irule decreases_gas_mono \\ rpt (goal_assum drule)
QED

Theorem decreases_gas_bind_right:
  decreases_gas sg g ∧ (∀x. decreases_gas sf (f x)) ⇒
  decreases_gas sf (bind g f)
Proof
  rw [] \\ irule decreases_gas_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_bind_false:
  decreases_gas sg g ∧ (∀x. decreases_gas F (f x)) ⇒
  decreases_gas sg (bind g f)
Proof
  rw [] \\ irule decreases_gas_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_ignore_bind_mono:
  decreases_gas sg g ∧ decreases_gas sf f ∧
  (sgf ⇒ sf ∨ sg) ⇒
  decreases_gas sgf (ignore_bind g f)
Proof
  rw [ignore_bind_def] \\ irule decreases_gas_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_ignore_bind:
  decreases_gas sg g ∧ decreases_gas sf f ⇒
  decreases_gas (sf ∨ sg) (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_ignore_bind_right:
  decreases_gas sg g ∧ decreases_gas sf f ⇒
  decreases_gas sf (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_ignore_bind_false:
  decreases_gas sg g ∧ decreases_gas sf f ⇒
  decreases_gas F (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_get_current_context[simp]:
  decreases_gas F get_current_context
Proof
  simp [decreases_gas_def, get_current_context_def, return_def]
QED

Theorem decreases_gas_assert[simp]:
  decreases_gas F (assert b e)
Proof
  simp [decreases_gas_def, assert_def]
  \\ Cases_on `b` \\ rw []
QED

Theorem decreases_gas_consume_gas:
  decreases_gas (0 < n) (consume_gas n)
Proof
  rw [decreases_gas_def, consume_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
  \\ CASE_TAC \\ rw []
QED

Theorem decreases_gas_consume_gas_bind[simp]:
  0 < n ∧ decreases_gas sf f ⇒
  decreases_gas T (do consume_gas n; f od)
Proof
  rw [] \\ irule decreases_gas_ignore_bind_mono
  \\ irule_at Any decreases_gas_consume_gas
  \\ metis_tac []
QED

Theorem decreases_gas_pop_stack[simp]:
  decreases_gas F (pop_stack n)
Proof
  rw [decreases_gas_def, pop_stack_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def] \\ rw []
QED

Theorem decreases_gas_step_pop[simp]:
  decreases_gas T step_pop
Proof
  rw [step_pop_def]
  \\ irule decreases_gas_ignore_bind_mono
  \\ irule_at Any decreases_gas_pop_stack
  \\ irule_at Any decreases_gas_consume_gas
  \\ simp []
QED

Theorem decreases_gas_push_stack[simp]:
  decreases_gas F (push_stack w)
Proof
  rw [decreases_gas_def, push_stack_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def] \\ rw []
QED

Theorem decreases_gas_step_push[simp]:
  decreases_gas T (step_push n ws)
Proof
  rw [step_push_def]
  \\ irule decreases_gas_ignore_bind_mono
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_push_stack
  \\ simp []
QED

Theorem decreases_gas_step_dup[simp]:
  decreases_gas T (step_dup n)
Proof
  rw [step_dup_def]
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_assert
  \\ irule_at Any decreases_gas_push_stack
QED

Theorem decreases_gas_step_swap[simp]:
  decreases_gas T (step_swap n)
Proof
  rw [step_swap_def]
  \\ irule decreases_gas_ignore_bind_mono
  \\ irule_at Any decreases_gas_consume_gas
  \\ qexists_tac `F` \\ rw []
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def] \\ rw []
QED

Theorem decreases_gas_memory_expansion_info[simp]:
  decreases_gas F (memory_expansion_info offset sz)
Proof
  rw [memory_expansion_info_def]
  \\ irule decreases_gas_bind_mono
  \\ irule_at Any decreases_gas_get_current_context
  \\ rw []
  \\ qexists_tac `F` \\ rw [decreases_gas_return]
QED

Theorem decreases_gas_expand_memory[simp]:
  decreases_gas F (expand_memory expand_by)
Proof
  rw [expand_memory_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def] \\ rw []
QED

Theorem decreases_gas_get_static[simp]:
  decreases_gas F get_static
Proof
  rw [get_static_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_assert_not_static[simp]:
  decreases_gas F assert_not_static
Proof
  rw [assert_not_static_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_static \\ rw []
QED

Theorem decreases_gas_get_callee[simp]:
  decreases_gas F get_callee
Proof
  rw [get_callee_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_read_memory[simp]:
  decreases_gas F (read_memory off sz)
Proof
  rw [read_memory_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_push_logs[simp]:
  decreases_gas F (push_logs logs)
Proof
  rw [push_logs_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def] \\ rw []
QED

Theorem decreases_gas_step_log[simp]:
  decreases_gas T (step_log n)
Proof
  rw [step_log_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ qexists_tac `F` \\ irule decreases_gas_ignore_bind_false
  \\ CONJ_TAC >- irule_at Any decreases_gas_expand_memory
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_assert_not_static
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_callee \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_read_memory \\ rw []
QED

Theorem decreases_gas_inc_pc_or_jump[simp]:
  decreases_gas F (inc_pc_or_jump op)
Proof
  rw [inc_pc_or_jump_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
  \\ CASE_TAC
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_reraise[simp]:
  decreases_gas b (reraise e)
Proof
  rw [decreases_gas_def, reraise_def]
QED

Theorem decreases_gas_get_gas_left[simp]:
  decreases_gas F get_gas_left
Proof
  rw [get_gas_left_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_set_return_data[simp]:
  decreases_gas F (set_return_data data)
Proof
  rw [set_return_data_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_get_num_contexts[simp]:
  decreases_gas F get_num_contexts
Proof
  rw [decreases_gas_def, get_num_contexts_def, return_def]
QED

Theorem decreases_gas_get_return_data[simp]:
  decreases_gas F get_return_data
Proof
  rw [get_return_data_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_get_output_to[simp]:
  decreases_gas F get_output_to
Proof
  rw [get_output_to_def]
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Definition unused_gas_def:
  unused_gas ctxs = SUM (MAP (λc. c.msgParams.gasLimit - c.gasUsed) ctxs)
End

Definition ok_state_def:
  ok_state s ⇔
      (∀c. c ∈ set s.contexts ⇒ c.gasUsed ≤ c.msgParams.gasLimit) ∧
      s.contexts ≠ []
End

Definition contexts_weight_def:
  contexts_weight c = (LENGTH c, unused_gas c)
End

Definition decreases_gas'_def:
  decreases_gas' b (m: execution_state -> α execution_result) =
    ∀s. ok_state s
      ⇒ ok_state (SND (m s)) ∧
      let (p,q) = (contexts_weight (SND (m s)).contexts,
                   contexts_weight s.contexts) in
      if b ∧ ISL (FST (m s))
      then ($< LEX $<) p q
      else ¬(($< LEX $<) q p)
End

Theorem transitive_LEX_LESS =
  CONJ transitive_LESS transitive_LESS
  |> MATCH_MP transitive_LEX
  |> REWRITE_RULE[transitive_def]

Theorem transitive_LE_LEX_LT:
   ¬($< LEX $<) y x ∧ ($< LEX $<) y z ⇒ ($< LEX $<) (x:num # num) z
Proof
  Cases_on`x` \\ Cases_on`y` \\ Cases_on`z`
  \\ rw[LEX_DEF]
QED

Theorem transitive_LT_LEX_LE:
   ($< LEX $<) x y ∧ ¬($< LEX $<) z y ⇒ ($< LEX $<) (x:num # num) z
Proof
  Cases_on`x` \\ Cases_on`y` \\ Cases_on`z`
  \\ rw[LEX_DEF]
QED

Theorem transitive_LE_LEX_LE:
   ¬($< LEX $<) y x ∧ ¬($< LEX $<) z y ⇒ ¬($< LEX $<) (z:num # num) x
Proof
  Cases_on`x` \\ Cases_on`y` \\ Cases_on`z`
  \\ rw[LEX_DEF]
QED

Theorem LEX_LT_IMP_LE:
  ($< LEX $<) x y ⇒ ¬($< LEX $<) y (x:num # num)
Proof
  Cases_on`x` \\ Cases_on`y` \\ rw[LEX_DEF]
QED

val lexs = [transitive_LEX_LESS, transitive_LE_LEX_LT,
            transitive_LT_LEX_LE, transitive_LE_LEX_LE,
            LEX_LT_IMP_LE]

Theorem decreases_gas'_handle[simp]:
  decreases_gas' T f ∧ (∀e. decreases_gas' T (h e)) ⇒
  decreases_gas' T (handle f h)
Proof
  simp [decreases_gas'_def, handle_def] \\ ntac 3 strip_tac
  \\ CASE_TAC \\ CASE_TAC >- (last_x_assum drule \\ rw [])
  \\ last_x_assum drule \\ simp [] \\ strip_tac
  \\ last_x_assum (drule_then (qspec_then`y`mp_tac)) \\ rw[]
  \\ metis_tac lexs
QED

Theorem decreases_gas'_true_false:
  decreases_gas' T m ⇒ decreases_gas' F m
Proof
  simp [decreases_gas'_def] \\ metis_tac lexs
QED

Theorem decreases_gas'_true:
  decreases_gas' T m ⇒ decreases_gas' b m
Proof
  Cases_on `b` \\ simp [decreases_gas'_true_false]
QED

Theorem decreases_gas'_mono:
  (b' ⇒ b) ∧ decreases_gas' b m ⇒ decreases_gas' b' m
Proof
  Cases_on `b'` \\ Cases_on `b` \\ simp [decreases_gas'_true_false]
QED

Theorem decreases_gas'_bind:
  decreases_gas' bg g ∧ (∀x. decreases_gas' bf (f x)) ⇒
  decreases_gas' (bf ∨ bg) (bind g f)
Proof
  simp [decreases_gas'_def, bind_def]
  \\ ntac 3 strip_tac
  \\ CASE_TAC
  \\ last_x_assum drule \\ simp[]
  \\ strip_tac
  \\ CASE_TAC \\ simp[]
  >- (
    last_x_assum (drule_then(qspec_then`x`mp_tac))
    \\ qhdtm_x_assum `COND` mp_tac \\ rw []
    \\ metis_tac (NOT_ISR_ISL::lexs) )
  \\ qhdtm_x_assum `COND` mp_tac \\ rw []
QED

Theorem decreases_gas'_bind_mono:
  decreases_gas' bg g ∧ (∀x. decreases_gas' bf (f x)) ∧
  (bgf ⇒ bf ∨ bg) ⇒
  decreases_gas' bgf (bind g f)
Proof
  rw [] \\ drule_then drule decreases_gas'_bind \\ strip_tac
  \\ irule decreases_gas'_mono \\ goal_assum drule \\ rw []
QED

Theorem decreases_gas'_bind_right:
  decreases_gas' bg g ∧ (∀x. decreases_gas' bf (f x)) ⇒
  decreases_gas' bf (bind g f)
Proof
  rw [] \\ irule decreases_gas'_bind_mono \\ metis_tac []
QED

Theorem decreases_gas'_bind_false:
  decreases_gas' bg g ∧ (∀x. decreases_gas' F (f x)) ⇒
  decreases_gas' bg (bind g f)
Proof
  rw [] \\ irule decreases_gas'_bind_mono \\ metis_tac []
QED

Theorem decreases_gas'_ignore_bind_mono:
  decreases_gas' bg g ∧ decreases_gas' bf f ∧
  (bgf ⇒ bf ∨ bg) ⇒
  decreases_gas' bgf (ignore_bind g f)
Proof
  rw [ignore_bind_def] \\ irule decreases_gas'_bind_mono \\ metis_tac []
QED

Theorem decreases_gas'_ignore_bind:
  decreases_gas' bg g ∧ decreases_gas' bf f ⇒
  decreases_gas' (bf ∨ bg) (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas'_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas'_ignore_bind_false:
  decreases_gas' bg g ∧ decreases_gas' bf f ⇒
  decreases_gas' F (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas'_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_imp[simp]:
  decreases_gas b m ⇒ decreases_gas' b m
Proof
  simp[decreases_gas_def, decreases_gas'_def]
  \\ strip_tac
  \\ gen_tac
  \\ strip_tac
  \\ Cases_on`s.contexts` >- gs[ok_state_def]
  \\ first_x_assum drule
  \\ impl_tac >- (fs[ok_state_def] \\ metis_tac[])
  \\ strip_tac
  \\ conj_asm1_tac >- ( gvs[ok_state_def] \\ metis_tac[] )
  \\ qmatch_goalsub_abbrev_tac`COND bb`
  \\ qhdtm_x_assum`COND`mp_tac
  \\ gvs[ok_state_def]
  \\ simp[contexts_weight_def, LEX_DEF]
  \\ rw[unused_gas_def]
QED

Theorem return_bind[simp]:
  bind (return x) f = f x
Proof
  rw[bind_def, return_def, FUN_EQ_THM]
QED

Theorem return_ignore_bind[simp]:
  ignore_bind (return x) f = f
Proof
  rw[ignore_bind_def, return_def]
QED

Theorem bind_assoc[simp]:
  bind (bind x f) g =
  bind x (λa. bind (f a) g)
Proof
  rw[bind_def, FUN_EQ_THM]
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
QED

Theorem decreases_gas_finish[simp]:
  decreases_gas T finish
Proof
  rw [decreases_gas_def, finish_def]
QED

Theorem decreases_gas_revert[simp]:
  decreases_gas T revert
Proof
  rw [decreases_gas_def, revert_def]
QED

Theorem decreases_gas_access_address[simp]:
  decreases_gas F (access_address a)
Proof
  rw [access_address_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def,
    cold_access_cost_def, warm_access_cost_def]
QED

Theorem decreases_gas_access_address_bind:
  (∀x. 0 < x ⇒ decreases_gas sf (f x)) ⇒
  decreases_gas sf (monad_bind (access_address a) f)
Proof
  strip_tac \\ irule decreases_gas_mono
  \\ irule_at Any decreases_gas_bind_pred
  \\ qexistsl_tac [`F`,`sf`,`λx. 0 < x`] \\ simp []
  \\ rw [access_address_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def,
    cold_access_cost_def, warm_access_cost_def]
QED

Theorem decreases_gas_get_accounts[simp]:
  decreases_gas F get_accounts
Proof
  rw [get_accounts_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas'_bind_pred:
  decreases_gas' sg g ∧
  (∀s a. FST (g s) = INL a ⇒ p a) ∧
  (∀x. p x ⇒ decreases_gas' sf (f x)) ⇒
  decreases_gas' (sf ∨ sg) (monad_bind g f)
Proof
  rw [decreases_gas'_def, bind_def]
  \\ last_x_assum drule \\ rw []
  \\ CASE_TAC \\ CASE_TAC \\ gvs []
  \\ last_x_assum (qspecl_then [`s`,`x`] mp_tac) \\ rw []
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum (drule_then mp_tac) \\ rw []
  \\ metis_tac lexs
QED

Theorem decreases_gas'_access_address_bind:
  (∀x. 0 < x ⇒ decreases_gas' sf (f x)) ⇒
  decreases_gas' sf (monad_bind (access_address a) f)
Proof
  strip_tac \\ irule decreases_gas'_mono
  \\ irule_at Any decreases_gas'_bind_pred
  \\ qexistsl_tac [`F`,`sf`,`λx. 0 < x`] \\ simp []
  \\ rw [access_address_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def,
    cold_access_cost_def, warm_access_cost_def]
QED

Theorem decreases_gas'_consume_gas_bind[simp]:
  0 < n ∧ decreases_gas' sf f ⇒
  decreases_gas' T (do consume_gas n; f od)
Proof
  rw [] \\ irule decreases_gas'_ignore_bind_mono
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_consume_gas
  \\ metis_tac []
QED

Theorem decreases_gas'_step_call[simp]:
  decreases_gas' T (step_call op)
Proof
  simp [step_call_def]
  \\ qmatch_goalsub_abbrev_tac`pop_stack (n + _)`
  \\ irule_at Any decreases_gas'_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_pop_stack
  \\ simp[] \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`max_expansion_range p1 p2`
  \\ Cases_on`max_expansion_range p1 p2` \\ simp[]
  \\ irule_at Any decreases_gas'_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_memory_expansion_info
  \\ simp[] \\ gen_tac
  \\ irule_at Any decreases_gas'_access_address_bind
  \\ simp[] \\ gen_tac \\ strip_tac
  \\ irule_at Any decreases_gas'_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_get_accounts
  \\ simp[] \\ gen_tac
  \\ irule_at Any decreases_gas'_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_get_gas_left
  \\ simp[] \\ gen_tac
  \\ qmatch_goalsub_abbrev_tac`call_gas v g l m e`
  \\ Cases_on`call_gas v g l m e` \\ simp[]
  \\ irule_at Any decreases_gas'_consume_gas_bind
  \\ conj_tac >- ( gvs[call_gas_def] \\ rw[Abbr`e`] )
  \\ qexists_tac`F`
  \\ irule_at Any decreases_gas'_ignore_bind_false
  \\ conj_tac
  >- (
    irule_at Any decreases_gas_imp
    \\ rw[]
    >- irule_at Any decreases_gas_assert_not_static
    \\ irule_at Any decreases_gas_return )
  \\ irule_at Any decreases_gas'_ignore_bind_false
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_expand_memory
  \\ irule_at Any decreases_gas'_bind_false
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_get_callee
  \\ simp[] \\ gen_tac
  \\ cheat
QED

Theorem decreases_gas_step_binop[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_binop op f)
Proof
  rw [step_binop_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule_at Any decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_push_stack
QED

Theorem decreases_gas_step_modop[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_modop op f)
Proof
  rw [step_modop_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ simp [] \\ gen_tac
  \\ irule_at Any decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_push_stack
QED

Theorem decreases_gas_step_monop[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_monop op f)
Proof
  rw [step_monop_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule_at Any decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_push_stack
QED

Theorem decreases_gas_bind_right_pred:
  decreases_gas F g ∧
  (∀s a. FST (g s) = INL a ⇒ p a) ∧
  (∀x. p x ⇒ decreases_gas sf (f x)) ⇒
  decreases_gas sf (monad_bind g f)
Proof
  rw [decreases_gas_def, bind_def]
  \\ CASE_TAC \\ reverse CASE_TAC \\ rw []
  >- (first_x_assum drule \\ rw [])
  \\ first_x_assum (qspecl_then [`s`, `x`] mp_tac) \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ last_x_assum drule \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ first_assum (irule_at Any)
  \\ qhdtm_x_assum `COND` mp_tac \\ rw []
QED

Theorem decreases_gas_step_balance[simp]:
  decreases_gas T step_balance
Proof
  rw [step_balance_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ simp [] \\ gen_tac
  \\ irule decreases_gas_access_address_bind \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_accounts \\ rw []
QED

Theorem decreases_gas_step_context[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_context op f)
Proof
  rw [step_context_def]
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_step_msgParams[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_msgParams op f)
Proof
  rw [step_msgParams_def]
QED

Theorem decreases_gas_get_tx_params[simp]:
  decreases_gas F get_tx_params
Proof
  rw [get_tx_params_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_step_txParams[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_txParams op f)
Proof
  rw [step_txParams_def]
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_tx_params \\ rw []
QED

Theorem decreases_gas_step_keccak256[simp]:
  decreases_gas T step_keccak256
Proof
  rw [step_keccak256_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_expand_memory
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_read_memory \\ rw []
QED

Theorem decreases_gas_step_exp[simp]:
  decreases_gas T step_exp
Proof
  rw [step_exp_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_push_stack
QED

Theorem decreases_gas_get_call_data[simp]:
  decreases_gas F get_call_data
Proof
  rw [get_call_data_def]
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_step_call_data_load[simp]:
  decreases_gas T step_call_data_load
Proof
  rw [step_call_data_load_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_call_data \\ rw []
QED

Theorem decreases_gas_write_memory[simp]:
  decreases_gas F (write_memory byteIndex bytes)
Proof
  rw [write_memory_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_copy_to_memory[simp]:
  0 < gas ∧ (case getSource of SOME f => decreases_gas F f | _ => T) ⇒
  decreases_gas T (copy_to_memory gas offset sourceOffset sz getSource)
Proof
  simp [copy_to_memory_def]
  \\ qpat_abbrev_tac `x = COND a b c` \\ Cases_on `x` \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule_at Any decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false \\ rw []
  \\ pop_assum mp_tac \\ CASE_TAC \\ rw []
  >- (irule_at Any decreases_gas_ignore_bind_false
    \\ irule_at Any decreases_gas_expand_memory
    \\ irule_at Any decreases_gas_read_memory \\ rw [])
  \\ irule_at Any decreases_gas_bind_false
  \\ first_x_assum (irule_at Any) \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_expand_memory
  \\ irule_at Any decreases_gas_return
QED

Theorem decreases_gas_step_copy_to_memory[simp]:
  0 < static_gas op ∧ (case getSource of SOME f => decreases_gas F f | _ => T) ⇒
  decreases_gas T (step_copy_to_memory op getSource)
Proof
  rw [step_copy_to_memory_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule_at Any decreases_gas_copy_to_memory \\ rw []
QED

Theorem decreases_gas_step_ext_code_size[simp]:
  decreases_gas T step_ext_code_size
Proof
  rw [step_ext_code_size_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_access_address_bind \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_accounts \\ rw []
QED

Theorem decreases_gas_get_code[simp]:
  decreases_gas F (get_code a)
Proof
  rw [get_code_def]
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_accounts \\ rw []
QED

Theorem decreases_gas_step_ext_code_copy[simp]:
  decreases_gas T step_ext_code_copy
Proof
  rw [step_ext_code_copy_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_access_address_bind \\ rw []
  \\ irule decreases_gas_copy_to_memory \\ rw []
  \\ irule decreases_gas_get_code
QED

Theorem decreases_gas_get_return_data[simp]:
  decreases_gas F get_return_data
Proof
  rw [get_return_data_def]
QED

Theorem decreases_gas_get_return_data_check[simp]:
  decreases_gas F (get_return_data_check off sz)
Proof
  rw [get_return_data_check_def]
  \\ irule_at Any decreases_gas_bind_false \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right \\ rw []
  \\ irule_at Any decreases_gas_assert
QED

Theorem decreases_gas_step_return_data_copy[simp]:
  decreases_gas T step_return_data_copy
Proof
  rw [step_return_data_copy_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
QED

Theorem decreases_gas_step_ext_code_hash[simp]:
  decreases_gas T step_ext_code_hash
Proof
  rw [step_ext_code_hash_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_access_address_bind \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_accounts \\ rw []
QED

Theorem decreases_gas_step_block_hash[simp]:
  decreases_gas T step_block_hash
Proof
  rw [step_block_hash_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_tx_params \\ rw []
QED

Theorem decreases_gas_step_self_balance[simp]:
  decreases_gas T step_self_balance
Proof
  rw [step_self_balance_def]
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_accounts \\ rw []
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_callee \\ rw []
QED

Theorem decreases_gas_step_mload[simp]:
  decreases_gas T step_mload
Proof
  rw [step_mload_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_bind_false \\ rw []
  \\ irule_at Any decreases_gas_read_memory
  \\ irule_at Any decreases_gas_expand_memory \\ rw []
QED

Theorem decreases_gas_step_mstore[simp]:
  0 < static_gas op ⇒ decreases_gas T (step_mstore op)
Proof
  strip_tac \\ simp [step_mstore_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ simp [] \\ gen_tac
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_memory_expansion_info \\ simp [] \\ gen_tac
  \\ irule decreases_gas_consume_gas_bind \\ simp []
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_expand_memory
  \\ irule_at Any decreases_gas_write_memory
QED

Theorem decreases_gas_access_slot[simp]:
  decreases_gas F (access_slot x)
Proof
  rw [access_slot_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_access_slot[simp]:
  decreases_gas F (access_slot x)
Proof
  rw [access_slot_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_get_tStorage[simp]:
  decreases_gas F get_tStorage
Proof
  rw [get_tStorage_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_step_sload[simp]:
  decreases_gas T (step_sload transient)
Proof
  rw [step_sload_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_callee \\ simp [] \\ gen_tac
  \\ irule decreases_gas_mono
  \\ irule_at Any decreases_gas_bind_pred
  \\ qexistsl_tac [`F`,`T`,`λx. 0 < x`]
  \\ rw [return_def, warm_access_cost_def]
  >- (pop_assum mp_tac \\
    rw [access_slot_def, return_def,
      cold_sload_cost_def, warm_access_cost_def])
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_false \\ rw []
  >- irule_at Any decreases_gas_get_tStorage
  >- irule_at Any decreases_gas_get_accounts
QED

Theorem decreases_gas_set_tStorage[simp]:
  decreases_gas F (set_tStorage x)
Proof
  rw [set_tStorage_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_write_transient_storage[simp]:
  decreases_gas F (write_transient_storage address key value)
Proof
  rw [write_transient_storage_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_tStorage \\ rw []
QED

Theorem decreases_gas_get_gas_left[simp]:
  decreases_gas F get_gas_left
Proof
  rw [get_gas_left_def]
QED

Theorem decreases_gas_get_original[simp]:
  decreases_gas F get_original
Proof
  rw [get_original_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_update_gas_refund[simp]:
  decreases_gas F (update_gas_refund p)
Proof
  Cases_on `p` \\ rw [update_gas_refund_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_step_sstore_gas_consumption[simp]:
  decreases_gas T (step_sstore_gas_consumption address key value)
Proof
  rw [step_sstore_gas_consumption_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_gas_left \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_assert \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_accounts \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_original \\ simp [] \\ gen_tac
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_access_slot \\ simp [] \\ gen_tac
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_update_gas_refund
  \\ irule_at Any decreases_gas_mono
  \\ irule_at Any decreases_gas_consume_gas
  \\ rw [warm_access_cost_def, storage_update_cost_def,
    cold_sload_cost_def, storage_set_cost_def]
QED

Theorem decreases_gas_update_accounts[simp]:
  decreases_gas F (update_accounts f)
Proof
  rw[decreases_gas_def, update_accounts_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_write_storage[simp]:
  decreases_gas F (write_storage address key value)
Proof
  rw [write_storage_def]
  \\ irule_at Any decreases_gas_update_accounts
QED

Theorem decreases_gas_step_sstore[simp]:
  decreases_gas T (step_sstore transient)
Proof
  rw [step_sstore_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_callee \\ rw []
  >- (
    irule decreases_gas_consume_gas_bind \\ rw [warm_access_cost_def]
    \\ irule_at Any decreases_gas_ignore_bind_false
    \\ irule_at Any decreases_gas_assert_not_static
    \\ irule_at Any decreases_gas_write_transient_storage)
  \\ irule_at Any decreases_gas_ignore_bind_mono
  \\ irule_at Any decreases_gas_step_sstore_gas_consumption
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_assert_not_static
  \\ irule_at Any decreases_gas_write_storage \\ rw []
QED

Theorem decreases_gas_set_jump_dest[simp]:
  decreases_gas F (set_jump_dest dest)
Proof
  rw [set_jump_dest_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_step_jump[simp]:
  decreases_gas T step_jump
Proof
  rw [step_jump_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_set_jump_dest
QED

Theorem decreases_gas_step_jumpi[simp]:
  decreases_gas T step_jumpi
Proof
  rw [step_jumpi_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule decreases_gas_consume_gas_bind \\ rw []
  \\ irule_at Any decreases_gas_set_jump_dest
QED

Theorem decreases_gas_step_create[simp]:
  decreases_gas T (step_create two)
Proof
  rw [step_create_def]
  \\ cheat
QED

Theorem decreases_gas_step_return[simp]:
  decreases_gas T (step_return b)
Proof
  simp [step_return_def]
  \\ qpat_abbrev_tac `x = COND b a c` \\ qpat_abbrev_tac `y = COND b a c`
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_consume_gas \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_expand_memory \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_read_memory \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_set_return_data \\ rw [Abbr`y`]
QED

Theorem decreases_gas_step_invalid[simp]:
  decreases_gas T step_invalid
Proof
  rw [step_invalid_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_gas_left \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_consume_gas \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_set_return_data \\ rw []
QED

Theorem decreases_gas_set_accounts[simp]:
  decreases_gas F (set_accounts x)
Proof
  rw [set_accounts_def]
QED

Theorem decreases_gas_add_to_delete[simp]:
  decreases_gas F (add_to_delete a)
Proof
  rw [add_to_delete_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_step_self_destruct[simp]:
  decreases_gas T step_self_destruct
Proof
  rw [step_self_destruct_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_pop_stack \\ rw []
  \\ irule_at Any decreases_gas_access_address_bind \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_callee \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_accounts \\ simp [] \\ gen_tac
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_consume_gas \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_assert_not_static \\ rw []
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_set_accounts \\ rw []
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_original \\ simp [] \\ gen_tac
  \\ irule_at Any decreases_gas_ignore_bind_right \\ reverse (rw [])
  >- irule_at Any decreases_gas_return
  \\ irule_at Any decreases_gas_ignore_bind_right
  \\ irule_at Any decreases_gas_update_accounts \\ rw []
  \\ irule_at Any decreases_gas_add_to_delete
QED

Theorem decreases_gas_get_current_code[simp]:
  decreases_gas F get_current_code
Proof
  rw [get_current_code_def]
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas'_step_inst[simp]:
  decreases_gas' T (step_inst inst)
Proof
  Cases_on `inst` \\ rw [step_inst_def]
  \\ irule decreases_gas_imp
  >- (irule decreases_gas_ignore_bind_right \\ rw []
    \\ irule_at Any decreases_gas_set_return_data)
  >- (irule decreases_gas_mono
    \\ irule_at Any decreases_gas_consume_gas \\ rw [])
QED

Definition pop_helper_def:
  pop_helper = do
    n <- get_num_contexts;
    assert (1 < n) Impossible;
    calleeGasLeft <- get_gas_left;
    callee <- pop_context;
    unuse_gas calleeGasLeft;
    return callee
  od
End

Definition after_pop_def:
  after_pop output outputTo success = do
        inc_pc;
        case outputTo of
          Memory r =>
            do
              set_return_data output;
              push_stack (b2w success);
              write_memory r.offset (TAKE r.size output)
            od
        | Code address =>
          if success then
            do set_return_data []; push_stack (w2w address) od
          else do set_return_data output; push_stack 0w od
  od
End

Definition handle_ex_helper_def:
  handle_ex_helper e = do
    n <- get_num_contexts;
    if n ≤ 1 then reraise e
    else
      do
        output <- get_return_data;
        outputTo <- get_output_to;
        pop_and_incorporate_context (e = NONE);
        after_pop output outputTo (e = NONE)
      od
    od
End

Theorem handle_ex_helper_thm:
  handle_ex_helper e = do
    n <- get_num_contexts;
    if n ≤ 1 then reraise e
    else
      do
        output <- get_return_data;
        outputTo <- get_output_to;
        callee <- pop_helper;
        if (e = NONE) then
          do
            push_logs callee.logs;
            update_gas_refund (callee.addRefund,callee.subRefund)
          od
        else set_rollback callee.rollback;
        after_pop output outputTo (e = NONE)
      od
    od
Proof
  rw[handle_ex_helper_def, FUN_EQ_THM, ignore_bind_def,
     pop_and_incorporate_context_def, pop_helper_def]
  \\ rw[get_num_contexts_def, get_return_data_def, get_output_to_def,
        assert_def, bind_def, return_def, get_current_context_def]
  \\ IF_CASES_TAC \\ gvs[]
QED

Theorem decreases_gas_update_gas_refund[simp]:
  decreases_gas F (update_gas_refund p)
Proof
  Cases_on`p` \\ rw[update_gas_refund_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_inc_pc[simp]:
  decreases_gas F inc_pc
Proof
  rw[inc_pc_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_write_memory[simp]:
  decreases_gas F (write_memory a b)
Proof
  rw[write_memory_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_set_rollback[simp]:
  decreases_gas F (set_rollback b)
Proof
  rw[set_rollback_def, decreases_gas_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
QED

Theorem decreases_gas_after_pop[simp]:
  decreases_gas F (after_pop a b c)
Proof
  rw[after_pop_def]
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_inc_pc
  \\ CASE_TAC
  \\ (
    reverse CASE_TAC
    \\ irule_at Any decreases_gas_ignore_bind_false
    \\ irule_at Any decreases_gas_set_return_data
    >- (irule_at Any decreases_gas_push_stack)
    \\ irule_at Any decreases_gas_ignore_bind_false
    \\ irule_at Any decreases_gas_push_stack
    \\ irule_at Any decreases_gas_write_memory)
QED

Theorem decreases_gas_step[simp]:
  decreases_gas' T step
Proof
  rw [step_def]
  \\ irule decreases_gas'_handle
  \\ CONJ_TAC >- (
    rw [handle_step_def]
    \\ irule decreases_gas'_handle
    \\ CONJ_TAC >- (
      simp [handle_exception_def] \\ strip_tac
      \\ irule decreases_gas'_ignore_bind_mono
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `F`
      \\ simp []
      \\ CONJ_TAC >- (rw []
        \\ irule decreases_gas_imp
        \\ irule decreases_gas_bind_right
        \\ irule_at Any decreases_gas_get_gas_left \\ rw []
        \\ irule decreases_gas_ignore_bind_mono
        \\ irule_at Any decreases_gas_consume_gas \\ rw []
        \\ irule_at Any decreases_gas_set_return_data)
      \\ simp[GSYM after_pop_def, GSYM handle_ex_helper_def]
      \\ simp[handle_ex_helper_thm]
      \\ irule decreases_gas'_bind_right \\ irule_at Any decreases_gas_imp
      \\ irule_at Any decreases_gas_get_num_contexts \\ rw []
      \\ irule decreases_gas'_bind_right \\ irule_at Any decreases_gas_imp
      \\ irule_at Any decreases_gas_get_return_data \\ rw []
      \\ irule decreases_gas'_bind_right \\ irule_at Any decreases_gas_imp
      \\ irule_at Any decreases_gas_get_output_to \\ rw []
      \\ irule_at Any decreases_gas'_bind_mono
      \\ qexistsl_tac[`F`,`T`]
      \\ simp[]
      \\ conj_tac >- (
        rw[] >- (
          irule decreases_gas_imp
          \\ irule decreases_gas_ignore_bind_false
          \\ conj_tac
          >- (
            qexists_tac`F`
            \\ irule decreases_gas_ignore_bind_false
            \\ conj_tac
            >- ( qexists_tac`F` \\ irule decreases_gas_push_logs)
            \\ qexists_tac`F` \\ irule decreases_gas_update_gas_refund
          )
          \\ irule_at Any decreases_gas_after_pop
        )
        \\ irule decreases_gas_imp
        \\ irule_at Any decreases_gas_ignore_bind_false
        \\ irule_at Any decreases_gas_set_rollback
        \\ irule_at Any decreases_gas_after_pop
      )
      \\ rw[pop_helper_def]
      \\ simp[bind_def, decreases_gas'_def, get_gas_left_def,
              get_current_context_def, return_def, pop_context_def,
              unuse_gas_def, ignore_bind_def, fail_def, assert_def,
              set_current_context_def, ok_state_def, get_num_contexts_def,
              assert_def]
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC \\ simp[]
      >- metis_tac lexs
      \\ Cases_on`s.contexts` \\ gvs[]
      \\ Cases_on`t` \\ gvs[]
      \\ rw[] \\ rw[] \\ fsrw_tac[DNF_ss][]
      >- decide_tac
      \\ gvs[contexts_weight_def, LEX_DEF]
    )
    \\ simp [handle_create_def]
    \\ irule decreases_gas_imp
    \\ irule_at Any decreases_gas_bind_right
    \\ irule_at Any decreases_gas_get_return_data \\ rw[]
    \\ irule_at Any decreases_gas_bind_right
    \\ irule_at Any decreases_gas_get_output_to \\ rw[]
    \\ BasicProvers.TOP_CASE_TAC \\ rw[]
    \\ BasicProvers.TOP_CASE_TAC \\ rw[]
    \\ irule_at Any decreases_gas_ignore_bind_mono
    \\ qexistsl_tac[`T`,`F`] \\ simp[]
    \\ irule_at Any decreases_gas_ignore_bind_mono
    \\ irule_at Any decreases_gas_consume_gas
    \\ qexists_tac`T` \\ simp[]
    \\ irule_at Any decreases_gas_ignore_bind_mono
    \\ irule_at Any decreases_gas_ignore_bind
    \\ irule_at Any decreases_gas_reraise
    \\ irule_at Any decreases_gas_assert
    \\ irule_at Any decreases_gas_update_accounts
    \\ rw[]
  )
  \\ irule decreases_gas'_bind_right
  \\ reverse conj_tac
  >- (
    irule_at Any decreases_gas_imp
    \\ irule_at Any decreases_gas_get_current_context  )
  \\ rw[]
  \\ CASE_TAC >- rw[]
  \\ irule_at Any decreases_gas'_ignore_bind_mono
  \\ irule_at Any decreases_gas'_step_inst
  \\ rw[]
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_inc_pc_or_jump
QED

val () = export_theory();
