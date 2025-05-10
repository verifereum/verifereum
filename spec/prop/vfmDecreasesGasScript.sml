open HolKernel boolLib bossLib Parse BasicProvers
     pairTheory sumTheory listTheory relationTheory arithmeticTheory
     vfmConstantsTheory vfmContextTheory vfmStateTheory
     vfmExecutionTheory vfmExecutionPropTheory;

val () = new_theory "vfmDecreasesGas";

Definition decreases_gas_def:
  decreases_gas strict (m: α execution) =
    ∀s. case s.contexts of
      [] => (SND (m s)).contexts = []
    | (c,r)::crs =>
      ∃c' r'.
        (SND (m s)).contexts = (c',r')::crs ∧
        c'.msgParams.gasLimit = c.msgParams.gasLimit ∧
        (c.gasUsed < c'.gasUsed ⇒ c'.gasUsed ≤ c'.msgParams.gasLimit) ∧
        (wf_context c ⇒ wf_context c') ∧
        if strict ∧ ISL (FST (m s))
        then c.gasUsed < c'.gasUsed
        else c.gasUsed ≤ c'.gasUsed
End

Theorem decreases_gas_mono:
  (s' ⇒ s) ∧
  decreases_gas s m ⇒ decreases_gas s' m
Proof
  rw [decreases_gas_def] \\ pop_assum (qspec_then `s''` mp_tac)
  \\ Cases_on `s''.contexts` \\ rw []
  \\ BasicProvers.TOP_CASE_TAC \\ gs[]
  \\ qhdtm_x_assum`COND`mp_tac
  \\ rw[] \\ gs[]
  \\ metis_tac[NOT_ISR_ISL]
QED

Theorem decreases_gas_return[simp]:
  decreases_gas F (return a)
Proof
  simp [decreases_gas_def, return_def] \\ gen_tac
  \\ CASE_TAC \\ rw []
  \\ CASE_TAC \\ rw []
QED

Theorem decreases_gas_bind_pred:
  decreases_gas sg g ∧
  (∀s a. FST (g s) = INL a ⇒ p a) ∧
  (∀x. p x ⇒ decreases_gas sf (f x)) ⇒
  decreases_gas (sf ∨ sg) (monad_bind g f)
Proof
  rw [decreases_gas_def, bind_def]
  \\ ntac 2 (last_x_assum (qspec_then `s` mp_tac))
  \\ Cases_on `g s` \\ Cases_on `q` \\ gvs [] \\ strip_tac
  \\ first_x_assum (drule_then (qspec_then `r` mp_tac))
  \\ Cases_on `s.contexts` \\ rw [] \\ gvs []
  \\ BasicProvers.TOP_CASE_TAC \\ gvs[]
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
  rw [decreases_gas_def, get_current_context_def, return_def]
  \\ Cases_on `s.contexts` \\ rw [fail_def]
  \\ BasicProvers.TOP_CASE_TAC \\ gs[]
QED

Theorem decreases_gas_assert[simp]:
  decreases_gas F (assert b e)
Proof
  rw [decreases_gas_def, assert_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ BasicProvers.TOP_CASE_TAC \\ gs[]
QED

Theorem decreases_gas_consume_gas:
  decreases_gas (0 < n) (consume_gas n)
Proof
  rw [decreases_gas_def, consume_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ gs[wf_context_def]
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ gs[wf_context_def]
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ gs[wf_context_def]
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ gs[wf_context_def, LENGTH_TAKE_EQ] \\ rw[]
  \\ qmatch_goalsub_rename_tac`h.stack`
  \\ Cases_on`h.stack` \\ gs[]
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ gs[wf_context_def]
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ gs[wf_context_def]
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC
  \\ CASE_TAC
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
  \\ gs[wf_context_def]
QED

Theorem decreases_gas_reraise[simp]:
  decreases_gas b (reraise e)
Proof
  rw [decreases_gas_def, reraise_def]
  \\ Cases_on `s.contexts`
  \\ CASE_TAC \\ TOP_CASE_TAC \\ rw []
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
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ rw []
  \\ TOP_CASE_TAC \\ gs[wf_context_def]
QED

Theorem decreases_gas_get_num_contexts[simp]:
  decreases_gas F get_num_contexts
Proof
  rw [decreases_gas_def, get_num_contexts_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ CASE_TAC \\ TOP_CASE_TAC \\ rw []
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

Definition contexts_weight_def:
  contexts_weight n c = (unused_gas (MAP FST c) + n, LENGTH c)
End

Definition decreases_gas_cred_def:
  decreases_gas_cred b n0 n1 (m: execution_state -> α execution_result) =
    ∀s. if s.contexts = []
      then (SND (m s)).contexts = []
      else (SND (m s)).contexts ≠ [] ∧
        (ok_state s ⇒ ok_state (SND (m s))) ∧
        let (p,q) = (contexts_weight n1 (SND (m s)).contexts,
                     contexts_weight n0 s.contexts) in
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

Theorem LE_IMP_contexts_weight_LE:
  m ≤ n ⇒ ¬($< LEX $<) (contexts_weight n c) (contexts_weight m c)
Proof
  rw[LEX_DEF, contexts_weight_def]
QED

Theorem contexts_weight_LT_mono:
  n1 ≤ n2 ∧
  ($< LEX $<) (contexts_weight 0 c1) (contexts_weight 0 c2) ⇒
  ($< LEX $<) (contexts_weight n1 c1) (contexts_weight n2 c2)
Proof
  rw[LEX_DEF, contexts_weight_def]
QED

Theorem contexts_weight_LE_mono:
  n1 ≤ n2 ∧
  ($< LEX $<) (contexts_weight n2 c1) (contexts_weight n1 c2) ⇒
  ($< LEX $<) (contexts_weight 0 c1) (contexts_weight 0 c2)
Proof
  rw[LEX_DEF, contexts_weight_def]
QED

val lexs = [transitive_LEX_LESS, transitive_LE_LEX_LT,
            transitive_LT_LEX_LE, transitive_LE_LEX_LE,
            LEX_LT_IMP_LE,
            contexts_weight_LT_mono, contexts_weight_LE_mono]

Theorem decreases_gas_cred_handle[simp]:
  decreases_gas_cred T 0 0 f ∧ (∀e. decreases_gas_cred T 0 0 (h e)) ⇒
  decreases_gas_cred T 0 0 (handle f h)
Proof
  simp [decreases_gas_cred_def, handle_def] \\ ntac 2 strip_tac
  \\ last_x_assum (qspec_then `s` mp_tac)
  \\ Cases_on `f s` \\ Cases_on `q` \\ simp []
  \\ last_x_assum (qspecl_then [`y`,`r`] mp_tac) \\ simp []
  \\ Cases_on `s.contexts = []` \\ rpt strip_tac \\ gs []
  \\ qhdtm_x_assum `COND` mp_tac \\ IF_CASES_TAC \\ simp []
  \\ metis_tac (lexs)
QED

Theorem decreases_gas_cred_true_false:
  decreases_gas_cred T n0 n1 m ⇒ decreases_gas_cred F n0 n1 m
Proof
  simp [decreases_gas_cred_def] \\ rw [FORALL_AND_THM]
  \\ first_x_assum (qspec_then `s` assume_tac) \\ rw [] \\ metis_tac lexs
QED

Theorem decreases_gas_cred_mono:
  (b' ⇒ b) ∧ decreases_gas_cred b n0 n1 m ⇒ decreases_gas_cred b' n0 n1 m
Proof
  Cases_on `b'` \\ Cases_on `b` \\ simp [decreases_gas_cred_true_false]
QED

Theorem decreases_gas_cred_bind_g:
  (∀s. ISR (FST (g s)) ⇒ n2 ≤ n1) ∧
  (∀s a s'. g s = (INL a, s') ⇒ p a) ∧
  decreases_gas_cred bg n0 n1 g ∧ (∀x. p x ⇒ decreases_gas_cred bf n1 n2 (f x)) ⇒
  decreases_gas_cred (bf ∨ bg) n0 n2 (bind g f)
Proof
  simp [decreases_gas_cred_def, bind_def, UNCURRY] \\ ntac 2 strip_tac
  \\ EVERY_ASSUM (TRY o qspec_then `s` assume_tac)
  \\ CASE_TAC \\ gvs [] \\ CASE_TAC \\ simp []
  >- (
    gvs [] \\ first_x_assum (qspec_then `x` mp_tac) \\ simp []
    \\ disch_then (qspec_then `r` mp_tac) \\ fs []
    \\ Cases_on `s.contexts = []` \\ fs []
    \\ qhdtm_x_assum `COND` mp_tac \\ rw []
    \\ metis_tac (NOT_ISR_ISL::lexs))
  \\ Cases_on `s.contexts = []` \\ gs [] \\ metis_tac lexs
QED

Theorem decreases_gas_cred_bind_pred:
  decreases_gas_cred sg n0 n0 g ∧
  (∀s a. FST (g s) = INL a ⇒ p a) ∧
  (∀x. p x ⇒ decreases_gas_cred sf n0 n0 (f x)) ⇒
  decreases_gas_cred (sf ∨ sg) n0 n0 (monad_bind g f)
Proof
  strip_tac \\ irule decreases_gas_cred_bind_g
  \\ qexistsl_tac [`n0`, `p`] \\ rw [] \\ metis_tac [FST]
QED

Theorem decreases_gas_cred_bind:
  decreases_gas_cred bg n0 n0 g ∧ (∀x. decreases_gas_cred bf n0 n0 (f x)) ⇒
  decreases_gas_cred (bf ∨ bg) n0 n0 (bind g f)
Proof
  strip_tac \\ irule decreases_gas_cred_bind_pred \\ rw []
  \\ qexists_tac `λ_. T` \\ rw []
QED

Theorem decreases_gas_cred_bind_mono:
  decreases_gas_cred bg n0 n0 g ∧ (∀x. decreases_gas_cred bf n0 n0 (f x)) ∧
  (bgf ⇒ bf ∨ bg) ⇒
  decreases_gas_cred bgf n0 n0 (bind g f)
Proof
  rw [] \\ drule_then drule decreases_gas_cred_bind \\ strip_tac
  \\ irule decreases_gas_cred_mono \\ goal_assum drule \\ rw []
QED

Theorem decreases_gas_cred_bind_right:
  decreases_gas_cred bg n0 n0 g ∧ (∀x. decreases_gas_cred bf n0 n0 (f x)) ⇒
  decreases_gas_cred bf n0 n0 (bind g f)
Proof
  rw [] \\ irule decreases_gas_cred_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_cred_bind_false:
  decreases_gas_cred bg n0 n0 g ∧ (∀x. decreases_gas_cred F n0 n0 (f x)) ⇒
  decreases_gas_cred bg n0 n0 (bind g f)
Proof
  rw [] \\ irule decreases_gas_cred_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_cred_ignore_bind_mono:
  decreases_gas_cred bg n0 n0 g ∧ decreases_gas_cred bf n0 n0 f ∧
  (bgf ⇒ bf ∨ bg) ⇒
  decreases_gas_cred bgf n0 n0 (ignore_bind g f)
Proof
  rw [ignore_bind_def] \\ irule decreases_gas_cred_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_cred_ignore_bind:
  decreases_gas_cred bg n0 n0 g ∧ decreases_gas_cred bf n0 n0 f ⇒
  decreases_gas_cred (bf ∨ bg) n0 n0 (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas_cred_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_cred_ignore_bind_false:
  decreases_gas_cred bg n0 n0 g ∧ decreases_gas_cred bf n0 n0 f ⇒
  decreases_gas_cred F n0 n0 (ignore_bind g f)
Proof
  rw [] \\ irule decreases_gas_cred_ignore_bind_mono \\ metis_tac []
QED

Theorem decreases_gas_imp[simp]:
  n1 ≤ n0 ∧ decreases_gas b m ⇒ decreases_gas_cred b n0 n1 m
Proof
  simp [decreases_gas_def, decreases_gas_cred_def] \\ ntac 2 strip_tac
  \\ pop_assum (qspec_then `s` mp_tac)
  \\ Cases_on `s.contexts` \\ gs [] \\ TOP_CASE_TAC \\ strip_tac
  \\ simp [ok_state_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ qhdtm_x_assum `COND` mp_tac
  \\ rw [contexts_weight_def, LEX_DEF, unused_gas_def]
QED

Theorem decreases_gas_revert[simp]:
  decreases_gas T revert
Proof
  rw [decreases_gas_def, revert_def]
  \\ Cases_on `s.contexts` \\ CASE_TAC \\ TOP_CASE_TAC \\ rw []
QED

Theorem decreases_gas_access_address[simp]:
  decreases_gas F (access_address a)
Proof
  rw [access_address_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, domain_check_def, set_domain_def,
    cold_access_cost_def, warm_access_cost_def]
  \\ Cases_on `s.msdomain` \\ gvs[]
  \\ Cases_on `s.contexts` \\ CASE_TAC \\ TOP_CASE_TAC \\ rw [fail_def]
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
    set_current_context_def, domain_check_def, set_domain_def,
    cold_access_cost_def, warm_access_cost_def, fail_def]
  \\ Cases_on `s.msdomain` \\ gvs []
  \\ rpt (pop_assum mp_tac) \\ rw[]
QED

Theorem decreases_gas_get_accounts[simp]:
  decreases_gas F get_accounts
Proof
  rw [get_accounts_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def]
  \\ Cases_on `s.contexts` \\ TOP_CASE_TAC \\ CASE_TAC \\ rw []
QED

Theorem decreases_gas_cred_access_address_bind:
  (∀x. 1 < x ⇒ decreases_gas_cred sf n0 n0 (f x)) ⇒
  decreases_gas_cred sf n0 n0 (monad_bind (access_address a) f)
Proof
  strip_tac \\ irule decreases_gas_cred_mono
  \\ irule_at Any decreases_gas_cred_bind_pred
  \\ qexistsl_tac [`F`,`sf`,`λx. 1 < x`] \\ simp []
  \\ rw [access_address_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def, domain_check_def, set_domain_def,
    cold_access_cost_def, warm_access_cost_def]
  \\ Cases_on `s.msdomain` \\ gvs []
  \\ rpt (pop_assum mp_tac) \\ rw[]
QED

Theorem decreases_gas_cred_consume_gas_debit_more:
  (if b then n0 < n1 + n else n0 ≤ n1 + n) ∧ decreases_gas_cred F n0 0 f ⇒
  decreases_gas_cred b n1 0 (do consume_gas n; f od)
Proof
  simp [decreases_gas_cred_def, consume_gas_def, bind_def, get_current_context_def,
    decreases_gas_cred_def, ok_state_def, ignore_bind_def,
    return_def, assert_def, set_current_context_def, fail_def]
  \\ ntac 2 strip_tac
  \\ qmatch_goalsub_abbrev_tac `f s'`
  \\ first_x_assum (qspec_then `s'` mp_tac) \\ simp [Abbr`s'`]
  \\ Cases_on `s.contexts` \\ gvs []
  \\ reverse CASE_TAC
  >- (
    simp [] \\ strip_tac
    \\ Cases_on`n1 = 0` >- metis_tac lexs
    \\ rw[contexts_weight_def, LEX_DEF] )
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM,
    contexts_weight_def, unused_gas_def]
  \\ qhdtm_x_assum `COND` mp_tac
  \\ qpat_abbrev_tac `v1 = COND a b' c` \\ strip_tac
  \\ rw [] \\ gs[EVERY_MEM]
  \\ gs[wf_context_def]
  \\ qmatch_goalsub_abbrev_tac `f s'`
  \\ qpat_abbrev_tac `n' = SUM (MAP _ (MAP _ t))`
  >- (gs []
    \\ qmatch_goalsub_abbrev_tac`_ rr bb`
    \\ qmatch_asmsub_abbrev_tac`¬(_ aa rr)`
    \\ `($< LEX $<) aa bb` suffices_by metis_tac lexs
    \\ rw [Abbr`aa`,Abbr`bb`,LEX_DEF])
  >- (gs[]
    \\ qmatch_goalsub_abbrev_tac`_ rr bb`
    \\ qmatch_asmsub_abbrev_tac`¬(_ aa bb)`
    \\ `¬($< LEX $<) rr aa` suffices_by metis_tac lexs
    \\ rw[Abbr`rr`,Abbr`aa`, LEX_DEF] )
  >- (qmatch_goalsub_abbrev_tac`_ bb rr`
    \\ qmatch_asmsub_abbrev_tac`_ aa rr`
    \\ `¬($< LEX $<) bb aa` suffices_by metis_tac lexs
    \\ `n0 ≤ n + n1` by (qhdtm_x_assum `COND` mp_tac \\ rw [])
    \\ rw [Abbr`aa`,Abbr`bb`,LEX_DEF])
QED

Theorem decreases_gas_cred_consume_gas_debit[simp]:
  n0 < n ∧ decreases_gas_cred F n0 0 f ⇒
  decreases_gas_cred T 0 0 (do consume_gas n; f od)
Proof
  strip_tac \\ irule decreases_gas_cred_consume_gas_debit_more
  \\ qexists_tac `n0` \\ rw []
QED

Theorem call_gas_stipend_LE:
  (if 0 < v then call_stipend else 0) + 1 < e ∧
  call_gas v g l m e = (q,r) ⇒ e ≤ q ∧ r + 1 < q
Proof
  simp [call_gas_def] \\ qpat_abbrev_tac `x = COND a b c` \\ rw []
QED

Theorem decreases_gas_update_accounts[simp]:
  (* (∀a. wf_accounts a ⇒ wf_accounts (f a)) ∧
  (∀a. no_change_to_code_size a (f a))
  ⇒ *)
  decreases_gas F (update_accounts f)
Proof
  rw[decreases_gas_def, update_accounts_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ CASE_TAC \\ CASE_TAC \\ rw []
QED

Theorem decreases_gas_get_rollback[simp]:
  decreases_gas F get_rollback
Proof
  rw [get_rollback_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ Cases_on `s.contexts` \\ CASE_TAC \\ CASE_TAC \\ rw []
QED

Theorem decreases_gas_get_caller[simp]:
  decreases_gas F get_caller
Proof
  rw [get_caller_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[]
  \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_get_value[simp]:
  decreases_gas F get_value
Proof
  rw [get_value_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_fail[simp]:
  decreases_gas F (fail e)
Proof
  rw[decreases_gas_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_finish[simp]:
  decreases_gas b finish
Proof
  rw[decreases_gas_def, finish_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_get_call_data[simp]:
  decreases_gas F get_call_data
Proof
  rw [get_call_data_def]
  \\ irule_at Any decreases_gas_bind_false
  \\ irule_at Any decreases_gas_get_current_context \\ rw []
QED

Theorem decreases_gas_precompile_identity[simp]:
  decreases_gas F precompile_identity
Proof
  rw[precompile_identity_def]
  \\ irule decreases_gas_bind_false \\ rw[]
  \\ rw[ignore_bind_def]
  \\ irule decreases_gas_bind_false \\ simp[]
  \\ conj_tac
  >- ( irule decreases_gas_bind_false \\ rw[] )
  \\ irule decreases_gas_mono
  \\ irule_at Any decreases_gas_consume_gas
  \\ rw[]
QED

Theorem decreases_gas_precompile_modexp[simp]:
  decreases_gas F precompile_modexp
Proof
  rw[precompile_modexp_def]
  \\ irule decreases_gas_bind_false \\ simp[]
  \\ gen_tac
  \\ qpat_abbrev_tac `v1 = COND a b c`
  \\ qpat_abbrev_tac `v2 = COND a b c`
  \\ rw[ignore_bind_def]
  \\ irule decreases_gas_bind_false \\ simp[]
  \\ conj_tac
  >- ( irule decreases_gas_bind_false \\ rw[] )
  \\ irule decreases_gas_mono
  \\ irule_at Any decreases_gas_consume_gas
  \\ rw[]
QED

Theorem decreases_gas_precompile_sha2_256[simp]:
  decreases_gas F precompile_sha2_256
Proof
  rw[precompile_sha2_256_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_precompile_ecrecover[simp]:
  decreases_gas F precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_precompile_ecadd[simp]:
  decreases_gas F precompile_ecadd
Proof
  rw[precompile_ecadd_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_precompile_ecmul[simp]:
  decreases_gas F precompile_ecmul
Proof
  rw[precompile_ecmul_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_precompile_ecpairing[simp]:
  decreases_gas F precompile_ecpairing
Proof
  rw[precompile_ecpairing_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_precompile_ripemd_160[simp]:
  decreases_gas F precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_precompile_blake2f[simp]:
  decreases_gas F precompile_blake2f
Proof
  rw[precompile_blake2f_def]
  \\ irule decreases_gas_bind_false \\ rw []
  \\ irule decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_consume_gas
  \\ irule_at Any decreases_gas_ignore_bind_false
  \\ irule_at Any decreases_gas_set_return_data
  \\ irule_at Any decreases_gas_finish
QED

Theorem decreases_gas_dispatch_precompiles[simp]:
  decreases_gas F (dispatch_precompiles address)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem decreases_gas_cred_bind_g_0:
  decreases_gas F g ∧ (∀x. decreases_gas_cred F n0 0 (f x)) ⇒
  decreases_gas_cred F n0 0 (bind g f)
Proof
  strip_tac \\ irule decreases_gas_cred_mono
  \\ irule_at Any decreases_gas_cred_bind_g
  \\ qexistsl_tac [`λ_. T`, `n0`, `F`, `F`] \\ rw []
QED

Theorem decreases_gas_cred_get_static_push_context:
  (∀st.
    (FST(ctx st)).msgParams.gasLimit < n0 ∧
    (FST(ctx st)).gasUsed ≤ (FST(ctx st)).msgParams.gasLimit ∧
    LENGTH (FST(ctx st)).stack ≤ stack_limit) ⇒
  decreases_gas_cred F n0 0 (do st <- get_static; push_context (ctx st) od)
Proof
  simp [decreases_gas_cred_def, get_static_def, push_context_def, return_def,
    contexts_weight_def, LEX_DEF, unused_gas_def, bind_def, fail_def,
    get_current_context_def]
  \\ ntac 2 strip_tac \\ Cases_on `s.contexts` \\ simp []
  \\ first_x_assum (qspec_then `(FST h).msgParams.static` mp_tac)
  \\ gvs [ok_state_def]
  \\ rw[]
  \\ gvs[wf_context_def]
QED

Theorem decreases_gas_cred_get_static_push_context_bind:
  ∀ctx.
  (∀st.
    (FST (ctx st)).msgParams.gasLimit < n0 ∧
    (FST (ctx st)).gasUsed ≤ (FST (ctx st)).msgParams.gasLimit ∧
    LENGTH (FST (ctx st)).stack ≤ stack_limit) ∧
  decreases_gas_cred F 0 0 f ⇒
  decreases_gas_cred F n0 0 (do st <- get_static; _ <- push_context (ctx st); f od)
Proof
  rpt strip_tac
  \\ `decreases_gas_cred F n0 0
      (do _ <- do st <- get_static; push_context (ctx st) od; f od)`
    suffices_by simp []
  \\ irule decreases_gas_cred_mono
  \\ irule_at Any decreases_gas_cred_bind_g
  \\ qexistsl_tac [`λ_. T`, `0`, `F`, `F`] \\ rw []
  \\ metis_tac [decreases_gas_cred_get_static_push_context]
QED

Theorem decreases_gas_cred_proceed_call[simp]:
  stipend < r ⇒
  decreases_gas_cred F r 0 (proceed_call op sender address value
    argsOffset argsSize code stipend outputTo)
Proof
  simp [proceed_call_def, ignore_bind_def] \\ strip_tac
  \\ qpat_abbrev_tac `v1 = COND a b c`
  \\ qpat_abbrev_tac `v2 = COND a b c`
  \\ qpat_abbrev_tac `v3 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ reverse (rw [])
  >- (
    rw [Abbr`v1`]
    \\ irule decreases_gas_update_accounts
    \\ gs[])
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp [] \\ gen_tac
  \\ qpat_abbrev_tac `v4 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp [] \\ gen_tac
  \\ qpat_abbrev_tac `v5 = COND a b c`
  \\ HO_MATCH_MP_TAC decreases_gas_cred_get_static_push_context_bind
  \\ rw [initial_context_def, initial_msg_params_def, Abbr`v3`]
QED

Theorem decreases_gas_cred_unuse_gas[simp]:
  n ≤ n' ∧ decreases_gas F (f ()) ⇒
  decreases_gas_cred F n' 0 (bind (unuse_gas n) f)
Proof
  strip_tac \\ irule decreases_gas_cred_mono
  \\ irule_at Any decreases_gas_cred_bind_g \\ rw []
  \\ qexistsl_tac [`λ_. T`, `0`, `F`, `F`] \\ rw []
  \\ rw [unuse_gas_def]
  \\ simp [decreases_gas_cred_def, consume_gas_def, bind_def, get_current_context_def,
    decreases_gas_cred_def, ok_state_def, ignore_bind_def,
    return_def, assert_def, set_current_context_def, fail_def]
  \\ strip_tac
  \\ Cases_on `s.contexts` >- gs [] \\ rw [] \\ rw [] \\ gs []
  >- gs[wf_context_def]
  \\ gs [contexts_weight_def, unused_gas_def, LEX_DEF]
QED

Theorem decreases_gas_inc_pc[simp]:
  decreases_gas F inc_pc
Proof
  rw [inc_pc_def]
  \\ simp [inc_pc_def, bind_def, get_current_context_def,
    decreases_gas_def, ok_state_def, ignore_bind_def,
    return_def, assert_def, set_current_context_def, fail_def]
  \\ strip_tac
  \\ TOP_CASE_TAC \\ gvs[]
  \\ TOP_CASE_TAC \\ gs[wf_context_def]
QED

Theorem decreases_gas_cred_abort_call_value[simp]:
  n ≤ n' ⇒ decreases_gas_cred F n' 0 (abort_call_value n)
Proof
  rw [abort_call_value_def, ignore_bind_def]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_unuse_gas \\ rw []
QED

Theorem decreases_gas_cred_abort_unuse[simp]:
  n ≤ n' ⇒ decreases_gas_cred F n' 0 (abort_unuse n)
Proof
  rw [abort_unuse_def, ignore_bind_def]
  \\ irule_at Any decreases_gas_cred_unuse_gas \\ rw []
  \\ irule_at Any decreases_gas_bind_false \\ rw []
QED

Theorem decreases_gas_cred_step_call[simp]:
  decreases_gas_cred T 0 0 (step_call op)
Proof
  simp [step_call_def]
  \\ qpat_abbrev_tac `v1 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_pop_stack \\ simp [] \\ gen_tac
  \\ qpat_abbrev_tac `v2 = COND a b c`
  \\ qpat_abbrev_tac `v3 = COND a b c`
  \\ qpat_abbrev_tac `v4 = COND a b c`
  \\ qmatch_goalsub_abbrev_tac`max_expansion_range p1 p2`
  \\ Cases_on`max_expansion_range p1 p2` \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule_at Any decreases_gas_cred_access_address_bind \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_get_accounts \\ simp [] \\ gen_tac
  \\ qpat_abbrev_tac `v5 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_get_gas_left \\ rw []
  \\ qmatch_goalsub_abbrev_tac `call_gas v3 g l m e`
  \\ Cases_on `call_gas v3 g l m e` \\ rw []
  \\ drule_at Any call_gas_stipend_LE
  \\ impl_tac >- fs [Abbr`e`, Abbr`v4`, call_stipend_def, call_value_cost_def]
  \\ rw [] \\ irule decreases_gas_cred_consume_gas_debit
  \\ qexists_tac `r'+1` \\ rw [ignore_bind_def]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw [Abbr`v2`]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ rw []
  \\ irule_at Any decreases_gas_cred_proceed_call \\ rw []
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
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
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
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gs[wf_context_def]
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

Theorem decreases_gas_step_blob_hash[simp]:
  decreases_gas T step_blob_hash
Proof
  rw [step_blob_hash_def]
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
    bind_def, return_def, assert_def, ignore_bind_def, set_domain_def,
    set_current_context_def, fail_def, domain_check_def]
  \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
  \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_get_tStorage[simp]:
  decreases_gas F get_tStorage
Proof
  rw [get_tStorage_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
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
    rw [access_slot_def, return_def, fail_def, domain_check_def,
        cold_sload_cost_def, warm_access_cost_def, set_domain_def,
        ignore_bind_def, bind_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ gvs[]
    \\ TOP_CASE_TAC \\ gvs[])
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
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_write_transient_storage[simp]:
  decreases_gas F (write_transient_storage address key value)
Proof
  rw [write_transient_storage_def]
  \\ irule_at Any decreases_gas_bind_right
  \\ irule_at Any decreases_gas_get_tStorage \\ rw []
QED

Theorem decreases_gas_get_original[simp]:
  decreases_gas F get_original
Proof
  rw [get_original_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_update_gas_refund[simp]:
  decreases_gas F (update_gas_refund p)
Proof
  Cases_on `p` \\ rw [update_gas_refund_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[wf_context_def]
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

Theorem decreases_gas_write_storage[simp]:
  decreases_gas F (write_storage address key value)
Proof
  rw [write_storage_def]
  \\ irule_at Any decreases_gas_update_accounts
  \\ reverse(rw[])
  (*
  >- (
    rw[(*no_change_to_code_size_def,*) update_account_def, lookup_account_def,
       APPLY_UPDATE_THM] \\ rw[] )
  *)
  \\ irule wf_accounts_update_account
  \\ gs[wf_accounts_def, lookup_account_def]
  \\ gs[wf_account_state_def]
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
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[wf_context_def]
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

Theorem step_create_lemma:
  do
    _ <- set_return_data [];
    sucDepth <- get_num_contexts;
    _ <- ensure_storage_in_domain v4;
    if b1 ∨ b2 ∨ sucDepth > 1024 then m1 else if b3 then m2 else
    proceed_create senderAddress address value code cappedGas
  od = do
    _ <- set_return_data [];
    sucDepth <- get_num_contexts;
    _ <- ensure_storage_in_domain v4;
    if b1 ∨ b2 ∨ sucDepth > 1024 then m1 else if b3 then m2 else do
      _ <- update_accounts $ increment_nonce senderAddress;
      subContextTx <<- <|
          from     := senderAddress
        ; to       := SOME address
        ; value    := value
        ; gasLimit := cappedGas
        ; data     := []
        (* unused: for concreteness *)
        ; nonce := 0; gasPrice := 0; accessList := []
        ; blobVersionedHashes := []
      |>;
      rollback <- get_rollback;
      original <- get_original;
      set_original $ update_account address empty_account_state original;
      _ <- update_accounts $
        transfer_value senderAddress address value o
        increment_nonce address;
      _ <- get_static;
      push_context $
        (initial_context address code F (Code address) subContextTx, rollback)
    od
  od
Proof
  simp [FUN_EQ_THM, ignore_bind_def, bind_def, set_return_data_def]
  \\ gen_tac \\ rpt CASE_TAC
  \\ simp [bind_def, proceed_create_def, ignore_bind_def, return_def,
    get_static_def, get_current_context_def, fail_def] \\ rpt CASE_TAC
  \\ `F` suffices_by rw []
  \\ gvs [update_accounts_def, return_def, get_rollback_def, fail_def,
          ensure_storage_in_domain_def, assert_def,
    get_num_contexts_def, set_current_context_def, get_current_context_def]
  \\ Cases_on `x.contexts` \\ gvs [domain_check_def]
  \\ gvs[CaseEq"domain_mode", CaseEq"bool", return_def, fail_def,
         ignore_bind_def, bind_def, set_domain_def, set_original_def]
QED

Theorem decreases_gas_ensure_storage_in_domain[simp]:
  decreases_gas F (ensure_storage_in_domain _)
Proof
  rw[ensure_storage_in_domain_def, decreases_gas_def, assert_def,
     domain_check_def, set_domain_def, ignore_bind_def, bind_def]
  \\ TOP_CASE_TAC \\ gvs[]
  \\ TOP_CASE_TAC \\ gvs[]
  \\ TOP_CASE_TAC \\ gvs[return_def]
  \\ TOP_CASE_TAC \\ gvs[]
QED

Theorem decreases_gas_cred_bind_set_original[simp]:
  decreases_gas_cred F n1 n2 f ⇒
  decreases_gas_cred F n1 n2 (ignore_bind (set_original a) f)
Proof
  rw[decreases_gas_cred_def, ignore_bind_def, bind_def, set_original_def]
  \\ rw[return_def, fail_def]
  \\ Cases_on`s.contexts = []` \\ gvs[SNOC_APPEND]
  \\ qmatch_goalsub_abbrev_tac`f ss`
  \\ `ss.contexts ≠ []`
  by ( strip_tac \\ gvs[Abbr`ss`] )
  \\ first_x_assum (qspec_then`ss`mp_tac)
  \\ rw[]
  >- (
    first_x_assum irule
    \\ gs[ok_state_def, Abbr`ss`, EVERY_MEM, FORALL_PROD]
    \\ rw[] \\ first_x_assum irule
    \\ metis_tac[rich_listTheory.MEM_FRONT, list_CASES,
                 rich_listTheory.LAST_MEM, pair_CASES, FST, SND] )
  \\ irule transitive_LE_LEX_LE
  \\ goal_assum drule
  \\ qmatch_goalsub_abbrev_tac`_ x1 x2`
  \\ `x1 = x2`
  by (
    unabbrev_all_tac
    \\ reverse $ rw[contexts_weight_def, rich_listTheory.LENGTH_FRONT, PRE_SUB1]
    >- (Cases_on`LENGTH s.contexts` \\ gs[])
    \\ qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES
    \\ gs[SNOC_APPEND] )
  \\ rw[LEX_DEF, UNCURRY]
QED

Theorem decreases_gas_cred_step_create[simp]:
  decreases_gas_cred T 0 0 (step_create two)
Proof
  simp [step_create_def]
  \\ qpat_abbrev_tac `v1 = COND a b c`
  \\ qpat_abbrev_tac `v2 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_pop_stack \\ simp [] \\ gen_tac
  \\ qpat_abbrev_tac `v3 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_right
  \\ irule_at Any decreases_gas_imp
  \\ irule_at Any decreases_gas_memory_expansion_info \\ rw []
  \\ irule decreases_gas_cred_consume_gas_debit
  \\ qexists_tac`30000`
  \\ conj_tac >- rw[Abbr`v2`]
  \\ rw[ignore_bind_def]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[] \\ gen_tac
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[] \\ gen_tac
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[] \\ gen_tac
  \\ simp[ignore_bind_def]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ qpat_abbrev_tac `v4 = COND a b c`
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[] \\ gen_tac
  \\ simp[GSYM ignore_bind_def]
  \\ irule decreases_gas_cred_consume_gas_debit_more
  \\ qmatch_goalsub_abbrev_tac`_ + gasLeft`
  \\ qexists_tac`gasLeft + 1` \\ simp[]
  \\ qpat_abbrev_tac `v5 = COND a b c`
  \\ rw[ignore_bind_def]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ simp [Abbr `v5`, step_create_lemma]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ gen_tac
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ IF_CASES_TAC
  >- ( irule decreases_gas_cred_abort_unuse \\ simp[] )
  \\ IF_CASES_TAC
  >- (
    irule decreases_gas_imp \\ rw[]
    \\ rw[abort_create_exists_def]
    \\ irule decreases_gas_ignore_bind_right
    \\ irule_at Any decreases_gas_ignore_bind_right
    \\ rw[]
    \\ qexists_tac`F` \\ rw[]
    \\ qexists_tac`F` \\ rw[] )
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ gen_tac
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ gen_tac
  \\ irule decreases_gas_cred_bind_set_original
  \\ irule_at Any decreases_gas_cred_bind_g_0 \\ simp[]
  \\ HO_MATCH_MP_TAC decreases_gas_cred_get_static_push_context
  \\ rw [initial_context_def, initial_msg_params_def]
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

Theorem decreases_gas_add_to_delete[simp]:
  decreases_gas F (add_to_delete a)
Proof
  rw [add_to_delete_def, decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
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
  \\ irule_at Any decreases_gas_update_accounts \\ rw []
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

Theorem decreases_gas_cred_step_inst[simp]:
  decreases_gas_cred T 0 0 (step_inst inst)
Proof
  Cases_on `inst` \\ rw [step_inst_def]
  \\ irule decreases_gas_imp \\ rw []
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
        callee_rb <- pop_helper;
        callee <<- FST callee_rb;
        if (e = NONE) then
          do
            push_logs callee.logs;
            update_gas_refund (callee.addRefund,callee.subRefund)
          od
        else set_rollback (SND callee_rb);
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

Theorem decreases_gas_set_rollback[simp]:
  decreases_gas F (set_rollback b)
Proof
  rw[set_rollback_def, decreases_gas_def]
  \\ rw [decreases_gas_def, get_current_context_def,
    bind_def, return_def, assert_def, ignore_bind_def,
    set_current_context_def, fail_def]
  \\ TOP_CASE_TAC \\ gvs[] \\ TOP_CASE_TAC \\ gvs[]
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

Theorem decreases_gas_cred_step[simp]:
  decreases_gas_cred T 0 0 step
Proof
  rw [step_def]
  \\ irule decreases_gas_cred_handle
  \\ CONJ_TAC >- (
    rw [handle_step_def]
    \\ irule decreases_gas_cred_handle
    \\ CONJ_TAC >- (
      simp [handle_exception_def] \\ strip_tac
      \\ irule decreases_gas_cred_ignore_bind_mono
      \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `F`
      \\ simp []
      \\ CONJ_TAC >- (rw []
        \\ irule decreases_gas_imp \\ rw []
        \\ irule decreases_gas_bind_right
        \\ irule_at Any decreases_gas_get_gas_left \\ rw []
        \\ irule decreases_gas_ignore_bind_mono
        \\ irule_at Any decreases_gas_consume_gas \\ rw []
        \\ irule_at Any decreases_gas_set_return_data)
      \\ simp[GSYM after_pop_def, GSYM handle_ex_helper_def]
      \\ simp[handle_ex_helper_thm]
      \\ irule decreases_gas_cred_bind_right \\ irule_at Any decreases_gas_imp
      \\ irule_at Any decreases_gas_get_num_contexts \\ rw []
      \\ irule decreases_gas_cred_bind_right \\ irule_at Any decreases_gas_imp
      \\ irule_at Any decreases_gas_get_return_data \\ rw []
      \\ irule decreases_gas_cred_bind_right \\ irule_at Any decreases_gas_imp
      \\ irule_at Any decreases_gas_get_output_to \\ rw []
      \\ irule_at Any decreases_gas_cred_bind_mono
      \\ qexistsl_tac[`F`,`T`]
      \\ simp[]
      \\ conj_tac >- (
        rw[] >- (
          irule decreases_gas_imp \\ rw []
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
        \\ irule decreases_gas_imp \\ rw []
        \\ irule_at Any decreases_gas_ignore_bind_false
        \\ irule_at Any decreases_gas_set_rollback
        \\ irule_at Any decreases_gas_after_pop
      )
      \\ rw[pop_helper_def]
      \\ simp[bind_def, decreases_gas_cred_def, get_gas_left_def,
              get_current_context_def, return_def, pop_context_def,
              unuse_gas_def, ignore_bind_def, fail_def, assert_def,
              set_current_context_def, ok_state_def, get_num_contexts_def,
              assert_def]
      \\ gen_tac
      \\ Cases_on`s.contexts` \\ gvs []
      \\ Cases_on`t` \\ gvs[] >- metis_tac lexs
      \\ reverse IF_CASES_TAC \\ fs [DISJ_IMP_THM, FORALL_AND_THM,
        contexts_weight_def, LEX_DEF, unused_gas_def]
      \\ gvs[wf_context_def]
    )
    \\ simp [handle_create_def]
    \\ irule decreases_gas_imp \\ rw []
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
  \\ irule decreases_gas_cred_bind_right
  \\ reverse conj_tac
  >- (
    irule_at Any decreases_gas_imp \\ rw []
    \\ irule_at Any decreases_gas_get_current_context  )
  \\ rw[]
  \\ CASE_TAC >- rw[]
  \\ irule_at Any decreases_gas_cred_ignore_bind_mono
  \\ irule_at Any decreases_gas_cred_step_inst
  \\ rw[]
  \\ irule_at Any decreases_gas_imp \\ rw []
  \\ irule_at Any decreases_gas_inc_pc_or_jump
QED

Definition run_tr_def:
  run_tr (r, s) =
    case r of INR x => (x, s)
       | _ => run_tr (step s)
Termination
  WF_REL_TAC `inv_image ($< LEX ($< LEX $<)) (λ(r, s).
    if ISR r then ((0:num), (0, 0))
    else (1, contexts_weight 0 s.contexts))`
  \\ rpt gen_tac
  \\ mp_tac (Q.SPEC `s` (REWRITE_RULE [decreases_gas_cred_def]
             decreases_gas_cred_step))
  \\ IF_CASES_TAC >- (
    rw [contexts_weight_def, unused_gas_def]
    \\ CCONTR_TAC \\ pop_assum kall_tac \\ pop_assum irule
    \\ simp [step_def, handle_def, bind_def, get_current_context_def, fail_def,
      handle_step_def, handle_create_def, get_return_data_def, reraise_def,
      handle_exception_def, ignore_bind_def, get_gas_left_def])
  \\ rw []
  \\ fs[LEX_DEF, UNCURRY]
  \\ metis_tac[sum_CASES, ISL, ISR]
End

Theorem run_eq_tr:
  run s = case run_tr (step s) of (x, y) => SOME (INR x, y)
Proof
  rw[run_def]
  \\ rw[Once whileTheory.OWHILE_THM]
  \\ qspec_tac(`step s`,`x`)
  \\ Cases
  \\ map_every qid_spec_tac [`r`,`q`]
  \\ recInduct run_tr_ind
  \\ rw[]
  \\ rw[Once run_tr_def]
  \\ CASE_TAC \\ gs[]
  \\ rw[Once whileTheory.OWHILE_THM]
QED

Theorem step_preserves_wf_state:
  wf_state s ⇒ wf_state (SND (step s))
Proof
  mp_tac decreases_gas_cred_step
  \\ mp_tac preserves_wf_accounts_step
  \\ mp_tac (GEN_ALL limits_num_contexts_step)
  \\ rewrite_tac[decreases_gas_cred_def, preserves_wf_accounts_def,
                 limits_num_contexts_def]
  \\ rw[wf_state_def]
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[] )
  >- ( `1026 = SUC 1025` by simp[] \\ metis_tac[LESS_EQ_IFF_LESS_SUC])
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ simp[ok_state_def])
QED

val () = export_theory();
