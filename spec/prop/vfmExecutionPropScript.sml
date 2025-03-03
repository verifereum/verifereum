open HolKernel boolLib bossLib Parse BasicProvers
     combinTheory sumTheory pairTheory relationTheory arithmeticTheory
     listTheory pred_setTheory finite_setTheory optionTheory
     vfmStateTheory vfmConstantsTheory vfmContextTheory vfmExecutionTheory;

val () = new_theory "vfmExecutionProp";

(* TODO: move? *)

Type execution = “:execution_state -> α execution_result”;

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

(* TODO: this probably needs to depend on block number (for hardforks) *)
Definition wf_account_state_def:
  wf_account_state a
  ⇔ a.nonce < 2 ** 64                  (* https://eips.ethereum.org/EIPS/eip-2681 *)
  ∧ LENGTH a.code <= 2 ** 14 + 2 ** 13 (* https://eips.ethereum.org/EIPS/eip-170 *)
End

Theorem wf_empty_account_state[simp]:
  wf_account_state empty_account_state
Proof
  rw[empty_account_state_def, wf_account_state_def]
QED

Definition wf_accounts_def:
  wf_accounts a ⇔ ∀x. wf_account_state (a x)
End

Theorem wf_accounts_transfer_value[simp]:
  wf_accounts a ⇒
  wf_accounts (transfer_value x y z a)
Proof
  rw[wf_accounts_def, wf_account_state_def, transfer_value_def,
     update_account_def, APPLY_UPDATE_THM]
  \\ rw[lookup_account_def]
QED

Theorem wf_accounts_update_account:
  wf_accounts a ∧ wf_account_state x ⇒
  wf_accounts (update_account addr x a)
Proof
  rw[wf_accounts_def, update_account_def, APPLY_UPDATE_THM]
  \\ rw[]
QED

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit ∧
    c.gasUsed ≤ c.msgParams.gasLimit
End

Definition all_accounts_def:
  all_accounts s =
  s.rollback.accounts :: (MAP (λcr. (SND cr).accounts) s.contexts)
End

Definition wf_state_def:
  wf_state s ⇔
    s.contexts ≠ [] ∧
    LENGTH s.contexts ≤ SUC context_limit ∧
    EVERY (wf_context o FST) s.contexts ∧
    EVERY wf_accounts (all_accounts s)
End

Definition ok_state_def:
  ok_state s ⇔
    EVERY (wf_context o FST) s.contexts
End

Theorem wf_initial_context[simp]:
  wf_context (initial_context callee c s rd t)
Proof
  rw[wf_context_def]
QED

Theorem wf_context_apply_intrinsic_cost:
  wf_context (apply_intrinsic_cost a c) =
  (wf_context c ∧
   c.gasUsed ≤ c.msgParams.gasLimit - intrinsic_cost a c.msgParams)
Proof
  rw[apply_intrinsic_cost_def, wf_context_def]
QED

Theorem wf_initial_state:
  wf_accounts a ∧ initial_state d st c h b a t = SOME s
  ⇒
  wf_state s
Proof
  rw[wf_accounts_def, wf_state_def, initial_state_def,
     pre_transaction_updates_def, update_account_def,
     initial_rollback_def, code_from_tx_def, lookup_account_def,
     wf_context_apply_intrinsic_cost, all_accounts_def] \\ rw[]
  \\ gs[wf_account_state_def, combinTheory.APPLY_UPDATE_THM]
  \\ rw[wf_context_apply_intrinsic_cost]
  \\ rw[apply_intrinsic_cost_def]
  \\ gs[wf_accounts_def, APPLY_UPDATE_THM] \\ rw[]
  \\ gs[wf_account_state_def]
QED

(* -- *)

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
        ; blobGasPrice := 0; blobVersionedHashes := []
      |>;
      rollback <- get_rollback;
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
         ignore_bind_def, bind_def, set_domain_def]
QED

Theorem SND_return[simp]:
  SND (return x s) = s
Proof
  rw[return_def]
QED

Theorem SND_fail[simp]:
  SND (fail x y) = y
Proof
  rw[fail_def]
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

Definition preserves_wf_accounts_def:
  preserves_wf_accounts (m: α execution) =
  ∀s. EVERY wf_accounts (all_accounts s) ⇒
      EVERY wf_accounts (all_accounts $ SND (m s))
End

Theorem preserves_wf_accounts_bind:
  (∀x. preserves_wf_accounts (f x)) ∧
  preserves_wf_accounts g
  ⇒
  preserves_wf_accounts (bind g f)
Proof
  rw[preserves_wf_accounts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem preserves_wf_accounts_bind_pred:
  (∀x. p x ⇒ preserves_wf_accounts (f x)) ∧
  (∀s a. EVERY wf_accounts (all_accounts s) ∧ FST (g s) = (INL a) ⇒ p a) ∧
  preserves_wf_accounts g
  ⇒
  preserves_wf_accounts (bind g f)
Proof
  rw[preserves_wf_accounts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND, FST]
QED

Theorem preserves_wf_accounts_ignore_bind:
  preserves_wf_accounts f ∧
  preserves_wf_accounts g
  ⇒
  preserves_wf_accounts (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule preserves_wf_accounts_bind
  \\ rw[]
QED

Theorem preserves_wf_accounts_get_current_context[simp]:
  preserves_wf_accounts get_current_context
Proof
  rw[preserves_wf_accounts_def, get_current_context_def]
  \\ rw[return_def, fail_def]
QED

Theorem preserves_wf_accounts_assert[simp]:
  preserves_wf_accounts (assert b e)
Proof
  rw[preserves_wf_accounts_def, assert_def]
QED

Theorem preserves_wf_accounts_set_current_context[simp]:
  preserves_wf_accounts (set_current_context c)
Proof
  rw[preserves_wf_accounts_def, set_current_context_def]
  \\ rw[fail_def, return_def]
  \\ gs[all_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[]
QED

Theorem preserves_wf_accounts_return[simp]:
  preserves_wf_accounts (return x)
Proof
  rw[return_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_fail[simp]:
  preserves_wf_accounts (fail x)
Proof
  rw[fail_def, preserves_wf_accounts_def]
QED

val tac =
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]));

Theorem preserves_wf_accounts_pop_stack[simp]:
  preserves_wf_accounts (pop_stack n)
Proof
  rw[pop_stack_def] \\ tac
QED

Theorem preserves_wf_accounts_consume_gas[simp]:
  preserves_wf_accounts (consume_gas n)
Proof
  rw[consume_gas_def] \\ tac
QED

Theorem preserves_wf_accounts_push_stack[simp]:
  preserves_wf_accounts (push_stack n)
Proof
  rw[push_stack_def] \\ tac
QED

Theorem preserves_wf_accounts_step_binop[simp]:
  preserves_wf_accounts (step_binop x y)
Proof
  rw[step_binop_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_modop[simp]:
  preserves_wf_accounts (step_modop x y)
Proof
  rw[step_modop_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_monop[simp]:
  preserves_wf_accounts (step_monop x y)
Proof
  rw[step_monop_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_tx_params[simp]:
  preserves_wf_accounts get_tx_params
Proof
  rw[get_tx_params_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_step_txParams[simp]:
  preserves_wf_accounts (step_txParams x y)
Proof
  rw[step_txParams_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_context[simp]:
  preserves_wf_accounts (step_context x y)
Proof
  rw[step_context_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_msgParams[simp]:
  preserves_wf_accounts (step_msgParams x y)
Proof
  rw[step_msgParams_def]
QED

Theorem preserves_wf_accounts_memory_expansion_info[simp]:
  preserves_wf_accounts (memory_expansion_info c e)
Proof
  rw[memory_expansion_info_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_write_memory[simp]:
  preserves_wf_accounts (write_memory c e)
Proof
  rw[write_memory_def] \\ tac
QED

Theorem preserves_wf_accounts_read_memory[simp]:
  preserves_wf_accounts (read_memory c e)
Proof
  rw[read_memory_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_expand_memory[simp]:
  preserves_wf_accounts (expand_memory c)
Proof
  rw[expand_memory_def] \\ tac
QED

Theorem preserves_wf_accounts_copy_to_memory[simp]:
  (∀f. e = SOME f ⇒ preserves_wf_accounts f) ⇒
  preserves_wf_accounts (copy_to_memory a b c d e)
Proof
  rw[copy_to_memory_def, max_expansion_range_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ TRY(irule preserves_wf_accounts_ignore_bind \\ rw[])
  \\ CASE_TAC \\ gs[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_copy_to_memory[simp]:
  (∀f. y = SOME f ⇒ preserves_wf_accounts f) ⇒
  preserves_wf_accounts (step_copy_to_memory x y)
Proof
  rw[step_copy_to_memory_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_exp[simp]:
  preserves_wf_accounts step_exp
Proof
  rw[step_exp_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_keccak256[simp]:
  preserves_wf_accounts step_keccak256
Proof
  rw[step_keccak256_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_accounts[simp]:
  preserves_wf_accounts get_accounts
Proof
  rw[get_accounts_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_access_address[simp]:
  preserves_wf_accounts (access_address a)
Proof
  rw[access_address_def, preserves_wf_accounts_def, return_def, fail_def,
     domain_check_def, bind_def, ignore_bind_def, set_domain_def]
  \\ rw[] \\ TOP_CASE_TAC \\ rw[] \\ gs[all_accounts_def]
QED

Theorem preserves_wf_accounts_access_slot[simp]:
  preserves_wf_accounts (access_slot a)
Proof
  rw[access_slot_def, preserves_wf_accounts_def, return_def, fail_def,
     domain_check_def, bind_def, ignore_bind_def, set_domain_def]
  \\ rw[] \\ TOP_CASE_TAC \\ rw[] \\ gs[all_accounts_def]
QED

Theorem preserves_wf_accounts_step_balance[simp]:
  preserves_wf_accounts step_balance
Proof
  rw[step_balance_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_call_data[simp]:
  preserves_wf_accounts get_call_data
Proof
  rw[get_call_data_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_call_data_load[simp]:
  preserves_wf_accounts step_call_data_load
Proof
  rw[step_call_data_load_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_code[simp]:
  preserves_wf_accounts (get_code x)
Proof
  rw[get_code_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_return_data[simp]:
  preserves_wf_accounts get_return_data
Proof
  rw[get_return_data_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_return_data_check[simp]:
  preserves_wf_accounts (get_return_data_check y x)
Proof
  rw[get_return_data_check_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_ext_code_copy[simp]:
  preserves_wf_accounts step_ext_code_copy
Proof
  rw[step_ext_code_copy_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_copy_to_memory
  \\ rw[]
QED

Theorem preserves_wf_accounts_step_ext_code_size[simp]:
  preserves_wf_accounts step_ext_code_size
Proof
  rw[step_ext_code_size_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_ext_code_hash[simp]:
  preserves_wf_accounts step_ext_code_hash
Proof
  rw[step_ext_code_hash_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_return_data_copy[simp]:
  preserves_wf_accounts step_return_data_copy
Proof
  rw[step_return_data_copy_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_copy_to_memory
  \\ rw[]
QED

Theorem preserves_wf_accounts_step_block_hash[simp]:
  preserves_wf_accounts step_block_hash
Proof
  rw[step_block_hash_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_callee[simp]:
  preserves_wf_accounts get_callee
Proof
  rw[get_callee_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_self_balance[simp]:
  preserves_wf_accounts step_self_balance
Proof
  rw[step_self_balance_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_pop[simp]:
  preserves_wf_accounts step_pop
Proof
  rw[step_pop_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_mload[simp]:
  preserves_wf_accounts step_mload
Proof
  rw[step_mload_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_mstore[simp]:
  preserves_wf_accounts (step_mstore x)
Proof
  rw[step_mstore_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_tStorage[simp]:
  preserves_wf_accounts get_tStorage
Proof
  rw[get_tStorage_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_step_sload[simp]:
  preserves_wf_accounts (step_sload x)
Proof
  rw[step_sload_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_rollback[simp]:
  preserves_wf_accounts get_rollback
Proof
  rw[get_rollback_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_bind_get_rollback:
  (∀x. wf_accounts x.accounts ⇒ preserves_wf_accounts (f x))
  ⇒
  preserves_wf_accounts (bind get_rollback f)
Proof
  strip_tac
  \\ irule preserves_wf_accounts_bind_pred
  \\ rw[]
  \\ qexists_tac`λx. wf_accounts x.accounts`
  \\ rw[get_rollback_def, return_def, all_accounts_def]
  \\ gs[]
QED

val tac =
  rpt ((irule preserves_wf_accounts_bind_get_rollback \\ rw[]) ORELSE
       (irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]));

Theorem preserves_wf_accounts_set_jump_dest[simp]:
  preserves_wf_accounts (set_jump_dest x)
Proof
  rw[set_jump_dest_def] >> tac
QED

Theorem preserves_wf_accounts_step_jump[simp]:
  preserves_wf_accounts step_jump
Proof
  rw[step_jump_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_jumpi[simp]:
  preserves_wf_accounts step_jumpi
Proof
  rw[step_jumpi_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_push[simp]:
  preserves_wf_accounts (step_push x y)
Proof
  rw[step_push_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_dup[simp]:
  preserves_wf_accounts (step_dup x)
Proof
  rw[step_dup_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_swap[simp]:
  preserves_wf_accounts (step_swap x)
Proof
  rw[step_swap_def] >> tac
QED

Theorem preserves_wf_accounts_push_logs[simp]:
  preserves_wf_accounts (push_logs x)
Proof
  rw[push_logs_def] >> tac
QED

Theorem preserves_wf_accounts_get_static[simp]:
  preserves_wf_accounts get_static
Proof
  rw[get_static_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_assert_not_static[simp]:
  preserves_wf_accounts assert_not_static
Proof
  rw[assert_not_static_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_log[simp]:
  preserves_wf_accounts (step_log x)
Proof
  rw[step_log_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_set_tStorage[simp]:
  preserves_wf_accounts (set_tStorage x)
Proof
  rw[set_tStorage_def, preserves_wf_accounts_def, return_def, all_accounts_def]
QED

Theorem preserves_wf_accounts_write_transient_storage[simp]:
  preserves_wf_accounts (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_write_storage[simp]:
  preserves_wf_accounts (write_storage x y z)
Proof
  rw[write_storage_def] >> tac
  \\ rw[preserves_wf_accounts_def, update_accounts_def, return_def]
  \\ rw[update_account_def, lookup_account_def]
  \\ gs[wf_accounts_def, APPLY_UPDATE_THM, all_accounts_def]
  \\ rw[] \\ gs[wf_account_state_def]
QED

Theorem preserves_wf_accounts_update_gas_refund_def[simp]:
  preserves_wf_accounts (update_gas_refund x)
Proof
  Cases_on`x` >>
  rw[update_gas_refund_def] >>
  tac
QED

Theorem preserves_wf_accounts_get_original[simp]:
  preserves_wf_accounts get_original
Proof
  rw[get_original_def, preserves_wf_accounts_def]
  \\ rw[return_def, fail_def]
QED

Theorem preserves_wf_accounts_get_gas_left[simp]:
  preserves_wf_accounts get_gas_left
Proof
  rw[get_gas_left_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_current_code[simp]:
  preserves_wf_accounts get_current_code
Proof
  rw[get_current_code_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_num_contexts[simp]:
  preserves_wf_accounts get_num_contexts
Proof
  rw[get_num_contexts_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_get_value[simp]:
  preserves_wf_accounts get_value
Proof
  rw[get_value_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_caller[simp]:
  preserves_wf_accounts get_caller
Proof
  rw[get_caller_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_sstore_gas_consumption[simp]:
  preserves_wf_accounts (step_sstore_gas_consumption x y z)
Proof
  rw[step_sstore_gas_consumption_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_sstore[simp]:
  preserves_wf_accounts (step_sstore x)
Proof
  rw[step_sstore_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_finish[simp]:
  preserves_wf_accounts finish
Proof
  rw[finish_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_revert[simp]:
  preserves_wf_accounts revert
Proof
  rw[revert_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_set_return_data[simp]:
  preserves_wf_accounts (set_return_data x)
Proof
  rw[set_return_data_def] >> tac
QED

Theorem preserves_wf_accounts_step_return[simp]:
  preserves_wf_accounts (step_return x)
Proof
  rw[step_return_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_invalid[simp]:
  preserves_wf_accounts step_invalid
Proof
  rw[step_invalid_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_add_to_delete[simp]:
  preserves_wf_accounts (add_to_delete x)
Proof
  rw[add_to_delete_def, preserves_wf_accounts_def, return_def, all_accounts_def]
QED

val defs = [bind_def, ignore_bind_def, access_address_def,
        get_callee_def, preserves_wf_accounts_def, pop_stack_def,
        get_current_context_def, assert_def, set_current_context_def,
        assert_not_static_def, add_to_delete_def, finish_def,
        set_return_data_def, get_num_contexts_def, get_rollback_def,
        get_static_def, update_accounts_def, get_gas_left_def,
        domain_check_def, set_domain_def,
        get_original_def, get_accounts_def, consume_gas_def, return_def, fail_def]

Theorem wf_account_state_with_balance[simp]:
  wf_account_state (a with balance updated_by b) = wf_account_state a
Proof
  rw[wf_account_state_def]
QED

Theorem preserves_wf_accounts_step_self_destruct[simp]:
  preserves_wf_accounts step_self_destruct
Proof
  rw[step_self_destruct_def]
  \\ rw defs \\ rw[]
  \\ rw defs \\ rw[]
  \\ rw defs
  \\ gs[wf_accounts_def, update_account_def, transfer_value_def,
        all_accounts_def, lookup_account_def]
  \\ rw[APPLY_UPDATE_THM, lookup_account_def] \\ rw[]
  \\ Cases_on`s.contexts` \\ gs[wf_accounts_def]
  \\ Cases_on`s.msdomain` \\ gs[] \\ rw[]
  \\ rw defs \\ rw[]
  \\ gs[wf_accounts_def, update_account_def, transfer_value_def,
        all_accounts_def, lookup_account_def]
  \\ rw[APPLY_UPDATE_THM, lookup_account_def] \\ rw[]
QED

Theorem preserves_wf_accounts_unuse_gas[simp]:
  preserves_wf_accounts (unuse_gas x)
Proof
  rw[unuse_gas_def] >> tac
QED

Theorem preserves_wf_accounts_inc_pc[simp]:
  preserves_wf_accounts inc_pc
Proof
  rw[inc_pc_def] >> tac
QED

Theorem preserves_wf_accounts_abort_unuse[simp]:
  preserves_wf_accounts (abort_unuse x)
Proof
  rw[abort_unuse_def] >> tac
QED

Theorem preserves_wf_accounts_abort_call_value[simp]:
  preserves_wf_accounts (abort_call_value x)
Proof
  rw[abort_call_value_def] >> tac
QED

Theorem preserves_wf_accounts_push_context[simp]:
  wf_accounts (SND x).accounts ⇒
  preserves_wf_accounts (push_context x)
Proof
  rw[push_context_def, preserves_wf_accounts_def, return_def, all_accounts_def]
QED

Theorem preserves_wf_accounts_update_accounts_transfer_value[simp]:
  preserves_wf_accounts (update_accounts (transfer_value x y z))
Proof
  rw[update_accounts_def, preserves_wf_accounts_def, return_def,
     all_accounts_def]
QED

Theorem preserves_wf_accounts_precompile_ecrecover[simp]:
  preserves_wf_accounts precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
QED

Theorem preserves_wf_accounts_precompile_ecadd[simp]:
  preserves_wf_accounts precompile_ecadd
Proof
  rw[precompile_ecadd_def]
QED

Theorem preserves_wf_accounts_precompile_ecmul[simp]:
  preserves_wf_accounts precompile_ecmul
Proof
  rw[precompile_ecmul_def]
QED

Theorem preserves_wf_accounts_precompile_ecpairing[simp]:
  preserves_wf_accounts precompile_ecpairing
Proof
  rw[precompile_ecpairing_def]
QED

Theorem preserves_wf_accounts_precompile_blake2f[simp]:
  preserves_wf_accounts precompile_blake2f
Proof
  rw[precompile_blake2f_def]
QED

Theorem preserves_wf_accounts_precompile_modexp[simp]:
  preserves_wf_accounts precompile_modexp
Proof
  rw[precompile_modexp_def]
  \\ rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_precompile_sha2_256[simp]:
  preserves_wf_accounts precompile_sha2_256
Proof
  rw[precompile_sha2_256_def]
  \\ rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_precompile_identity[simp]:
  preserves_wf_accounts precompile_identity
Proof
  rw[precompile_identity_def]
  \\ rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_precompile_ripemd_160[simp]:
  preserves_wf_accounts precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
QED

Theorem preserves_wf_accounts_dispatch_precompiles[simp]:
  preserves_wf_accounts (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem preserves_wf_accounts_step_call[simp]:
  preserves_wf_accounts (step_call x)
Proof
  rw[step_call_def, UNCURRY] >> tac
  \\ rw[proceed_call_def] >> tac
QED

Definition preserves_wf_accounts_pred_def:
  preserves_wf_accounts_pred p m ⇔
  ∀s. p s ∧ EVERY wf_accounts (all_accounts s)
      ⇒ EVERY wf_accounts (all_accounts (SND (m s)))
End

Theorem preserves_wf_accounts_bind_get_accounts:
  (∀x. wf_accounts x ⇒ preserves_wf_accounts (f x))
  ⇒
  preserves_wf_accounts (bind get_accounts f)
Proof
  strip_tac
  \\ irule preserves_wf_accounts_bind_pred
  \\ rw[]
  \\ qexists_tac`wf_accounts`
  \\ rw[get_accounts_def, return_def, all_accounts_def]
  \\ rw[]
QED

Theorem preserves_wf_accounts_pred_bind_get_accounts:
  (∀x. preserves_wf_accounts_pred (λs. x = s.rollback.accounts) (f x))
  ⇒
  preserves_wf_accounts (bind get_accounts f)
Proof
  rw[preserves_wf_accounts_pred_def, preserves_wf_accounts_def, bind_def]
  \\ gs[all_accounts_def, get_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_pred_pred_bind:
   (∀x. preserves_wf_accounts_pred q (f x)) ∧
   (∀s s'. p s ⇒ q (SND (g s))) ∧
   preserves_wf_accounts_pred p g ⇒
   preserves_wf_accounts_pred p (monad_bind g f)
Proof
  rw[preserves_wf_accounts_pred_def, bind_def]
  \\ CASE_TAC \\ gs[] \\ reverse CASE_TAC \\ gs[]
  >- metis_tac[SND]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem preserves_wf_accounts_imp_pred:
   preserves_wf_accounts g ⇒
   preserves_wf_accounts_pred p g
Proof
  rw[preserves_wf_accounts_pred_def, preserves_wf_accounts_def]
QED

Theorem wf_accounts_increment_nonce:
  wf_accounts a ∧ SUC (a x).nonce < 2 ** 64 ⇒
  wf_accounts (increment_nonce x a)
Proof
  rw[wf_accounts_def, wf_account_state_def, increment_nonce_def]
  \\ gs[update_account_def, lookup_account_def, APPLY_UPDATE_THM]
  \\ rw[] \\ rw[]
QED

Theorem preserves_wf_accounts_pred_proceed_create:
  preserves_wf_accounts_pred (λs.
    SUC (s.rollback.accounts a).nonce < 2 ** 64 ∧
    (s.rollback.accounts b).nonce = 0)
  (proceed_create a b c d e)
Proof
  simp[proceed_create_def]
  \\ simp[ignore_bind_def]
  \\ irule preserves_wf_accounts_pred_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    qexists_tac`λs. SUC (s.rollback.accounts b).nonce < 2 ** 64 ∧
                    (s.rollback.accounts a).nonce < 2 ** 64` >>
    rw[preserves_wf_accounts_pred_def,
       get_rollback_def, update_accounts_def,
       push_context_def, bind_def, return_def]
    \\ gs[all_accounts_def]
    >- (
      irule wf_accounts_transfer_value
      \\ irule wf_accounts_increment_nonce
      \\ gs[] )
    \\ (rw[increment_nonce_def, update_account_def,
           lookup_account_def, APPLY_UPDATE_THM]) )
  \\ rw[preserves_wf_accounts_pred_def,update_accounts_def]
  \\ gvs[return_def, all_accounts_def]
  \\ rw[increment_nonce_def, lookup_account_def,
        update_account_def, APPLY_UPDATE_THM]
  \\ gvs[wf_accounts_def, APPLY_UPDATE_THM]
  \\ rw[]
  \\ gvs[wf_account_state_def]
QED

Theorem preserves_wf_accounts_pred_mono:
  preserves_wf_accounts_pred p f ∧ (∀s. q s ⇒ p s)
  ⇒
  preserves_wf_accounts_pred q f
Proof
  rw[preserves_wf_accounts_pred_def]
QED

Theorem preserves_wf_accounts_ensure_storage_in_domain[simp]:
  preserves_wf_accounts (ensure_storage_in_domain _)
Proof
  rw[preserves_wf_accounts_def, ensure_storage_in_domain_def, assert_def,
     domain_check_def]
  \\ TOP_CASE_TAC \\ gvs[set_domain_def, bind_def, ignore_bind_def]
  \\ rw[return_def] \\ gs[all_accounts_def]
QED

Theorem preserves_wf_accounts_step_create[simp]:
  preserves_wf_accounts (step_create x)
Proof
  simp[step_create_def]
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ irule preserves_wf_accounts_pred_bind_get_accounts
  \\ qx_gen_tac`accounts` \\ simp[]
  \\ simp[ignore_bind_def]
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- rw[assert_def]
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[access_address_def, return_def, fail_def, domain_check_def]
    \\ Cases_on`s.msdomain` \\ gs[]
    \\ rw[set_domain_def, bind_def, ignore_bind_def, return_def] )
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- rw[get_gas_left_def, return_def, get_current_context_def,
        bind_def, fail_def]
  \\ gen_tac
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[consume_gas_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def]
    \\ rw[] )
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[assert_not_static_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def, get_static_def])
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[set_return_data_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def, get_static_def])
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[get_num_contexts_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def, get_static_def])
  \\ gen_tac
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[ensure_storage_in_domain_def, return_def, ignore_bind_def,
       bind_def, fail_def, assert_def, get_static_def, domain_check_def]
    \\ Cases_on`s.msdomain` \\ gs defs \\ rw[])
  \\ IF_CASES_TAC
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ IF_CASES_TAC
  >- (
    simp[abort_create_exists_def]
    \\ simp[ignore_bind_def]
    \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
    \\ reverse conj_tac
    >- (
      rw[preserves_wf_accounts_pred_def, update_accounts_def, return_def]
      \\ gvs[all_accounts_def]
      \\ irule wf_accounts_increment_nonce
      \\ gs[lookup_account_def] )
    \\ qexists_tac`K T` \\ rw[]
    \\ irule preserves_wf_accounts_imp_pred
    \\ tac )
  \\ gs[account_already_created_def]
  \\ irule preserves_wf_accounts_pred_mono
  \\ irule_at Any preserves_wf_accounts_pred_proceed_create
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ gvs[lookup_account_def]
QED

Theorem preserves_wf_accounts_step_inst[simp]:
  preserves_wf_accounts (step_inst op)
Proof
  Cases_on`op` \\ rw[step_inst_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_handle:
  preserves_wf_accounts f ∧
  (∀e. preserves_wf_accounts (g e))
  ⇒
  preserves_wf_accounts (handle f g)
Proof
  rw[handle_def, preserves_wf_accounts_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem preserves_wf_accounts_get_output_to[simp]:
  preserves_wf_accounts get_output_to
Proof
  rw[get_output_to_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_pop_and_incorporate_context[simp]:
  preserves_wf_accounts (pop_and_incorporate_context x)
Proof
  rw[pop_and_incorporate_context_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ rw[bind_def, ignore_bind_def, pop_context_def, unuse_gas_def,
        preserves_wf_accounts_def, fail_def, return_def, assert_def,
        get_current_context_def, set_current_context_def, update_gas_refund_def,
        push_logs_def]
  \\ rw[] \\ rw[]
  \\ rw[get_current_context_def, set_current_context_def, bind_def,
        ignore_bind_def, return_def, fail_def]
  \\ gs[all_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[set_rollback_def, return_def]
  \\ Cases_on`t` \\ gs[]
QED

Theorem preserves_wf_accounts_reraise[simp]:
  preserves_wf_accounts (reraise e)
Proof
  rw[reraise_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_step[simp]:
  preserves_wf_accounts step
Proof
  rw[step_def]
  \\ irule preserves_wf_accounts_handle
  \\ reverse conj_tac
  >- (
    irule preserves_wf_accounts_bind \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ rw[inc_pc_or_jump_def]
    \\ irule preserves_wf_accounts_bind \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[] )
  \\ rw[handle_step_def]
  \\ irule preserves_wf_accounts_handle
  \\ conj_tac
  >- (
    simp[handle_exception_def] \\ gen_tac
    \\ irule preserves_wf_accounts_ignore_bind
    \\ reverse conj_tac
    >- (
      rw[]
      \\ irule preserves_wf_accounts_bind \\ rw[]
      \\ irule preserves_wf_accounts_ignore_bind \\ rw[] )
    \\ irule preserves_wf_accounts_bind
    \\ rw[]
    \\ irule preserves_wf_accounts_bind \\ rw[]
    \\ irule preserves_wf_accounts_bind \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ CASE_TAC \\ rw[] \\ CASE_TAC \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[])
  \\ rw[handle_create_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC \\ rw[]
  >- (
    tac
    \\ rw[preserves_wf_accounts_def, update_accounts_def, return_def]
    \\ gs[all_accounts_def, update_account_def]
    \\ gs[wf_accounts_def, APPLY_UPDATE_THM] \\ rw[]
    \\ gs[lookup_account_def, wf_account_state_def] )
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ rw[preserves_wf_accounts_def, assert_def, bind_def, update_accounts_def,
        ignore_bind_def, return_def, reraise_def]
  \\ gs[all_accounts_def, update_account_def, lookup_account_def]
  \\ gs[wf_accounts_def, APPLY_UPDATE_THM] \\ rw[]
  \\ gs[wf_account_state_def]
QED

Definition limits_num_contexts_def:
  limits_num_contexts n1 n2 (m: α execution) =
  ∀s. LENGTH s.contexts < n1 ⇒
      LENGTH (SND (m s)).contexts < n2
End

Theorem limits_num_contexts_bind:
  (∀x. limits_num_contexts n2 n3 (f x)) ∧
  limits_num_contexts n1 n2 g ∧
  n2 ≤ n3
  ⇒
  limits_num_contexts n1 n3 (bind g f)
Proof
  rw[limits_num_contexts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem limits_num_contexts_bind_same:
  (∀x. limits_num_contexts n n (f x)) ∧
  limits_num_contexts n n g
  ⇒
  limits_num_contexts n n (bind g f)
Proof
  strip_tac
  \\ irule limits_num_contexts_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_ignore_bind:
  limits_num_contexts n2 n3 f ∧
  limits_num_contexts n1 n2 g ∧
  n2 ≤ n3
  ⇒
  limits_num_contexts n1 n3 (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule limits_num_contexts_bind \\ rw[]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_ignore_bind_same:
  limits_num_contexts n n f ∧
  limits_num_contexts n n g
  ⇒
  limits_num_contexts n n (ignore_bind g f)
Proof
  strip_tac
  \\ irule limits_num_contexts_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_get_current_context[simp]:
  limits_num_contexts n n get_current_context
Proof
  rw[limits_num_contexts_def, get_current_context_def]
  \\ rw[return_def, fail_def]
QED

Theorem limits_num_contexts_assert[simp]:
  limits_num_contexts n n (assert b e)
Proof
  rw[limits_num_contexts_def, assert_def]
QED

Theorem limits_num_contexts_set_current_context[simp]:
  limits_num_contexts n n (set_current_context c)
Proof
  rw[limits_num_contexts_def, set_current_context_def]
  \\ rw[fail_def, return_def]
  \\ gs[all_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[]
QED

Theorem limits_num_contexts_return[simp]:
  limits_num_contexts n n (return x)
Proof
  rw[return_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_fail[simp]:
  limits_num_contexts n n (fail x)
Proof
  rw[fail_def, limits_num_contexts_def]
QED

val tac = rpt (
  (irule limits_num_contexts_bind_same \\ rw[]) ORELSE
  (irule limits_num_contexts_ignore_bind_same \\ rw[])
)

Theorem limits_num_contexts_pop_stack[simp]:
  limits_num_contexts n n (pop_stack m)
Proof
  rw[pop_stack_def] \\ tac
QED

Theorem limits_num_contexts_consume_gas[simp]:
  limits_num_contexts n n (consume_gas m)
Proof
  rw[consume_gas_def] \\ tac
QED

Theorem limits_num_contexts_push_stack[simp]:
  limits_num_contexts n n (push_stack m)
Proof
  rw[push_stack_def] \\ tac
QED

Theorem limits_num_contexts_step_binop[simp]:
  limits_num_contexts n n (step_binop x y)
Proof
  rw[step_binop_def] \\ tac
QED

Theorem limits_num_contexts_step_modop[simp]:
  limits_num_contexts n n (step_modop x y)
Proof
  rw[step_modop_def] \\ tac
QED

Theorem limits_num_contexts_step_monop[simp]:
  limits_num_contexts n n (step_monop x y)
Proof
  rw[step_monop_def] \\ tac
QED

Theorem limits_num_contexts_get_tx_params[simp]:
  limits_num_contexts n n get_tx_params
Proof
  rw[get_tx_params_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_step_txParams[simp]:
  limits_num_contexts n n (step_txParams x y)
Proof
  rw[step_txParams_def] \\ tac
QED

Theorem limits_num_contexts_step_context[simp]:
  limits_num_contexts n n (step_context x y)
Proof
  rw[step_context_def] \\ tac
QED

Theorem limits_num_contexts_step_msgParams[simp]:
  limits_num_contexts n n (step_msgParams x y)
Proof
  rw[step_msgParams_def]
QED

Theorem limits_num_contexts_memory_expansion_info[simp]:
  limits_num_contexts n n (memory_expansion_info c e)
Proof
  rw[memory_expansion_info_def] \\ tac
QED

Theorem limits_num_contexts_write_memory[simp]:
  limits_num_contexts n n (write_memory c e)
Proof
  rw[write_memory_def] \\ tac
QED

Theorem limits_num_contexts_read_memory[simp]:
  limits_num_contexts n n (read_memory c e)
Proof
  rw[read_memory_def] \\ tac
QED

Theorem limits_num_contexts_expand_memory[simp]:
  limits_num_contexts n n (expand_memory c)
Proof
  rw[expand_memory_def] \\ tac
QED

Theorem limits_num_contexts_copy_to_memory[simp]:
  (∀f. e = SOME f ⇒ limits_num_contexts n n f) ⇒
  limits_num_contexts n n (copy_to_memory a b c d e)
Proof
  rw[copy_to_memory_def, max_expansion_range_def]
  \\ irule limits_num_contexts_bind_same \\ rw[]
  \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
  \\ irule limits_num_contexts_bind_same \\ rw[]
  \\ TRY(irule limits_num_contexts_ignore_bind_same \\ rw[])
  \\ CASE_TAC \\ gs[]
  \\ irule limits_num_contexts_bind_same \\ rw[]
  \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
QED

Theorem limits_num_contexts_step_copy_to_memory[simp]:
  (∀f. y = SOME f ⇒ limits_num_contexts n n f) ⇒
  limits_num_contexts n n (step_copy_to_memory x y)
Proof
  rw[step_copy_to_memory_def] \\ tac
QED

Theorem limits_num_contexts_step_exp[simp]:
  limits_num_contexts n n step_exp
Proof
  rw[step_exp_def] \\ tac
QED

Theorem limits_num_contexts_step_keccak256[simp]:
  limits_num_contexts n n step_keccak256
Proof
  rw[step_keccak256_def] \\ tac
QED

Theorem limits_num_contexts_get_accounts[simp]:
  limits_num_contexts n n get_accounts
Proof
  rw[get_accounts_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_access_address[simp]:
  limits_num_contexts n n (access_address a)
Proof
  rw[access_address_def, limits_num_contexts_def, return_def, fail_def,
     domain_check_def, ignore_bind_def, bind_def, set_domain_def]
  \\ Cases_on`s.msdomain`
  \\ rw[] \\ gs[all_accounts_def]
QED

Theorem limits_num_contexts_access_slot[simp]:
  limits_num_contexts n n (access_slot a)
Proof
  rw[access_slot_def, limits_num_contexts_def, return_def, fail_def,
     domain_check_def, ignore_bind_def, bind_def, set_domain_def]
  \\ Cases_on`s.msdomain`
  \\ rw[] \\ gs[all_accounts_def]
QED

Theorem limits_num_contexts_step_balance[simp]:
  limits_num_contexts n n step_balance
Proof
  rw[step_balance_def] \\ tac
QED

Theorem limits_num_contexts_get_call_data[simp]:
  limits_num_contexts n n get_call_data
Proof
  rw[get_call_data_def] \\ tac
QED

Theorem limits_num_contexts_step_call_data_load[simp]:
  limits_num_contexts n n step_call_data_load
Proof
  rw[step_call_data_load_def] \\ tac
QED

Theorem limits_num_contexts_get_code[simp]:
  limits_num_contexts n n (get_code x)
Proof
  rw[get_code_def] \\ tac
QED

Theorem limits_num_contexts_get_return_data[simp]:
  limits_num_contexts n n get_return_data
Proof
  rw[get_return_data_def] \\ tac
QED

Theorem limits_num_contexts_get_return_data_check[simp]:
  limits_num_contexts n n (get_return_data_check y x)
Proof
  rw[get_return_data_check_def] \\ tac
QED

Theorem limits_num_contexts_step_ext_code_copy[simp]:
  limits_num_contexts n n step_ext_code_copy
Proof
  rw[step_ext_code_copy_def] \\ tac
QED

Theorem limits_num_contexts_step_ext_code_size[simp]:
  limits_num_contexts n n step_ext_code_size
Proof
  rw[step_ext_code_size_def] \\ tac
QED

Theorem limits_num_contexts_step_ext_code_hash[simp]:
  limits_num_contexts n n step_ext_code_hash
Proof
  rw[step_ext_code_hash_def] \\ tac
QED

Theorem limits_num_contexts_step_return_data_copy[simp]:
  limits_num_contexts n n step_return_data_copy
Proof
  rw[step_return_data_copy_def] \\ tac
QED

Theorem limits_num_contexts_step_block_hash[simp]:
  limits_num_contexts n n step_block_hash
Proof
  rw[step_block_hash_def] \\ tac
QED

Theorem limits_num_contexts_get_callee[simp]:
  limits_num_contexts n n get_callee
Proof
  rw[get_callee_def] \\ tac
QED

Theorem limits_num_contexts_step_self_balance[simp]:
  limits_num_contexts n n step_self_balance
Proof
  rw[step_self_balance_def] \\ tac
QED

Theorem limits_num_contexts_step_pop[simp]:
  limits_num_contexts n n step_pop
Proof
  rw[step_pop_def] \\ tac
QED

Theorem limits_num_contexts_step_mload[simp]:
  limits_num_contexts n n step_mload
Proof
  rw[step_mload_def] \\ tac
QED

Theorem limits_num_contexts_step_mstore[simp]:
  limits_num_contexts n n (step_mstore x)
Proof
  rw[step_mstore_def] \\ tac
QED

Theorem limits_num_contexts_get_tStorage[simp]:
  limits_num_contexts n n get_tStorage
Proof
  rw[get_tStorage_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_step_sload[simp]:
  limits_num_contexts n n (step_sload x)
Proof
  rw[step_sload_def] >> tac
QED

Theorem limits_num_contexts_get_rollback[simp]:
  limits_num_contexts n n get_rollback
Proof
  rw[get_rollback_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_set_jump_dest[simp]:
  limits_num_contexts n n (set_jump_dest x)
Proof
  rw[set_jump_dest_def] >> tac
QED

Theorem limits_num_contexts_step_jump[simp]:
  limits_num_contexts n n step_jump
Proof
  rw[step_jump_def] >> tac
QED

Theorem limits_num_contexts_step_jumpi[simp]:
  limits_num_contexts n n step_jumpi
Proof
  rw[step_jumpi_def] >> tac
QED

Theorem limits_num_contexts_step_push[simp]:
  limits_num_contexts n n (step_push x y)
Proof
  rw[step_push_def] >> tac
QED

Theorem limits_num_contexts_step_dup[simp]:
  limits_num_contexts n n (step_dup x)
Proof
  rw[step_dup_def] >> tac
QED

Theorem limits_num_contexts_step_swap[simp]:
  limits_num_contexts n n (step_swap x)
Proof
  rw[step_swap_def] >> tac
QED

Theorem limits_num_contexts_push_logs[simp]:
  limits_num_contexts n n (push_logs x)
Proof
  rw[push_logs_def] >> tac
QED

Theorem limits_num_contexts_get_static[simp]:
  limits_num_contexts n n get_static
Proof
  rw[get_static_def] >> tac
QED

Theorem limits_num_contexts_assert_not_static[simp]:
  limits_num_contexts n n assert_not_static
Proof
  rw[assert_not_static_def] >> tac
QED

Theorem limits_num_contexts_step_log[simp]:
  limits_num_contexts n n (step_log x)
Proof
  rw[step_log_def] >> tac
QED

Theorem limits_num_contexts_set_tStorage[simp]:
  limits_num_contexts n n (set_tStorage x)
Proof
  rw[set_tStorage_def, limits_num_contexts_def, return_def, all_accounts_def]
QED

Theorem limits_num_contexts_write_transient_storage[simp]:
  limits_num_contexts n n (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def] >> tac
QED

Theorem limits_num_contexts_write_storage[simp]:
  limits_num_contexts n n (write_storage x y z)
Proof
  rw[write_storage_def] >> tac
  \\ rw[limits_num_contexts_def, update_accounts_def, return_def]
QED

Theorem limits_num_contexts_update_gas_refund_def[simp]:
  limits_num_contexts n n (update_gas_refund x)
Proof
  Cases_on`x` >>
  rw[update_gas_refund_def] >>
  tac
QED

Theorem limits_num_contexts_get_original[simp]:
  limits_num_contexts n n get_original
Proof
  rw[get_original_def, limits_num_contexts_def]
  \\ rw[return_def, fail_def]
QED

Theorem limits_num_contexts_get_gas_left[simp]:
  limits_num_contexts n n get_gas_left
Proof
  rw[get_gas_left_def] >> tac
QED

Theorem limits_num_contexts_get_current_code[simp]:
  limits_num_contexts n n get_current_code
Proof
  rw[get_current_code_def] >> tac
QED

Theorem limits_num_contexts_get_num_contexts[simp]:
  limits_num_contexts n n get_num_contexts
Proof
  rw[get_num_contexts_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_get_value[simp]:
  limits_num_contexts n n get_value
Proof
  rw[get_value_def] >> tac
QED

Theorem limits_num_contexts_get_caller[simp]:
  limits_num_contexts n n get_caller
Proof
  rw[get_caller_def] >> tac
QED

Theorem limits_num_contexts_step_sstore_gas_consumption[simp]:
  limits_num_contexts n n (step_sstore_gas_consumption x y z)
Proof
  rw[step_sstore_gas_consumption_def] >> tac
QED

Theorem limits_num_contexts_step_sstore[simp]:
  limits_num_contexts n n (step_sstore x)
Proof
  rw[step_sstore_def] >> tac
QED

Theorem limits_num_contexts_finish[simp]:
  limits_num_contexts n n finish
Proof
  rw[finish_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_revert[simp]:
  limits_num_contexts n n revert
Proof
  rw[revert_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_set_return_data[simp]:
  limits_num_contexts n n (set_return_data x)
Proof
  rw[set_return_data_def] >> tac
QED

Theorem limits_num_contexts_step_return[simp]:
  limits_num_contexts n n (step_return x)
Proof
  rw[step_return_def] >> tac
QED

Theorem limits_num_contexts_step_invalid[simp]:
  limits_num_contexts n n step_invalid
Proof
  rw[step_invalid_def] >> tac
QED

Theorem limits_num_contexts_add_to_delete[simp]:
  limits_num_contexts n n (add_to_delete x)
Proof
  rw[add_to_delete_def, limits_num_contexts_def, return_def, all_accounts_def]
QED

Theorem limits_num_contexts_step_self_destruct[simp]:
  limits_num_contexts n n step_self_destruct
Proof
  rw[step_self_destruct_def] \\ tac
  \\ rw[update_accounts_def, limits_num_contexts_def,
        return_def]
QED

Theorem limits_num_contexts_unuse_gas[simp]:
  limits_num_contexts n n (unuse_gas x)
Proof
  rw[unuse_gas_def] >> tac
QED

Theorem limits_num_contexts_inc_pc[simp]:
  limits_num_contexts n n inc_pc
Proof
  rw[inc_pc_def] >> tac
QED

Theorem limits_num_contexts_abort_unuse[simp]:
  limits_num_contexts n n (abort_unuse x)
Proof
  rw[abort_unuse_def] >> tac
QED

Theorem limits_num_contexts_abort_call_value[simp]:
  limits_num_contexts n n (abort_call_value x)
Proof
  rw[abort_call_value_def] >> tac
QED

Theorem limits_num_contexts_push_context[simp]:
  limits_num_contexts n (SUC n) (push_context x)
Proof
  rw[push_context_def, limits_num_contexts_def, return_def, all_accounts_def]
QED

Theorem limits_num_contexts_update_accounts_transfer_value[simp]:
  limits_num_contexts n n (update_accounts (transfer_value x y z))
Proof
  rw[update_accounts_def, limits_num_contexts_def, return_def,
     all_accounts_def]
QED

Theorem limits_num_contexts_precompile_ecrecover[simp]:
  limits_num_contexts n n precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
QED

Theorem limits_num_contexts_precompile_ecadd[simp]:
  limits_num_contexts n n precompile_ecadd
Proof
  rw[precompile_ecadd_def]
QED

Theorem limits_num_contexts_precompile_ecmul[simp]:
  limits_num_contexts n n precompile_ecmul
Proof
  rw[precompile_ecmul_def]
QED

Theorem limits_num_contexts_precompile_ecpairing[simp]:
  limits_num_contexts n n precompile_ecpairing
Proof
  rw[precompile_ecpairing_def]
QED

Theorem limits_num_contexts_precompile_blake2f[simp]:
  limits_num_contexts n n precompile_blake2f
Proof
  rw[precompile_blake2f_def]
QED

Theorem limits_num_contexts_precompile_modexp[simp]:
  limits_num_contexts n n precompile_modexp
Proof
  rw[precompile_modexp_def] \\ tac
QED

Theorem limits_num_contexts_precompile_sha2_256[simp]:
  limits_num_contexts n n precompile_sha2_256
Proof
  rw[precompile_sha2_256_def] \\ tac
QED

Theorem limits_num_contexts_precompile_identity[simp]:
  limits_num_contexts n n precompile_identity
Proof
  rw[precompile_identity_def] \\ tac
QED

Theorem limits_num_contexts_precompile_ripemd_160[simp]:
  limits_num_contexts n n precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
QED

Theorem limits_num_contexts_dispatch_precompiles[simp]:
  limits_num_contexts n n (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem limits_num_contexts_mono:
  limits_num_contexts n1 n2 f ∧ n0 ≤ n1 ∧ n2 ≤ n3 ⇒
  limits_num_contexts n0 n3 f
Proof
  rw[limits_num_contexts_def]
  \\ first_x_assum(qspec_then`s`mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_check:
  (n > m ⇒ limits_num_contexts n n2 f) ∧
  (∀n1. n1 ≤ (MIN (PRE n) m) ⇒ limits_num_contexts (SUC n1) n2 g)
  ⇒
  limits_num_contexts n n2 (do
    sd <- get_num_contexts;
    if sd > m then f else g
  od)
Proof
  rw[limits_num_contexts_def, bind_def, ignore_bind_def,
     get_num_contexts_def, return_def, ensure_storage_in_domain_def,
     assert_def]
  \\ rw[] \\ gvs[]
  \\ first_x_assum irule
  \\ Cases_on`n ≤ m` \\ gs[]
  >- (qexists_tac`PRE n` \\ gs[])
  \\ qexists_tac`m` \\ gs[]
QED

Theorem limits_num_contexts_step_call:
  0 < n ∧ n ≤ context_limit + 2 ⇒
  limits_num_contexts n (MIN (SUC n) (context_limit + 2)) (step_call x)
Proof
  strip_tac
  \\ gs[step_call_def, UNCURRY]
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ qpat_abbrev_tac`b4 = COND _ _ _`
  \\ qpat_abbrev_tac`b5 = COND _ _ _`
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ qpat_abbrev_tac`b6 = COND _ _ _`
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ rw[Abbr`b5`]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ rw[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ rw[]
  >- ( irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ rw[]
  \\ irule limits_num_contexts_check \\ simp[]
  \\ reverse conj_tac
  >- (
    strip_tac
    \\ irule limits_num_contexts_mono
    \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  \\ gen_tac \\ strip_tac
  \\ simp[proceed_call_def]
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ reverse conj_tac >- rw[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind
  \\ qexists_tac`SUC (SUC n1)`
  \\ gs[]
  \\ irule limits_num_contexts_mono
  \\ qexistsl_tac[`n1 + 2`,`n1 + 2`] \\ rw[]
QED

Theorem limits_num_contexts_ensure_storage_in_domain[simp]:
  limits_num_contexts n n (ensure_storage_in_domain _)
Proof
  rw[limits_num_contexts_def, ensure_storage_in_domain_def, assert_def,
     domain_check_def]
  \\ Cases_on`s.msdomain` \\ gs[bind_def, ignore_bind_def, set_domain_def]
  \\ rw[return_def, fail_def]
QED

Theorem limits_num_contexts_reorder_ensure_storage:
  limits_num_contexts x y
  do
    sucDepth <- get_num_contexts;
    ensure_storage_in_domain a;
    f sucDepth
  od ⇔
  limits_num_contexts x y
  do
    ensure_storage_in_domain a;
    sucDepth <- get_num_contexts;
    f sucDepth
  od
Proof
  rw[limits_num_contexts_def, bind_def, ignore_bind_def, get_num_contexts_def,
     ensure_storage_in_domain_def, assert_def, return_def, domain_check_def]
  \\ rw[EQ_IMP_THM] \\ first_x_assum drule
  \\ Cases_on`s.msdomain` \\ gs[fail_def, set_domain_def, return_def]
  \\ rw[]
QED

Theorem limits_num_contexts_step_create:
  0 < n ∧ n ≤ context_limit + 2 ⇒
  limits_num_contexts n (MIN (SUC n) (context_limit + 2)) (step_create x)
Proof
  strip_tac
  \\ gs[step_create_def]
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ qpat_abbrev_tac`b4 = COND _ _ _`
  \\ qmatch_goalsub_abbrev_tac`b5 ∨ _`
  \\ Cases_on`b5` \\ gs[]
  >- (
    irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[]
    \\ tac )
  \\ qmatch_goalsub_abbrev_tac`b5 ∨ _`
  \\ Cases_on`b5` \\ gs[]
  >- (
    irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[]
    \\ tac )
  \\ simp[limits_num_contexts_reorder_ensure_storage]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_check
  \\ reverse conj_tac
  >- (
    strip_tac
    \\ irule limits_num_contexts_mono
    \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  \\ gen_tac \\ strip_tac
  \\ simp[Abbr`b4`]
  \\ `SUC n1 ≤ n` by gs[]
  \\ `n ≤ MIN (SUC n) 1026` by gs[]
  \\ IF_CASES_TAC
  >- (
    irule limits_num_contexts_mono
    \\ qexistsl_tac[`n`,`n`] \\ simp[]
    \\ rw[abort_create_exists_def]
    \\ tac
    \\ rw[limits_num_contexts_def, update_accounts_def, return_def])
  \\ simp[proceed_create_def]
  \\ qpat_abbrev_tac`b4 = COND _ _ _`
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ reverse conj_tac >- rw[limits_num_contexts_def, update_accounts_def, return_def]
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ reverse conj_tac >- rw[limits_num_contexts_def, update_accounts_def, return_def]
  \\ irule limits_num_contexts_mono
  \\ qexistsl_tac[`SUC n1`,`SUC(SUC n1)`] \\ rw[]
  \\ gs[]
QED

Theorem limits_num_contexts_step_inst:
  n = context_limit + 2 ⇒
  limits_num_contexts n n (step_inst op)
Proof
  Cases_on`op` \\ rw[step_inst_def]
  >- (irule limits_num_contexts_ignore_bind_same \\ rw[])
  \\ `MIN (SUC 1026) (context_limit + 2) = 1026` by rw[]
  \\ `0 < 1026` by rw[]
  \\ `1026 ≤ context_limit + 2` by rw[]
  \\ drule_at Any limits_num_contexts_step_create \\ simp[]
  \\ drule_at Any limits_num_contexts_step_call \\ simp[]
QED

Theorem limits_num_contexts_handle:
  limits_num_contexts n n f ∧
  (∀e. limits_num_contexts n n (g e))
  ⇒
  limits_num_contexts n n (handle f g)
Proof
  rw[handle_def, limits_num_contexts_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem limits_num_contexts_get_output_to[simp]:
  limits_num_contexts n n get_output_to
Proof
  rw[get_output_to_def] \\ tac
QED

Theorem limits_num_contexts_pop_and_incorporate_context[simp]:
  limits_num_contexts n n (pop_and_incorporate_context x)
Proof
  rw[pop_and_incorporate_context_def]
  \\ tac
  \\ rw[bind_def, ignore_bind_def, pop_context_def, unuse_gas_def,
        limits_num_contexts_def, fail_def, return_def, assert_def,
        get_current_context_def, set_current_context_def, update_gas_refund_def,
        push_logs_def, set_rollback_def]
  \\ rw[] \\ rw[]
  \\ Cases_on`s.contexts` \\ gs[]
QED

Theorem limits_num_contexts_reraise[simp]:
  limits_num_contexts n n (reraise e)
Proof
  rw[reraise_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_step[simp]:
  n = context_limit + 2 ⇒
  limits_num_contexts n n step
Proof
  rw[step_def]
  \\ irule limits_num_contexts_handle
  \\ reverse conj_tac
  >- (
    irule limits_num_contexts_bind_same \\ rw[]
    >- ( irule limits_num_contexts_step_inst \\ rw[] )
    \\ CASE_TAC \\ rw[]
    >- ( irule limits_num_contexts_step_inst \\ rw[] )
    \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
    \\ TRY ( irule limits_num_contexts_step_inst \\ rw[] )
    \\ rw[inc_pc_or_jump_def]
    \\ tac
    \\ CASE_TAC \\ rw[]
    \\ tac)
  \\ rw[handle_step_def]
  \\ irule limits_num_contexts_handle
  \\ conj_tac
  >- (
    simp[handle_exception_def] \\ gen_tac
    \\ irule limits_num_contexts_ignore_bind_same
    \\ reverse conj_tac
    >- ( rw[] \\ tac )
    \\ irule limits_num_contexts_bind_same \\ rw[]
    \\ irule limits_num_contexts_bind_same \\ rw[]
    \\ irule limits_num_contexts_bind_same \\ rw[]
    \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
    \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
    \\ CASE_TAC \\ rw[] \\ CASE_TAC \\ rw[]
    \\ tac )
  \\ rw[handle_create_def]
  \\ tac
  \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ tac
  >- rw[limits_num_contexts_def, update_accounts_def, return_def]
  \\ rw[limits_num_contexts_def, assert_def, bind_def, update_accounts_def,
        ignore_bind_def, return_def, reraise_def]
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

Definition subdomain_def:
  subdomain s1 s2 ⇔
  toSet s1.addresses ⊆ toSet s2.addresses ∧
  toSet s1.storageKeys ⊆ toSet s2.storageKeys ∧
  toSet s1.fullStorages ⊆ toSet s2.fullStorages
End

Definition accounts_agree_modulo_storage_def:
  accounts_agree_modulo_storage addr (a1:evm_accounts) a2 ⇔
  a1 addr = a2 addr with storage := (a1 addr).storage
End

Theorem accounts_agree_modulo_storage_refl[simp]:
  accounts_agree_modulo_storage x a a
Proof
  rw[accounts_agree_modulo_storage_def,
     account_state_component_equality]
QED

Theorem accounts_agree_modulo_storage_trans:
  accounts_agree_modulo_storage a a1 a2 ∧
  accounts_agree_modulo_storage a a2 a3 ⇒
  accounts_agree_modulo_storage a a1 a3
Proof
  rw[accounts_agree_modulo_storage_def]
  \\ gvs[account_state_component_equality]
QED

Definition rollback_states_agree_modulo_accounts_def:
  rollback_states_agree_modulo_accounts r1 r2 ⇔
  r1 = r2 with accounts := r1.accounts
End

Theorem rollback_states_agree_modulo_accounts_refl[simp]:
  rollback_states_agree_modulo_accounts r r
Proof
  rw[rollback_states_agree_modulo_accounts_def,
     rollback_state_component_equality]
QED

Theorem rollback_states_agree_modulo_accounts_trans:
  rollback_states_agree_modulo_accounts r1 r2 ∧
  rollback_states_agree_modulo_accounts r2 r3 ⇒
  rollback_states_agree_modulo_accounts r1 r3
Proof
  rw[rollback_states_agree_modulo_accounts_def]
  \\ gvs[rollback_state_component_equality]
QED

Definition states_agree_modulo_accounts_def:
  states_agree_modulo_accounts s1 s2 ⇔
  s1.txParams = s2.txParams ∧
  s1.msdomain = s2.msdomain ∧
  rollback_states_agree_modulo_accounts s1.rollback s2.rollback ∧
  MAP FST s1.contexts = MAP FST s2.contexts ∧
  LIST_REL rollback_states_agree_modulo_accounts
    (MAP SND s1.contexts) (MAP SND s2.contexts)
End

Theorem states_agree_modulo_accounts_refl[simp]:
  states_agree_modulo_accounts s s
Proof
  rw[states_agree_modulo_accounts_def]
  \\ irule EVERY2_refl \\ rw[]
QED

Theorem states_agree_modulo_accounts_trans:
  states_agree_modulo_accounts s1 s2 ∧
  states_agree_modulo_accounts s2 s3 ⇒
  states_agree_modulo_accounts s1 s3
Proof
  rw[states_agree_modulo_accounts_def]
  \\ metis_tac[rollback_states_agree_modulo_accounts_trans, LIST_REL_trans]
QED

Definition domain_compatible_def:
  domain_compatible s1 s2 ⇔
  states_agree_modulo_accounts s1 s2 ∧
  case s1.msdomain of Enforce d =>
  (∀addr.
       fIN addr d.addresses ⇒
       LIST_REL (accounts_agree_modulo_storage addr)
         (all_accounts s1) (all_accounts s2)) ∧
  (∀addr key.
       fIN (SK addr key) d.storageKeys ⇒
       LIST_REL (λa1 a2. (a1 addr).storage key = (a2 addr).storage key)
         (all_accounts s1) (all_accounts s2)) ∧
  (∀addr.
       fIN addr d.fullStorages ⇒
       LIST_REL (λa1 a2. (a1 addr).storage = (a2 addr).storage)
         (all_accounts s1) (all_accounts s2))
  | _ => T
End

Theorem domain_compatible_refl[simp]:
  domain_compatible x x
Proof
  rw[domain_compatible_def, domain_check_def]
  \\ TOP_CASE_TAC \\ rw[]
  \\ irule EVERY2_refl
  \\ rw[]
QED

Theorem domain_compatible_trans:
  domain_compatible s1 s2 ∧
  domain_compatible s2 s3 ⇒
  domain_compatible s1 s3
Proof
  rw[domain_compatible_def, domain_check_def]
  >- metis_tac[states_agree_modulo_accounts_trans]
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC \\ gvs[]
  \\ gvs[states_agree_modulo_accounts_def]
  \\ rw[] \\ irule LIST_REL_trans \\ gs[]
  \\ qexists_tac`all_accounts s2`
  \\ gvs[]
  \\ metis_tac[accounts_agree_modulo_storage_trans]
QED

Theorem domain_compatible_lengths:
  domain_compatible s1 s2 ⇒
  LENGTH s1.contexts = LENGTH s2.contexts
Proof
  rw[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gs[LIST_REL_EL_EQN]
QED

Definition domain_has_callee_def:
  domain_has_callee s ⇔
  ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses
End

Definition preserves_domain_has_callee_def:
  preserves_domain_has_callee p f ⇔
  ∀s r t. p s ∧ domain_has_callee s ∧ f s = (r, t) ⇒
          domain_has_callee t
End

Definition ignores_extra_domain_pred_def:
  ignores_extra_domain_pred p m ⇔
  ∀s r t d1. p s ∧ m s = (r, t) ∧ s.msdomain = Enforce d1 ⇒
    t.msdomain = s.msdomain ∧
    ((∀x. r ≠ INR $ SOME $ OutsideDomain x) ⇒
      ∀d2. subdomain d1 d2 ⇒
        m (s with msdomain := Enforce d2) = (r, t with msdomain := Enforce d2)) ∧
    (∀s'. domain_compatible s s' ⇒
          ∃t'. domain_compatible t t' ∧ m s' = (r, t'))
End

Definition ignores_extra_domain_def:
  ignores_extra_domain (m: α execution) =
  ignores_extra_domain_pred (K T) m
End

val ignores_extra_domain_def =
  SIMP_RULE std_ss [ignores_extra_domain_pred_def]
  ignores_extra_domain_def

Theorem handle_ignores_extra_domain_pred_allow:
  ignores_extra_domain_pred p f ∧
  (∀s. p s ⇒ p (SND (f s))) ∧
  (∀e. if (∃x. e = SOME (OutsideDomain x))
       then (∀s d. s.msdomain = Enforce d ⇒
             ∃t. (g e) s = (INR e, t) ∧
             t.msdomain = s.msdomain ∧
             (∀s'. domain_compatible s s' ⇒
              ∃t'. (g e) s' = (INR e, t') ∧
                    domain_compatible t t'))
       else ignores_extra_domain_pred p (g e))
  ⇒
  ignores_extra_domain_pred p (handle f g)
Proof
  simp[handle_def, ignores_extra_domain_pred_def]
  \\ strip_tac \\ rpt gen_tac
  \\ gvs[CaseEq"prod",CaseEq"sum",IS_SOME_EXISTS]
  \\ strip_tac \\ gvs[]
  >- (
    first_x_assum(drule_then drule)
    \\ simp[] \\ strip_tac
    \\ gen_tac \\ strip_tac
    \\ first_x_assum drule \\ strip_tac
    \\ goal_assum drule \\ simp[] )
  \\ conj_asm1_tac >- (
    last_x_assum (drule_then drule) \\ rw[]
    \\ first_x_assum(qspec_then`e`mp_tac)
    \\ rw[PULL_EXISTS] \\ gs[]
    \\ last_x_assum drule \\ rw[]
    \\ last_x_assum drule \\ rw[])
  \\ conj_tac
  >- (
    rw[]
    \\ first_x_assum(drule_then drule) \\ rw[]
    \\ first_x_assum(qspec_then`e`mp_tac)
    \\ rw[]
    >- ( first_x_assum(qspec_then`s'`mp_tac) \\ rw[] )
    \\ gs[]
    \\ first_x_assum(qspec_then`s'`mp_tac)
    \\ simp[]
    \\ impl_tac >- metis_tac[SND]
    \\ rw[] )
  \\ rw[]
  \\ first_x_assum(drule_then drule) \\ rw[]
  \\ first_x_assum(qspec_then`e`mp_tac)
  \\ rw[]
  >- (
    first_x_assum drule \\ rw[] \\ rw[]
    \\ first_assum(qspec_then`s'`mp_tac)
    \\ impl_tac >- rw[] \\ strip_tac
    \\ gvs[]
    \\ first_x_assum drule \\ rw[] \\ simp[]
    \\ first_x_assum drule \\ rw[] \\ rw[])
  \\ gs[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ rw[]
QED

Theorem handle_ignores_extra_domain:
  ignores_extra_domain f ∧
  (∀s x. FST (f s) ≠ INR (SOME (OutsideDomain x))) ∧
  (∀e. (∀x. e ≠ SOME (OutsideDomain x)) ⇒ ignores_extra_domain (g e))
  ⇒
  ignores_extra_domain (handle f g)
Proof
  rw[handle_def, ignores_extra_domain_def]
  \\ gvs[CaseEq"prod",CaseEq"sum"]
  \\ first_x_assum drule \\ gs[]
  \\ first_x_assum(qspec_then`e`mp_tac) \\ rw[]
  \\ gs[]
  \\ metis_tac[PAIR_EQ, FST]
QED

Theorem bind_ignores_extra_domain:
  ignores_extra_domain g ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind g f)
Proof
  simp[ignores_extra_domain_def, bind_def]
  \\ ntac 2 strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ gs[CaseEq"prod"]
  \\ first_x_assum drule
  \\ strip_tac \\ gs[CaseEq"sum"]
  \\ TRY (first_x_assum (drule_at Any) \\ simp[])
  \\ rpt strip_tac \\ gvs[]
  \\ TRY (first_x_assum (drule_at Any) \\ simp[])
  \\ rpt strip_tac \\ gvs[]
  \\ TRY (first_x_assum (drule_at Any) \\ simp[])
  \\ rpt strip_tac \\ gvs[]
QED

Theorem ignore_bind_ignores_extra_domain:
  ignores_extra_domain g ∧
  ignores_extra_domain f
  ⇒
  ignores_extra_domain (ignore_bind g f)
Proof
  simp[ignore_bind_def]
  \\ strip_tac
  \\ irule bind_ignores_extra_domain
  \\ rw[]
QED

Theorem ignores_extra_domain_pred_imp:
  ignores_extra_domain f ⇒
  ignores_extra_domain_pred p f
Proof
  rw[ignores_extra_domain_def, ignores_extra_domain_pred_def]
  \\ metis_tac[]
QED

Theorem ignores_extra_domain_imp_pred_bind:
  (∀s s'. p s ⇒ p (SND (g s))) ∧
  ignores_extra_domain g ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind g f)
Proof
  rw[ignores_extra_domain_pred_def, bind_def,
     ignores_extra_domain_def]
  \\ gvs[CaseEq"prod", CaseEq"sum"]
  \\ last_x_assum drule
  \\ last_x_assum drule
  \\ rw[]
  \\ TRY (first_x_assum (drule_then drule))
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem ignores_extra_domain_imp_pred_pred_bind:
  (∀s s'. p s ⇒ p (SND (g s))) ∧
  ignores_extra_domain_pred p g ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind g f)
Proof
  rw[ignores_extra_domain_pred_def, bind_def,
     ignores_extra_domain_def]
  \\ gvs[CaseEq"prod", CaseEq"sum"]
  \\ last_x_assum drule
  \\ last_x_assum drule
  \\ rw[]
  \\ TRY (first_x_assum (drule_then drule))
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem return_ignores_extra_domain[simp]:
  ignores_extra_domain (return x)
Proof
  rw[return_def, ignores_extra_domain_def]
QED

val tac = rpt (
  (irule bind_ignores_extra_domain \\ rw[]) ORELSE
  (irule ignore_bind_ignores_extra_domain \\ rw[])
);

Theorem get_current_context_ignores_extra_domain[simp]:
  ignores_extra_domain get_current_context
Proof
  simp[get_current_context_def, ignores_extra_domain_def]
  \\ rw[fail_def, return_def]
  \\ goal_assum drule \\ rw[]
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[] \\ Cases_on`s'.contexts` \\ gs[]
QED

Theorem get_gas_left_ignores_extra_domain[simp]:
  ignores_extra_domain get_gas_left
Proof
  rw[get_gas_left_def] \\ tac
QED

Theorem assert_ignores_extra_domain[simp]:
  ignores_extra_domain (assert e n)
Proof
  rw[assert_def, ignores_extra_domain_def]
QED

Theorem set_current_context_ignores_extra_domain[simp]:
  ignores_extra_domain (set_current_context c)
Proof
  rw[set_current_context_def, ignores_extra_domain_def, fail_def, return_def]
  \\ gvs[CaseEq"prod",CaseEq"bool"]
  \\ drule domain_compatible_lengths \\ rw[]
  \\ TRY strip_tac \\ gvs[]
  \\ gs[domain_compatible_def]
  \\ gs[all_accounts_def, states_agree_modulo_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[]
  \\ Cases_on`s'.contexts` \\ gvs[]
  \\ metis_tac[]
QED

Theorem consume_gas_ignores_extra_domain[simp]:
  ignores_extra_domain (consume_gas n)
Proof
  rw[consume_gas_def] \\ tac
QED

Theorem set_return_data_ignores_extra_domain[simp]:
  ignores_extra_domain (set_return_data n)
Proof
  rw[set_return_data_def] \\ tac
QED

Theorem reraise_ignores_extra_domain[simp]:
  ignores_extra_domain (reraise n)
Proof
  rw[reraise_def, ignores_extra_domain_def]
QED

Theorem inc_pc_ignores_extra_domain[simp]:
  ignores_extra_domain inc_pc
Proof
  rw[inc_pc_def] \\ tac
QED

Theorem get_output_to_ignores_extra_domain[simp]:
  ignores_extra_domain get_output_to
Proof
  rw[get_output_to_def] \\ tac
QED

Theorem get_return_data_ignores_extra_domain[simp]:
  ignores_extra_domain get_return_data
Proof
  rw[get_return_data_def] \\ tac
QED

Theorem get_num_contexts_ignores_extra_domain[simp]:
  ignores_extra_domain get_num_contexts
Proof
  rw[get_num_contexts_def, ignores_extra_domain_def, return_def]
  \\ irule EQ_SYM \\ irule domain_compatible_lengths \\ rw[]
QED

Theorem unuse_gas_ignores_extra_domain[simp]:
  ignores_extra_domain (unuse_gas n)
Proof
  rw[unuse_gas_def] \\ tac
QED

Theorem push_logs_ignores_extra_domain[simp]:
  ignores_extra_domain (push_logs n)
Proof
  rw[push_logs_def] \\ tac
QED

Theorem push_stack_ignores_extra_domain[simp]:
  ignores_extra_domain (push_stack n)
Proof
  rw[push_stack_def] \\ tac
QED

Theorem update_gas_refund_ignores_extra_domain[simp]:
  ignores_extra_domain (update_gas_refund n)
Proof
  Cases_on`n` \\ rw[update_gas_refund_def] \\ tac
QED

Theorem FST_pop_context_ignores_extra_domain:
  (∀x y. FST x = FST y ⇒ f x = f y) ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind pop_context f)
Proof
  rw[ignores_extra_domain_def, bind_def, CaseEq"prod", CaseEq"sum"]
  \\ TRY(first_x_assum drule \\ rw[])
  \\ gvs[pop_context_def, CaseEq"bool", fail_def, return_def]
  >- (
    srw_tac[DNF_ss][]
    \\ qmatch_goalsub_abbrev_tac`f _ ss`
    \\ first_x_assum(qspec_then`ss`mp_tac)
    \\ impl_tac >- (
      gvs[Abbr`ss`, domain_compatible_def, all_accounts_def]
      \\ gvs[states_agree_modulo_accounts_def]
      \\ Cases_on`s.contexts` \\ gvs[]
      \\ qmatch_goalsub_rename_tac`TL ss.contexts`
      \\ Cases_on`ss.contexts` \\ gvs[]
      \\ gs[domain_check_def] \\ TOP_CASE_TAC \\ gs[])
    \\ strip_tac
    \\ disj2_tac
    \\ goal_assum drule
    \\ conj_tac
    >- (strip_tac \\ gs[domain_compatible_def, states_agree_modulo_accounts_def])
    \\ irule EQ_SYM
    \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ AP_THM_TAC
    \\ first_x_assum irule
    \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`HD s2.contexts`
    \\ Cases_on`s2.contexts` \\ gvs[] )
  \\ srw_tac[DNF_ss][]
  \\ disj1_tac
  \\ drule domain_compatible_lengths
  \\ rw[]
QED

Theorem pop_and_incorporate_context_ignores_extra_domain[simp]:
  ignores_extra_domain (pop_and_incorporate_context x)
Proof
  rw[pop_and_incorporate_context_def]
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ Cases_on`x` \\ rw[]
  >- (
    irule FST_pop_context_ignores_extra_domain \\ rw[]
    \\ tac )
  \\ rw[bind_def, ignores_extra_domain_def, ignore_bind_def,
        pop_context_def, unuse_gas_def, set_rollback_def, return_def,
        fail_def, get_current_context_def, set_current_context_def,
        assert_def, CaseEq"prod", CaseEq"sum", CaseEq"bool"]
  \\ srw_tac[DNF_ss][] \\ gvs[]
  \\ drule domain_compatible_lengths \\ rw[]
  \\ TRY (strip_tac \\ gvs[])
  \\ TRY (Cases_on`s.contexts` \\ gvs[])
  \\ qmatch_asmsub_rename_tac`domain_compatible s s2`
  \\ Cases_on`s2.contexts` \\ gvs[]
  \\ TRY (
    gs[domain_compatible_def, states_agree_modulo_accounts_def,
       all_accounts_def, domain_check_def]
    \\ TOP_CASE_TAC \\ gs[]
    \\ qmatch_goalsub_rename_tac`FST (HD ls)`
    \\ Cases_on`ls` \\ gs[]
    \\ qmatch_asmsub_rename_tac`MAP FST ls = _::_`
    \\ Cases_on`ls` \\ gvs[]
    \\ NO_TAC)
  \\ Cases_on`t` \\ gvs[]
  \\ qmatch_goalsub_rename_tac`HD t`
  \\ Cases_on`t` \\ gvs[]
  \\ qmatch_goalsub_rename_tac`FST p`
  \\ Cases_on`p` \\ gvs[]
  \\ TRY (qmatch_goalsub_rename_tac`FST p`
          \\ Cases_on`p` \\ gvs[])
  \\ gvs[domain_compatible_def, domain_check_def]
  \\ TRY TOP_CASE_TAC
  \\ gvs[states_agree_modulo_accounts_def]
  \\ gvs[all_accounts_def]
QED

Theorem write_memory_ignores_extra_domain[simp]:
  ignores_extra_domain (write_memory n m)
Proof
  rw[write_memory_def] \\ tac
QED

Theorem handle_exception_ignores_extra_domain[simp]:
  ignores_extra_domain (handle_exception e)
Proof
  simp[handle_exception_def]
  \\ irule ignore_bind_ignores_extra_domain
  \\ conj_tac
  >- ( rw[] \\ tac )
  \\ tac
  \\ BasicProvers.TOP_CASE_TAC
  >- tac
  \\ rw[]
  \\ tac
QED

Theorem handle_create_ignores_extra_domain[simp]:
  ignores_extra_domain (handle_create e)
Proof
  simp[handle_create_def]
  \\ tac
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ tac
  \\ rw[ignores_extra_domain_def, update_accounts_def, return_def]
  \\ gvs[domain_compatible_def, all_accounts_def, update_account_def,
         lookup_account_def, APPLY_UPDATE_THM, states_agree_modulo_accounts_def,
         rollback_states_agree_modulo_accounts_def, domain_check_def,
         rollback_state_component_equality, accounts_agree_modulo_storage_def,
         account_state_component_equality]
  \\ TOP_CASE_TAC \\ gs[]
  \\ rw[]
QED

Theorem handle_step_ignores_extra_domain[simp]:
  ignores_extra_domain (handle_step e)
Proof
  rw[handle_step_def]
  \\ irule handle_ignores_extra_domain
  \\ rw[]
  \\ rw[handle_create_def, bind_def, ignore_bind_def, get_return_data_def,
        get_output_to_def, get_current_context_def, fail_def, return_def]
  \\ BasicProvers.TOP_CASE_TAC \\ rw[reraise_def]
  >- (strip_tac \\ gs[])
  \\ BasicProvers.TOP_CASE_TAC \\ rw[reraise_def]
  \\ rw[assert_def, bind_def, reraise_def, consume_gas_def,
        get_current_context_def, return_def, ignore_bind_def,
        set_current_context_def, update_accounts_def]
  >- (strip_tac \\ gs[])
QED

Theorem inc_pc_or_jump_ignores_extra_domain[simp]:
  ignores_extra_domain (inc_pc_or_jump x)
Proof
  rw[inc_pc_or_jump_def]
  \\ tac
  \\ BasicProvers.TOP_CASE_TAC
  \\ tac \\ rw[]
QED

Theorem finish_ignore_extra_domain[simp]:
  ignores_extra_domain finish
Proof
  rw[finish_def, ignores_extra_domain_def]
QED

Theorem pop_stack_ignores_extra_domain[simp]:
  ignores_extra_domain (pop_stack n)
Proof
  rw[pop_stack_def] \\ tac
QED

Theorem step_binop_ignore_extra_domain[simp]:
  ignores_extra_domain (step_binop x y)
Proof
  rw[step_binop_def] \\ tac
QED

Theorem step_modop_ignore_extra_domain[simp]:
  ignores_extra_domain (step_modop x y)
Proof
  rw[step_modop_def] \\ tac
QED

Theorem step_monop_ignore_extra_domain[simp]:
  ignores_extra_domain (step_monop x y)
Proof
  rw[step_monop_def] \\ tac
QED

Theorem step_context_ignore_extra_domain[simp]:
  ignores_extra_domain (step_context x y)
Proof
  rw[step_context_def] \\ tac
QED

Theorem step_msgParams_ignore_extra_domain[simp]:
  ignores_extra_domain (step_msgParams x y)
Proof
  rw[step_msgParams_def] \\ tac
QED

Theorem get_accounts_ignore_extra_domain_slot_bind:
  (∀x y s d. s.msdomain = Enforce d ∧
    (∀a k. fIN (SK a k) d.storageKeys ⇒
           (x a).storage k = (y a).storage k) ⇒
         f x s = f y s) ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind get_accounts f)
Proof
  rw[bind_def, get_accounts_def, ignores_extra_domain_def, return_def]
  >- metis_tac[]
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ goal_assum drule
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ irule EQ_SYM
  \\ first_x_assum irule
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def,
        domain_check_def]
  \\ rw[] \\ gs[all_accounts_def]
  \\ qexists_tac`d1` \\ gs[]
QED

Theorem get_accounts_ignore_extra_domain_pred_bind:
  (∀x y s d. p s ∧ s.msdomain = Enforce d ∧
    (∀a. fIN a d.addresses ⇒ accounts_agree_modulo_storage a x y) ∧
    (∀a. fIN a d.fullStorages ⇒ (x a).storage = (y a).storage)
    ⇒ f x s = f y s) ∧
  (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_accounts f)
Proof
  rw[bind_def, get_accounts_def, ignores_extra_domain_pred_def, return_def]
  >- metis_tac[]
  \\ first_x_assum (drule_then drule) \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ goal_assum drule
  \\ `p s'` by metis_tac[]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ irule EQ_SYM
  \\ first_x_assum irule
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def,
        domain_check_def]
  \\ rw[] \\ gs[all_accounts_def]
  \\ qexists_tac`d1` \\ gs[]
QED

Theorem get_accounts_ignore_extra_domain_slot_pred_bind:
  (∀x y s d. p s ∧ s.msdomain = Enforce d ∧
    (∀a k. fIN (SK a k) d.storageKeys ⇒
           (x a).storage k = (y a).storage k) ⇒
         f x s = f y s) ∧
  (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
  (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_accounts f)
Proof
  rw[bind_def, get_accounts_def, ignores_extra_domain_pred_def, return_def]
  >- metis_tac[]
  \\ first_x_assum (drule_then drule) \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ goal_assum drule
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ irule EQ_SYM
  \\ first_x_assum irule
  \\ conj_asm1_tac >- metis_tac[]
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def,
        domain_check_def]
  \\ rw[] \\ gs[all_accounts_def]
  \\ qexists_tac`d1` \\ gs[]
QED

Theorem access_address_ignore_extra_domain[simp]:
  ignores_extra_domain (access_address x)
Proof
  rw[access_address_def, ignores_extra_domain_def, return_def, fail_def,
     domain_check_def]
  \\ gvs[CaseEq"bool", CaseEq"domain_mode"]
  \\ gs[subdomain_def, SUBSET_DEF, fIN_IN]
  \\ `cold_access_cost ≠ warm_access_cost` by EVAL_TAC
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def,
        rollback_states_agree_modulo_accounts_def, domain_check_def,
        rollback_state_component_equality, all_accounts_def]
  \\ CASE_TAC \\ gvs[]
QED

Theorem access_slot_ignore_extra_domain[simp]:
  ignores_extra_domain (access_slot x)
Proof
  rw[access_slot_def, ignores_extra_domain_def, return_def, fail_def,
     domain_check_def]
  \\ gvs[CaseEq"bool", CaseEq"domain_mode"]
  \\ gs[subdomain_def, SUBSET_DEF, fIN_IN]
   \\ `cold_sload_cost ≠ warm_access_cost` by EVAL_TAC
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def,
        rollback_states_agree_modulo_accounts_def, domain_check_def,
        rollback_state_component_equality, all_accounts_def]
  \\ CASE_TAC \\ gvs[]
QED

Theorem access_address_ignore_extra_domain_bind:
  (∀x. ignores_extra_domain_pred (λs. ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.addresses) (f x))
  ⇒
  ignores_extra_domain (monad_bind (access_address a) f)
Proof
  rw[access_address_def, ignores_extra_domain_def, return_def, fail_def,
     ignores_extra_domain_pred_def, bind_def, domain_check_def]
  \\ gvs[CaseEq"bool", CaseEq"prod", CaseEq"sum", CaseEq"option",
         CaseEq"domain_mode"]
  \\ gs[subdomain_def, SUBSET_DEF, fIN_IN]
  \\ `cold_access_cost ≠ warm_access_cost` by EVAL_TAC
  \\ TRY(first_x_assum (drule_at (Pat`f _ _ = _`)) \\ rw[])
  \\ TRY(
     gs[domain_compatible_def, states_agree_modulo_accounts_def,
        rollback_states_agree_modulo_accounts_def,
        rollback_state_component_equality, all_accounts_def]
     \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]
     \\ NO_TAC)
  \\ fsrw_tac[DNF_ss][]
  \\ qmatch_goalsub_abbrev_tac`f _ ss`
  \\ first_x_assum(qspec_then`ss`mp_tac)
  \\ ( reverse impl_tac
  >- (
    strip_tac
    \\ disj1_tac \\ disj1_tac
    \\ goal_assum drule
    \\ rw[]
    \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]) )
  \\ gs[domain_compatible_def, Abbr`ss`, all_accounts_def]
  \\ gs[states_agree_modulo_accounts_def,
        rollback_states_agree_modulo_accounts_def]
  \\ gs[rollback_state_component_equality]
QED

Theorem access_address_ignore_extra_domain_pred_bind:
  (∀x. ignores_extra_domain_pred
       (λs. q s ∧ ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.addresses)
       (f x)) ∧
  (∀s. q s ⇒ q (SND (access_address a s)))
  ⇒
  ignores_extra_domain_pred q (monad_bind (access_address a) f)
Proof
  rw[access_address_def, ignores_extra_domain_def, return_def, fail_def,
     ignores_extra_domain_pred_def, bind_def, domain_check_def]
  \\ gvs[CaseEq"bool", CaseEq"prod", CaseEq"sum", CaseEq"domain_mode"]
  \\ gs[subdomain_def, SUBSET_DEF, fIN_IN]
  \\ `cold_access_cost ≠ warm_access_cost` by EVAL_TAC
  \\ TRY(first_x_assum (drule_at (Pat`f _ _ = _`)) \\ rw[])
  \\ fsrw_tac[DNF_ss][]
  \\ TRY(
     gs[domain_compatible_def, states_agree_modulo_accounts_def,
        rollback_states_agree_modulo_accounts_def, domain_check_def,
        rollback_state_component_equality, all_accounts_def]
     \\ first_x_assum drule \\ rw[]
     \\ first_x_assum irule \\ rw[] \\ gvs[]
     \\ NO_TAC)
  \\ TRY (
    gs[domain_compatible_def, states_agree_modulo_accounts_def,
       set_domain_def, ignore_bind_def, bind_def, return_def]
    \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]
    \\ NO_TAC)
  \\ qmatch_goalsub_abbrev_tac`f _ ss`
  \\ first_x_assum(qspec_then`ss`mp_tac)
  \\ (impl_tac >- (
    first_x_assum drule \\ rw[]
    \\ first_x_assum drule \\ rw[]
    \\ gvs[domain_check_def]
    \\ gs[domain_compatible_def]
    ))
  \\ TRY (
    gs[domain_check_def]
    \\ last_x_assum drule \\ rw[] \\ gs[Abbr`ss`]
    \\ NO_TAC )
  \\ ( reverse impl_tac
  >- (
    strip_tac
    \\ rpt disj1_tac
    \\ goal_assum drule
    \\ rw[]
    \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]) )
  \\ gs[domain_compatible_def, Abbr`ss`, all_accounts_def]
  \\ gs[states_agree_modulo_accounts_def,
        rollback_states_agree_modulo_accounts_def]
  \\ gs[rollback_state_component_equality]
QED

Theorem access_slot_ignore_extra_domain_bind:
  (∀x. ignores_extra_domain_pred
         (λs. ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.storageKeys)
         (f x))
  ⇒
  ignores_extra_domain (monad_bind (access_slot a) f)
Proof
  rw[access_slot_def, ignores_extra_domain_def, return_def, fail_def,
     ignores_extra_domain_pred_def, bind_def]
  >- (
    gvs[CaseEq"bool", CaseEq"prod", CaseEq"sum",CaseEq"option",
        CaseEq"domain_mode",domain_check_def, fail_def]
    \\ first_x_assum (drule_at (Pat`f _ _ = _`)) \\ rw[]
    \\ gs[fIN_IN] )
  \\ gs[subdomain_def, SUBSET_DEF, fIN_IN]
  \\ `cold_access_cost ≠ warm_access_cost` by EVAL_TAC
  >- (
    gvs[CaseEq"bool", CaseEq"prod", CaseEq"sum",CaseEq"option",
        CaseEq"domain_mode",domain_check_def, fail_def]
    \\ first_x_assum (drule_at (Pat`f _ _ = _`)) \\ rw[] )
  \\ gs[domain_check_def]
  \\ `s'.msdomain = Enforce d1`
  by gs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gs[]
  \\ `s'.rollback.accesses = s.rollback.accesses`
  by (
    gs[domain_compatible_def, states_agree_modulo_accounts_def,
       rollback_states_agree_modulo_accounts_def,
       rollback_state_component_equality] )
  \\ gs[]
  \\ IF_CASES_TAC \\ gs[fail_def]
  \\ first_x_assum (drule_at (Pat`f _ _ = _`)) \\ simp[]
  \\ strip_tac
  \\ first_x_assum irule
  \\ gs[domain_compatible_def, domain_check_def, all_accounts_def]
  \\ gs[states_agree_modulo_accounts_def]
  \\ gs[rollback_states_agree_modulo_accounts_def]
  \\ gs[rollback_state_component_equality]
QED

Theorem step_balance_ignore_extra_domain[simp]:
  ignores_extra_domain step_balance
Proof
  rw[step_balance_def]
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ irule access_address_ignore_extra_domain_bind \\ rw[]
  \\ rw[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse(rw[])
  >- (
    gs[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
       return_def, fail_def, assert_def, CaseEq"sum", CaseEq"prod", CaseEq"bool"]
    \\ pop_assum mp_tac \\ rw[]
    \\ pop_assum mp_tac \\ rw[]
    \\ pop_assum mp_tac
    \\ rw[set_current_context_def, return_def] )
  \\ irule get_accounts_ignore_extra_domain_pred_bind
  \\ rw[]
  >- gs[domain_compatible_def, states_agree_modulo_accounts_def]
  >- (
    gs[accounts_agree_modulo_storage_def, lookup_account_def,
       account_state_component_equality, fIN_IN] )
  \\ irule ignores_extra_domain_pred_imp
  \\ rw[]
QED

Theorem step_exp_ignore_extra_domain[simp]:
  ignores_extra_domain step_exp
Proof
  rw[step_exp_def] \\ tac
QED

Theorem expand_memory_ignores_extra_domain[simp]:
  ignores_extra_domain (expand_memory z)
Proof
  rw[expand_memory_def] \\ tac
QED

Theorem read_memory_ignores_extra_domain[simp]:
  ignores_extra_domain (read_memory y z)
Proof
  rw[read_memory_def] \\ tac
QED

Theorem memory_expansion_info_ignores_extra_domain[simp]:
  ignores_extra_domain (memory_expansion_info y z)
Proof
  rw[memory_expansion_info_def] \\ tac
QED

Theorem step_keccak256_ignore_extra_domain[simp]:
  ignores_extra_domain step_keccak256
Proof
  rw[step_keccak256_def] \\ tac
QED

Theorem copy_to_memory_ignore_extra_domain[simp]:
  (∀f. z = SOME f ⇒ ignores_extra_domain f) ⇒
  ignores_extra_domain (copy_to_memory a b x y z)
Proof
  rw[copy_to_memory_def, max_expansion_range_def] \\ tac
  \\ BasicProvers.TOP_CASE_TAC \\ gvs[] \\ tac
QED

Theorem step_copy_to_memory_ignore_extra_domain[simp]:
  (∀f. y = SOME f ⇒ ignores_extra_domain f) ⇒
  ignores_extra_domain (step_copy_to_memory x y)
Proof
  rw[step_copy_to_memory_def] \\ tac
QED

Theorem get_call_data_ignores_extra_domain[simp]:
  ignores_extra_domain (get_call_data )
Proof
  rw[get_call_data_def] \\ tac
QED

Theorem step_call_data_load_ignore_extra_domain[simp]:
  ignores_extra_domain step_call_data_load
Proof
  rw[step_call_data_load_def] \\ tac
QED

Theorem step_ext_code_size_ignore_extra_domain[simp]:
  ignores_extra_domain step_ext_code_size
Proof
  rw[step_ext_code_size_def]
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ irule access_address_ignore_extra_domain_bind \\ rw[]
  \\ rw[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse(rw[])
  >- (
    gs[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
       return_def, fail_def, assert_def, CaseEq"sum", CaseEq"prod", CaseEq"bool"]
    \\ pop_assum mp_tac \\ rw[]
    \\ pop_assum mp_tac \\ rw[]
    \\ pop_assum mp_tac
    \\ rw[set_current_context_def, return_def] )
  \\ irule get_accounts_ignore_extra_domain_pred_bind \\ rw[]
  >- gs[domain_compatible_def, states_agree_modulo_accounts_def]
  >- (
    gs[accounts_agree_modulo_storage_def, lookup_account_def,
       account_state_component_equality, fIN_IN] )
  \\ irule ignores_extra_domain_pred_imp
  \\ rw[]
QED

Theorem step_ext_code_hash_ignore_extra_domain[simp]:
  ignores_extra_domain step_ext_code_hash
Proof
  rw[step_ext_code_hash_def]
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ irule access_address_ignore_extra_domain_bind \\ rw[]
  \\ rw[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse(rw[])
  >- (
    gs[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
       return_def, fail_def, assert_def, CaseEq"sum", CaseEq"prod", CaseEq"bool"]
    \\ pop_assum mp_tac \\ rw[]
    \\ pop_assum mp_tac \\ rw[]
    \\ pop_assum mp_tac
    \\ rw[set_current_context_def, return_def] )
  \\ irule get_accounts_ignore_extra_domain_pred_bind \\ simp[]
  \\ conj_tac >- (
    rw[] \\ gs[domain_compatible_def, states_agree_modulo_accounts_def] )
  \\ conj_tac >- (
    rpt gen_tac \\ strip_tac
    \\ gs[accounts_agree_modulo_storage_def, lookup_account_def,
          account_state_component_equality, fIN_IN]
    \\ rw[account_empty_def])
  \\ gen_tac
  \\ irule ignores_extra_domain_pred_imp
  \\ rw[]
QED

Theorem get_code_ignores_extra_domain:
  ignores_extra_domain_pred (λs. ∀d. s.msdomain = Enforce d ⇒ x ∈ toSet d.addresses) (get_code x)
Proof
  rw[get_code_def]
  \\ rw[bind_def, ignores_extra_domain_pred_def,
        ignore_bind_def, return_def, get_accounts_def]
  \\ gs[domain_compatible_def, lookup_account_def, domain_check_def]
  \\ gs[all_accounts_def, accounts_agree_modulo_storage_def, fIN_IN]
  \\ gs[account_state_component_equality]
QED

Theorem SND_memory_expansion_info[simp]:
  SND (memory_expansion_info x y s) = s
Proof
  rw[memory_expansion_info_def, get_current_context_def, bind_def,
     fail_def, return_def]
QED

Theorem SND_consume_gas_msdomain[simp]:
  (SND (consume_gas n s)).msdomain = s.msdomain
Proof
  rw[consume_gas_def, bind_def, get_current_context_def, return_def, fail_def,
     assert_def, ignore_bind_def, set_current_context_def]
  \\ rw[]
QED

Theorem step_ext_code_copy_ignore_extra_domain[simp]:
  ignores_extra_domain step_ext_code_copy
Proof
  rw[step_ext_code_copy_def]
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ irule access_address_ignore_extra_domain_bind
  \\ rw[]
  \\ rw[copy_to_memory_def, max_expansion_range_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ rw[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse(rw[])
  \\ irule ignores_extra_domain_imp_pred_pred_bind
  \\ reverse(rw[])
  >- irule get_code_ignores_extra_domain
  >- (
    gs[get_code_def, bind_def, ignore_bind_def, get_current_context_def,
       get_accounts_def,
       return_def, fail_def, assert_def, CaseEq"sum", CaseEq"prod", CaseEq"bool"]
    \\ rw[] \\ rw[] \\ rw[set_current_context_def, return_def] )
  \\ irule ignores_extra_domain_pred_imp
  \\ tac
QED

Theorem get_tx_params_ignores_extra_domain[simp]:
  ignores_extra_domain get_tx_params
Proof
  rw[get_tx_params_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def]
QED

Theorem step_txParams_ignores_extra_domain[simp]:
  ignores_extra_domain (step_txParams x y)
Proof
  rw[step_txParams_def] \\ tac
QED

Theorem get_return_data_check_ignores_extra_domain[simp]:
  ignores_extra_domain (get_return_data_check x y)
Proof
  rw[get_return_data_check_def] \\ tac
QED

Theorem step_return_data_copy_ignore_extra_domain[simp]:
  ignores_extra_domain step_return_data_copy
Proof
  rw[step_return_data_copy_def] \\ tac
QED

Theorem step_block_hash_ignore_extra_domain[simp]:
  ignores_extra_domain step_block_hash
Proof
  rw[step_block_hash_def] \\ tac
QED

Theorem get_callee_ignores_extra_domain[simp]:
  ignores_extra_domain get_callee
Proof
  rw[get_callee_def] \\ tac
QED

Theorem step_self_balance_ignore_extra_domain:
  ignores_extra_domain_pred (λs.
    ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  step_self_balance
Proof
  rw[step_self_balance_def]
  \\ rw[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse(rw[])
  >- (
    gs[consume_gas_def, ignore_bind_def, get_current_context_def,
       assert_def, set_current_context_def, bind_def, return_def,
       fail_def]
    \\ rpt (pop_assum mp_tac) \\ rw[]
    \\ rpt (pop_assum mp_tac) \\ rw[]
    \\ Cases_on`s.contexts` \\ gvs[CaseEq"bool"]
    \\ Cases_on`h` \\gs[] )
  \\ irule get_accounts_ignore_extra_domain_pred_bind
  \\ rw[]
  >- (
    gs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ Cases_on`s.contexts` \\ gs[]
    \\ Cases_on`h` \\ gs[] )
  >- (
    gs[bind_def, ignore_bind_def, get_callee_def, get_current_context_def]
    \\ gvs[fail_def, return_def, CaseEq"sum", CaseEq"prod"]
    \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`s.contexts` \\ gs[]
    \\ Cases_on`h` \\ gs[]
    \\ gs[accounts_agree_modulo_storage_def, account_state_component_equality,
          fIN_IN, lookup_account_def])
  >- (
    irule ignores_extra_domain_pred_imp
    \\ tac
  )
QED

Theorem step_pop_ignores_extra_domain[simp]:
  ignores_extra_domain step_pop
Proof
  rw[step_pop_def] \\ tac
QED

Theorem step_mload_ignores_extra_domain[simp]:
  ignores_extra_domain step_mload
Proof
  rw[step_mload_def] \\ tac
QED

Theorem step_mstore_ignores_extra_domain[simp]:
  ignores_extra_domain (step_mstore x)
Proof
  rw[step_mstore_def] \\ tac
QED

Theorem get_tStorage_ignores_extra_domain[simp]:
  ignores_extra_domain get_tStorage
Proof
  rw[get_tStorage_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gvs[rollback_states_agree_modulo_accounts_def,
         rollback_state_component_equality]
QED

Theorem step_sload_ignores_extra_domain[simp]:
  ignores_extra_domain (step_sload x)
Proof
  rw[step_sload_def]
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ Cases_on`x` \\ gs[] >- tac
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ irule access_slot_ignore_extra_domain_bind
  \\ rw[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse(rw[])
  \\ irule get_accounts_ignore_extra_domain_slot_pred_bind
  \\ rw[]
  >- (
    gs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ Cases_on`s.contexts` \\ gs[]
    \\ Cases_on`h` \\ gs[] )
  >- (
    gs[accounts_agree_modulo_storage_def, account_state_component_equality,
       fIN_IN, lookup_account_def, lookup_storage_def])
  >- ( irule ignores_extra_domain_pred_imp \\ rw[])
QED

Theorem set_jump_dest_ignores_extra_domain[simp]:
  ignores_extra_domain (set_jump_dest i)
Proof
  rw[set_jump_dest_def] \\ tac
QED

Theorem step_jump_ignores_extra_domain[simp]:
  ignores_extra_domain step_jump
Proof
  rw[step_jump_def] \\ tac
QED

Theorem step_jumpi_ignores_extra_domain[simp]:
  ignores_extra_domain step_jumpi
Proof
  rw[step_jumpi_def] \\ tac
QED

Theorem step_push_ignores_extra_domain[simp]:
  ignores_extra_domain (step_push x y)
Proof
  rw[step_push_def] \\ tac
QED

Theorem step_dup_ignores_extra_domain[simp]:
  ignores_extra_domain (step_dup x)
Proof
  rw[step_dup_def] \\ tac
QED

Theorem get_static_ignores_extra_domain[simp]:
  ignores_extra_domain get_static
Proof
  rw[get_static_def] \\ tac
QED

Theorem assert_not_static_ignores_extra_domain[simp]:
  ignores_extra_domain assert_not_static
Proof
  rw[assert_not_static_def] \\ tac
QED

Theorem step_log_ignores_extra_domain[simp]:
  ignores_extra_domain (step_log x)
Proof
  rw[step_log_def] \\ tac
QED

Theorem step_swap_ignores_extra_domain[simp]:
  ignores_extra_domain (step_swap n)
Proof
  rw[step_swap_def] \\ tac
QED

Theorem revert_ignores_extra_domain[simp]:
  ignores_extra_domain revert
Proof
  rw[ignores_extra_domain_def, revert_def]
QED

Theorem step_return_ignores_extra_domain[simp]:
  ignores_extra_domain (step_return n)
Proof
  rw[step_return_def] \\ tac
QED

Theorem step_invalid_ignores_extra_domain[simp]:
  ignores_extra_domain step_invalid
Proof
  rw[step_invalid_def] \\ tac
QED

Theorem get_current_code_ignores_extra_domain[simp]:
  ignores_extra_domain get_current_code
Proof
  rw[get_current_code_def] \\ tac
QED

Theorem set_tStorage_ignores_extra_domain[simp]:
  ignores_extra_domain (set_tStorage z)
Proof
  rw[set_tStorage_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gvs[all_accounts_def, rollback_states_agree_modulo_accounts_def]
  \\ gvs[rollback_state_component_equality]
  \\ CASE_TAC \\ gs[]
QED

Theorem write_transient_storage_ignores_extra_domain[simp]:
  ignores_extra_domain (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def] \\ tac
QED

Theorem get_original_ignores_extra_domain_pred_bind:
  (∀x y s d.
      p s ∧ s.msdomain = Enforce d ∧
      (∀a.
         fIN a d.addresses ⇒
         accounts_agree_modulo_storage a x y) ⇒
      f x s = f y s) ∧ (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
   (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_original f)
Proof
  rw[bind_def, get_original_def, ignores_extra_domain_pred_def, return_def,
     CaseEq"bool",CaseEq"prod",CaseEq"sum", CaseEq"domain_mode", fail_def]
  \\ TRY (qmatch_rename_tac`_.msdomain = _` \\ metis_tac[])
  \\ fsrw_tac[DNF_ss][]
  >- ( drule domain_compatible_lengths \\ rw[] )
  \\ disj2_tac
  \\ qspec_then`s.contexts`strip_assume_tac SNOC_CASES
  \\ qmatch_asmsub_rename_tac`domain_compatible s ss`
  \\ qspec_then`ss.contexts`strip_assume_tac SNOC_CASES
  >- ( drule domain_compatible_lengths \\ rw[] )
  \\ gvs[]
  \\ first_x_assum irule
  \\ goal_assum drule \\ rw[]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ irule EQ_SYM
  \\ first_x_assum irule
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gs[all_accounts_def, domain_check_def]
  \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]
QED

Theorem get_original_ignores_extra_domain_pred_slot_bind:
  (∀x y s d.
      p s ∧ s.msdomain = Enforce d ∧
      (∀a k.
         fIN (SK a k) d.storageKeys ⇒
         (x a).storage k = (y a).storage k) ⇒
      f x s = f y s) ∧ (∀s s'. p s ∧ domain_compatible s s' ⇒ p s') ∧
   (∀x. ignores_extra_domain_pred p (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_original f)
Proof
  rw[bind_def, get_original_def, ignores_extra_domain_pred_def, return_def,
     CaseEq"bool",CaseEq"prod",CaseEq"sum", fail_def]
  \\ TRY (qmatch_rename_tac`_.msdomain = _` \\ metis_tac[])
  \\ fsrw_tac[DNF_ss][]
  >- ( drule domain_compatible_lengths \\ rw[] )
  \\ disj2_tac
  \\ qspec_then`s.contexts`strip_assume_tac SNOC_CASES
  \\ qmatch_asmsub_rename_tac`domain_compatible s ss`
  \\ qspec_then`ss.contexts`strip_assume_tac SNOC_CASES
  >- ( drule domain_compatible_lengths \\ rw[] )
  \\ gvs[]
  \\ first_x_assum irule
  \\ goal_assum drule \\ rw[]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ irule EQ_SYM
  \\ first_x_assum irule
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gs[all_accounts_def, domain_check_def]
  \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]
QED

Theorem get_original_ignores_extra_domain_slot_bind:
   (∀x y s d. s.msdomain = Enforce d ∧
      (∀a k.
         fIN (SK a k) d.storageKeys ⇒
         (x a).storage k = (y a).storage k) ⇒
      f x s = f y s) ∧ (∀x. ignores_extra_domain (f x)) ⇒
   ignores_extra_domain (monad_bind get_original f)
Proof
  rw[bind_def, get_original_def, ignores_extra_domain_def, return_def,
     CaseEq"bool",CaseEq"prod",CaseEq"sum", fail_def]
  \\ TRY (qmatch_rename_tac`_.msdomain = _` \\ metis_tac[])
  \\ fsrw_tac[DNF_ss][]
  >- ( drule domain_compatible_lengths \\ rw[] )
  \\ disj2_tac
  \\ qspec_then`s.contexts`strip_assume_tac SNOC_CASES
  \\ qmatch_asmsub_rename_tac`domain_compatible s ss`
  \\ qspec_then`ss.contexts`strip_assume_tac SNOC_CASES
  >- ( drule domain_compatible_lengths \\ rw[] )
  \\ gvs[]
  \\ first_x_assum irule
  \\ goal_assum (drule_at Any) \\ rw[]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ irule EQ_SYM
  \\ first_x_assum irule
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ gs[all_accounts_def, domain_check_def]
  \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]
QED

Theorem step_sstore_gas_consumption_ignores_extra_domain[simp]:
  ignores_extra_domain (step_sstore_gas_consumption z y x)
Proof
  simp[step_sstore_gas_consumption_def]
  \\ qpat_abbrev_tac`b0 = COND _ _ _`
  \\ irule bind_ignores_extra_domain \\ rw[]
  \\ irule ignore_bind_ignores_extra_domain \\ rw[]
  \\ irule get_accounts_ignore_extra_domain_slot_bind
  \\ conj_tac
  >- (
    simp[]
    \\ rpt gen_tac \\ strip_tac
    \\ gs[lookup_account_def, lookup_storage_def]
    \\ simp[bind_def]
    \\ TOP_CASE_TAC \\ TOP_CASE_TAC \\ gs[]
    \\ TOP_CASE_TAC \\ TOP_CASE_TAC \\ gs[]
    \\ `r = s`
    by gvs[get_original_def, CaseEq"bool", return_def, fail_def]
    \\ gvs[access_slot_def, CaseEq"bool", return_def, fail_def, domain_check_def] )
  \\ gen_tac \\ simp[]
  \\ irule get_original_ignores_extra_domain_slot_bind
  \\ conj_tac
  >- (
    simp[]
    \\ rpt gen_tac \\ strip_tac
    \\ gs[lookup_account_def, lookup_storage_def]
    \\ simp[bind_def]
    \\ TOP_CASE_TAC \\ TOP_CASE_TAC \\ gs[]
    \\ gvs[access_slot_def, CaseEq"bool", return_def, fail_def, domain_check_def] )
  \\ gen_tac \\ simp[]
  \\ tac
QED

Theorem write_storage_ignores_extra_domain[simp]:
  ignores_extra_domain (write_storage x y z)
Proof
  rw[write_storage_def] \\ tac
  \\ rw[assert_def, bind_def, reraise_def, consume_gas_def,
        get_current_context_def, return_def, ignore_bind_def,
        set_current_context_def, update_accounts_def,
        ignores_extra_domain_def]
  \\ gs[domain_compatible_def, all_accounts_def, update_account_def,
        lookup_account_def, APPLY_UPDATE_THM, domain_check_def]
  \\ gs[states_agree_modulo_accounts_def]
  \\ gs[rollback_states_agree_modulo_accounts_def]
  \\ gs[rollback_state_component_equality]
  \\ gs[accounts_agree_modulo_storage_def, APPLY_UPDATE_THM]
  \\ rw[]
  \\ gs[account_state_component_equality]
  \\ rw[update_storage_def, APPLY_UPDATE_THM]
QED

Theorem step_sstore_ignores_extra_domain[simp]:
  ignores_extra_domain (step_sstore x)
Proof
  simp[step_sstore_def] \\ tac
QED

Theorem add_to_delete_ignores_extra_domain[simp]:
  ignores_extra_domain (add_to_delete _)
Proof
  rw[add_to_delete_def, ignores_extra_domain_def, return_def]
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def,
        all_accounts_def, rollback_states_agree_modulo_accounts_def]
  \\ gs[rollback_state_component_equality]
  \\ CASE_TAC \\ gs[]
QED

Theorem get_callee_ignores_extra_domain_pred_bind:
  (∀x. ignores_extra_domain_pred (λs. p s ∧ (∃c r t. s.contexts = (c,r)::t ∧
                                                     c.msgParams.callee = x))
        (f x))
  ⇒
  ignores_extra_domain_pred p (monad_bind get_callee f)
Proof
  rw[ignores_extra_domain_pred_def, bind_def, get_callee_def,
     get_current_context_def, return_def, fail_def]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ TRY(drule domain_compatible_lengths \\ rw[])
  \\ fsrw_tac[DNF_ss][]
  \\ Cases_on`h` \\ gvs[]
  >- metis_tac[]
  \\ Cases_on`s'.contexts` \\ gvs[]
  \\ Cases_on`h` \\ gvs[]
  \\ first_x_assum drule \\ gvs[]
  \\ disch_then drule
  \\ strip_tac
  \\ goal_assum drule
  \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def]
QED

Theorem self_destruct_helper:
  do
    accounts <- get_accounts;
    sender <<- lookup_account senderAddress accounts;
    balance <<- sender.balance;
    beneficiaryEmpty <<- account_empty (lookup_account address accounts);
    transferCost <<-
      if 0 < balance ∧ beneficiaryEmpty then
        self_destruct_new_account_cost
      else 0;
    consume_gas
      (static_gas SelfDestruct + zero_warm accessCost + transferCost);
    assert_not_static;
    update_accounts (transfer_value senderAddress address balance);
    original <- get_original;
    originalContract <<- lookup_account senderAddress original;
    if account_empty originalContract then
      do
        update_accounts
          (update_account senderAddress (sender with balance := 0));
        add_to_delete senderAddress
      od
    else return ();
    finish
  od =
  do
    accounts <- get_accounts;
    sender <<- lookup_account senderAddress accounts;
    balance <<- sender.balance;
    beneficiaryEmpty <<- account_empty (lookup_account address accounts);
    transferCost <<-
      if 0 < balance ∧ beneficiaryEmpty then
        self_destruct_new_account_cost
      else 0;
    consume_gas
      (static_gas SelfDestruct + zero_warm accessCost + transferCost);
    assert_not_static;
    update_accounts (transfer_value senderAddress address balance);
    original <- get_original;
    originalContract <<- lookup_account senderAddress original;
    if account_empty originalContract then
      do
        update_accounts
          (λa. (senderAddress =+ a senderAddress with balance := 0) a);
        add_to_delete senderAddress
      od
    else return ();
    finish
  od
Proof
  rw[FUN_EQ_THM, bind_def, ignore_bind_def,
     assert_not_static_def, update_accounts_def,
     return_def, fail_def, consume_gas_def, get_original_def,
     update_accounts_def, get_static_def, get_current_context_def,
     set_current_context_def, assert_def, get_accounts_def]
  \\ rw[] \\ gvs[return_def, bind_def]
  \\ rw[] \\ gvs[return_def, bind_def, update_accounts_def, add_to_delete_def]
  \\ rw[] \\ gvs[finish_def]
  \\ gvs[execution_state_component_equality, rollback_state_component_equality]
  \\ gvs[update_account_def, transfer_value_def, lookup_account_def,
         APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ rw[account_state_component_equality, APPLY_UPDATE_THM]
  \\ rw[]
QED

Theorem ignores_extra_domain_update_accounts_transfer_value[simp]:
  ignores_extra_domain (update_accounts (transfer_value x y z))
Proof
  rw[update_accounts_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, all_accounts_def,
         states_agree_modulo_accounts_def, domain_check_def,
         rollback_states_agree_modulo_accounts_def,
         rollback_state_component_equality, transfer_value_def ]
  \\ gvs[accounts_agree_modulo_storage_def, update_account_def,
         APPLY_UPDATE_THM, account_state_component_equality,
         lookup_account_def]
  \\ rw[APPLY_UPDATE_THM]
  \\ CASE_TAC \\ rw[] \\ gvs[]
QED

Theorem ignores_extra_domain_update_accounts_increment_nonce[simp]:
  ignores_extra_domain (update_accounts (increment_nonce a))
Proof
  rw[update_accounts_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, all_accounts_def,
         states_agree_modulo_accounts_def, rollback_state_component_equality,
         rollback_states_agree_modulo_accounts_def, APPLY_UPDATE_THM,
         accounts_agree_modulo_storage_def, increment_nonce_def,
         update_account_def, lookup_account_def, domain_check_def]
  \\ CASE_TAC
  \\ gvs[account_state_component_equality] \\ rw[]
QED

Theorem step_self_destruct_ignores_extra_domain[simp]:
  ignores_extra_domain_pred (λs.
    ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  step_self_destruct
Proof
  rw[step_self_destruct_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse conj_tac
  >- (
    rw[] \\
    gvs[pop_stack_def, bind_def, ignore_bind_def, get_current_context_def,
        fail_def, return_def, assert_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ gvs[]
    \\ TOP_CASE_TAC \\ gvs[CaseEq"bool"]
    \\ TOP_CASE_TAC \\ gvs[CaseEq"bool"]
    \\ gvs[set_current_context_def, return_def]
    \\ qmatch_goalsub_rename_tac`HD s.contexts`
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ qx_gen_tac`args` \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`access_address address`
  \\ irule access_address_ignore_extra_domain_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    rw[access_address_def, return_def, fail_def, domain_check_def]
    \\ Cases_on`s.msdomain` \\ gvs[ignore_bind_def, bind_def,set_domain_def]
    \\ rpt (pop_assum mp_tac) \\ rw[return_def])
  \\ qx_gen_tac`accessCost`
  \\ irule get_callee_ignores_extra_domain_pred_bind
  \\ simp[]
  \\ qx_gen_tac`senderAddress`
  \\ simp[]
  \\ simp[SIMP_RULE(srw_ss())[LET_THM, AC ADD_ASSOC ADD_COMM]self_destruct_helper]
  \\ irule get_accounts_ignore_extra_domain_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    rw[domain_compatible_def, states_agree_modulo_accounts_def] \\ gvs[]
    \\ Cases_on`s'.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ simp[lookup_account_def, update_account_def]
    \\ rpt strip_tac
    \\ qmatch_goalsub_abbrev_tac`consume_gas n1`
    \\ qmatch_goalsub_abbrev_tac`update_accounts a1`
    \\ qmatch_goalsub_abbrev_tac`ignore_bind (update_accounts u1)
                                   (add_to_delete _)`
    \\ qmatch_goalsub_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`consume_gas n2`
    \\ qmatch_goalsub_abbrev_tac`update_accounts a2`
    \\ `n1 = n2`
    by (
      simp[Abbr`n1`,Abbr`n2`]
      \\ gvs[fIN_IN, accounts_agree_modulo_storage_def,
             account_state_component_equality, account_empty_def] )
    \\ `a1 = a2`
    by (
      simp[Abbr`a1`,Abbr`a2`]
      \\ gvs[fIN_IN, accounts_agree_modulo_storage_def,
             account_state_component_equality, account_empty_def])
    \\ simp[Abbr`lhs`] )
  \\ qx_gen_tac`balance`
  \\ simp[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    gen_tac
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`consume_gas nn`
    \\ simp[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
            assert_def, return_def, fail_def, set_current_context_def]
    \\ rw[] \\ rw[] )
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    gen_tac
    \\ strip_tac
    \\ simp[assert_not_static_def, bind_def, ignore_bind_def, get_current_context_def,
            assert_def, get_static_def, return_def, fail_def,
            set_current_context_def])
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    gen_tac
    \\ strip_tac
    \\ simp[update_accounts_def, bind_def, ignore_bind_def, get_current_context_def,
            assert_def, get_static_def, return_def, fail_def,
            set_current_context_def] )
  \\ irule get_original_ignores_extra_domain_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    rw[]
    \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ Cases_on`s'.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ conj_tac
  >- (
    rw[]
    \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def,
           account_empty_def, fIN_IN, accounts_agree_modulo_storage_def,
           lookup_account_def, account_state_component_equality] )
  \\ rw[]
  \\ irule ignores_extra_domain_pred_imp
  \\ tac \\ rw[]
  \\ rw[update_accounts_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, all_accounts_def,
         states_agree_modulo_accounts_def, rollback_state_component_equality,
         rollback_states_agree_modulo_accounts_def, APPLY_UPDATE_THM,
         accounts_agree_modulo_storage_def, domain_check_def]
  \\ TOP_CASE_TAC
  \\ gvs[account_state_component_equality] \\ rw[]
QED

Theorem abort_unuse_ignores_extra_domain[simp]:
  ignores_extra_domain (abort_unuse x)
Proof
  rw[abort_unuse_def] \\ tac
QED

Theorem abort_call_value_ignores_extra_domain[simp]:
  ignores_extra_domain (abort_call_value x)
Proof
  rw[abort_call_value_def] \\ tac
QED

Theorem abort_create_exists_ignores_extra_domain[simp]:
  ignores_extra_domain (abort_create_exists x)
Proof
  rw[abort_create_exists_def] \\ tac
  \\ rw[update_accounts_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, all_accounts_def,
         states_agree_modulo_accounts_def, increment_nonce_def,
         lookup_account_def,
         rollback_states_agree_modulo_accounts_def,
         rollback_state_component_equality ]
  \\ gvs[accounts_agree_modulo_storage_def, update_account_def,
         APPLY_UPDATE_THM, account_state_component_equality]
  \\ rw[]
QED

Theorem get_caller_ignores_extra_domain[simp]:
  ignores_extra_domain get_caller
Proof
  rw[get_caller_def] \\ tac
QED

Theorem get_value_ignores_extra_domain[simp]:
  ignores_extra_domain get_value
Proof
  rw[get_value_def] \\ tac
QED

Theorem fail_ignores_extra_domain[simp]:
  ignores_extra_domain (fail x)
Proof
  rw[ignores_extra_domain_def, fail_def]
QED

Theorem precompile_ecrecover_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
QED

Theorem precompile_ripemd_160_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
QED

Theorem precompile_sha2_256_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_sha2_256
Proof
  rw[precompile_sha2_256_def] \\ tac
QED

Theorem precompile_identity_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_identity
Proof
  rw[precompile_identity_def] \\ tac
QED

Theorem precompile_modexp_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_modexp
Proof
  rw[precompile_modexp_def] \\ tac
QED

Theorem precompile_ecadd_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecadd
Proof
  rw[precompile_ecadd_def] \\ tac
QED

Theorem precompile_ecmul_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecmul
Proof
  rw[precompile_ecmul_def] \\ tac
QED

Theorem precompile_ecpairing_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecpairing
Proof
  rw[precompile_ecpairing_def] \\ tac
QED

Theorem precompile_blake2f_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_blake2f
Proof
  rw[precompile_blake2f_def] \\ tac
QED

Theorem dispatch_precompiles_ignores_extra_domain[simp]:
  ignores_extra_domain (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem ignores_extra_domain_update_accounts_nonce[simp]:
  ignores_extra_domain
    (update_accounts (update_account a (b with nonce updated_by f)))
Proof
  rw[update_accounts_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, all_accounts_def,
         states_agree_modulo_accounts_def, domain_check_def,
         rollback_states_agree_modulo_accounts_def,
         rollback_state_component_equality, transfer_value_def ]
  \\ TOP_CASE_TAC
  \\ gvs[accounts_agree_modulo_storage_def, update_account_def,
         APPLY_UPDATE_THM, account_state_component_equality,
         lookup_account_def]
  \\ rw[APPLY_UPDATE_THM]
  \\ rw[]
QED

Theorem ignores_extra_domain_update_accounts_o[simp]:
  ignores_extra_domain (update_accounts f) ∧
  ignores_extra_domain (update_accounts g)
  ⇒
  ignores_extra_domain (update_accounts (g o f))
Proof
  rw[ignores_extra_domain_def, update_accounts_def, return_def]
  \\ qmatch_goalsub_abbrev_tac`_ with rollback updated_by gf`
  \\ `∀s. s with rollback updated_by gf =
          (s with rollback updated_by (λr. r with accounts updated_by f))
          with rollback updated_by (λr. r with accounts updated_by g)`
  by ( rw[execution_state_component_equality, Abbr`gf`] )
  \\ full_simp_tac std_ss []
  \\ first_x_assum irule \\ simp[]
QED

Theorem get_rollback_ignores_extra_domain_bind:
  (∀x y s d.
    rollback_states_agree_modulo_accounts x y ∧
    s.msdomain = Enforce d ∧
           (∀a. a ∈ toSet d.addresses ⇒
                accounts_agree_modulo_storage a x.accounts y.accounts) ∧
           (∀a k. SK a k ∈ toSet d.storageKeys ⇒
                (x.accounts a).storage k = (y.accounts a).storage k) ∧
           (∀a. a ∈ toSet d.fullStorages ⇒
                (x.accounts a).storage = (y.accounts a).storage)
    ⇒
    FST (f x s) = FST (f y s) ∧
    domain_compatible (SND (f x s)) (SND (f y s))) ∧
  (∀x. ignores_extra_domain (f x))
  ⇒
  ignores_extra_domain (monad_bind get_rollback f)
Proof
  rw[get_rollback_def, ignores_extra_domain_def, return_def, bind_def]
  \\ first_assum drule \\ rw[]
  \\ first_x_assum(qspecl_then[`s.rollback`,`s'.rollback`,`s'`,`d1`]mp_tac)
  \\ impl_tac
  >- (
    fs[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ gs[all_accounts_def, fIN_IN, domain_check_def] )
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ gvs[]
  \\ qexists_tac`SND (f s'.rollback s')`
  \\ conj_tac >- metis_tac[domain_compatible_trans]
  \\ metis_tac[PAIR]
QED

Theorem push_context_ignores_extra_domain[simp]:
  ignores_extra_domain (push_context c)
Proof
  rw[push_context_def, ignores_extra_domain_def, return_def]
  \\ gvs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ CASE_TAC
  \\ gvs[all_accounts_def]
QED

Theorem FST_bind_eq:
  (∀x s'. f s = (INL x, s') ⇒ FST (g1 x s') = FST (g2 x s'))
  ⇒
  FST (monad_bind f g1 s) = FST (monad_bind f g2 s)
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC
  \\ gs[FUN_EQ_THM]
QED

Theorem bind_eq:
  (∀x s'. f s = (INL x, s') ⇒ (g1 x s') = (g2 x s'))
  ⇒
  (monad_bind f g1 s) = (monad_bind f g2 s)
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC
  \\ gs[FUN_EQ_THM]
QED

Theorem SND_bind_domain_compatible:
  (∀x s'. f s = (INL x, s') ⇒ domain_compatible (SND (g1 x s')) (SND (g2 x s')))
  ⇒
  domain_compatible (SND (monad_bind f g1 s)) (SND (monad_bind f g2 s))
Proof
  rw[bind_def]
  \\ CASE_TAC
  \\ CASE_TAC
  \\ gs[]
QED

Theorem proceed_call_ignores_extra_domain[simp]:
  ignores_extra_domain (proceed_call a b c d e f g h i)
Proof
  simp[proceed_call_def]
  \\ irule get_rollback_ignores_extra_domain_bind
  \\ reverse conj_asm2_tac
  >- ( simp[] \\ gen_tac \\ tac )
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ simp[]
  \\ qho_match_abbrev_tac`(FST ((ff x) _) = _) ∧ _` \\ gs[]
  \\ conj_tac
  >- (
    simp[Abbr`ff`]
    \\ irule FST_bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ simp[ignore_bind_def]
    \\ irule FST_bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule FST_bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule FST_bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule FST_bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ simp[bind_def, push_context_def, return_def, COND_RATOR]
    \\ qmatch_goalsub_abbrev_tac`cc,x`
    \\ IF_CASES_TAC \\ gs[]
    \\ qmatch_goalsub_abbrev_tac`dispatch_precompiles c s1`
    \\ (dispatch_precompiles_ignores_extra_domain
        |> REWRITE_RULE[ignores_extra_domain_def]
        |> GEN_ALL
        |> INST_TYPE[alpha|->“:unit”]
        |> qspecl_then[`c`,`s1`]mp_tac)
    \\ qmatch_goalsub_abbrev_tac`FST p`
    \\ Cases_on`p` \\ simp[]
    \\ disch_then(qspec_then`d'`mp_tac)
    \\ impl_keep_tac
    >- (
       gvs[Abbr`s1`,get_static_def,bind_def,CaseEq"prod",CaseEq"sum",return_def,
           get_current_context_def,CaseEq"bool",fail_def,get_value_def,
           get_caller_def,COND_RATOR,update_accounts_def,read_memory_def] )
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`dispatch_precompiles c s2`
    \\ first_x_assum(qspec_then`s2`mp_tac)
    \\ impl_tac
    >- (
      gs[Abbr`s1`,Abbr`s2`]
      \\ simp[domain_compatible_def, domain_check_def]
      \\ simp[states_agree_modulo_accounts_def]
      \\ simp[all_accounts_def] \\ gs[fIN_IN]
      \\ rw[]
      \\ TRY (irule EVERY2_refl \\ rw[])
      \\ first_x_assum irule
      \\ gvs[get_static_def, get_value_def, get_caller_def, bind_def,
             return_def, CaseEq"prod", CaseEq"sum", get_current_context_def,
             fail_def, CaseEq"bool", COND_RATOR, update_accounts_def,
             read_memory_def] )
    \\ rw[] \\ rw[] )
  \\ simp[Abbr`ff`, ignore_bind_def]
  \\ rpt (
    irule SND_bind_domain_compatible
    \\ simp[] \\ rpt gen_tac \\ strip_tac )
  \\ qmatch_goalsub_abbrev_tac`cc,x`
  \\ simp[bind_def, push_context_def, return_def, COND_RATOR]
  \\ rw[]
  >- (
    qmatch_goalsub_abbrev_tac`dispatch_precompiles c s1`
    \\ (dispatch_precompiles_ignores_extra_domain
        |> REWRITE_RULE[ignores_extra_domain_def]
        |> GEN_ALL
        |> INST_TYPE[alpha|->“:unit”]
        |> qspecl_then[`c`,`s1`]mp_tac)
    \\ qmatch_goalsub_abbrev_tac`SND p`
    \\ Cases_on`p` \\ simp[]
    \\ disch_then(qspec_then`d'`mp_tac)
    \\ impl_keep_tac
    >- (
       gvs[Abbr`s1`,get_static_def,bind_def,CaseEq"prod",CaseEq"sum",return_def,
           get_current_context_def,CaseEq"bool",fail_def,get_value_def,
           get_caller_def,COND_RATOR,update_accounts_def,read_memory_def] )
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`dispatch_precompiles c s2`
    \\ first_x_assum(qspec_then`s2`mp_tac)
    \\ impl_tac
    >- (
      gs[Abbr`s1`,Abbr`s2`]
      \\ simp[domain_compatible_def, domain_check_def]
      \\ simp[states_agree_modulo_accounts_def]
      \\ simp[all_accounts_def] \\ gs[fIN_IN]
      \\ rw[]
      \\ TRY (irule EVERY2_refl \\ rw[])
      \\ first_x_assum irule
      \\ gvs[get_static_def, get_value_def, get_caller_def, bind_def,
             return_def, CaseEq"prod", CaseEq"sum", get_current_context_def,
             fail_def, CaseEq"bool", COND_RATOR, update_accounts_def,
             read_memory_def] )
    \\ rw[] \\ rw[] )
  \\ simp[domain_compatible_def, domain_check_def]
  \\ qmatch_goalsub_rename_tac`s1.msdomain`
  \\ `s1.msdomain = Enforce d'` by (
       gvs[get_static_def,bind_def,CaseEq"prod",CaseEq"sum",return_def,
           get_current_context_def,CaseEq"bool",fail_def,get_value_def,
           get_caller_def,COND_RATOR,update_accounts_def,read_memory_def] )
  \\ simp[states_agree_modulo_accounts_def]
  \\ simp[all_accounts_def] \\ gs[fIN_IN]
  \\ rw[] \\ TRY (irule EVERY2_refl \\ rw[])
  \\ first_x_assum irule
  \\ gvs[get_static_def, get_value_def, get_caller_def, bind_def,
         return_def, CaseEq"prod", CaseEq"sum", get_current_context_def,
         fail_def, CaseEq"bool", COND_RATOR, update_accounts_def,
         read_memory_def]
QED

Theorem SND_update_accounts_msdomain[simp]:
  (SND (update_accounts f s)).msdomain = s.msdomain
Proof
  rw[update_accounts_def, bind_def, get_current_context_def,
     fail_def, return_def]
QED

Theorem proceed_create_ignores_extra_domain[simp]:
  ignores_extra_domain (proceed_create a b c d e)
Proof
  simp[proceed_create_def]
  \\ irule ignore_bind_ignores_extra_domain \\ rw[]
  \\ irule get_rollback_ignores_extra_domain_bind
  \\ reverse conj_asm2_tac
  >- ( simp[] \\ gen_tac \\ tac )
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ simp[]
  \\ conj_tac
  >- (
    simp[ignore_bind_def]
    \\ rpt ( irule FST_bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac )
    \\ simp[push_context_def, return_def] )
  \\ simp[ignore_bind_def]
  \\ rpt (
    irule SND_bind_domain_compatible
    \\ simp[] \\ rpt gen_tac \\ strip_tac )
  \\ qmatch_goalsub_abbrev_tac`cc,x`
  \\ simp[push_context_def, return_def]
  \\ simp[domain_compatible_def, domain_check_def]
  \\ simp[states_agree_modulo_accounts_def]
  \\ simp[all_accounts_def] \\ gs[fIN_IN]
  \\ `s'.msdomain = s.msdomain` by metis_tac[SND_update_accounts_msdomain, SND]
  \\ rw[] \\ TRY (irule EVERY2_refl \\ rw[])
  \\ first_x_assum irule
  \\ gvs[get_static_def, get_value_def, get_caller_def, bind_def,
         return_def, CaseEq"prod", CaseEq"sum", get_current_context_def,
         fail_def, CaseEq"bool", COND_RATOR, update_accounts_def,
         read_memory_def]
QED

Theorem step_call_ignores_extra_domain:
  ignores_extra_domain_pred
  (λs. ∀c r t d.
    s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  (step_call x)
Proof
  simp[step_call_def, UNCURRY]
  \\ qpat_abbrev_tac`b0 = COND _ _ _`
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    rw[pop_stack_def, bind_def, get_current_context_def, fail_def, return_def,
       ignore_bind_def, assert_def, set_current_context_def]
    \\ pop_assum mp_tac \\ rw[] \\ gvs[]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ gen_tac
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ gen_tac
  \\ irule access_address_ignore_extra_domain_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    rw[access_address_def, bind_def, get_current_context_def,
       fail_def, return_def, domain_check_def, ignore_bind_def, bind_def,
       set_domain_def]
    \\ Cases_on`s.msdomain` \\ gvs[]
    \\ rpt(pop_assum mp_tac)\\rw[])
  \\ gen_tac
  \\ irule get_accounts_ignore_extra_domain_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    rw[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ gs[]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[]
  )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ strip_tac
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ simp[ignore_bind_def]
    \\ qmatch_goalsub_abbrev_tac`account_empty la`
    \\ qmatch_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`account_empty lb`
    \\ qunabbrev_tac`lhs`
    \\ `account_empty la = account_empty lb`
    by (
      gvs[Abbr`la`, Abbr`lb`, account_empty_def, lookup_account_def]
      \\ gvs[accounts_agree_modulo_storage_def, fIN_IN]
      \\ gvs[account_state_component_equality] )
    \\ gvs[]
    \\ qmatch_goalsub_abbrev_tac`FST pp`
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`n1 < b1`
    \\ qmatch_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`n2 < b1`
    \\ qunabbrev_tac`lhs`
    \\ `n1 = n2`
    by (
      gvs[Abbr`n1`,Abbr`n2`,lookup_account_def,accounts_agree_modulo_storage_def]
      \\ gvs[fIN_IN, account_state_component_equality]
      \\ fsrw_tac[DNF_ss][]
      \\ first_x_assum irule
      \\ gvs[get_callee_def, bind_def, get_current_context_def, CaseEq"prod",
             CaseEq"sum", return_def, CaseEq"bool", fail_def]
      \\ gvs[expand_memory_def, bind_def, get_current_context_def, CaseEq"prod",
             CaseEq"sum", return_def, CaseEq"bool", fail_def]
      \\ gvs[set_current_context_def, bind_def, get_current_context_def, CaseEq"prod",
             CaseEq"sum", return_def, CaseEq"bool", fail_def]
      \\ gvs[Abbr`b3`, assert_not_static_def, bind_def, set_current_context_def,
             get_current_context_def, CaseEq"prod", ignore_bind_def, assert_def,
             CaseEq"sum", return_def, CaseEq"bool", fail_def, COND_RATOR,
             get_static_def, consume_gas_def, get_gas_left_def]
      \\ Cases_on`HD s.contexts` \\ gvs[]
      \\ Cases_on`s.contexts` \\ gvs[] )
    \\ gs[]
    \\ IF_CASES_TAC \\ gs[]
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ IF_CASES_TAC \\ gs[]
    \\ `la.code = lb.code`
    by (
      gs[Abbr`la`,Abbr`lb`,lookup_account_def, accounts_agree_modulo_storage_def]
      \\ gvs[account_state_component_equality, fIN_IN] )
    \\ simp[])
  \\ gen_tac
  \\ simp[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ simp[]
  \\ reverse conj_tac
  >- ( rw[get_gas_left_def, bind_def, get_current_context_def,
          fail_def, return_def] )
  \\ gen_tac
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse conj_tac
  >- (
    simp[consume_gas_def, bind_def, get_current_context_def,
         ignore_bind_def, return_def, fail_def, assert_def, COND_RATOR]
    \\ gen_tac \\ strip_tac
    \\ IF_CASES_TAC \\ gs[]
    \\ IF_CASES_TAC \\ gs[]
    \\ simp[set_current_context_def, return_def]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[])
  \\ simp[]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse conj_tac
  >- (
    simp[Abbr`b3`]
    \\ reverse conj_tac >- rw[]
    \\ rw[assert_not_static_def, return_def, bind_def, ignore_bind_def,
          get_static_def, assert_def, get_current_context_def, fail_def]
    \\ rw[]
    \\ Cases_on`s.contexts` \\ gvs[])
  \\ simp[]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse conj_tac
  >- (
    simp[]
    \\ rw[expand_memory_def, get_current_context_def, set_current_context_def,
          bind_def, return_def, fail_def]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[])
  \\ simp[]
  \\ irule get_callee_ignores_extra_domain_pred_bind
  \\ simp[] \\ gen_tac
  \\ IF_CASES_TAC
  >- ( irule ignores_extra_domain_pred_imp \\ simp[] )
  \\ irule ignores_extra_domain_pred_imp
  \\ tac
QED

Theorem ensure_storage_in_domain_ignores_extra_domain[simp]:
  ignores_extra_domain (ensure_storage_in_domain a)
Proof
  rw[ensure_storage_in_domain_def, ignores_extra_domain_def, assert_def,
     domain_check_def, CaseEq"domain_mode", CaseEq"bool"]
  \\ gvs[return_def, fail_def]
  >- gs[subdomain_def, fIN_IN, SUBSET_DEF]
  \\ rw[]
  \\ gs[domain_compatible_def, states_agree_modulo_accounts_def]
  \\ qpat_x_assum`Enforce _ = _`(assume_tac o SYM) \\ gs[]
QED

Theorem step_create_ignores_extra_domain:
  ignores_extra_domain_pred
  (λs. ∀c r t d.
    s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
    c.msgParams.callee ∈ toSet d.addresses)
  (step_create x)
Proof
  simp[step_create_def]
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    rw[pop_stack_def, bind_def, get_current_context_def, fail_def, return_def,
       ignore_bind_def, assert_def, set_current_context_def]
    \\ pop_assum mp_tac \\ rw[] \\ gvs[]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ gen_tac
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ gen_tac
  \\ simp[ignore_bind_def]
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    rw[consume_gas_def, bind_def, get_current_context_def,
       fail_def, return_def, assert_def, ignore_bind_def,
       set_current_context_def]
    \\ rpt (pop_assum mp_tac) \\ rw[] \\ gvs[]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    rw[expand_memory_def, bind_def, get_current_context_def,
       fail_def, return_def, assert_def, ignore_bind_def,
       set_current_context_def]
    \\ Cases_on`s.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ irule ignores_extra_domain_imp_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    rw[read_memory_def, bind_def, get_current_context_def,
       fail_def, return_def, assert_def, ignore_bind_def,
       set_current_context_def])
  \\ gen_tac
  \\ irule get_callee_ignores_extra_domain_pred_bind
  \\ simp[] \\ gen_tac
  \\ irule get_accounts_ignore_extra_domain_pred_bind
  \\ simp[]
  \\ conj_tac
  >- (
    rw[domain_compatible_def, states_agree_modulo_accounts_def]
    \\ gs[]
    \\ Cases_on`s'.contexts` \\ gvs[]
    \\ Cases_on`h` \\ gvs[] )
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ strip_tac
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`address_for_create _ la.nonce`
    \\ qmatch_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`address_for_create _ lb.nonce`
    \\ qunabbrev_tac`lhs`
    \\ `la.nonce = lb.nonce ∧ la.balance = lb.balance`
    by (
      gvs[Abbr`la`, Abbr`lb`, account_empty_def, lookup_account_def]
      \\ gvs[accounts_agree_modulo_storage_def, fIN_IN]
      \\ gvs[account_state_component_equality] )
    \\ gvs[]
    \\ rpt (irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac)
    \\ IF_CASES_TAC \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`account_already_created la1`
    \\ qmatch_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`account_already_created la2`
    \\ qunabbrev_tac`lhs`
    \\ `account_already_created la1 = account_already_created la2`
    by (
      qmatch_asmsub_abbrev_tac`ensure_storage_in_domain toCreate`
      \\ gvs[Abbr`la1`, Abbr`la2`, account_already_created_def, lookup_account_def]
      \\ gvs[accounts_agree_modulo_storage_def, fIN_IN,
             ensure_storage_in_domain_def, assert_def]
      \\ gvs[account_state_component_equality]
      \\ rw[] \\ gvs[domain_check_def]
      \\ qmatch_asmsub_rename_tac`domain_mode_CASE st.msdomain`
      \\ `st.msdomain = s.msdomain`
      by (
        gvs[get_num_contexts_def, set_return_data_def, assert_not_static_def,
            bind_def, return_def, ignore_bind_def, get_static_def,
            domain_check_def,
            get_current_context_def, assert_def, fail_def, CaseEq"prod",
            CaseEq"sum", set_current_context_def, CaseEq"bool", consume_gas_def,
            CaseEq"domain_mode", get_gas_left_def, access_address_def, set_domain_def] )
      \\ gvs[fail_def, return_def, CaseEq"bool"]
      \\ `toCreate ∈ toSet d.addresses`
      by (
        gvs[access_address_def, return_def, fail_def, CaseEq"prod",
            CaseEq"bool", fIN_IN, domain_check_def] )
      \\ gs[])
    \\ gs[] )
  \\ gen_tac
  \\ irule ignores_extra_domain_pred_imp
  \\ tac
QED

Theorem step_inst_ignores_extra_domain:
  ignores_extra_domain_pred
  (λs. ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
       c.msgParams.callee ∈ toSet d.addresses)
  (step_inst op)
Proof
  Cases_on`op` \\ rw[step_inst_def]
  \\ TRY (irule ignores_extra_domain_pred_imp \\ simp[] \\ tac \\ NO_TAC)
  \\ TRY $ irule step_self_balance_ignore_extra_domain
  \\ TRY $ irule step_create_ignores_extra_domain
  \\ TRY $ irule step_call_ignores_extra_domain
QED

Theorem preserves_domain_has_callee_bind:
  preserves_domain_has_callee p g ∧
  (∀s. p s ⇒ p (SND (g s))) ∧
  (∀x. preserves_domain_has_callee p (f x))
  ⇒
  preserves_domain_has_callee p (monad_bind g f)
Proof
  rw[bind_def, preserves_domain_has_callee_def]
  \\ gvs[CaseEq"prod",CaseEq"sum"]
  \\ metis_tac[SND]
QED

Theorem preserves_domain_has_callee_ignore_bind:
  preserves_domain_has_callee p g ∧
  (∀s. p s ⇒ p (SND (g s))) ∧
  preserves_domain_has_callee p f
  ⇒
  preserves_domain_has_callee p (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule preserves_domain_has_callee_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_get_current_context_bind:
  (∀x. preserves_domain_has_callee
       (λs. p s ∧ ∀d. s.msdomain = Enforce d ⇒ x.msgParams.callee ∈ toSet d.addresses)
       (f x))
  ⇒
  preserves_domain_has_callee p (monad_bind get_current_context f)
Proof
  rw[preserves_domain_has_callee_def, bind_def, get_current_context_def,
     return_def, fail_def, CaseEq"prod", CaseEq"bool", CaseEq"sum"]
  \\ gvs[]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ Cases_on`h` \\ gvs[]
  \\ metis_tac[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_set_current_context:
  (∀s. p s ⇒ ∀d. s.msdomain = Enforce d ⇒ x.msgParams.callee ∈ toSet d.addresses)
  ⇒
  preserves_domain_has_callee p (set_current_context x)
Proof
  rw[set_current_context_def, preserves_domain_has_callee_def]
  \\ gvs[fail_def, return_def, CaseEq"prod", CaseEq"bool"]
  \\ gs[domain_has_callee_def]
  \\ metis_tac[]
QED

Theorem preserves_domain_has_callee_set_return_data[simp]:
  preserves_domain_has_callee (K T) (set_return_data _)
Proof
  rw[set_return_data_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context
  \\ rw[]
QED

Theorem preserves_domain_has_callee_finish[simp]:
  preserves_domain_has_callee (K T) (finish)
Proof
  rw[finish_def, preserves_domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_assert[simp]:
  preserves_domain_has_callee (K T) (assert b e)
Proof
  rw[assert_def, preserves_domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_mono:
  preserves_domain_has_callee q f ∧ (∀s. p s ⇒ q s) ⇒
  preserves_domain_has_callee p f
Proof
  rw[preserves_domain_has_callee_def]
  \\ metis_tac[SND]
QED

Theorem assert_msdomain[simp]:
  (SND (assert b e s)).msdomain = s.msdomain
Proof
  rw[assert_def]
QED

Theorem return_msdomain[simp]:
  (SND (return x s)).msdomain = s.msdomain
Proof
  rw[return_def]
QED

Theorem fail_msdomain[simp]:
  (SND (fail x s)).msdomain = s.msdomain
Proof
  rw[fail_def]
QED

Theorem set_current_context_msdomain[simp]:
  (SND (set_current_context x s)).msdomain = s.msdomain
Proof
  rw[set_current_context_def]
QED

Theorem preserves_domain_has_callee_return[simp]:
  preserves_domain_has_callee (K T) (return x)
Proof
  rw[return_def, preserves_domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_imp[simp]:
  preserves_domain_has_callee (K T) f ⇒
  preserves_domain_has_callee p f
Proof
  strip_tac
  \\ irule preserves_domain_has_callee_mono
  \\ qexists_tac`K T`
  \\ rw[]
QED

Theorem preserves_domain_has_callee_pop_stack[simp]:
  preserves_domain_has_callee (K T) (pop_stack n)
Proof
  rw[pop_stack_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_consume_gas[simp]:
  preserves_domain_has_callee (K T) (consume_gas n)
Proof
  rw[consume_gas_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_push_stack[simp]:
  preserves_domain_has_callee (K T) (push_stack n)
Proof
  rw[push_stack_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_step_binop[simp]:
  preserves_domain_has_callee (K T) (step_binop x y)
Proof
  rw[step_binop_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_modop[simp]:
  preserves_domain_has_callee (K T) (step_modop x y)
Proof
  rw[step_modop_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_monop[simp]:
  preserves_domain_has_callee (K T) (step_monop x y)
Proof
  rw[step_monop_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_exp[simp]:
  preserves_domain_has_callee (K T) step_exp
Proof
  rw[step_exp_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_memory_expansion_info[simp]:
  preserves_domain_has_callee (K T) (memory_expansion_info x y)
Proof
  simp[memory_expansion_info_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ simp[]
QED

Theorem preserves_domain_has_callee_expand_memory[simp]:
  preserves_domain_has_callee (K T) (expand_memory x)
Proof
  simp[expand_memory_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_read_memory[simp]:
  preserves_domain_has_callee (K T) (read_memory x y)
Proof
  rw[read_memory_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_keccak256[simp]:
  preserves_domain_has_callee (K T) step_keccak256
Proof
  rw[step_keccak256_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_context[simp]:
  preserves_domain_has_callee (K T) (step_context x y)
Proof
  rw[step_context_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_msgParams[simp]:
  preserves_domain_has_callee (K T) (step_msgParams x y)
Proof
  rw[step_msgParams_def]
QED

Theorem preserves_domain_has_callee_get_tx_params[simp]:
  preserves_domain_has_callee (K T) get_tx_params
Proof
  rw[get_tx_params_def, preserves_domain_has_callee_def, return_def]
QED

Theorem preserves_domain_has_callee_step_txParams[simp]:
  preserves_domain_has_callee (K T) (step_txParams x y)
Proof
  rw[step_txParams_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_access_address[simp]:
  preserves_domain_has_callee (K T) (access_address a)
Proof
  rw[access_address_def, preserves_domain_has_callee_def, CaseEq"bool",
     return_def, fail_def, domain_check_def, CaseEq"domain_mode"]
  \\ gvs[domain_has_callee_def, set_domain_def, bind_def,
         ignore_bind_def, return_def]
QED

Theorem preserves_domain_has_callee_get_accounts[simp]:
  preserves_domain_has_callee (K T) get_accounts
Proof
  rw[get_accounts_def, preserves_domain_has_callee_def, return_def]
QED

Theorem preserves_domain_has_callee_step_balance[simp]:
  preserves_domain_has_callee (K T) step_balance
Proof
  rw[step_balance_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_call_data[simp]:
  preserves_domain_has_callee (K T) get_call_data
Proof
  rw[get_call_data_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_step_call_data_load[simp]:
  preserves_domain_has_callee (K T) step_call_data_load
Proof
  rw[step_call_data_load_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_write_memory[simp]:
  preserves_domain_has_callee (K T) (write_memory x y)
Proof
  rw[write_memory_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context
  \\ rw[]
QED

Theorem preserves_domain_has_callee_copy_to_memory[simp]:
  (∀g. f = SOME g ⇒ preserves_domain_has_callee (K T) g)
  ⇒
  preserves_domain_has_callee (K T) (copy_to_memory a b c d f)
Proof
  strip_tac
  \\ simp[copy_to_memory_def, UNCURRY]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ TOP_CASE_TAC
  >- (
    irule preserves_domain_has_callee_bind \\ rw[]
    \\ irule preserves_domain_has_callee_ignore_bind \\ rw[] )
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_copy_to_memory[simp]:
  (∀g. f = SOME g ⇒ preserves_domain_has_callee (K T) g)
  ⇒
  preserves_domain_has_callee (K T) (step_copy_to_memory x f)
Proof
  rw[step_copy_to_memory_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_copy_to_memory
QED

Theorem preserves_domain_has_callee_get_current_code[simp]:
  preserves_domain_has_callee (K T) get_current_code
Proof
  rw[get_current_code_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_get_code[simp]:
  preserves_domain_has_callee (K T) (get_code x)
Proof
  rw[get_code_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_ext_code_size[simp]:
  preserves_domain_has_callee (K T) step_ext_code_size
Proof
  rw[step_ext_code_size_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_ext_code_copy[simp]:
  preserves_domain_has_callee (K T) step_ext_code_copy
Proof
  rw[step_ext_code_copy_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_return_data[simp]:
  preserves_domain_has_callee (K T) (get_return_data)
Proof
  rw[get_return_data_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_get_return_data_check[simp]:
  preserves_domain_has_callee (K T) (get_return_data_check x y)
Proof
  rw[get_return_data_check_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_return_data_copy[simp]:
  preserves_domain_has_callee (K T) step_return_data_copy
Proof
  rw[step_return_data_copy_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_copy_to_memory \\ rw[]
QED

Theorem preserves_domain_has_callee_step_ext_code_hash[simp]:
  preserves_domain_has_callee (K T) step_ext_code_hash
Proof
  rw[step_ext_code_hash_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_block_hash[simp]:
  preserves_domain_has_callee (K T) step_block_hash
Proof
  rw[step_block_hash_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_callee[simp]:
  preserves_domain_has_callee (K T) get_callee
Proof
  rw[get_callee_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_step_self_balance[simp]:
  preserves_domain_has_callee (K T) step_self_balance
Proof
  rw[step_self_balance_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_pop[simp]:
  preserves_domain_has_callee (K T) step_pop
Proof
  rw[step_pop_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_mload[simp]:
  preserves_domain_has_callee (K T) step_mload
Proof
  rw[step_mload_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_mstore[simp]:
  preserves_domain_has_callee (K T) (step_mstore x)
Proof
  simp[step_mstore_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
QED

Theorem preserves_domain_has_callee_access_slot[simp]:
  preserves_domain_has_callee (K T) (access_slot x)
Proof
  rw[access_slot_def, preserves_domain_has_callee_def,
     CaseEq"bool", return_def, fail_def, domain_check_def,
     bind_def, ignore_bind_def, set_domain_def, CaseEq"domain_mode"]
  \\ gvs[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_get_tStorage[simp]:
  preserves_domain_has_callee (K T) get_tStorage
Proof
  rw[get_tStorage_def, preserves_domain_has_callee_def, return_def]
QED

Theorem preserves_domain_has_callee_step_sload[simp]:
  preserves_domain_has_callee (K T) (step_sload x)
Proof
  rw[step_sload_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[]
  \\ reverse conj_tac >- rw[]
  \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_static[simp]:
  preserves_domain_has_callee (K T) get_static
Proof
  rw[get_static_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_assert_not_static[simp]:
  preserves_domain_has_callee (K T) assert_not_static
Proof
  rw[assert_not_static_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_set_tStorage[simp]:
  preserves_domain_has_callee (K T) (set_tStorage x)
Proof
  rw[set_tStorage_def, preserves_domain_has_callee_def, return_def]
  \\ gs[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_write_transient_storage[simp]:
  preserves_domain_has_callee (K T) (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_gas_left[simp]:
  preserves_domain_has_callee (K T) get_gas_left
Proof
  rw[get_gas_left_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem preserves_domain_has_callee_get_original[simp]:
  preserves_domain_has_callee (K T) get_original
Proof
  rw[get_original_def, preserves_domain_has_callee_def, CaseEq"bool",
     return_def, fail_def]
  \\ gs[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_update_gas_refund[simp]:
  preserves_domain_has_callee (K T) (update_gas_refund x)
Proof
  Cases_on`x`
  \\ rw[update_gas_refund_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context
  \\ rw[]
QED

Theorem preserves_domain_has_callee_step_sstore_gas_consumption[simp]:
  preserves_domain_has_callee (K T) (step_sstore_gas_consumption x y z)
Proof
  simp[step_sstore_gas_consumption_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
QED

Theorem preserves_domain_has_callee_update_accounts[simp]:
  preserves_domain_has_callee (K T) (update_accounts f )
Proof
  rw[update_accounts_def, preserves_domain_has_callee_def, return_def]
  \\ gs[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_write_storage[simp]:
  preserves_domain_has_callee (K T) (write_storage x y z)
Proof
  rw[write_storage_def]
QED

Theorem preserves_domain_has_callee_step_sstore[simp]:
  preserves_domain_has_callee (K T) (step_sstore x)
Proof
  simp[step_sstore_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ IF_CASES_TAC \\ gs[]
  >- (
    irule preserves_domain_has_callee_ignore_bind \\ rw[]
    \\ irule preserves_domain_has_callee_ignore_bind \\ rw[] )
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_set_jump_dest[simp]:
  preserves_domain_has_callee (K T) (set_jump_dest x)
Proof
  rw[set_jump_dest_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_step_jump[simp]:
  preserves_domain_has_callee (K T) step_jump
Proof
  simp[step_jump_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_jumpi[simp]:
  preserves_domain_has_callee (K T) step_jumpi
Proof
  simp[step_jumpi_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_push[simp]:
  preserves_domain_has_callee (K T) (step_push x y)
Proof
  simp[step_push_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_dup[simp]:
  preserves_domain_has_callee (K T) (step_dup y)
Proof
  simp[step_dup_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_swap[simp]:
  preserves_domain_has_callee (K T) (step_swap y)
Proof
  simp[step_swap_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_push_logs[simp]:
  preserves_domain_has_callee (K T) (push_logs y)
Proof
  rw[push_logs_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_step_log[simp]:
  preserves_domain_has_callee (K T) (step_log y)
Proof
  simp[step_log_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_revert[simp]:
  preserves_domain_has_callee (K T) revert
Proof
  rw[revert_def, preserves_domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_step_return[simp]:
  preserves_domain_has_callee (K T) (step_return _)
Proof
  simp[step_return_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_step_invalid[simp]:
  preserves_domain_has_callee (K T) step_invalid
Proof
  simp[step_invalid_def]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_add_to_delete[simp]:
  preserves_domain_has_callee (K T) (add_to_delete x)
Proof
  rw[add_to_delete_def, preserves_domain_has_callee_def, return_def]
  \\ gs[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_step_self_destruct[simp]:
  preserves_domain_has_callee (K T) step_self_destruct
Proof
  rw[step_self_destruct_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
QED

Theorem preserves_domain_has_callee_unuse_gas[simp]:
  preserves_domain_has_callee (K T) (unuse_gas x)
Proof
  rw[unuse_gas_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_inc_pc[simp]:
  preserves_domain_has_callee (K T) inc_pc
Proof
  rw[inc_pc_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ irule preserves_domain_has_callee_set_current_context \\ rw[]
QED

Theorem preserves_domain_has_callee_abort_call_value[simp]:
  preserves_domain_has_callee (K T) (abort_call_value x)
Proof
  rw[abort_call_value_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_num_contexts[simp]:
  preserves_domain_has_callee (K T) get_num_contexts
Proof
  rw[get_num_contexts_def, preserves_domain_has_callee_def, return_def]
QED

Theorem preserves_domain_has_callee_abort_unuse[simp]:
  preserves_domain_has_callee (K T) (abort_unuse x)
Proof
  rw[abort_unuse_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem preserves_domain_has_callee_get_rollback[simp]:
  preserves_domain_has_callee (K T) get_rollback
Proof
  rw[get_rollback_def, preserves_domain_has_callee_def, return_def]
QED

Theorem SND_get_rollback[simp]:
  SND (get_rollback s) = s
Proof
  rw[get_rollback_def]
QED

Theorem SND_get_current_context[simp]:
  SND (get_current_context s) = s
Proof
  rw[get_current_context_def]
QED

Theorem SND_read_memory[simp]:
  SND (read_memory x y s) = s
Proof
  rw[read_memory_def, bind_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ mp_tac SND_get_current_context
  \\ asm_rewrite_tac[] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[]
QED

Theorem SND_get_caller[simp]:
  SND (get_caller s) = s
Proof
  rw[get_caller_def, bind_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ mp_tac SND_get_current_context
  \\ asm_rewrite_tac[] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[]
QED

Theorem preserves_domain_has_callee_get_caller[simp]:
  preserves_domain_has_callee (K T) get_caller
Proof
  rw[get_caller_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem SND_get_value[simp]:
  SND (get_value s) = s
Proof
  rw[get_value_def, bind_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ mp_tac SND_get_current_context
  \\ asm_rewrite_tac[] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[]
QED

Theorem preserves_domain_has_callee_get_value[simp]:
  preserves_domain_has_callee (K T) get_value
Proof
  rw[get_value_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind
  \\ rw[]
QED

Theorem SND_get_static[simp]:
  SND (get_static s) = s
Proof
  rw[get_static_def, bind_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ mp_tac SND_get_current_context
  \\ asm_rewrite_tac[] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[]
QED

Theorem preserves_domain_has_callee_push_context:
  (∀s. p s ⇒ ∀d. s.msdomain = Enforce d ⇒
      (FST cr).msgParams.callee ∈ toSet d.addresses)
  ⇒
  preserves_domain_has_callee p (push_context cr)
Proof
  rw[push_context_def, preserves_domain_has_callee_def, return_def]
  \\ gs[domain_has_callee_def]
  \\ Cases_on`cr` \\ gvs[]
  \\ metis_tac[]
QED

Theorem SND_push_context[simp]:
  SND (push_context cr s) =
  s with contexts updated_by CONS cr
Proof
  rw[push_context_def]
QED

Theorem preserves_domain_has_callee_fail[simp]:
  preserves_domain_has_callee (K T) (fail x)
Proof
  rw[fail_def, preserves_domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_precompiles[simp]:
    preserves_domain_has_callee (K T) precompile_ecrecover
  ∧ preserves_domain_has_callee (K T) precompile_sha2_256
  ∧ preserves_domain_has_callee (K T) precompile_ripemd_160
  ∧ preserves_domain_has_callee (K T) precompile_identity
  ∧ preserves_domain_has_callee (K T) precompile_modexp
  ∧ preserves_domain_has_callee (K T) precompile_ecadd
  ∧ preserves_domain_has_callee (K T) precompile_ecmul
  ∧ preserves_domain_has_callee (K T) precompile_ecpairing
  ∧ preserves_domain_has_callee (K T) precompile_blake2f
Proof
  rw[precompile_ecrecover_def,
     precompile_sha2_256_def,
     precompile_ripemd_160_def,
     precompile_identity_def,
     precompile_modexp_def,
     precompile_ecadd_def,
     precompile_ecmul_def,
     precompile_ecpairing_def,
     precompile_blake2f_def]
  \\ rpt (
    (irule preserves_domain_has_callee_bind ORELSE
     irule preserves_domain_has_callee_ignore_bind)
    \\ rw[])
QED

Theorem preserves_domain_has_callee_dispatch_precompiles[simp]:
  preserves_domain_has_callee (K T) (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem preserves_domain_has_callee_proceed_call[simp]:
  (∀s d. p s ∧ s.msdomain = Enforce d ⇒
           b ∈ toSet d.addresses ∧
           c ∈ toSet d.addresses) ∧
  (∀s. p s ⇒ ∀x. p (SND (update_accounts x s))) ∧
  (∀s. p s ⇒ ∀cr. (FST cr).msgParams.callee ∈ {b;c} ⇒
                   p (s with contexts updated_by CONS cr))
  ⇒
  preserves_domain_has_callee p (proceed_call a b c d e f g h i)
Proof
  strip_tac
  \\ simp[proceed_call_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ conj_tac >- rw[]
  \\ conj_tac >- rw[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ conj_tac
  >- (
    gen_tac \\ strip_tac
    \\ first_x_assum irule
    \\ rw[initial_msg_params_def] )
  \\ conj_tac
  >- (
    irule preserves_domain_has_callee_push_context
    \\ rw[initial_msg_params_def]
    \\ first_x_assum (drule_then drule) \\ rw[])
  \\ rw[]
QED

Theorem preserves_domain_has_callee_access_address_bind:
  (∀x. preserves_domain_has_callee
         (λs. ∀d. s.msdomain = Enforce d ⇒ a ∈ toSet d.addresses ) (f x))
  ⇒
  preserves_domain_has_callee p
    (monad_bind (access_address a) f)
Proof
  rw[preserves_domain_has_callee_def, ignore_bind_def, bind_def,
     access_address_def, return_def, fail_def, CaseEq"bool",
     CaseEq"prod", CaseEq"sum", fIN_IN, CaseEq"domain_mode",
     domain_check_def, set_domain_def]
  \\ TRY (
    first_x_assum (drule_at (Pos(el 3)))
    \\ rw[]
    \\ first_x_assum irule
    \\ gs[domain_has_callee_def, domain_check_def]
    \\ rw[] \\ gs[] \\ NO_TAC)
  \\ TRY (
    first_x_assum irule
    \\ goal_assum (drule_at (Pat`f _ _ = _`))
    \\ rw[]
    \\ gs[domain_has_callee_def, domain_check_def] \\ NO_TAC)
QED

Theorem SND_get_accounts[simp]:
  SND (get_accounts s) = s
Proof
  rw[get_accounts_def]
QED

Theorem SND_get_gas_left[simp]:
  SND (get_gas_left s) = s
Proof
  rw[get_gas_left_def, get_current_context_def, bind_def, fail_def, return_def]
QED

Theorem SND_assert_not_static[simp]:
  SND (assert_not_static s) = s
Proof
  rw[assert_not_static_def, bind_def, ignore_bind_def, get_static_def,
     get_current_context_def, fail_def, return_def, assert_def]
QED

Theorem SND_expand_memory_msdomain[simp]:
  (SND (expand_memory x s)).msdomain = s.msdomain
Proof
  rw[expand_memory_def, get_current_context_def, bind_def, ignore_bind_def,
     return_def, fail_def, set_current_context_def]
QED

Theorem preserves_domain_has_callee_get_callee_bind:
  (∀x. preserves_domain_has_callee (λs. p s ∧ ∀d. s.msdomain = Enforce d ⇒
                                                x ∈ toSet d.addresses)
       (f x))
  ⇒
  preserves_domain_has_callee p (monad_bind get_callee f)
Proof
  rw[bind_def, get_callee_def, get_current_context_def,
     preserves_domain_has_callee_def]
  \\ gvs[CaseEq"prod",CaseEq"bool",CaseEq"sum",fail_def,return_def]
  \\ first_x_assum irule
  \\ goal_assum (drule_at(Pat`f _ _ = _`)) \\ rw[]
  \\ gs[domain_has_callee_def]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ Cases_on`h` \\ gvs[]
QED

Theorem SND_set_return_data_msdomain[simp]:
  (SND (set_return_data x s)).msdomain = s.msdomain
Proof
  rw[set_return_data_def, bind_def, get_current_context_def,
     fail_def, return_def]
QED

Theorem SND_get_num_contexts[simp]:
  SND (get_num_contexts s) = s
Proof
  rw[get_num_contexts_def, bind_def, get_current_context_def,
     fail_def, return_def]
QED

Theorem preserves_domain_has_callee_step_call[simp]:
  preserves_domain_has_callee (K T) (step_call x)
Proof
  simp[step_call_def, UNCURRY]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_access_address_bind
  \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ conj_tac >- rw[]
  \\ conj_tac >- rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`SND cg`
  \\ irule preserves_domain_has_callee_get_callee_bind \\ simp[]
  \\ gen_tac
  \\ IF_CASES_TAC >- rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ IF_CASES_TAC >- rw[]
  \\ irule preserves_domain_has_callee_proceed_call
  \\ simp[]
QED

Theorem preserves_domain_has_callee_proceed_create:
  (∀s d. p s ∧ s.msdomain = Enforce d ⇒ b ∈ toSet d.addresses) ∧
  (∀s. p s ⇒ ∀x. p (SND (update_accounts x s))) ∧
  (∀s. p s ⇒ ∀cr. (FST cr).msgParams.callee = b ⇒
                   p (s with contexts updated_by CONS cr))
  ⇒
  preserves_domain_has_callee p (proceed_create a b c d e)
Proof
  strip_tac
  \\ rw[proceed_create_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_push_context
  \\ rw[initial_msg_params_def]
  \\ metis_tac[]
QED

Theorem preserves_domain_has_callee_ensure_storage_in_domain[simp]:
  preserves_domain_has_callee (K T) (ensure_storage_in_domain x)
Proof
  rw[ensure_storage_in_domain_def, preserves_domain_has_callee_def]
  \\ gvs[assert_def, domain_check_def, CaseEq"domain_mode", CaseEq"bool"]
  \\ gvs[fail_def, return_def, bind_def, ignore_bind_def, set_domain_def]
  \\ gs[domain_has_callee_def]
QED

Theorem preserves_domain_has_callee_abort_create_exists[simp]:
  preserves_domain_has_callee (K T) (abort_create_exists x)
Proof
  rw[abort_create_exists_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
QED

Theorem SND_ensure_storage_in_domain_msdomain_eq_Enforce[simp]:
  ((SND (ensure_storage_in_domain x y)).msdomain = Enforce d) =
  (y.msdomain = Enforce d)
Proof
  rw[ensure_storage_in_domain_def, domain_check_def]
  \\ CASE_TAC \\ rw[set_domain_def, bind_def, ignore_bind_def]
  \\ rw[return_def]
QED

Theorem preserves_domain_has_callee_step_create[simp]:
  preserves_domain_has_callee (K T) (step_create x)
Proof
  simp[step_create_def]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ simp[ignore_bind_def]
  \\ irule preserves_domain_has_callee_access_address_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[]
  \\ qpat_abbrev_tac`b0 = COND _ _ _`
  \\ IF_CASES_TAC >- rw[]
  \\ IF_CASES_TAC >- rw[]
  \\ irule preserves_domain_has_callee_proceed_create
  \\ rw[]
QED

Theorem step_inst_preserves_domain_has_callee[simp]:
  preserves_domain_has_callee (K T) (step_inst op)
Proof
  Cases_on`op` \\ rw[step_inst_def]
  \\ TRY (irule preserves_domain_has_callee_ignore_bind \\ rw[])
  \\ TRY (irule preserves_domain_has_callee_step_copy_to_memory \\ rw[])
QED

Theorem preserves_domain_has_callee_inc_pc_or_jump[simp]:
  preserves_domain_has_callee (K T) (inc_pc_or_jump x)
Proof
  rw[inc_pc_or_jump_def]
  \\ irule preserves_domain_has_callee_get_current_context_bind \\ rw[]
  \\ TOP_CASE_TAC
  >- ( irule preserves_domain_has_callee_set_current_context \\ rw[] )
  \\ irule preserves_domain_has_callee_ignore_bind \\ rw[]
  >- ( irule preserves_domain_has_callee_set_current_context \\ rw[] )
QED

Theorem step_ignores_extra_domain_pred:
  ignores_extra_domain_pred
  (λs. ∀c r t d. s.contexts = (c,r)::t ∧ s.msdomain = Enforce d ⇒
       c.msgParams.callee ∈ toSet d.addresses)
  step
Proof
  rw[step_def]
  \\ irule handle_ignores_extra_domain_pred_allow
  \\ simp[]
  \\ reverse conj_asm2_tac
  >- (
    reverse conj_tac
    >- (
      irule ignores_extra_domain_imp_pred_bind \\ rw[]
      >- irule step_inst_ignores_extra_domain
      \\ simp[ignore_bind_def]
      \\ TOP_CASE_TAC
      >- irule step_inst_ignores_extra_domain
      \\ irule ignores_extra_domain_imp_pred_pred_bind \\ simp[]
      \\ reverse conj_tac
      >- (
        reverse conj_asm2_tac
        >- irule step_inst_ignores_extra_domain
        \\ rw[]
        \\ qmatch_asmsub_rename_tac`step_inst op`
        \\ mp_tac step_inst_preserves_domain_has_callee
        \\ rewrite_tac[preserves_domain_has_callee_def]
        \\ disch_then(qspec_then`s`mp_tac)
        \\ Cases_on`step_inst op s`
        \\ rw[domain_has_callee_def] \\ gvs[])
      \\ irule ignores_extra_domain_pred_imp \\ rw[] )
    \\ rw[]
    >- rw[handle_step_def, reraise_def]
    \\ irule ignores_extra_domain_pred_imp \\ rw[] )
  \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`SND (f s)`
  \\ `domain_has_callee s` by fs[domain_has_callee_def]
  \\ `preserves_domain_has_callee (K T) f` by (
    qunabbrev_tac`f`
    \\ irule preserves_domain_has_callee_get_current_context_bind
    \\ simp[] \\ qx_gen_tac`ss`
    \\ IF_CASES_TAC >- rw[]
    \\ TOP_CASE_TAC >- rw[]
    \\ irule preserves_domain_has_callee_imp
    \\ irule preserves_domain_has_callee_ignore_bind \\ simp[])
  \\ gs[preserves_domain_has_callee_def]
  \\ first_x_assum drule
  \\ simp[domain_has_callee_def]
  \\ metis_tac[PAIR]
QED

val () = export_theory();
