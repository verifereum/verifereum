Theory vfmDomainSeparation
Ancestors
  arithmetic combin list pair pred_set finite_set
  vfmState vfmContext vfmExecution vfmExecutionProp
Libs
  BasicProvers

Definition subdomain_def:
  subdomain s1 s2 ⇔
  toSet s1.addresses ⊆ toSet s2.addresses ∧
  toSet s1.storageKeys ⊆ toSet s2.storageKeys ∧
  toSet s1.fullStorages ⊆ toSet s2.fullStorages
End

Theorem subdomain_refl[simp]:
  subdomain d d
Proof
  rw[subdomain_def]
QED

Theorem subdomain_trans:
  subdomain d1 d2 ∧ subdomain d2 d3 ⇒
  subdomain d1 d3
Proof
  rw[subdomain_def]
  \\ metis_tac[SUBSET_TRANS]
QED

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
  \\ gvs[CaseEq"prod",CaseEq"sum"]
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
    \\ qmatch_asmsub_rename_tac`f s = (_,s')`
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
    \\ qmatch_asmsub_rename_tac`f s = (_,s1)`
    \\ first_assum(qspec_then`s1`mp_tac)
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

Theorem step_blob_hash_ignore_extra_domain[simp]:
  ignores_extra_domain step_blob_hash
Proof
  rw[step_blob_hash_def] \\ tac
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
  \\ gvs[LIST_REL_SNOC, MAP_SNOC]
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
  \\ gvs[LIST_REL_SNOC, MAP_SNOC]
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
  \\ gvs[LIST_REL_SNOC, MAP_SNOC]
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
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ tac
QED

Theorem precompile_ripemd_160_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
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
  \\ CASE_TAC
  \\ rw[]
  \\ CASE_TAC
  \\ tac
QED

Theorem precompile_ecmul_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecmul
Proof
  rw[precompile_ecmul_def] \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ CASE_TAC
  \\ tac
QED

Theorem precompile_ecpairing_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_ecpairing
Proof
  rw[precompile_ecpairing_def] \\ tac
  \\ CASE_TAC \\ rw[]
  \\ tac
QED

Theorem precompile_point_eval_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_point_eval
Proof
  rw[precompile_point_eval_def] \\ tac
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ tac
QED

Theorem precompile_blake2f_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_blake2f
Proof
  rw[precompile_blake2f_def] \\ tac
QED

Theorem precompile_bls_g1add_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem precompile_bls_g1msm_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem precompile_bls_g2add_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem precompile_bls_g2msm_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem precompile_bls_pairing_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem precompile_bls_map_fp_to_g1_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem precompile_bls_map_fp2_to_g2_ignores_extra_domain[simp]:
  ignores_extra_domain precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
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

Theorem get_original_set_original_ignores_extra_domain:
  ignores_extra_domain f ⇒
  ignores_extra_domain
    (do original <- get_original;
        set_original (update_account addr a original);
        f od)
Proof
  rw[ignores_extra_domain_def, bind_def, ignore_bind_def,
     get_original_def, set_original_def, return_def, fail_def]
  \\ gvs[CaseEq"prod", CaseEq"sum", CaseEq"bool"]
  \\ TRY(first_x_assum drule \\ rw[] \\ NO_TAC)
  >- (
    fsrw_tac[DNF_ss][]
    \\ drule domain_compatible_lengths
    \\ simp[] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ rpt disj2_tac
    \\ first_x_assum drule
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`f ss`
    \\ disch_then(qspec_then`ss`mp_tac)
    \\ reverse impl_tac
    >- (
      rw[]
      \\ rpt disj2_tac
      \\ goal_assum drule
      \\ imp_res_tac domain_compatible_lengths
      \\ rpt strip_tac \\ gvs[] )
    \\ qpat_x_assum`!_. _`kall_tac
    \\ qpat_x_assum`!_. _`kall_tac
    \\ qpat_x_assum`domain_compatible _ _`mp_tac
    \\ simp[domain_compatible_def, Abbr`ss`, all_accounts_def,
            states_agree_modulo_accounts_def, set_last_accounts_def]
    \\ qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES \\ gvs[]
    \\ qspec_then`s'.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES \\ gvs[]
    \\ rw[] \\ TRY(CASE_TAC \\ gvs[] \\ rw[])
    \\ gvs[EVERY2_MAP, LIST_REL_SNOC, MAP_SNOC]
    \\ gvs[rollback_states_agree_modulo_accounts_def,
           accounts_agree_modulo_storage_def]
    \\ gvs[rollback_state_component_equality,
           account_state_component_equality,
           update_account_def, APPLY_UPDATE_THM]
    \\ rw[]
    \\ gvs[MAP_FRONT])
QED

Theorem proceed_create_ignores_extra_domain[simp]:
  ignores_extra_domain (proceed_create a b c d e)
Proof
  simp[proceed_create_def]
  \\ irule ignore_bind_ignores_extra_domain \\ rw[]
  \\ irule get_rollback_ignores_extra_domain_bind
  \\ reverse conj_asm2_tac
  >- (
    simp[]
    \\ gen_tac
    \\ irule get_original_set_original_ignores_extra_domain
    \\ tac)
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
  \\ gvs[get_original_def, set_original_def, CaseEq"bool",
         fail_def, return_def]
  \\ qmatch_goalsub_rename_tac`MAP SND s'.contexts`
  \\ `s'.msdomain = s.msdomain` by (
    qpat_x_assum`update_accounts _ _ = _`
      (mp_tac o Q.AP_TERM`λx. (SND x).msdomain`)
    \\ simp[SND_update_accounts_msdomain] )
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
    \\ qmatch_goalsub_abbrev_tac`monad_bind f1 g1 s = monad_bind f2 g2 s`
    \\ sg `monad_bind f2 g2 s = monad_bind f1 g2 s`
    >- (
      `f1 s = f2 s` suffices_by rw[bind_def]
      \\ unabbrev_all_tac
      \\ gvs[lookup_account_def, accounts_agree_modulo_storage_def]
      \\ gvs[account_state_component_equality, fIN_IN]
      \\ gvs[get_delegate_def]
      \\ rw[bind_def]
      \\ CASE_TAC
      \\ CASE_TAC \\ gvs[]
      \\ rw[return_def]
      \\ fsrw_tac[DNF_ss][]
      \\ first_x_assum irule
      \\ gvs[access_address_def, domain_check_def, fIN_IN]
      \\ CCONTR_TAC \\ gvs[fail_def] )
    \\ simp[]
    \\ irule bind_eq \\ simp[] \\ Cases \\ gen_tac \\ strip_tac
    \\ simp[ignore_bind_def, Abbr`g1`, Abbr`g2`]
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
    \\ irule bind_eq \\ simp[] \\ rpt gen_tac \\ strip_tac
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
      \\ qpat_x_assum`_ s = _ s`kall_tac
      \\ gvs[fIN_IN, account_state_component_equality]
      \\ fsrw_tac[DNF_ss][Abbr`f1`,Abbr`f2`]
      \\ first_x_assum irule
      \\ sg `s'.contexts = s.contexts`
      >- (
        Cases_on`get_delegate la.code` \\ gvs[return_def,bind_def]
        \\ gvs[CaseEq"prod",CaseEq"sum"]
        \\ gvs[access_address_def, domain_check_def]
        \\ gvs[COND_RATOR,CaseEq"bool",return_def,fail_def] )
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
    \\ simp[]
    \\ simp[get_delegate_def]
    \\ IF_CASES_TAC \\ simp[]
    \\ ntac 4 (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ gvs[lookup_account_def, accounts_agree_modulo_storage_def]
    \\ gvs[account_state_component_equality, fIN_IN])
  \\ gen_tac
  \\ simp[]
  \\ irule ignores_extra_domain_imp_pred_bind
  \\ reverse conj_tac
  >- (
    simp[]
    \\ reverse conj_tac
    >- (
      CASE_TAC \\ simp[]
      \\ irule bind_ignores_extra_domain
      \\ simp[] )
    \\ rw[]
    \\ ntac 2 $ pop_assum mp_tac \\ CASE_TAC
    \\ gvs[return_def, bind_def]
    \\ CASE_TAC \\ gvs[]
    \\ CASE_TAC \\ gvs[]
    \\ pop_assum mp_tac
    \\ simp[access_address_def, domain_check_def]
    \\ TOP_CASE_TAC \\ rw[return_def, fail_def] \\ gvs[]
    \\ gvs[bind_def, ignore_bind_def, set_domain_def, return_def] )
  \\ Cases
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

Theorem preserves_domain_has_callee_step_blob_hash[simp]:
  preserves_domain_has_callee (K T) step_blob_hash
Proof
  rw[step_blob_hash_def]
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
  ∧ preserves_domain_has_callee (K T) precompile_point_eval
  ∧ preserves_domain_has_callee (K T) precompile_bls_g1add
  ∧ preserves_domain_has_callee (K T) precompile_bls_g1msm
  ∧ preserves_domain_has_callee (K T) precompile_bls_g2add
  ∧ preserves_domain_has_callee (K T) precompile_bls_g2msm
  ∧ preserves_domain_has_callee (K T) precompile_bls_pairing
  ∧ preserves_domain_has_callee (K T) precompile_bls_map_fp_to_g1
  ∧ preserves_domain_has_callee (K T) precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_ecrecover_def,
     precompile_sha2_256_def,
     precompile_ripemd_160_def,
     precompile_identity_def,
     precompile_modexp_def,
     precompile_ecadd_def,
     precompile_ecmul_def,
     precompile_ecpairing_def,
     precompile_blake2f_def,
     precompile_point_eval_def,
     precompile_bls_g1add_def,
     precompile_bls_g1msm_def,
     precompile_bls_g2add_def,
     precompile_bls_g2msm_def,
     precompile_bls_pairing_def,
     precompile_bls_map_fp_to_g1_def,
     precompile_bls_map_fp2_to_g2_def]
  \\ rpt (
    (irule preserves_domain_has_callee_bind ORELSE
     irule preserves_domain_has_callee_ignore_bind)
    \\ rw[])
  \\ CASE_TAC \\ rw[] \\ TRY CASE_TAC \\ rw[]
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
  \\ irule preserves_domain_has_callee_bind \\ simp[]
  \\ reverse conj_tac
  >- (
    CASE_TAC \\ reverse(rw[]) \\ gvs[bind_def]
    >- (
      irule preserves_domain_has_callee_access_address_bind
      \\ rw[] )
    \\ pop_assum mp_tac \\ CASE_TAC
    \\ CASE_TAC \\ rw[return_def]
    \\ first_x_assum irule
    \\ rpt $ pop_assum mp_tac
    \\ simp[access_address_def, domain_check_def]
    \\ TOP_CASE_TAC \\ rw[] \\ gvs[fail_def, return_def,
         bind_def, ignore_bind_def, set_domain_def])
  \\ Cases \\ simp[]
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

Theorem preserves_domain_has_callee_set_original[simp]:
  preserves_domain_has_callee p (set_original a)
Proof
  rw[preserves_domain_has_callee_def, set_original_def]
  \\ gvs[CaseEq"bool", fail_def, return_def]
  \\ gvs[domain_has_callee_def, set_last_accounts_def]
  \\ Cases_on`s.contexts` \\ gvs[]
  \\ Cases_on`h` \\ gvs[] \\ rw[]
  \\ gvs[APPEND_EQ_CONS]
  \\ Cases_on`t` \\ gvs[]
QED

Theorem preserves_domain_has_callee_proceed_create:
  (∀s d. p s ∧ s.msdomain = Enforce d ⇒ b ∈ toSet d.addresses) ∧
  (∀s. p s ⇒ ∀x. p (SND (update_accounts x s))) ∧
  (∀s. p s ⇒ p (SND (get_original s))) ∧
  (∀s. p s ⇒ ∀a. p (SND (set_original a s))) ∧
  (∀s. p s ⇒ ∀cr. (FST cr).msgParams.callee = b ⇒
                   p (s with contexts updated_by CONS cr))
  ⇒
  preserves_domain_has_callee p (proceed_create a b c d e)
Proof
  strip_tac
  \\ rw[proceed_create_def]
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_bind \\ simp[] \\ gen_tac
  \\ irule preserves_domain_has_callee_ignore_bind \\ simp[]
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
  \\ gvs[get_original_def, set_original_def]
  \\ pop_assum mp_tac \\ rw[]
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
